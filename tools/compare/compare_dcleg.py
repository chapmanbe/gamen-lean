#!/usr/bin/env python3
"""Side-by-side comparison of the Haskell and Lean `dcleg-service` binaries.

The service is stateful (a registry of built models), so the corpus is a
list of *sessions*: request sequences, each run through a fresh process of
each binary. Every reply pair is classified:

  identical       byte-for-byte equal lines
  equivalent      equal as JSON, or both `parse_error` replies to a line that
                  is not JSON at all (the message text is each language's
                  JSON library: aeson vs Lean.Json)
  div:<name>      a listed intentional divergence
                  (tools/compare/intentional-divergences.md, dcleg-service):
    div:crash         gamen-hs died on the request (no reply, process exited
                      non-zero); Lean answered `internal_error`        (D1)
    div:premises      the answer depends on the default premise function F,
                      which Lean fixes at single-move and outcome vertices
                      (Gamen.Dcleg.withMovePremises): a `counterfactual` at
                      such a vertex, a `sat`/`true_in` formula containing a
                      counterfactual, or `axiom_check` results that differ only
                      in centering / contemporary_universality /
                      minimal_revision                                 (D2)
    div:build-premises  gamen-hs built a model whose default premises Lean's
                      validateDclegModel rejects (all extra violations are
                      Centering / Contemporary Universality)           (D3)
    div:max_violations  `axiom_check` with max_violations <= 0       (D4)
    div:duplicate-key   the request repeats a JSON key: aeson keeps the
                      first, Lean.Json the last                        (D5)
  after_crash     requests after gamen-hs died in the same session (not
                  compared)
  DISAGREE        anything else: a real difference to investigate

`counterfactual` disagreements at a decision vertex with two or more moves
are DISAGREE: the premise divergence cannot reach them.

Usage:  lake build dcleg-service && python3 tools/compare/compare_dcleg.py [--seed N]
        (writes tools/compare/results-dcleg/; needs gamen-hs's dcleg-service
        built: cabal build dcleg-service in ~/Projects/Logic/Haskell/gamen-hs)
Standard library only.
"""
import argparse
import glob
import json
import random
import subprocess
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent  # the gamen-lean repository
LEAN_BIN = ROOT / ".lake" / "build" / "bin" / "dcleg-service"
HS_DIR = Path.home() / "Projects/Logic/Haskell/gamen-hs"
HS_GLOB = "dist-newstyle/build/*/ghc-*/gamen-*/x/dcleg-service/build/dcleg-service/dcleg-service"
SENTINEL = '{"id":"__sentinel__","op":"ping"}'
PREMISE_AXIOMS = {"centering", "contemporary_universality", "minimal_revision"}


def dumps(o):
    return json.dumps(o, ensure_ascii=False, separators=(",", ":"))


def rq(rid, op, **kw):
    return dumps({"id": str(rid), "op": op, **kw})


# ── formulas ─────────────────────────────────────────────────────────

def f_prop(n): return {"type": "prop", "name": n}


def rand_formula(rng, d, moves, agents=("p1", "p2"), conditional=False, bad_agent=False):
    """Random DCLEG formula. `conditional` allows φ □→ ψ; `bad_agent` lets
    a belief name an agent the model lacks."""
    if d == 0 or rng.random() < 0.25:
        k = rng.randrange(6)
        if k == 0: return rng.choice([{"type": "bot"}, {"type": "top"}])
        if k == 1: return f_prop(rng.choice(["p", "q", "r"]))
        if k == 2: return {"type": "turn", "agent": rng.choice(agents)}
        if k == 3: return {"type": "move", "move": rng.choice(moves)}
        if k == 4: return {"type": "payoff", "value": rng.randint(0, 3), "agent": rng.choice(agents)}
        return f_prop("p")
    sub = lambda: rand_formula(rng, d - 1, moves, agents, conditional, bad_agent)
    ops = ["neg", "or", "and", "implies", "next", "yesterday", "box", "diamond",
           "belief", "plausible"] + (["conditional"] * 2 if conditional else [])
    t = rng.choice(ops)
    if t in ("neg", "next", "yesterday", "box", "diamond"):
        return {"type": t, "operand": sub()}
    if t in ("or", "and", "implies"):
        return {"type": t, "left": sub(), "right": sub()}
    if t in ("belief", "plausible"):
        ag = "p9" if bad_agent and rng.random() < 0.5 else rng.choice(agents)
        return {"type": t, "agent": ag, "operand": sub()}
    return {"type": "conditional", "antecedent": sub(), "consequent": sub()}


def has_conditional(f):
    if isinstance(f, dict):
        return f.get("type") == "conditional" or any(has_conditional(v) for v in f.values())
    if isinstance(f, list):
        return any(has_conditional(v) for v in f)
    return False


# ── models ───────────────────────────────────────────────────────────

class Game:
    """A random game tree, its complete plays as worlds, and the JSON model."""

    def __init__(self, rng, max_depth=3, max_moves=3, players=("p1", "p2"),
                 dox_agents=None, drop_worlds=True):
        self.nodes, self.ends, self.player, self.moves, self.nxt = [], [], {}, {}, {}
        counter = [0]

        def new():
            v = f"v{counter[0]}"; counter[0] += 1; self.nodes.append(v); return v

        def grow(v, depth):
            if depth >= max_depth or (depth > 0 and rng.random() < 0.3):
                self.ends.append(v); return
            self.player[v] = rng.choice(players)
            k = rng.randint(1, max_moves)
            ms = rng.sample(["L", "R", "M", "X"], k)
            self.moves[v] = ms
            for m in ms:
                w = new(); self.nxt[(v, m)] = w; grow(w, depth + 1)

        root = new(); grow(root, 0)
        plays = []

        def walk(v, acc):
            if v in self.ends:
                plays.append((acc, v)); return
            for m in self.moves[v]:
                walk(self.nxt[(v, m)], acc + [(v, m)])

        walk(root, [])
        if drop_worlds and len(plays) > 1:
            plays = rng.sample(plays, rng.randint(max(1, len(plays) // 2), len(plays)))
        self.worlds = [f"g{i}" for i in range(len(plays))]
        self.hist = {g: p for g, p in zip(self.worlds, plays)}
        self.reach = {g: [v for v, _ in p[0]] + [p[1]] for g, p in self.hist.items()}
        self.move_of = {g: dict(p[0]) for g, p in self.hist.items()}
        pairs = [(g, v) for g in self.worlds for v in self.reach[g]]
        self.pairs = pairs
        self.valuation = [{"prop": p, "pairs": [list(x) for x in pairs if rng.random() < 0.4]}
                          for p in ("p", "q")]
        self.dox_agents = list(players) if dox_agents is None else list(dox_agents)
        self.doxastic = []
        for ag in self.dox_agents:
            entries = []
            for v in self.nodes:
                at = [g for g in self.worlds if v in self.reach[g]]
                if not at:
                    continue
                ws = []
                for g in at:
                    succ = [h for h in at if rng.random() < 0.5]
                    if not succ:
                        succ = [rng.choice(at)]
                    ws.append({"world": g, "successors": succ})
                entries.append({"vertex": v, "worlds": ws})
            self.doxastic.append({"agent": ag, "entries": entries})
        self.payoff = [{"agent": ag, "entries": [[v, rng.randint(0, 3)] for v in self.ends]}
                       for ag in players]

    def model(self):
        return {
            "strategic_structure": {
                "nodes": self.nodes, "end_nodes": self.ends,
                "player": [[v, a] for v, a in self.player.items()],
                "moves": [[v, ms] for v, ms in self.moves.items()],
                "next": [[v, m, w] for (v, m), w in self.nxt.items()]},
            "worlds": self.worlds,
            "histories": [{"world": g, "moves": [list(x) for x in p[0]], "end": p[1]}
                          for g, p in self.hist.items()],
            "valuation": self.valuation, "doxastic": self.doxastic, "payoff": self.payoff,
            "premises": "auto"}

    def all_moves(self):
        return sorted({m for ms in self.moves.values() for m in ms}) or ["L"]

    def premise_divergent(self, v):
        """Vertices where Lean's default premises differ from gamen-hs's: outcome
        nodes, and single-move decision vertices reached by more than one world."""
        if v in self.ends:
            return True
        at = [g for g in self.worlds if v in self.reach[g]]
        return len(self.moves.get(v, [])) == 1 and len(at) > 1


SEVEN = {  # the example model of the protocol note §7 (and RegressionIssue18 task 18)
    "strategic_structure": {"nodes": ["v0", "v1", "v2"], "end_nodes": ["v1", "v2"],
                            "player": [["v0", "p1"]], "moves": [["v0", ["L", "R"]]],
                            "next": [["v0", "L", "v1"], ["v0", "R", "v2"]]},
    "worlds": ["gL", "gR"],
    "histories": [{"world": "gL", "moves": [["v0", "L"]], "end": "v1"},
                  {"world": "gR", "moves": [["v0", "R"]], "end": "v2"}],
    "valuation": [{"prop": "p", "pairs": [["gL", "v1"]]}],
    "doxastic": [{"agent": "p1", "entries": [{"vertex": "v0", "worlds": [
        {"world": "gL", "successors": ["gL"]}, {"world": "gR", "successors": ["gR"]}]}]}],
    "payoff": [{"agent": "p1", "entries": [["v1", 1], ["v2", 0]]}],
    "premises": "auto"}


# ── corpus ───────────────────────────────────────────────────────────

def build_corpus(rng):
    """Sessions: (section, [request lines], context) with context giving what
    the classifier needs per request (the Game, if any)."""
    sessions = []

    def add(section, lines, game=None):
        sessions.append((section, lines, game))

    # A. envelope and protocol errors (no model needed)
    add("A envelope", [
        "not json", "{", "[1]", "3", "null", '"s"', '{"op":"ping"}', '{"id":1,"op":"ping"}',
        '{"id":null,"op":"ping"}', '{"id":"2"}', '{"id":"x","op":3}', '{"id":"3","op":"nope"}',
        '{"id":"4","op":"enumerate_counterfactuals"}', '{"id":"5","op":"info"}',
        '{"id":"6","op":"ping","extra":[1,2]}',
        '{"id":"é\\u0001<>&\\u007f\\u2028/\\b\\f\\n\\r\\t\\"\\\\","op":"ping"}',
        '{"id":"7","op":"ping"} trailing', '  {"id":"8","op":"ping"}  ', "   ", "\t", "",
        '{"id":"9","op":"ping","x":1e400}', '{"id":"a","id":"b","op":"ping"}',
        '{"id":"10","op":"sat"}', '{"id":"11","op":"sat","handle":5}',
        '{"id":"12","op":"sat","handle":"none"}', '{"id":"13","op":"drop"}',
        '{"id":"14","op":"drop","handle":"none"}', '{"id":"15","op":"list"}',
        '{"id":"16","op":"true_in","handle":null}', '{"id":"17","op":"axiom_check"}',
        '{"id":"18","op":"counterfactual","handle":"none"}', '{"id":"19","op":"build"}',
        # numbers echoed in details.received, written as Python's json cannot
        '{"id":"20","op":"build","model":{"strategic_structure":{"nodes":[],"end_nodes":[],'
        '"player":[],"moves":[],"next":[]},"worlds":[],"histories":[],'
        '"premises":[1e1025,1e1024,1e-1025,1E400,1.50e1,15e0,-0.0,0.000,123e-2,7E+2]}}',
    ])

    # B. registry: handles, drop, list, generated-handle collisions
    reg = [rq(1, "build", model=SEVEN), rq(2, "build", model=SEVEN, handle="h-1"),
           rq(3, "build", model=SEVEN), rq(4, "build", model=SEVEN),
           rq(5, "build", model=SEVEN, handle="mine"), rq(6, "build", model=SEVEN, handle="mine"),
           rq(7, "list"), rq(8, "drop", handle="h-0"), rq(9, "drop", handle="h-0"),
           rq(10, "sat", handle="h-0", world="gL", vertex="v0", formula={"type": "bot"}),
           rq(11, "build", model=SEVEN, handle=5), rq(12, "build", model=SEVEN, handle=None),
           rq(13, "list"), rq(14, "build", model=SEVEN, strict=True),
           rq(15, "build", model=SEVEN, strict=False), rq(16, "build", model=SEVEN, strict="yes"),
           rq(17, "build", model={**SEVEN, "premises": None}),
           rq(18, "build", model={**SEVEN, "premises": [1.5, 1e10, 0.01, 12345678.9, -3, 0.0,
                                                       True, None, "s", {"b": 1, "a": []}]}),
           rq(19, "build", model={**SEVEN, "premises": "explicit"}),
           rq(20, "build", model=SEVEN, handle="é "), rq(21, "list"),
           rq(22, "drop", handle="mine"), rq(23, "list")]
    add("B registry", reg)

    # C. build validation: JSON shape errors and structural violations
    shape = []
    base = json.loads(dumps(SEVEN))
    mutations = [
        lambda m: m.pop("strategic_structure"), lambda m: m.pop("worlds"),
        lambda m: m.pop("histories"), lambda m: m.update(worlds="x"),
        lambda m: m.update(worlds=[1]), lambda m: m.update(worlds=[None]),
        lambda m: m["strategic_structure"].update(nodes={}),
        lambda m: m["strategic_structure"].update(player=[["a"]]),
        lambda m: m["strategic_structure"].update(player=[5]),
        lambda m: m["strategic_structure"].update(moves=[["a", "b"]]),
        lambda m: m["strategic_structure"].update(next=[["a", "b"]]),
        lambda m: m["strategic_structure"].update(next=[["a", "b", "c", "d"]]),
        lambda m: m["strategic_structure"].update(next=[5]),
        lambda m: m["histories"].append(5), lambda m: m["histories"].append({"world": "g"}),
        lambda m: m["histories"].append({"world": "g", "moves": [["a", 1]], "end": "e"}),
        lambda m: m.update(valuation=5), lambda m: m.update(valuation=None),
        lambda m: m.update(valuation=[{"prop": "p", "pairs": [["a"]]}]),
        lambda m: m.update(doxastic=[{"agent": "a", "entries": [
            {"vertex": "v", "worlds": [{"world": "g", "successors": "x"}]}]}]),
        lambda m: m.update(payoff=[{"agent": "a", "entries": [["v", "1"]]}]),
        lambda m: m.update(payoff=[{"agent": "p1", "entries": [["v1", 1.0], ["v2", 1e2]]}]),
        lambda m: m.update(payoff=[{"agent": "a", "entries": [["v", 1.5]]}]),
        lambda m: m.update(payoff=[{"agent": "a", "entries": [["v", -0.5e-3]]}]),
        lambda m: m.update(payoff=[{"agent": "a", "entries": [["v", 9223372036854775807]]}]),
        lambda m: m.update(payoff=[{"agent": "a", "entries": [["v", 9223372036854775808]]}]),
        lambda m: m.update(payoff=[{"agent": "a", "entries": [["v", 1, 2]]}]),
        # structural / referential violations
        lambda m: m["strategic_structure"]["end_nodes"].append("v9"),
        lambda m: m["strategic_structure"]["player"].append(["v1", "p1"]),
        lambda m: m["strategic_structure"]["moves"].append(["v1", ["X"]]),
        lambda m: m["strategic_structure"]["next"].append(["v0", "Q", "v0"]),
        lambda m: m["strategic_structure"]["next"].append(["v0", "Z", "v7"]),
        lambda m: m["histories"].append({"world": "gZ", "moves": [], "end": "v1"}),
        lambda m: m["histories"].append({"world": "gL", "moves": [["v0", "L"], ["v8", "L"]], "end": "v1"}),
        lambda m: m["doxastic"][0]["entries"][0]["worlds"][1].update(world="gZ", successors=["gZ"]),
        lambda m: m["doxastic"][0]["entries"][0]["worlds"][0].update(successors=["gR"]),
        lambda m: m["doxastic"][0]["entries"][0]["worlds"].pop(),
        lambda m: m["payoff"].append({"agent": "p2", "entries": []}),
        lambda m: m["strategic_structure"]["nodes"].remove("v2"),
        # histories that disagree with the structure (D3)
        lambda m: m["histories"][1].update(moves=[["v0", "X"]]),
        lambda m: m["histories"][1].update(end="v0", moves=[]),
    ]
    for i, mut in enumerate(mutations):
        m = json.loads(dumps(base)); mut(m)
        shape.append(rq(i, "build", model=m))
    shape.append(rq("n", "build", model=5))
    shape.append(rq("s", "build", model=SEVEN, strict=True, handle="x"))
    add("C build-validation", shape)
    for _ in range(40):  # random invalid structures
        g = Game(rng)
        m = g.model()
        k = rng.randrange(6)
        if k == 0: m["strategic_structure"]["end_nodes"].append(rng.choice(g.nodes))
        if k == 1 and m["strategic_structure"]["player"]: m["strategic_structure"]["player"].pop()
        if k == 2: m["worlds"].pop()
        if k == 3 and m["doxastic"][0]["entries"]: m["doxastic"][0]["entries"][0]["worlds"][0]["successors"] = ["gX"]
        if k == 4: m["payoff"][0]["entries"] = m["payoff"][0]["entries"][1:]
        if k == 5: m["strategic_structure"]["next"].append([g.nodes[0], "Q", "v99"])
        add("C build-validation", [rq(0, "build", model=m)], g)

    # D. sat / true_in without counterfactuals: must be identical
    for _ in range(60):
        g = Game(rng)
        lines = [rq("b", "build", model=g.model(), handle="m")]
        for j in range(15):
            f = rand_formula(rng, 3, g.all_moves())
            if rng.random() < 0.85:
                gamma, v = rng.choice(g.pairs)
            else:
                gamma, v = rng.choice(g.worlds), rng.choice(g.nodes + ["vX"])
                gamma = rng.choice([gamma, "gX"])
            lines.append(rq(j, "sat", handle="m", world=gamma, vertex=v, formula=f))
        for j in range(5):
            lines.append(rq(f"t{j}", "true_in", handle="m",
                            formula=rand_formula(rng, 3, g.all_moves())))
        add("D sat/true_in", lines, g)

    # E. sat / true_in with counterfactuals inside
    for _ in range(30):
        g = Game(rng)
        lines = [rq("b", "build", model=g.model(), handle="m")]
        for j in range(10):
            gamma, v = rng.choice(g.pairs)
            lines.append(rq(j, "sat", handle="m", world=gamma, vertex=v,
                            formula=rand_formula(rng, 3, g.all_moves(), conditional=True)))
        lines.append(rq("t", "true_in", handle="m",
                        formula=rand_formula(rng, 3, g.all_moves(), conditional=True)))
        add("E sat-conditional", lines, g)

    # F. counterfactual
    for _ in range(50):
        g = Game(rng)
        lines = [rq("b", "build", model=g.model(), handle="m")]
        for j in range(12):
            gamma, v = rng.choice(g.pairs)
            kw = {}
            if rng.random() < 0.5: kw["return_witnesses"] = rng.random() < 0.7
            mv = g.all_moves()
            ant = ({"type": "move", "move": rng.choice(mv)} if rng.random() < 0.5
                   else rand_formula(rng, 2, mv))
            lines.append(rq(j, "counterfactual", handle="m", world=gamma, vertex=v,
                            antecedent=ant, consequent=rand_formula(rng, 2, mv), **kw))
        lines.append(rq("u", "counterfactual", handle="m", world="gX", vertex="v0",
                        antecedent={"type": "bot"}, consequent={"type": "bot"}))
        lines.append(rq("w", "counterfactual", handle="m", world=g.worlds[0]))
        lines.append(rq("x", "counterfactual", handle="m", world=g.worlds[0], vertex="v0",
                        antecedent={"type": "nope"}, consequent={"type": "bot"}))
        add("F counterfactual", lines, g)

    # G. axiom_check
    for _ in range(80):
        g = Game(rng, players=("p1", "p2"))
        lines = [rq("b", "build", model=g.model(), handle="m")]
        lines.append(rq("all", "axiom_check", handle="m"))
        for j in range(4):
            kw = {}
            if rng.random() < 0.7:
                kw["axioms"] = rng.sample(["presence", "present_seriality", "transitivity",
                                           "euclideanness", "self_awareness",
                                           "intentional_awareness", "centering",
                                           "contemporary_universality", "minimal_revision",
                                           "expectational_continuity", "recall"],
                                          rng.randint(0, 4))
            if rng.random() < 0.6:
                kw["max_violations"] = rng.choice([1, 2, 3, 5, 100, "x", 2.0, 2.5])
            lines.append(rq(j, "axiom_check", handle="m", **kw))
        lines.append(rq("u", "axiom_check", handle="m", axioms=["presence", "bogus", "x"]))
        lines.append(rq("s", "axiom_check", handle="m", axioms="presence"))
        add("G axiom_check", lines, g)
    for model in (SEVEN,):
        add("G axiom_check", [rq("b", "build", model=model, handle="m"),
                              rq("a", "axiom_check", handle="m")])

    # H. max_violations <= 0 (D4)
    for _ in range(10):
        g = Game(rng)
        add("H max_violations<=0", [rq("b", "build", model=g.model(), handle="m"),
                                    rq("z", "axiom_check", handle="m",
                                       max_violations=rng.choice([0, -1]))], g)

    # I. requests on which gamen-hs crashes (D1): last in their session
    for _ in range(15):
        g = Game(rng)
        gamma, v = rng.choice(g.pairs)
        add("I crash", [rq("b", "build", model=g.model(), handle="m"),
                        rq("c", "sat", handle="m", world=gamma, vertex=v,
                           formula={"type": "belief", "agent": "p9", "operand": {"type": "bot"}})], g)
    for _ in range(10):
        g = Game(rng, dox_agents=["p1"], players=("p1", "p2"))
        add("I crash", [rq("b", "build", model=g.model(), handle="m"),
                        rq("c", "axiom_check", handle="m",
                           axioms=["self_awareness", "intentional_awareness"])], g)
    return sessions


# ── run and classify ─────────────────────────────────────────────────

def run(binary, lines):
    """One process per session. Each request is followed by a sentinel ping,
    so that lines with no reply (empty lines) keep alignment. Replies are
    split on newline only: a reply may contain U+2028, which Python's
    splitlines would also split on."""
    stream = []
    for ln in lines:
        stream.append(ln)
        stream.append(SENTINEL)
    proc = subprocess.run([str(binary)], input="\n".join(stream) + "\n",
                          capture_output=True, text=True, timeout=600)
    outs, cur = [], []
    for out in proc.stdout.split("\n"):
        if out == "":
            continue
        if '"__sentinel__"' in out:
            outs.append(cur[0] if cur else None)
            cur = []
        else:
            cur.append(out)
    done = len(outs)  # requests fully answered (their sentinel came back)
    while len(outs) < len(lines):
        outs.append(None)
    return outs, done, proc.returncode, proc.stderr


def is_json(line):
    try:
        json.loads(line)
        return True
    except json.JSONDecodeError:
        return False


def has_dup_key(line):
    dup = [False]

    def hook(pairs):
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            dup[0] = True
        return dict(pairs)
    try:
        json.loads(line, object_pairs_hook=hook)
    except json.JSONDecodeError:
        return False
    return dup[0]


def classify(req_line, hs, ln, game, hs_crashed_here):
    if hs == ln:
        return "identical"
    if hs is None:
        if hs_crashed_here and ln is not None:
            l = json.loads(ln)
            if l.get("ok") is False and l.get("error", {}).get("code") == "internal_error":
                return "div:crash"
        return "DISAGREE"
    if ln is None:
        return "DISAGREE"
    h, l = json.loads(hs), json.loads(ln)
    if h == l:
        return "equivalent"
    if has_dup_key(req_line):
        return "div:duplicate-key"
    he, le = h.get("error") or {}, l.get("error") or {}
    if (not is_json(req_line) and he.get("code") == le.get("code") == "parse_error"
            and "id" not in h and "id" not in l):
        return "equivalent"
    r = json.loads(req_line)
    op = r.get("op")
    if op == "axiom_check" and h.get("ok") and l.get("ok"):
        mv = r.get("max_violations")
        if isinstance(mv, int) and not isinstance(mv, bool) and mv <= 0:
            return "div:max_violations"
        hr, lr = h["result"], l["result"]
        diff = {k for k in set(hr) | set(lr) if hr.get(k) != lr.get(k)}
        if diff and diff <= PREMISE_AXIOMS:
            return "div:premises"
    if op == "counterfactual" and game is not None and game.premise_divergent(r.get("vertex")):
        return "div:premises"
    if op in ("sat", "true_in") and has_conditional(r.get("formula")):
        return "div:premises"
    if op == "build" and h.get("ok") and le.get("code") == "model_invalid":
        vs = le.get("details", {}).get("violations", [])
        if vs and all("Centering" in v or "Contemporary Universality" in v for v in vs):
            return "div:build-premises"
    return "DISAGREE"


def find_hs_bin():
    hits = sorted(glob.glob(str(HS_DIR / HS_GLOB)))
    if not hits:
        sys.exit(f"gamen-hs dcleg-service not built (looked for {HS_DIR / HS_GLOB}); "
                 "run `cabal build dcleg-service` in gamen-hs")
    return hits[-1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261006)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    if not LEAN_BIN.exists():
        sys.exit(f"{LEAN_BIN} missing; run `lake build dcleg-service`")
    hs_bin = find_hs_bin()
    sessions = build_corpus(rng)

    results = HERE / "results-dcleg"
    results.mkdir(exist_ok=True)
    cols = ["identical", "equivalent", "div:crash", "div:premises", "div:build-premises",
            "div:max_violations", "div:duplicate-key", "after_crash", "DISAGREE"]
    per_section, disagreements, nreq = {}, [], 0
    with open(results / "corpus.jsonl", "w") as corpus:
        for section, lines, game in sessions:
            nreq += len(lines)
            for ln_ in lines:
                corpus.write(dumps({"section": section, "request": ln_}) + "\n")
            hs_out, hs_done, hs_code, _ = run(hs_bin, lines)
            ln_out, _, ln_code, ln_err = run(LEAN_BIN, lines)
            if ln_code != 0:
                disagreements.append({"section": section, "lean_exit": ln_code, "stderr": ln_err})
            # gamen-hs died if it exited non-zero, on the first request whose
            # sentinel never came back.
            crash_at = hs_done if hs_code != 0 else None
            cnt = per_section.setdefault(section, Counter())
            for i, (req_line, h, l) in enumerate(zip(lines, hs_out, ln_out)):
                if crash_at is not None and i > crash_at:
                    c = "after_crash"
                else:
                    c = classify(req_line, h, l, game, crash_at == i)
                cnt[c] += 1
                if c == "DISAGREE":
                    disagreements.append({"section": section, "request": req_line,
                                          "haskell": h, "lean": l})

    with open(results / "disagreements.jsonl", "w") as fh:
        for d in disagreements:
            fh.write(json.dumps(d, ensure_ascii=False) + "\n")

    short = {c: c.replace("div:", "")[:11] for c in cols}
    total = Counter()
    rows = [f"{'section':<22}" + "".join(f"{short[c]:>12}" for c in cols)]
    for section, cnt in per_section.items():
        total.update(cnt)
        rows.append(f"{section:<22}" + "".join(f"{cnt[c]:>12}" for c in cols))
    rows.append(f"{'TOTAL':<22}" + "".join(f"{total[c]:>12}" for c in cols))
    summary = "\n".join(rows)
    summary += f"\n\nsessions: {len(sessions)}   requests: {nreq}   seed: {args.seed}"
    summary += f"\nhaskell: {hs_bin}"
    (results / "summary.txt").write_text(summary + "\n")
    print(summary)
    return 1 if disagreements else 0


if __name__ == "__main__":
    sys.exit(main())
