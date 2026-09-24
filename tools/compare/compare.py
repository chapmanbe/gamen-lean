#!/usr/bin/env python3
"""Side-by-side comparison of the Haskell and Lean `gamen-validate` binaries.

Builds a corpus of JSON Lines requests, sends the identical stream to each
binary, and classifies every response pair:

  identical     byte-for-byte equal lines
  equivalent    equal as JSON, or both are parser errors whose message text
                comes from each language's JSON library (aeson vs Lean.Json)
  scope_gap     Lean answered "not ported in Lean slice" (the request needs
                the doxastic, ranking, or deontic-STIT backends)
  DISAGREE      anything else: a real difference to investigate

Usage:  lake build gamen-validate && python3 tools/compare/compare.py [--seed N]
        (writes tools/compare/results/; needs gamen-hs built at ~/Projects/Logic/Haskell/gamen-hs)
Standard library only.
"""
import argparse
import json
import random
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent  # the gamen-lean repository
LEAN_BIN = ROOT / ".lake" / "build" / "bin" / "gamen-validate"
HS_DIR = Path.home() / "Projects/Logic/Haskell/gamen-hs"
GUIDELINE_DATA = Path.home() / "Projects/Logic/Julia/guideline-validation/data"

# ── formula builders ─────────────────────────────────────────────────

def atom(n): return {"type": "atom", "name": n}
def un(t, f): return {"type": t, "operand": f}
def bi(t, l, r): return {"type": t, "left": l, "right": r}
def ag(t, a, f): return {"type": t, "agent": a, "operand": f}
def ags(t, a, f): return {"type": t, "agents": a, "operand": f}

UNARY = ["not", "box", "diamond", "future_box", "future_diamond", "past_box",
         "past_diamond", "group_stit", "next"]
BINARY = ["and", "or", "implies", "iff", "since", "until", "announce"]
AGENT = ["knowledge", "belief", "stit", "choice_diamond", "ought", "permitted"]
AGENTS = ["coalition", "can_next", "can_always", "can_eventually"]


def one_of_each():
    """One formula per constructor: all 30 tree-format types."""
    p, q = atom("p"), atom("q")
    fs: list[dict] = [{"type": "bot"}, p]
    fs += [un(t, p) for t in UNARY]
    fs += [bi(t, p, q) for t in BINARY]
    fs += [ag(t, "a", p) for t in AGENT]
    fs.append({"type": "ranked_belief", "agent": "a", "rank": -2, "operand": p})
    fs += [ags(t, ["a", "b"], p) for t in AGENTS]
    fs.append({"type": "can_until", "agents": ["a"], "left": p, "right": q})
    return fs


def rand_any(rng, d):
    """Random formula over all 30 constructors (for codec round-trips)."""
    if d == 0 or rng.random() < 0.25:
        return rng.choice([{"type": "bot"}, atom(rng.choice(["p", "q", "r", "statin", "β"]))])
    k = rng.randrange(6)
    if k == 0: return un(rng.choice(UNARY), rand_any(rng, d - 1))
    if k == 1: return bi(rng.choice(BINARY), rand_any(rng, d - 1), rand_any(rng, d - 1))
    if k == 2: return ag(rng.choice(AGENT), rng.choice(["a", "clinician"]), rand_any(rng, d - 1))
    if k == 3: return {"type": "ranked_belief", "agent": "a", "rank": rng.randint(-3, 3),
                       "operand": rand_any(rng, d - 1)}
    if k == 4: return ags(rng.choice(AGENTS), rng.sample(["a", "b", "c"], rng.randint(0, 2)),
                          rand_any(rng, d - 1))
    return {"type": "can_until", "agents": ["a"], "left": rand_any(rng, d - 1),
            "right": rand_any(rng, d - 1)}


def rand_k(rng, d, atoms=("p", "q", "r")):
    """Random formula in the ported consistency fragment: propositional + □/◇."""
    if d == 0 or rng.random() < 0.3:
        return rng.choice([{"type": "bot"}] + [atom(a) for a in atoms] * 3)
    t = rng.choice(["not", "not", "box", "box", "diamond", "diamond",
                    "and", "or", "implies", "iff"])
    if t in ("not", "box", "diamond"):
        return un(t, rand_k(rng, d - 1, atoms))
    return bi(t, rand_k(rng, d - 1, atoms), rand_k(rng, d - 1, atoms))


def req(action, **kw):
    return json.dumps({"action": action, **kw}, ensure_ascii=False)


# ── corpus ───────────────────────────────────────────────────────────

def guideline_flat_formulas():
    """Flat-format formulas from guideline-validation's extracted YAML.

    Minimal parser for the `formula:` blocks, which are indented
    `key: "value"` lines; avoids a PyYAML dependency."""
    out = []
    for path in sorted(GUIDELINE_DATA.glob("*.yaml")):
        lines = path.read_text().splitlines()
        i = 0
        while i < len(lines):
            m = re.match(r"^(\s*)formula:\s*$", lines[i])
            if not m:
                i += 1
                continue
            indent = len(m.group(1))
            block = {}
            i += 1
            while i < len(lines):
                km = re.match(r'^(\s*)([a-z_]+):\s*"?([^"#]*?)"?\s*$', lines[i])
                if not km or len(km.group(1)) <= indent:
                    break
                block[km.group(2)] = km.group(3)
                i += 1
            if "op" in block:
                out.append((path.name, block))
    return out


def build_corpus(rng):
    sections = []

    def add(section, lines):
        sections.extend((section, ln) for ln in lines)

    # A. Protocol envelope and error handling
    add("A envelope", [
        req("ping"),
        '{"action": "ping", "extra": 1}',
        "not json",
        "[1, 2]",
        '{"no_action": true}',
        req("frobnicate"),
        req("check_consistency"),
        req("check_consistency", formulas="p"),
        req("check_consistency", formulas=[]),
        req("check_consistency", formulas=[{"type": "bogus"}]),
        req("check_consistency", formulas=[{"name": "p"}]),
        req("validate_formula"),
        req("validate_formula", formula={"type": "bogus"}),
        req("validate_formula", formula={"type": "atom"}),
        req("validate_formula", formula=42),
        req("validate_agent", formula=atom("p")),
        req("validate_agent", formula=atom("p"), agent=7),
        "   ",
        '{"action":"ping"}\r',
    ])

    # B. Codec: every constructor, then random trees over all 30
    add("B codec-each", [req("validate_formula", formula=f) for f in one_of_each()])
    add("B codec-random", [req("validate_formula", formula=rand_any(rng, 4)) for _ in range(500)])

    # C. Flat extraction format: every op/agent/temporal/conditional combination
    flat = []
    for op in ["box", "diamond", "box_not", "weird"]:
        for agent in [None, "clinician"]:
            for temp in [None, "future_box", "future_diamond", "periodic", "sometimes"]:
                for cond in [None, "ascvd"]:
                    f: dict = {"op": op, "atom": "statin"}
                    if agent: f["agent"] = agent
                    if temp: f["temporal_op"] = temp
                    if cond: f["conditional"] = cond
                    flat.append(f)
    flat.append({"op": "box"})                       # missing atom
    flat.append({"op": "box", "atom": "x", "agent": None})   # null agent
    flat.append({"type": "atom", "name": "t", "op": "box", "atom": "o"})  # both keys
    add("C flat", [req("validate_formula", formula=f) for f in flat])
    add("C flat-consistency", [req("check_consistency", formulas=[f]) for f in flat])

    # D. check_consistency on the ported K fragment (random sets)
    add("D consistency-K", [
        req("check_consistency", formulas=[rand_k(rng, rng.randint(1, 4))
                                           for _ in range(rng.randint(1, 4))])
        for _ in range(2000)])
    # D'. Mixed sets: fragment rejections and scope gaps
    mixed = []
    for _ in range(300):
        fs = [rand_k(rng, 2) for _ in range(rng.randint(1, 3))]
        fs.insert(rng.randrange(len(fs) + 1), rand_any(rng, 2))
        mixed.append(req("check_consistency", formulas=fs))
    add("D consistency-mixed", mixed)

    # D''. Explicit regression: GroupStit must not be treated as an agent
    # operator via its operand (Formula.hs:230 excludes it outright, unlike
    # Stit/ChoiceDiamond/Ought/Permitted/.../CanUntil, which recurse). Both
    # backends agree the operator itself is unsupported either way, but the
    # *prover* named in the error message differs ("kdt+doxasticD" if
    # hasAgentOperator is False as it should be, "deontic-stit" if a
    # regression makes it recurse into Stit) -- exercising the dispatch,
    # not just the fragment gate.
    add("D consistency-groupstit-regression", [
        req("check_consistency", formulas=[un("group_stit", ag("stit", "a", atom("p")))])
    ])

    # E. check_pairwise
    add("E pairwise-K", [
        req("check_pairwise", formulas=[rand_k(rng, 3) for _ in range(rng.randint(0, 6))])
        for _ in range(300)])
    add("E pairwise-mixed", [
        req("check_pairwise", formulas=[rand_k(rng, 2), un("future_box", atom("p")),
                                        rand_k(rng, 2)])
        for _ in range(20)])

    # F. validate_agent heuristic
    agent_lines = []
    for a in ["clinician", "patient", "joint"]:
        for at in ["take_statin", "fill_rx", "lipid_profile", "exercise_regular"]:
            agent_lines.append(req("validate_agent", formula=bi("and", atom(at), atom("q")), agent=a))
    add("F validate_agent", agent_lines)

    # G. Real guideline extractions (guideline-validation/data/*.yaml)
    g = guideline_flat_formulas()
    add("G guideline-validate", [req("validate_formula", formula=f) for _, f in g])
    add("G guideline-consistency", [req("check_consistency", formulas=[f]) for _, f in g])
    by_file = {}
    for name, f in g:
        by_file.setdefault(name, []).append(f)
    add("G guideline-set", [req("check_consistency", formulas=fs) for fs in by_file.values()])
    add("G guideline-pairwise", [req("check_pairwise", formulas=fs) for fs in by_file.values()])
    no_agent = [f for _, f in g if "agent" not in f]
    add("G guideline-noagent-pairwise",
        [req("check_pairwise", formulas=no_agent[i:i + 12]) for i in range(0, len(no_agent), 12)])

    # H. Plain belief (no ranked belief, no agent operator) on the KDt +
    # doxastic-D system. Added with the Doxastic wiring: no earlier section
    # sends a belief-only set down the tableau path. Last in the corpus so
    # its random draws leave every earlier section unchanged.
    # Mostly agent "a" over atoms p, q, with belief in both a formula and its
    # negation common enough that the doxastic D rule decides many sets.
    def rand_belief(d):
        if d == 0 or rng.random() < 0.3:
            return rand_k(rng, 1, atoms=("p", "q"))
        k = rng.randrange(5)
        if k <= 1:
            f = rand_belief(d - 1)
            if rng.random() < 0.4:
                f = un("not", f)
            return ag("belief", "a" if rng.random() < 0.8 else "b", f)
        if k == 2:
            return un("not", rand_belief(d - 1))
        return {"type": rng.choice(["and", "or", "implies"]),
                "left": rand_belief(d - 1), "right": rand_belief(d - 1)}
    p, q = atom("p"), atom("q")
    Ba = lambda f: ag("belief", "a", f)
    add("H consistency-belief", [
        req("check_consistency", formulas=[Ba(p), Ba(un("not", p))]),
        req("check_consistency", formulas=[Ba(p), un("not", p)]),
        req("check_consistency", formulas=[Ba(p), ag("belief", "b", un("not", p))]),
        req("check_consistency", formulas=[Ba({"type": "and", "left": p, "right": un("not", p)})]),
        req("check_consistency", formulas=[Ba(ag("belief", "b", q)), un("not", Ba(ag("belief", "b", q)))]),
        req("check_consistency", formulas=[un("box", Ba(p)), un("diamond", Ba(un("not", p)))]),
    ] + [req("check_consistency", formulas=[rand_belief(3) for _ in range(rng.randint(1, 4))])
         for _ in range(300)])
    add("H pairwise-belief", [
        req("check_pairwise", formulas=[Ba(p), q, Ba(un("not", p))]),
    ] + [req("check_pairwise", formulas=[rand_belief(3) for _ in range(rng.randint(2, 5))])
         for _ in range(100)])
    return sections


# ── run and classify ─────────────────────────────────────────────────

def run(binary, lines):
    """One process per binary, all lines through stdin, as the downstream
    projects use it. Empty/whitespace lines may produce no output line, so
    each request is paired with a ping sentinel to keep alignment."""
    stream = []
    for ln in lines:
        stream.append(ln)
        stream.append('{"action":"__sentinel__"}')
    proc = subprocess.run([str(binary)], input="\n".join(stream) + "\n",
                          capture_output=True, text=True, timeout=1800)
    outs, cur = [], []
    for out in proc.stdout.splitlines():
        if "__sentinel__" in out:
            outs.append(cur[0] if cur else None)
            cur = []
        else:
            cur.append(out)
    return outs, proc.stderr


def is_library_parse_error(resp):
    """Errors whose text comes from the JSON library, not from gamen."""
    if resp.get("ok") is False:
        e = resp.get("error", "")
        return not (e.startswith("unsupported operator") or e.startswith("not ported"))
    return False


def classify(hs, ln):
    if hs == ln:
        return "identical"
    if hs is None or ln is None:
        return "DISAGREE"
    try:
        h, l = json.loads(hs), json.loads(ln)
    except json.JSONDecodeError:
        return "DISAGREE"
    if h == l:
        return "equivalent"
    if l.get("ok") is False and l.get("error", "").startswith("not ported in Lean slice"):
        return "scope_gap"
    if is_library_parse_error(h) and is_library_parse_error(l):
        return "equivalent"
    hr, lr = h.get("result"), l.get("result")
    if (isinstance(hr, dict) and isinstance(lr, dict) and "parse_error" in hr
            and "parse_error" in lr and hr.get("valid") == lr.get("valid") is False):
        return "equivalent"
    return "DISAGREE"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260923)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    hs_bin = subprocess.run(["cabal", "list-bin", "gamen-validate"], cwd=HS_DIR,
                            capture_output=True, text=True, check=True).stdout.strip()
    corpus = build_corpus(rng)
    lines = [ln for _, ln in corpus]

    hs_out, hs_err = run(hs_bin, lines)
    ln_out, ln_err = run(LEAN_BIN, lines)

    results = HERE / "results"
    results.mkdir(exist_ok=True)
    (results / "corpus.jsonl").write_text("\n".join(lines) + "\n")

    per_section = {}
    disagreements = []
    for (section, line), h, l in zip(corpus, hs_out, ln_out):
        c = classify(h, l)
        per_section.setdefault(section, Counter())[c] += 1
        if c == "DISAGREE":
            disagreements.append({"section": section, "request": line,
                                  "haskell": h, "lean": l})

    with open(results / "disagreements.jsonl", "w") as fh:
        for d in disagreements:
            fh.write(json.dumps(d, ensure_ascii=False) + "\n")

    cols = ["identical", "equivalent", "scope_gap", "DISAGREE"]
    total = Counter()
    rows = [f"{'section':<30}" + "".join(f"{c:>12}" for c in cols)]
    for section, cnt in per_section.items():
        total.update(cnt)
        rows.append(f"{section:<30}" + "".join(f"{cnt[c]:>12}" for c in cols))
    rows.append(f"{'TOTAL':<30}" + "".join(f"{total[c]:>12}" for c in cols))
    summary = "\n".join(rows)
    summary += f"\n\nrequests: {len(lines)}   seed: {args.seed}"
    summary += f"\nstderr bytes: haskell {len(hs_err)}, lean {len(ln_err)}"
    (results / "summary.txt").write_text(summary + "\n")
    print(summary)
    return 1 if disagreements else 0


if __name__ == "__main__":
    sys.exit(main())
