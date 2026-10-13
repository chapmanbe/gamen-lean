import Validate.BuildInfo

/-!
# gamen-validate (Lean port)

Port of `gamen-hs/validate/Main.hs`: a JSON Lines service on stdin/stdout.

    {"action": "ping"}
    {"action": "version"}                       (Lean-only; see below)
    {"action": "check_consistency", "formulas": [...]}
    {"action": "validate_formula", "formula": {...}}
    {"action": "validate_agent", "formula": {...}, "agent": "clinician"}
    {"action": "check_pairwise", "formulas": [...]}
    {"action": "atl_model_check", "model": {...}, "formulas": [...]}   (Lean-only; see below)
    {"action": "epistemic_check", "model": {...}, "updates": [...], "formulas": [...]}   (Lean-only)
    {"action": "atl_update_search", "model": {...}, "state": "q0", "goal": {...}, "bound": 2}   (Lean-only)

Responses are `{"ok": true, "result": ...}` or `{"ok": false, "error": "..."}`.

**`version` (Lean-only, protocol 1).** Answers
`{"ok":true,"result":{"commit":"<rev>","implementation":"gamen-lean","protocol":1}}`
(keys in the order Lean's `Json.compress` writes them), so a caller can
check which binary answered: both implementations answer `ping` with the
same `"pong"`, and gamen-hs answers `version` with
`{"error":"Error in $: Unknown action: version","ok":false}` (checked
against gamen-hs's binary, 2026-09-30). The other five actions
are unchanged. Plan: `plans/downstream-migration-2026-09-29.md`, Phase 0a.

**`atl_model_check` (Lean-only, protocol 2; issue #2).** Model-checks ATL
formulas (tree format: `can_next`, `can_always`, `can_eventually`, `can_until`,
`coalition`, plus propositional) on a concurrent game structure given as JSON.
Model spec and validation: `Gamen/CgsJson.lean`. Optional fields: `states`
(states to report; default all) and `semantics` (`perfect`, the default,
`imperfect_subjective` or `imperfect_objective`; the latter two use the model's
`indistinguishable` classes, singletons by default). Reply result:
`{"semantics", "states", "results": [{"index", "formula", "satisfying", "holds",
"true_in_model"} | {"index", "formula", "error"}]}`; an unsupported operator is a
per-formula `error`. A bad model or `states` entry fails the whole request with
`{"ok":false,"error":msg,"error_code":code}`; codes: `malformed_spec`,
`unknown_state`, `unknown_agent`, `unknown_move`, `empty_moves`, `missing_moves`,
`incomplete_joint_move`, `duplicate_transition`, `missing_transition`,
`duplicate_state`, `duplicate_agent`, `invalid_cgs`, `overlapping_classes`,
`invalid_indistinguishability`. Tests: `Tests/ValidateAtl.lean`.

**ATL-D and ATEL-D (Lean-only, protocols 3 and 4; issue #3).** `"dynamic": true` makes
`atl_model_check` read its formulas as ATL-D/ATEL-D (`Gamen.Atl.Dynamic`; Galimullin,
Grosinger & Mittelmann, KR 2026): tree format plus `{"type":"has","agent","action"}`,
`{"type":"knowledge","agent","operand"}`,
`{"type":"grant"|"revoke","updates":[{"condition":F,"action","agents","informed"?}],"operand":F}`
and `can_release` (`left`, `right`). `informed` (optional) lists agents who learn the
condition without gaining or losing the action. `semantics` picks how `⟨⟨A⟩⟩` quantifies:
`perfect` (default; ATL-D), `imperfect_subjective` or `imperfect_objective` (memoryless
uniform strategies over the model's `indistinguishable` classes). ATEL-D means
`imperfect_subjective` (the extended paper's Example 2; it matches `atlirSat`); objective
is offered for comparison. The reply's `semantics`
carries a `_dynamic` suffix. The model may add `"actions": [...]` (the whole action universe)
and `"default_next": {"stay":true}` or `{"state":"s"}` (the successor of every unlisted
joint move). Without a default, an update that enables a joint move with no listed
successor is a per-formula error, even if the operand never uses that move. Extra error codes:
`unknown_action`, `semantics_mismatch`. `semantics: perfect` is refused (`semantics_mismatch`) on
a model with indistinguishable states, since it would read `K_a` by them and `⟨⟨A⟩⟩` without them.
`"dynamic"` must be a boolean. An update needs at least one clause. Coalitions naming an unknown
agent are an error.
Tests: `Tests/AtlDynamic.lean` (the paper's Example 1, plus ATEL-D).

**`epistemic_check` (Lean-only, protocol 5; issue #3 item 3).** Evaluates epistemic formulas
(tree format: `knowledge`, `announce`, connectives, atoms) on a model given as JSON
(`Gamen.EpistemicJson`: `worlds`, `agents`, `relations` edges and/or `indistinguishable`
classes, `valuation` world → atoms), after an optional sequence of DEL updates
(`Gamen.ActionModel`; Lorini, Perrotin & Schwarzentruber, KR 2022). Each update is an
explicit action model (`events`, `relations` with an entry for every agent, `pre`, `post`)
or a builder (`public_announcement`, `semi_private_whether`, `private_announcement`), plus
an optional `"event"`. Without `"event"`, public and private announcements run `!`, and
otherwise the unique event executable at each world is used (two executable events:
`ambiguous_event`). Optional `worlds` restricts the report. Reply:
`{"worlds", "updates", "results": [{"index","formula","satisfying","holds","not_executable"}
| {"index","formula","error"}]}`; worlds are original names, `not_executable` lists where
some update's event could not run (`holds` is `null` there), and an unsupported operator is a
per-formula `error`. Error codes: `malformed_spec`, `unknown_world`, `unknown_agent`,
`duplicate_world`, `duplicate_agent`, `overlapping_classes`, `invalid_formula`, `invalid_action_model`,
`unknown_event`, `ambiguous_event`, `update_failed`. In `indistinguishable`, a world in no class is alone in its class. An action model is one builder or explicit fields, not a mix. A builder's `group` must be agents of the model. Repeated JSON object keys keep the last one, as everywhere in `gamen-validate` (`tools/compare/intentional-divergences.md`, D5). Tests: `Tests/ValidateEpistemic.lean`.

**`atl_update_search` (Lean-only, protocol 6; issue #3 item 1).** The bounded update existence
problem of the ATL-D paper (Def 7): is there a sequence of updates of at most `bound`
clauses after which the ATL-D/ATEL-D `goal` holds at `state`? `model` and `semantics` as
for `atl_model_check` with `"dynamic": true`. The search is over a finite candidate `pool`,
not over every possible condition formula: `pool` is optional (default: every `⊤`/atom/`¬atom`
condition × action × single agent × grant/revoke) and is
`[{"kind":"grant"|"revoke","condition":F,"action","agents","informed"?}]`; the size of a
sequence is its number of clauses. `fuel` (default 100000) caps the clause sets tried. Reply:
`{"found":false,"explored","illegal","semantics","complete_for"}` or `{"found":true,"size",
"updates":[{"kind","clauses":[...]}],"formula","witness",…}`, where `witness` is the goal
wrapped in the found updates, as a tree-format formula to pass to `atl_model_check`. A
`found:false` means no sequence over this pool within the bound, not that none exists.
Updates that would be errors (a grant enabling a joint move with no listed successor, an
update that breaks `∼`) are not legal moves and are counted in `illegal`. Budget exhaustion is
`error_code: search_failed`; an unknown `state`, pool action or pool agent has its own code
(`unknown_state`, `unknown_action`, `unknown_agent`), and `bound` above 1000 is `bound_too_large`.
The default pool has no informed-only clauses; pass a pool for those. An error evaluating the goal
at any visited model aborts the search. Tests: `Tests/UpdateSearch.lean`.

**Backends.** gamen-hs dispatches consistency checks to two backends:
the KDt tableau with its doxastic-D and ranking-theory rules (for
`belief`/`ranked_belief`), and the deontic-STIT prover G3DS (for agent
operators). Both are ported. Fragment rejections ("unsupported operator …")
happen before dispatch and are fully ported. The one Lean-only reply,
`"prover error: …"`, is unreachable (see `classifyConsistency`).

There is no `deepseq` crash guard: the Lean code has no `error` calls to
guard against, and evaluation is strict.

The non-`IO` request/response logic lives in `Validate.Core`, so it can be
`import`ed from `Tests.Main` without this file's `main` and `Tests.Main`'s
`main` colliding.
-/

/-- Read JSON Lines until EOF; skip empty lines, as `BL.null` does in Haskell. -/
partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return  -- EOF
    let body := if line.endsWith "\n" then line.dropEnd 1 |>.toString else line
    unless body.isEmpty do
      stdout.putStrLn (serveLine body).compress
      stdout.flush
    loop
  loop
