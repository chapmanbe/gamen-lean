# Plan: machine-checking the proofs in Jeremiah Chapman's DCLEG thesis

*Written 2026-09-29, right after `Gamen.Dcleg` was merged (`53a94bc`). Read
this once; implement against it. This is separate from the port: it checks
the thesis's own claims, not gamen-hs's behavior.*

## Objective

For every validity the thesis claims about DCLEG (Doxastic Conditional
Logic of Extensive Games):

1. **Try to falsify it.** Check it on many small models that satisfy all of
   the thesis's frame conditions, and report any counterexample.
2. **Prove it in Lean** for all models, following Jeremiah's hand proof
   where there is one.
3. **Record, for each claim,** whether it was proved, disproved (with the
   countermodel) or still open, and where a hand proof needed repair.

The result is a machine-checked companion to the thesis, and possibly a
short paper with Jeremiah.

## Inputs and their status

- **The v5.0 draft,** pinned by hash in `notes/dcleg-edition.md`: 13 pages
  of definitions and stated validities, with short justifications but no
  full proofs.
- **The full thesis with the hand proofs: needed, not yet here.** Brian is
  getting it from Jeremiah (2026-09-29). The thesis is signed for release
  but not yet in GUPEA. Pin it by hash in `notes/dcleg-edition.md`, and
  keep it out of the repository until it is published or Jeremiah agrees.
  Stages 1–3 can start from the draft. Stages 4–5 need the thesis.
- **Jeremiah's involvement:** at minimum, he signs off that the Lean
  definitions (stage 4) mean what the thesis means. The most likely serious
  error in this project is formalizing the wrong definition, not a failed
  proof.

## What the draft claims (the inventory to start from)

- **Frame conditions (17):**
  - §2.1: the 7 conditions on strategic structures (the nx/Q/PM/EV
    conditions; unnamed);
  - §2.2, on the counterfactual premise function F: Centering and
    Contemporary Universality;
  - §2.2, on belief: Presence, Present Seriality, Transitivity,
    Euclideanness, Self-Awareness, Minimal Revision, Expectational
    Continuity and Recall.
- **Tagged validities (§2.4–2.7):**
  - Counterfactual K′, D, 4, 5 and C4;
  - Intentional Awareness;
  - K, T and 5 for □;
  - Counterfactual K′ for X and for Y;
  - Conditioned FUNC for X and for Y;
  - Ctf. K′ for X and for AX;
  - Det for X;
  - Table 1 (§2.7): PerfectInfo, NxtVert, TurnStr, TimeVert, Aware,
    CompletePref, SinglePref, OneAct, SingleAct, TurnTaking, SingleTurn,
    TimePref, End Act and StrAct.
- **Untagged claims:**
  - §2.5: five B/□ interactions ("Interaction Between B_i and □");
  - §2.6: the B/X biconditional and `B_i AX φ □→ X B_i φ`, and the B/Y
    biconditional `B_i Y B_i φ □↔ Y B_i φ` (□↔ is the draft's `\boxiff`);
  - the derived claims "□ is S5, so D, B, 4, C and C4 hold" (§2.5) and
    "`B_i φ □↔ B_i B_i φ` is valid" (§2.4).
- **Refresh the inventory from the full thesis** when it arrives. Record
  each claim's number there, its hand proof's length, and the frame
  conditions the proof uses.

**Known discrepancy to carry in:** Table 1 states PerfectInfo, TurnStr and
SinglePref with `□→`, but gamen-hs's tests (`PaperCorrespondence.hs`
~1161–1210) check the weaker material `→` at a single point. Because the
spheres are centered, `φ □→ ψ` implies `φ → ψ` at a point, but not the
other way round. Stage 3 tests every claim exactly as the thesis states it.

## Stages

### 1. A frame-condition checker (`Gamen/Dcleg/Conditions.lean`; Lean-only)

- The executable `DclegModel` does **not** enforce the thesis's frame
  conditions. `validateDclegModel` only catches structural problems, such
  as stray vertices or doxastic worlds.
- Write one `Bool` function per condition, named after the thesis
  ("centering", "presentSeriality", "recall", …), each citing its § and
  condition number in the v5.0 draft, plus
  `satisfiesAllConditions : DclegModel → Except String (List String)`,
  which lists the conditions that fail.
- **First finding to record:** do gamen-hs's own fixture models (the
  two-world FPIE game in `Tests/PropertyHelpers.lean`, and the
  PaperCorrespondence models) satisfy every condition? If one doesn't,
  that's worth knowing on its own.

### 2. A generator of models that satisfy the conditions

- Plausible generators for small games: depth ≤ 3, ≤ 2 agents, ≤ 2 moves
  per vertex, ≤ 4 strategy worlds.
- Build premise systems F that satisfy Centering and Contemporary
  Universality **by construction**, as nested spheres around (γ,w).
- Build the doxastic relations by construction where that's easy, and by
  rejection with stage 1's checker otherwise.
- The generator must report its acceptance rate. Every generated model must
  pass `satisfiesAllConditions` (a test).
- **Exhaustive enumeration:** also enumerate every model up to a small
  bound where that's feasible (e.g. one agent, depth 2).

### 3. Falsification (automated; results are a dated record)

- Encode every inventoried claim as a `DclegFormula` schema over a few
  atoms, exactly as stated, `□→` included.
- For each claim, check `dclegTrueIn` on every generated or enumerated
  model and all atom instantiations.
- A counterexample is shrunk to a minimal model, re-checked with
  `satisfiesAllConditions`, and written to
  `docs/assessment/dcleg-falsification-<date>.md` together with the claim,
  its source and the model.
- **Surviving this is evidence, not proof.** A counterexample is a definite
  finding, and gets raised with Jeremiah before anything else.
- **Guard against false alarms:** before reporting a counterexample, check
  the claim's formula encoding and the model's conditions a second time.
  Planted checks: one deliberately false claim must be caught, and a model
  that deliberately violates Recall must be rejected by the checker.

### 4. Formal semantics (separate package; needs Jeremiah's sign-off)

- **Location:** a new Lake package, **`dcleg-proofs`**, in its own
  repository or a subdirectory with its own `lakefile`. It depends on
  **Mathlib**, pinned to the tag matching `lean-toolchain` 4.34.0.
  gamen-lean deliberately does not depend on Mathlib, and this keeps it
  that way.
- **Prop-level definitions over arbitrary types, with no `TreeSet`:**
  - strategic structures;
  - histories and V_γ;
  - the game model ⟨T, Γ, H, F, π, {R^w}, {N^w_i}, {P_i}⟩;
  - the frame conditions;
  - satisfaction (§2.3), including the counterfactual clause.

  The delicate part is the counterfactual's limit clause: a non-empty
  G ⊆ F(γ,w) such that for every G′ with G ⊂ G′ ⊆ F(γ,w), … Formalize it
  literally first, and simplify only with a proved equivalence.
- **Sign-off gate:** Jeremiah reviews the definitions side by side with
  the thesis before any proof work starts. Record the review in the
  package.
- **Optional:** an adequacy lemma linking the Prop semantics to
  `Gamen.Dcleg.dclegSatisfies` on finite models, so stage 3's
  counterexamples carry over formally.

### 5. Proofs, easiest first

1. □ is S5 (K, T and 5; then D, B, 4, C and C4 as corollaries).
2. Intentional Awareness and the belief axioms (Counterfactual K′, D, 4, 5
   and C4), which use Presence, Present Seriality, Transitivity,
   Euclideanness and Self-Awareness.
3. The temporal claims for X and Y (K′, Conditioned FUNC, Det).
4. The belief–time interactions, which use Expectational Continuity,
   Minimal Revision and Recall.
5. Table 1.

Other rules for this stage:
- **Follow Jeremiah's hand proof step by step** where one exists. Where
  the formal proof needs a step the hand proof skips, or a condition it
  doesn't cite, record it: that is the main output.
- **No `sorry` on the main branch,** as in gamen-lean. Unproved claims are
  listed as open in the report, not stubbed.
- **Axiom audit:** `#print axioms` for each theorem shows only `propext`,
  `Classical.choice` and `Quot.sound`. Classical logic is expected here,
  because the semantics is set-theoretic.

### 6. Report

A table with one row per claim: its source (thesis number and v5.0
section), its status (proved / disproved with countermodel / open), the
Lean theorem name, the frame conditions it actually uses, and notes on the
hand proof. It goes to Jeremiah first. A paper is his and Brian's decision.

## Order, models, and gates

- Stages 1–3 can start now in gamen-lean. Sonnet builds the checker and
  generator; Opus reviews them, since the condition definitions are the
  risky part. Stage 3's counterexamples, if any, go to Brian and Jeremiah
  before stage 4.
- Stages 4–5 wait for the full thesis and for Jeremiah's sign-off on the
  definitions. Use Opus or Fable, one claim group per session.
- **Stop and ask the user** before:
  - creating the new repository or package, or adding Mathlib;
  - copying any thesis text or PDF into a repository;
  - filing gamen-hs issues arising from this work (e.g. testing Table 1's
    `□→` forms);
  - contacting anyone outside the project about results.
