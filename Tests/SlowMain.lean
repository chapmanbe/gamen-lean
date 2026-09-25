import Tests.PropertyHelpers

/-!
# Tests.SlowMain (`lake exe slowtests`)

The seven `==>`-shaped properties from `test/Properties.hs`'s
"Gamen.Tableau: soundness vs. Kripke semantics" and "Gamen.RankingTheory:
structural invariants" describe blocks, at Haskell's full `numInst`,
discard caps (`maxDiscardRatio`), and sizes (`Tests.PropertyHelpers`'
`genFormula`/`genPropFormula`, uncapped, via `checkGuarded`). gamen-hs's
own run of this same set takes on the order of 460s; running it here
takes a similar order of magnitude, which is why it is a separate
executable rather than part of `lake test` (see `checkGuarded`'s
docstring in `Tests/PropertyHelpers.lean`, and `PORTING.md`'s
`Properties` row).

Run after touching `Gamen.Tableau`, `Gamen.Semantics`, or
`Gamen.RankingTheory` — anything the seven properties below exercise.
-/
open Gamen Plausible

def slowProperties : List (String × IO Bool) :=
  [ ("unsatisfiable ⇒ no random model satisfies it (K)",
      do
        let (checks, ok) ← checkGuarded "unsatisfiable ⇒ no random model satisfies it (K)" 300 10
          (fun size => do let f ← genFormula size; let m ← genKripkeModel; pure (f, m))
          (fun (f, _) => pure (tableauConsistent systemK defaultMaxSteps [f] == .definitely false))
          (fun (f, m) => do let b ← anySatisfies m f; pure (!b))
        IO.println s!"    real checks: {checks}/300"
        return ok),
    ("provable entailment ⇒ holds pointwise in random models (K)",
      do
        let (checks, ok) ← checkGuarded "provable entailment ⇒ holds pointwise in random models (K)" 300 10
          (fun size => do
            let p ← genFormula size
            let c ← genFormula size
            let m ← genKripkeModel
            pure (p, c, m))
          (fun (p, c, _) => pure (tableauProves systemK defaultMaxSteps [p] c == .definitely true))
          (fun (p, c, m) => allSatisfies m (.implies p c))
        IO.println s!"    real checks: {checks}/300"
        return ok),
    ("satisfied in some model ⇒ prover does not call it unsatisfiable (K)",
      do
        let (checks, ok) ← checkGuarded "satisfied in some model ⇒ prover does not call it unsatisfiable (K)" 300 10
          (fun size => do let f ← genFormula size; let m ← genKripkeModel; pure (f, m))
          (fun (f, m) => anySatisfies m f)
          (fun (f, _) => pure (!(tableauConsistent systemK defaultMaxSteps [f] == .definitely false)))
        IO.println s!"    real checks: {checks}/300"
        return ok),
    ("S5 unsatisfiable ⇒ no equivalence-frame model satisfies it",
      do
        let (checks, ok) ← checkGuarded "S5 unsatisfiable ⇒ no equivalence-frame model satisfies it" 200 10
          (fun size => do let f ← genFormula size; let m0 ← genKripkeModel; pure (f, m0))
          (fun (f, _) => pure (tableauConsistent systemS5 2000 [f] == .definitely false))
          (fun (f, m0) => do
            let m ← s5ClosureModel m0
            let b ← anySatisfies m f
            pure (!b))
        IO.println s!"    real checks: {checks}/200"
        return ok),
    ("extracted countermodel actually satisfies the formula (K)",
      do
        -- `gen` precomputes `extractedModelsFor f` once per attempt (not
        -- once in the guard and again in the check): `buildTableau` runs
        -- to `defaultMaxSteps`, so recomputing it per attempt was doubling
        -- the cost of this property's whole discard budget.
        let (checks, ok) ← checkGuarded "extracted countermodel actually satisfies the formula (K)" 200 10
          (fun size => do let f ← genFormula size; pure (f, extractedModelsFor f))
          (fun (_, ms) => pure (!ms.isEmpty))
          (fun (f, ms) => do
            let oks ← ms.mapM fun m => anySatisfies m f
            pure (oks.all id))
        IO.println s!"    real checks: {checks}/200"
        return ok),
    -- Gamen.RankingTheory: structural invariants — deferred (before wave
    -- 2 of this port) for lack of a `KappaModel` generator.
    ("negation symmetry (Spohn Thm 2a, p.115): τ(¬φ) = −τ(φ) for contingent φ",
      do
        let (checks, ok) ← checkGuarded
          "negation symmetry (Spohn Thm 2a, p.115): τ(¬φ) = −τ(φ) for contingent φ" 100 20
          (fun size => do let m ← genKappaModel; let f ← genPropFormula size; pure (m, f))
          (fun (m, f) => isContingentK m f)
          (fun (m, f) => do
            let l ← tau m "c" (.not f)
            let r ← tau m "c" f
            pure (l == -r))
        IO.println s!"    real checks: {checks}/100"
        return ok),
    ("conditionalize preserves wellFormed for contingent φ, any rank n",
      do
        let (checks, ok) ← checkGuarded
          "conditionalize preserves wellFormed for contingent φ, any rank n" 100 20
          (fun size => do
            let m ← genKappaModel
            let f ← genPropFormula size
            let ⟨n, _⟩ ← Gen.choose Int (-(size : Int)) (size : Int) (by omega)
            pure (m, f, n))
          (fun (m, f, _) => isContingentK m f)
          (fun (m, f, n) => do
            let m' ← conditionalize m "c" f n
            pure (wellFormed m'))
        IO.println s!"    real checks: {checks}/100"
        return ok) ]

def main : IO UInt32 := do
  IO.println "Slow properties (lake exe slowtests; Haskell's full numInst/discard-cap/size)"
  let mut failures := 0
  for (name, prop) in slowProperties do
    let ok ← prop
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  IO.println s!"{slowProperties.length - failures}/{slowProperties.length} passed"
  return if failures == 0 then 0 else 1
