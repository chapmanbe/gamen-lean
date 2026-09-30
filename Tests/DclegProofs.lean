import Tests.ManyValued
import DclegProofs.Lemma5_2

/-!
# Axiom audit for `DclegProofs`

Every theorem in `DclegProofs/` is listed here under `#assert_kernel_only`
(defined in `Tests/ManyValued.lean`), which fails the build unless the
theorem depends on nothing beyond Lean's three standard axioms `propext`,
`Quot.sound` and `Classical.choice`. An allowlist, so `sorryAx`,
`Lean.ofReduceBool`, `Lean.trustCompiler`, and the per-theorem axiom that
`native_decide` introduces at Lean 4.34 (`<thm>._native.native_decide.ax_…`)
are all rejected. The claims (`claim_lemma4_1`, …) are `def`s of type
`Prop`, not theorems, and are not listed: there is nothing to audit.

When a proof is added or finished in `DclegProofs/`, add its name here.
-/

namespace DclegProofsTests

open DclegProofs

#assert_kernel_only
  -- Basics: abbreviations
  sat_neg sat_or sat_turn sat_move sat_bel sat_next sat_cf
  sat_top sat_and sat_bigAnd sat_bigOr sat_bigOr_map sat_bigAnd_map sat_dia sat_dbel sat_belE
  -- Basics: histories
  moveAt_reaches moveAt_pmoves moveAt_next_defined moveAt_not_end reaches_move_of_not_end
  PathFrom.next_mem reaches_next outcome_reaches PathFrom.last_step PathFrom.head_mem
  root_reaches_ne_outcome
  -- Basics: end, X⊤, □
  sat_nextTop_iff sat_end_iff sat_box_iff box_world_indep box_elim
  -- Basics: counterfactual and validity
  maxConsistent_sat valid_cf_of_imp F_nonempty maxConsistent_of_sat maxConsistent_eq_of_sat
  sat_cf_of_sat valid_cf_iff
  -- Basics: maximal extension, cautious monotonicity
  exists_maximal_extension exists_maxConsistent_of_local exists_maxConsistent_of_dia
  maxConsistent_and_of_sat maxConsistent_of_and_of_local
  -- Basics: belief
  dox_reaches dox_cluster sat_bel_of_dox sat_dbel_of_dox bel_D bel_4 bel_5 bel_C4
  bel_box_imp_box box_imp_bel_box box_imp_bel bel_dia_imp_dia
  -- Basics: histories are simple paths
  Reach.trans PathFrom.reach_of_mem no_cycle_from_root PathFrom.cycle_of_two_moves moveAt_unique
  -- Lemma 4.1
  sat_payoffAtLeast sat_payoffAtMost sat_BIupto depth_zero_iff sat_BI_zero_iff lemma4_1_zero
  followsBI_of_sat_BI_zero
  -- Theorem 4.2
  theorem4_2_zero belE_belE_imp_belE belE_dia_imp_dia sat_rat_of_dox rat_imp_bel_rat
  bel_rat_imp_rat
  -- Theorem 5.1
  sat_next_iff bel_next_of_bel_AX
  -- Lemma 5.2
  mem_others lemma5_2_actual_move

end DclegProofsTests
