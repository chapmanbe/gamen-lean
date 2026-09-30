# Plan: the logic that guideline validation needs, and how to add it

*Written 2026-09-29. Read this once; implement against it. It spans three
repositories:*
- *gamen-lean, where the provers live;*
- *the Lean guideline-validation port (`~/Projects/Logic/Lean/guideline-validation`);*
- *the canonical guideline-validation (`~/Projects/Logic/Julia/guideline-validation`),
  which is **read-only** for agents per the Lean port's plan.*

*Each phase says where its changes go.*

## Objective

Guideline validation checks sets of extracted clinical obligations for
conflicts. It currently ignores the three things that decide most real
conflicts:
- **when** the obligations apply: deadlines, durations, periods, order;
- **whether** they apply to a given patient, whose data may be missing;
- **what happens** when an obligation is missed (deadlines, contrary-to-duty).

Add each as a decidable layer with a soundness proof in Lean. Don't switch
to one large logic. Keep the existing deontic core: G3DS for deontic STIT,
KD and doxastic D.

## Evidence

The literature search is in
`references/logic-for-guideline-validation-2026-09-29.md` (13 papers, all
verified by Crossref DOI). Its PDFs live in `references/pdfs/` (decision D1,
resolved 2026-09-29: references that drive gamen-lean's implementation live
in gamen-lean).

What this plan relies on:
- **anselma2006** (Anselma, Terenziani, Montani, Bottrighi, *AI in
  Medicine* 38, 2006): a temporal-constraint framework for guidelines, with
  durations, delays and periodic repetitions. The paper reports that its
  consistency checking is correct, complete and tractable.
- **broersen2004** (Broersen, Dignum, Dignum, Meyer, DEON 2004, LNCS):
  deadline obligations "O(ρ ≤ δ)", reduced to CTL over branching time.
  That's the same kind of frame our STIT modules use.
- **governatori2007** (Governatori, Hulstijn, Riveret, Rotolo, LNCS):
  deadlines in temporal modal defeasible logic, and the distinction between
  achievement and maintenance obligations.
- **The search's gaps** are the case for this plan:
  - no candidate gives missing patient data a formal semantics;
  - nothing combines clock or periodic time with contrary-to-duty
    obligations in a decidable system applied to guidelines.

**Before citing any of these in a paper:** check the LNCS volume numbers
(taken from search snippets or memory, not Crossref); check the report's
characterizations of zamborlini2017 and hommersom2007, which rest partly on
recall; and fetch the paywalled or bot-blocked PDFs in a browser. Only
broersen2004's PDF is saved.

## Where things stand (checked 2026-09-29)

- **`gamen-validate` rejects every temporal operator** at the fragment
  boundary (gamen-hs#25). A request with even one timed obligation returns
  `unsupported operator: FutureBox`, for the whole request.
- **The canonical pipeline drops `temporal_op` and `conditional`** before
  checking (`decisions/0002-lean-conflict-detection.md`).
- **The Lean port already reports this honestly.** It quarantines by
  default: `unsupported` is counted and listed, and never reported as
  consistent. `--temporal=abstract` is available as an option. It records
  the gamen-lean and repository commits for every run.
- **Extracted data**, across the canonical `data/` files, which may count a
  guideline more than once:
  - ~96 of ~696 records carry `temporal_op`: 39 `periodic`, 30
    `future_diamond`, 27 `future_box`;
  - they also carry a free-text `temporal_period`, with 14 distinct values.
    These include `annually`, `twice_annually`, `weekly`, `daily`,
    `2_to_4_weeks` and `48_to_72_hours_before_surgery`, and also
    `each_consultation`, `periodically_and_at_transitions_of_care`,
    `risk_based_interval` and `regular`. The protocol discards this field.
- **Planned work this builds on:**
  - `plans/three-valued-logic-2026-09-29.md` (strong Kleene logic, checked
    against CQL 2.0.0 and FHIRPath 3.0.0);
  - the Lean soundness method of Part B of
    `plans/countermodel-explorer-and-k-soundness-2026-09-29.md`.

## Phases

### Phase 1: honest reporting (Lean port; small)

Most of this exists. Add:
- **Flag conflicts that involve timing.** Under `--temporal=abstract`, mark
  every conflict involving a timed obligation "timing may dissolve this".
  Report the counts per guideline pair.
- **Count what's dropped.** Report how many obligations carry
  `temporal_period`, and which values, so the paper can say exactly what is
  dropped.
- **A reviewed sentence for the manuscript,** stating the limitation.

### Phase 2: applicability under missing data (gamen-lean + Lean port)

Obligations are conditional (`conditional: "ckd_g4_g5_or_age_over_65…"`).
For a real patient, a condition may be unknown.
- **Semantics:** evaluate each obligation's condition in strong Kleene
  logic (the `ManyValued` module from the three-valued plan). A conflict
  becomes **definite** (both conditions true), **possible** (depends on
  unknown data) or **absent** (a condition is false).
- **Why this is worth doing:** it's the gap no paper covers, and it matches
  how CQL, the language quality measures are written in, already treats
  null.
- **Proofs in Lean:**
  - definite ⇒ conflict in every completion of the patient's data;
  - absent ⇒ conflict in no completion;
  - possible ⇔ conflict in some completions but not all.

  These are small and teachable, and the notebooks can reuse them.
- **Data:** patient facts come from the simulation or C-CDA side
  (guideline-cds-simulation, patient-agent-assistant). Pin the condition
  vocabulary in a data file, not in code.

### Phase 3: structured time in the extraction (the canonical repository; **needs your approval**)

- **Map `temporal_period` into a structured form** instead of free text.
  The proposal is the **FHIR `Timing` datatype** (repeat: frequency, period,
  periodUnit, boundsDuration, when/offset). Check the exact FHIR R4 fields
  against the spec before adopting it. It's the healthcare standard for
  schedules, and it keeps domain knowledge in data from an authoritative
  source.
- **Classify the 14 current values:**

  | Kind | Values |
  |---|---|
  | Metric period | annually, twice_annually, weekly, daily |
  | Metric window | 2_to_4_weeks |
  | Anchored offset | 48_to_72_hours_before_surgery (window before an event) |
  | Event-anchored, not metric | each_consultation, at transitions of care |
  | Unquantified | risk_based_interval, regular, regular_intervals |

  Unquantified values stay qualitative (G F), and are reported as such.
- **Where the mapping lives:** a data file, applied in the Lean port
  (`data/`), so the canonical repository needn't change for a first
  version.
- **Changes to the extraction prompt and schema** belong in the canonical
  repository, and are your call.

### Phase 4: temporal-constraint layer (gamen-lean; Lean-only module)

- **Start with simple temporal networks:** difference constraints
  `lo ≤ t_j − t_i ≤ hi` over the time points of events, covering deadlines,
  durations, offsets and windows. Consistency means the distance graph has
  no negative cycle (Floyd–Warshall or Bellman–Ford).
- **Prove in Lean** that the check is sound and complete: a negative cycle
  exists ⇔ the network is inconsistent. This is well-trodden mathematics
  and a good first proof. The classic source is Dechter, Meiri & Pearl 1991,
  "Temporal constraint networks", *Artificial Intelligence* 49. It's not in
  the search report, so verify it by DOI before citing.
- **Then add periodicity** following anselma2006, starting with a
  repetition count and period between two points. Keep it decidable, and
  prove each extension before using it.
- **Link to obligations:** each timed obligation contributes constraints on
  its action's time points. A conflict found here is a *timing* conflict,
  e.g. "within 7 days" against "not before 14 days". Report it separately
  from deontic conflicts.

### Phase 5: deadline obligations (gamen-lean; research, possibly with Jeremiah)

- **Implement broersen2004's O(ρ ≤ δ)** on finite branching models: model
  checking first, a decision procedure later. Its violation condition
  becomes a checkable event.
- **Use governatori2007's typing** of achievement vs maintenance
  obligations, to classify `future_diamond` (achievement) vs `future_box`
  (maintenance).
- **Prove the reduction to CTL correct in Lean** for the fragment used.
- **The open problem:** combining this with contrary-to-duty obligations
  ("if not done by δ, then do Y"), decidably. The search found nothing that
  does this for guidelines. It sits close to Jeremiah's thesis (belief,
  time and counterfactuals in extensive games), which makes it a natural
  joint research question rather than an engineering task. Start only
  after Phases 2–4.

### Phase 6: getting it into the checker

**Decision D2, resolved 2026-09-29: Lean-only. gamen-hs is not updated.**
Brian's direction is that gamen-lean is now the primary implementation, and
Haskell work stops unless Lean proves unable to implement a logic. So:
- the new layers are a Lean-only protocol extension: new request fields or
  actions, plus a version field;
- `compare.py` treats these requests as out of scope for gamen-hs;
- the existing requests stay byte-compatible, so `gamen-validate` still
  replaces the Haskell binary for downstream callers.
- The Lean guideline-validation port calls gamen-lean as a library, so it
  can use Phases 2 and 4 **without** protocol changes. That makes it the
  natural first consumer.

## Evaluation (built into each phase)

- For each phase, rerun the Lean port on the canonical extracted data and
  report how the conflict list changes:
  - conflicts that timing dissolves (false positives removed);
  - new timing conflicts;
  - definite vs possible conflicts under typical missing-data patterns.
- A clinician should read a sample of the changed conflicts. That's human
  work, so it's your call, and it's worth doing before any claim in the
  paper.

## Order, models, and gates

1. Phase 1. Sonnet, small.
2. Phase 2, together with the three-valued plan's library module (shared
   `ManyValued`). Opus.
3. Phase 4's simple temporal networks with their proof (Opus or Fable),
   then Phase 3's mapping, which is data work.
4. Phase 4's periodicity, then Phase 5, as research milestones.

**Stop and ask the user** before:
- any change in the canonical repository (the extraction schema or prompt,
  the manuscript);
- involving Jeremiah, or clinicians;
- any claim in the paper based on these results.
