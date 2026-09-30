# Facts behind `Notebooks/ThreeValued.lean`, verified 2026-09-30

A dated record. The plan (`plans/three-valued-logic-2026-09-29.md`) listed
two claims as "not yet verified; check before stating it in a notebook."
Both were checked against the primary sources before the notebook stated
them. Quotes are verbatim.

## CQL: null at a query boundary (plan: "Not yet verified")

- **`where` keeps only true.** CQL 2.0.0 Author's Guide, Queries,
  "Filtering" (<https://cql.hl7.org/02-authorsguide.html>): "For the
  purposes of evaluating a filter, only elements where the condition
  evaluates to true are included in the result, effectively ignoring the
  entries for which the logical expression evaluates to null." The same
  page, on `if`/`case`: "Note that if the condition evaluates to null, it
  is interpreted as false."
- **Population criteria.** Quality Measure IG v5.0.0, Measure Conformance,
  Conformance Requirement 3.11
  (<https://hl7.org/fhir/us/cqfmeasures/measure-conformance.html>): "If
  population criteria evaluate to null for a patient-based measure it is
  interpreted as false. If population criteria evaluate to null for a
  non-patient-based measure it is interpreted as an empty list."
- **`is true`.** CQL Reference, Nullological Operators
  (<https://cql.hl7.org/09-b-cqlreference.html>): "If the argument
  evaluates to true, the result is true; otherwise, the result is false."
  So `null is true` is false.
- **Comparison with null.** CQL Reference, Comparison Operators, `>`: "If
  either argument is null, the result is null."

## FHIRPath 3.0.0 `implies`: note vs. table (plan: "check errata")

- The note (3.0.0, <https://hl7.org/fhirpath/en/index.html>, and the CI
  build, <https://build.fhir.org/ig/HL7/FHIRPath/en/index.html>, identical):
  "Note carefully that if the left side of an implies evaluates to empty,
  the result of the operation is the right side."
- The operator's definition in words (identical in both): "Otherwise, this
  operator returns true if the right operand evaluates to true, and the
  empty collection ( { } ) otherwise."
- The table (identical in both): empty row gives `true` → true,
  `false` → `{ }`, `empty` → `{ }`. So `{ } implies false = { }`, which
  contradicts the note (which gives `false`) and agrees with strong Kleene.
- N1 (v2.0.0) has the same definition and table and no note.
- History, from the HL7/FHIRPath GitHub repository: commit `e2d25cb`
  (2026-02-04, "QA: wording updates based on feedback from Bryn") added
  the sentence; the latest commit checked (`c95ad83`, 2026-05-21) still
  has it.
- **No ticket or erratum found.** jira.hl7.org returned 403 to anonymous
  search, so Jira was not searched; a logged-in search would settle it.
  The notebook says only that none was found, and does not raise the issue
  with HL7 (outward-facing; the plan requires asking Brian first).

## CMS122

- eCQI Resource Center, CMS122v13 (2025 performance period,
  <https://ecqi.healthit.gov/ecqm/ec/2025/cms0122v13>), title "Diabetes:
  Glycemic Status Assessment Greater Than 9%"; numerator: "Patients whose
  most recent glycemic status assessment (HbA1c or GMI) (performed during
  the measurement period) is >9.0% or is missing, or was not performed
  during the measurement period".

## B&D Appendix C (the primer's citations)

Checked in `notes/bd-screen.pdf` (SHA-256 matches `notes/bd-edition.md`)
with `pdftotext`: Definition C.1 (formula; propositional variables), C.2
(defined operators, including ↔), Theorem C.4 (induction on formulas), C.14
(valuations), C.15 (evaluation), C.19 (satisfiable, tautology, contingent,
entailment; items 1–5), Proposition C.21 (Γ ⊨ A iff Γ ∪ {¬A}
unsatisfiable).
