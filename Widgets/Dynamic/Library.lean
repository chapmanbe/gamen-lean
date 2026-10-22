import Widgets.Dynamic.Widget

/-!
# Dynamic-scenarios explorer: the scenario library

Scenarios are data, in `data/scenarios/*.json` (Buchanan's separation
principle). Each is read at compile time with `include_str` and decoded by
`Scenario.ofJson`, so a malformed file is an `Except` error that
`dynamicExplorerOr` shows on the page, never a crash.
-/

namespace Gamen.Widgets.Dynamic.Library

open Lean (Json)

/-- Parse and decode scenario JSON text; errors name the file. -/
def load (file text : String) : Except String Scenario :=
  (do Scenario.ofJson (← Json.parse text)).mapError fun e => s!"{file}: {e}"

/-- Scenario 1: a lab page that may be lost. -/
def handoff : Except String Scenario :=
  load "data/scenarios/handoff.json"
    (include_str ".." / ".." / "data" / "scenarios" / "handoff.json")

/-- Scenario 2 (ATL-D, grant): the patient lacks the referral action. -/
def wouldIfCould : Except String Scenario :=
  load "data/scenarios/would-if-could.json"
    (include_str ".." / ".." / "data" / "scenarios" / "would-if-could.json")

/-- Scenario 3 (ATL-D, revoke): revoking an override, and the reasonableness rule. -/
def safetyAccess : Except String Scenario :=
  load "data/scenarios/safety-access.json"
    (include_str ".." / ".." / "data" / "scenarios" / "safety-access.json")

/-- Scenario 5 (ATEL-D): ordering authority changes hands at shift change, and
the pharmacist is not told. -/
def shiftChange : Except String Scenario :=
  load "data/scenarios/shift-change.json"
    (include_str ".." / ".." / "data" / "scenarios" / "shift-change.json")

/-- Every scenario, with the data file it comes from. -/
def allScenarios : List (String × Except String Scenario) :=
  [("data/scenarios/handoff.json", handoff),
   ("data/scenarios/would-if-could.json", wouldIfCould),
   ("data/scenarios/safety-access.json", safetyAccess),
   ("data/scenarios/shift-change.json", shiftChange)]

end Gamen.Widgets.Dynamic.Library

namespace Gamen.Widgets

open ProofWidgets

/-- The explorer for a loaded scenario, or a visible error message (which names
the data file) when the scenario did not load. Notebooks call this one. -/
def dynamicExplorerOr (r : Except String Dynamic.Scenario) : Html :=
  match r with
  | .ok sc => dynamicExplorer sc
  | .error e => Html.element "p" #[] #[Html.text s!"The scenario did not load. {e}"]

end Gamen.Widgets
