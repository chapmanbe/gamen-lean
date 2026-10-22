import ProofWidgets.Component.HtmlDisplay
import Widgets.Dynamic.Explorer

/-!
# Dynamic-scenarios explorer: the widget

The infoview side of the explorer. The JS component (`js/dynamicExplorer.js`)
holds a `StepResult` in React state and sends every student action to the
server as one `dynamicExplorerStep` call; the server folds the event into the
state with `step` and renders it with `view`. All logic stays in Lean, and the
widget never polls.
-/

namespace Gamen.Widgets.Dynamic

open Lean Server

structure StepParams where
  state : ExplorerState
  event : Event
  deriving ToJson, FromJson, RpcEncodable

structure StepResult where
  state : ExplorerState
  /-- What the widget draws: `view state`. -/
  view : Json
  deriving ToJson, FromJson, RpcEncodable

/-- The pure function the RPC method wraps. -/
def stepResult (p : StepParams) : StepResult :=
  let s := step p.state p.event
  { state := s, view := view s }

/-- The widget's contents before any action. -/
def initialResult (sc : Scenario) : StepResult :=
  let s := ExplorerState.init sc
  { state := s, view := view s }

end Gamen.Widgets.Dynamic

open Lean Server RequestM Gamen.Widgets.Dynamic in
/-- One student action. Pure: `step` then `view`. At the root so the JS can call
it by a fixed name. -/
@[server_rpc_method]
def dynamicExplorerStep (p : StepParams) : RequestM (RequestTask StepResult) :=
  RequestM.pureTask (pure (stepResult p))

namespace Gamen.Widgets

open ProofWidgets

@[widget_module]
def DynamicExplorerWidget : Component Dynamic.StepResult where
  javascript := include_str ".." / "js" / "dynamicExplorer.js"

/-- The HTML to pass to `#html`. -/
def dynamicExplorer (sc : Dynamic.Scenario) : Html :=
  Html.ofComponent DynamicExplorerWidget (Dynamic.initialResult sc) #[]

end Gamen.Widgets
