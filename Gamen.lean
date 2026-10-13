import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics
import Gamen.FrameProperties
import Gamen.Verdict
import Gamen.Tableau
import Gamen.Temporal
import Gamen.Doxastic
import Gamen.RankingTheory
import Gamen.Plausibility
import Gamen.DeonticStit
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules
import Gamen.DeonticStit.Saturation
import Gamen.DeonticStit.Prove
import Gamen.DeonticStit.CounterModel
import Gamen.Fragment
import Gamen.Notation
import Gamen.Protocol
import Gamen.Teaching
import Gamen.Cgs
import Gamen.Coalition
import Gamen.Atl.ModelCheck
import Gamen.Laca
import Gamen.Stit
import Gamen.Xstit
import Gamen.Epistemic
import Gamen.Atl.Strategy
import Gamen.Atl
import Gamen.Atel
import Gamen.Atl.ImperfectInfo
import Gamen.CgsJson
import Gamen.Atl.UpdateSearch
import Gamen.Atl.SocialLaws
import Gamen.ActionModel
import Gamen.EpistemicJson
import Gamen.Dcleg
import Gamen.Service.Protocol
import Gamen.Service.Formula
import Gamen.Service.Model
import Gamen.Service.Axioms
import Gamen.Visualize
import Gamen.ManyValued
import Gamen.ManyValued.Completion

/-!
# gamen

Lean 4 port of [gamen-hs](https://github.com/chapmanbe/gamen-hs): modal,
temporal, epistemic, and STIT logic with applications to clinical guideline
validation. See `PORTING.md` for which gamen-hs modules are ported.
-/
