import Linglib.Semantics.Events.CEM
import Linglib.Semantics.Spatial.Path
import Linglib.Features.Aktionsart

/-!
# Spatial trace function σ

The spatial trace σ maps events to the paths they traverse ([zwarts-2005],
[gawron-2009]): the spatial member of [krifka-1998]'s family of trace
dimensions, alongside the temporal trace τ (`Event.runtime`) and the thematic
dimension θ. Following the mixin convention of `Semantics/Events/CEM.lean`,
`Trace` carries only the function σ; its structural assumptions — sum
homomorphism (`Mereology.IsSumHom`) and injectivity — are stated at use sites.

## Main declarations

* `Trace`: the spatial trace σ of an event theory.
* `Trace.bounded_path_telic`: QUA path predicates pull back through an
  injective sum-homomorphic σ — *walk to the store* is telic because
  *to the store* denotes a QUA set of paths ([zwarts-2005]).
* `Trace.unbounded_path_atelic`: CUM path predicates pull back through a
  sum-homomorphic σ — *walk towards the store* is atelic.
* `Trace.pathShapeToTelicity`: the `PathShape → Telicity` bridge, agreeing
  with scale boundedness (`Trace.telicity_boundedness_agree`).
-/

open Features
open Mereology

namespace Semantics.Spatial

/-- Spatial trace: `σ e` is the path traversed in event `e` ([zwarts-2005],
    [gawron-2009]), parallel to the temporal trace τ (`Event.runtime`).
    Structural assumptions on σ are stated as mixins at use sites, per
    `Semantics/Events/CEM.lean`: `[Mereology.IsSumHom st.σ]` for sum
    preservation, `Function.Injective st.σ` where QUA pullback needs it. -/
class Trace (Loc Time : Type*) [LinearOrder Time] where
  /-- The path traversed in an event. -/
  σ : Event Time → Path Loc

namespace Trace

/-! ### Telicity transfer through σ -/

variable {Loc Time : Type*} [LinearOrder Time] [Event.Mereology Time]
  [ClassicalMereology (Event Time)] [SemilatticeSup (Path Loc)]
  [st : Trace Loc Time] {P : Path Loc → Prop}

/-- Bounded path predicate → telic VP: QUA pulls back through an injective
    sum-homomorphic σ. *Walk to the store* is telic because *to the store*
    denotes a QUA set of paths ([zwarts-2005]). -/
theorem bounded_path_telic [hσ : IsSumHom st.σ]
    (hinj : Function.Injective st.σ) (hP : QUA P) : QUA (P ∘ st.σ) :=
  qua_of_injective_sumHom hσ hinj hP

/-- Unbounded path predicate → atelic VP: CUM pulls back through a
    sum-homomorphic σ. *Walk towards the store* is atelic because *towards
    the store* denotes a CUM set of paths ([zwarts-2005]). -/
theorem unbounded_path_atelic [hσ : IsSumHom st.σ] (hP : CUM P) :
    CUM (P ∘ st.σ) :=
  cum_pullback hσ hP

/-! ### PathShape → Telicity bridge -/

/-- Bounded and source paths yield telic VPs; unbounded paths atelic ones —
    [zwarts-2005]'s boundedness-telicity generalization at the `PathShape`
    level, the spatial analog of `Features.VendlerClass.telicity`. -/
def pathShapeToTelicity : PathShape → Telicity
  | .bounded => .telic
  | .source => .telic
  | .unbounded => .atelic

/-- The telicity bridge agrees with the scale-boundedness bridge
    (`PathShape.toBoundedness`): a path shape is telic iff its boundedness
    is licensed (closed scale). -/
theorem telicity_boundedness_agree (s : PathShape) :
    (pathShapeToTelicity s = .telic) ↔ s.toBoundedness.IsLicensed := by
  cases s <;> decide

end Trace

end Semantics.Spatial
