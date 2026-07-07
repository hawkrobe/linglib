import Linglib.Features.ScalarDimension
import Linglib.Features.Aktionsart
import Mathlib.Order.Basic
import Mathlib.Order.WithBot
import Mathlib.Tactic.NormNum
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Data.Set.Basic

/-!
# Degree structure of scalar dimensions

The order-theoretic apparatus over `Features.ScalarDimension`: a
computable degree carrier per scale shape, the endpoint grounding, and
the derived aspectual views ([kennedy-levin-2008]).

## Main declarations

* `Core.Order.Boundedness.degreeShape` — degree carrier per scale shape;
  `ScalarDimension.degree` inherits it, grounded by
  `hasGreatest_degree_iff`.
* `ScalarDimension.defaultTelicity` / `defaultVendlerClass` — the
  Kennedy–Levin telicity defaults, with
  `defaultTelicity_telic_iff_hasGreatest` deriving them from the scale's
  order structure.
-/

open Core.Order (Boundedness ScalePolarity LicensingPipeline)
open Features (Telicity VendlerClass ScalarDimension)

namespace Features

/-! ### Degree fiber, grounded through `Boundedness` (proved once, not per dimension) -/

/-- Degree carrier per boundedness shape: a greatest element exists exactly when the
    scale `HasMax`. A computable order-proxy — only the `OrderTop`/`NoMaxOrder` mixin
    matters, not the carrier. -/
abbrev _root_.Core.Order.Boundedness.degreeShape : Boundedness → Type
  | .open_ | .lowerBounded => ℕ
  | .upperBounded | .closed => WithTop ℕ

instance instLinearOrderDegreeShape (b : Boundedness) : LinearOrder b.degreeShape := by
  cases b <;> exact inferInstance

/-- **Grounding, proved once at the 4-case level.** -/
theorem _root_.Core.Order.Boundedness.hasGreatest_degreeShape_iff (b : Boundedness) :
    (∃ m : b.degreeShape, IsTop m) ↔ b.HasMax := by
  cases b
  · exact iff_of_false (fun ⟨m, hm⟩ => not_isMax m hm.isMax) (by decide)
  · exact iff_of_false (fun ⟨m, hm⟩ => not_isMax m hm.isMax) (by decide)
  · exact iff_of_true ⟨⊤, isTop_top⟩ (by decide)
  · exact iff_of_true ⟨⊤, isTop_top⟩ (by decide)

/-- Each dimension's degree type — inherited from its boundedness, so the grounding
    transports rather than re-casing per dimension. -/
abbrev ScalarDimension.degree (d : ScalarDimension) : Type := d.boundedness.degreeShape
instance instLinearOrderDimensionDegree (d : ScalarDimension) : LinearOrder d.degree :=
  inferInstance

/-- The scale's order structure has a greatest element exactly when the dimension's
    canonical scale `HasMax` — grounded for all dimensions in one application. -/
theorem ScalarDimension.hasGreatest_degree_iff (d : ScalarDimension) :
    (∃ m : d.degree, IsTop m) ↔ d.boundedness.HasMax :=
  Boundedness.hasGreatest_degreeShape_iff d.boundedness

/-! ### Derived aspectual views (verb side) -/

/-- Default telicity of a degree achievement on this dimension: a scale with a
    greatest degree gives a telic reading ([kennedy-levin-2008]). -/
def ScalarDimension.defaultTelicity (d : ScalarDimension) : Telicity :=
  match d.boundedness with
  | .closed | .upperBounded => .telic
  | .open_ | .lowerBounded => .atelic

/-- Default Vendler class: degree achievements are dynamic and durative, so a
    closed scale gives an accomplishment, an open one an activity. -/
def ScalarDimension.defaultVendlerClass (d : ScalarDimension) : VendlerClass :=
  match d.boundedness with
  | .closed | .upperBounded => .accomplishment
  | .open_ | .lowerBounded => .activity

/-- **The Kennedy–Levin thesis as a theorem.** `defaultTelicity` is exactly the
    order-theoretic fact: a degree achievement is telic iff its scale's degree type
    has a greatest element — grounded in the scale's order structure, not stipulated. -/
theorem ScalarDimension.defaultTelicity_telic_iff_hasGreatest (d : ScalarDimension) :
    d.defaultTelicity = .telic ↔ ∃ m : d.degree, IsTop m := by
  rw [ScalarDimension.hasGreatest_degree_iff]; cases d <;> decide

/-! ### The endpoint: one more `LicensingPipeline` instance -/

instance : LicensingPipeline ScalarDimension where
  toBoundedness := ScalarDimension.boundedness

end Features
