module

public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Tactic.NormNum

/-!
# Measure phrases and the changes of scale they survive

A measure-phrase differential (*3 inches taller*) says that two measures differ by a given amount,
and a factor phrase (*twice as tall*) that one measure is a multiple of another. In measurement
theory a statement about measurements is meaningful when its truth survives every admissible change
of scale: a strictly monotone map on an ordinal scale, a positive affine map on an interval scale,
a positive scaling on a ratio scale. A differential survives translations, and under a change of
unit it holds once its amount is rescaled too. A factor phrase survives scalings but not
translations, so *twice as hot* in degrees Celsius is not meaningful. Neither survives an arbitrary
strictly monotone change of scale, which is why an ordinal adjective such as *beautiful* takes
neither.

## Main statements

* `differentialComparative_comp_of_commute`, `factorEquative_comp_of_commute`: a differential or a
  factor phrase survives any injective change of scale that commutes with adding its amount or
  multiplying by its factor.
* `differentialComparative_add_const`, `differentialComparative_const_mul_add_const`: a
  differential survives translations, and a change of unit rescales its amount.
* `factorEquative_const_mul`, `factorEquative_not_add_const`: a factor phrase survives scalings
  but not translations.
* `differentialComparative_not_natural`: a differential does not survive every order embedding.

## References

* [stevens-1946]
* [krantz-1971]
* [sassoon-2010]
* [van-rooij-2011]
* [schwarzschild-2005]
* [winter-2005]
-/

@[expose] public section

namespace Degree

open Function

/-! ### Differential and factor semantics -/

/-- The differential comparative *A is d-much Adj-er than B* holds when `μ A - μ B = d`. It needs
subtraction, not just an ordering, which makes measure-phrase differentials more restrictive than
bare comparatives. -/
def differentialComparative {Entity D : Type*} [Sub D]
    (μ : Entity → D) (a b : Entity) (diff : D) : Prop :=
  μ a - μ b = diff

/-- The factor-phrase equative *A is n times as tall as B* holds when `μ A = n * μ B`, which needs a
meaningful zero, a ratio scale. -/
def factorEquative {Entity D : Type*} [Mul D]
    (μ : Entity → D) (a b : Entity) (factor : D) : Prop :=
  μ a = factor * μ b

/-- A positive differential entails the bare comparative. -/
theorem differentialComparative_lt_of_pos {Entity D : Type*}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (μ : Entity → D) (a b : Entity) {diff : D} (hdiff : 0 < diff)
    (h : differentialComparative μ a b diff) : μ b < μ a :=
  sub_pos.mp (h.symm ▸ hdiff)

/-! ### Differentials under a change of scale -/

section Differential

variable {E D : Type*}

/-- A differential survives any injective change of scale that commutes with adding its
amount. -/
theorem differentialComparative_comp_of_commute [AddGroup D] {g : D → D} (hg : Injective g)
    {d : D} (hc : Function.Commute g (d + ·)) (μ : E → D) (a b : E) :
    differentialComparative (g ∘ μ) a b d ↔ differentialComparative μ a b d := by
  have h : g (d + μ b) = d + g (μ b) := hc (μ b)
  rw [differentialComparative, differentialComparative, comp_apply, comp_apply,
    sub_eq_iff_eq_add, sub_eq_iff_eq_add, ← h, hg.eq_iff]

/-- A differential survives translating the scale. -/
theorem differentialComparative_add_const [AddGroup D] (μ : E → D) (c : D) (a b : E) (d : D) :
    differentialComparative (fun x ↦ μ x + c) a b d ↔ differentialComparative μ a b d :=
  differentialComparative_comp_of_commute (g := (· + c)) (add_left_injective c)
    (fun x ↦ add_assoc d x c) μ a b

/-- Under a change of unit and origin, a differential holds once its amount is rescaled by the
same unit. -/
theorem differentialComparative_const_mul_add_const {k : Type*} [CommRing k] [IsDomain k]
    (μ : E → k) {a : k} (ha : a ≠ 0) (b : k) (x y : E) (d : k) :
    differentialComparative (fun e ↦ a * μ e + b) x y (a * d) ↔
      differentialComparative μ x y d := by
  rw [differentialComparative_add_const (μ := fun e ↦ a * μ e)]
  simp only [differentialComparative, ← mul_sub, (mul_right_injective₀ ha).eq_iff]

/-- A differential does not survive every order embedding of the scale, so it is not meaningful on
an ordinal scale. -/
theorem differentialComparative_not_natural :
    ∃ f : ℚ ↪o ℚ, ∃ (μ : ℚ → ℚ) (a b d : ℚ),
      differentialComparative μ a b d ∧ ¬ differentialComparative (f ∘ μ) a b d :=
  ⟨(OrderIso.mulLeft₀ 2 two_pos).toOrderEmbedding, id, 1, 0, 1,
    by norm_num [differentialComparative], by norm_num [differentialComparative]⟩

end Differential

/-! ### Factor phrases under a change of scale -/

section Factor

variable {E D : Type*}

/-- A factor phrase survives any injective change of scale that commutes with multiplying by its
factor. -/
theorem factorEquative_comp_of_commute [Mul D] {g : D → D} (hg : Injective g) {n : D}
    (hc : Function.Commute g (n * ·)) (μ : E → D) (a b : E) :
    factorEquative (g ∘ μ) a b n ↔ factorEquative μ a b n := by
  have h : g (n * μ b) = n * g (μ b) := hc (μ b)
  simp only [factorEquative, comp_apply, ← h, hg.eq_iff]

/-- A factor phrase survives scaling the measure. -/
theorem factorEquative_const_mul [CommMonoidWithZero D] [IsCancelMulZero D] (μ : E → D) {c : D}
    (hc : c ≠ 0) (a b : E) (n : D) :
    factorEquative (fun x ↦ c * μ x) a b n ↔ factorEquative μ a b n :=
  factorEquative_comp_of_commute (g := (c * ·)) (mul_right_injective₀ hc)
    (fun x ↦ mul_left_comm c n x) μ a b

/-- A factor phrase does not survive translating the scale: moving the zero point destroys
ratios. -/
theorem factorEquative_not_add_const :
    ∃ (μ : ℚ → ℚ) (c a b n : ℚ),
      factorEquative μ a b n ∧ ¬ factorEquative (fun x ↦ μ x + c) a b n := by
  refine ⟨id, 1, 2, 1, 2, ?_, ?_⟩ <;> norm_num [factorEquative]

end Factor

end Degree
