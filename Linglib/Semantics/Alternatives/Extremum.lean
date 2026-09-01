import Mathlib.Order.Bounds.Image
import Linglib.Semantics.Degree.Predicate
import Linglib.Semantics.Exhaustification.Chain

/-!
# Maximally informative alternatives

This file defines the maximally informative member of a scale-indexed family of
propositions `P : α → Set W`: `IsMaxInf P x w` holds when `P x` is true at `w` and entails
every member of the family true at `w`, i.e. `P x` is the least element under `⊆` of the
image of the true set `{y | w ∈ P y}`. The per-world reading `IsLeast {y | w ∈ P y} x` maps
to it along a monotone `P` by mathlib's `Monotone.map_isLeast`, and along an antitone one
by `Antitone.map_isGreatest`.

## Main declarations

* `IsMaxInf`, `HasMaxInf`: the maximally informative alternative and its existence.
* `hasMaxInf_iff_isGreatest`, `hasMaxInf_iff_isLeast`: on a strictly antitone (monotone)
  family, the maximally informative degree is the greatest (least) true one.
* `exhChain_iff_isMaxInf`: exhaustifying a strictly antitone family against its stronger
  members is asserting the prejacent maximally informative.
* `hasMaxInf_ge_over`, `isMaxInf_ge_over_iff`: "at least `d`" always has a maximally
  informative degree, the true measure; `hasMaxInf_le_over`, `isMaxInf_le_over_iff` are
  the duals.
* `not_hasMaxInf_gt_over`, `hasMaxInf_gt_over_nat`: "more than `d`" has no maximally
  informative degree on a dense scale and has one on `ℕ`.

## References

* [D. Fox, *Free choice and the theory of scalar implicatures* (2007)][fox-2007]
* [D. Fox and M. Hackl, *The universal density of measurement* (2006)][fox-hackl-2006]
* [S. Beck and H. Rullmann, *A flexible approach to exhaustivity in questions*
  (1999)][beck-rullmann-1999]
* [K. von Fintel, D. Fox and S. Iatridou, *Definiteness as maximal informativeness*
  (2014)][von-fintel-fox-iatridou-2014]
* [V. Rouillard, *Maximal informativity accounts for the distribution of temporal
  in-adverbials* (2026)][rouillard-2026]
-/

namespace Alternatives

open Degree (Comparison)
open OrderDual

variable {α W : Type*}

/-- `P x` is maximally informative at `w`: true at `w`, and the least under `⊆` among the
members of the family true at `w`. -/
def IsMaxInf (P : α → Set W) (x : α) (w : W) : Prop :=
  IsLeast (P '' {y | w ∈ P y}) (P x)

/-- The family has a maximally informative member at `w`. -/
def HasMaxInf (P : α → Set W) (w : W) : Prop :=
  ∃ x, IsMaxInf P x w

theorem isMaxInf_iff {P : α → Set W} {x : α} {w : W} :
    IsMaxInf P x w ↔ w ∈ P x ∧ ∀ y, w ∈ P y → P x ⊆ P y :=
  and_congr ⟨fun ⟨_, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩ Set.forall_mem_image

/-! ### Strictly monotone families -/

section
variable [LinearOrder α] {φ : α → Set W} {w : W}

/-- On a strictly antitone family, a maximally informative degree is a greatest true degree. -/
theorem hasMaxInf_iff_isGreatest (hφ : StrictAnti φ) :
    HasMaxInf φ w ↔ ∃ m, IsGreatest {d | w ∈ φ d} m := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨m, hm⟩ => ⟨m, hφ.antitone.map_isGreatest hm⟩⟩
  obtain ⟨hxw, hent⟩ := isMaxInf_iff.1 hx
  exact ⟨x, hxw, fun y hy => not_lt.1 fun hxy => (hφ hxy).2 (hent y hy)⟩

/-- On a strictly monotone family, a maximally informative degree is a least true degree. -/
theorem hasMaxInf_iff_isLeast (hφ : StrictMono φ) :
    HasMaxInf φ w ↔ ∃ m, IsLeast {d | w ∈ φ d} m :=
  hasMaxInf_iff_isGreatest (φ := fun d : αᵒᵈ => φ (ofDual d)) fun _ _ h => hφ h

/-- Exhaustifying a strictly antitone family against all stronger members asserts that the
prejacent is maximally informative. -/
theorem exhChain_iff_isMaxInf (hφ : StrictAnti φ) {i : α} :
    Exhaustification.exhChain φ i w ↔ IsMaxInf φ i w := by
  rw [isMaxInf_iff]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h j hij hj => (hφ hij).2 (h j hj)⟩
  exact hφ.antitone (not_lt.1 fun hiy => h y hiy hy)

end

/-! ### Threshold properties -/

section
variable [Preorder α] (μ : W → α) (w : W)

/-- "At least `d`" is maximally informative at the true measure. -/
theorem hasMaxInf_ge_over : HasMaxInf (Comparison.ge.over μ) w :=
  ⟨μ w, (Comparison.antitone_ge_over μ).map_isGreatest isGreatest_Iic⟩

end

section
variable [PartialOrder α] (μ : W → α) {m : α} (w : W)

/-- The maximally informative "at least" degree is the true measure, whenever `m` is
realized. -/
theorem isMaxInf_ge_over_iff (hm : m ∈ Set.range μ) :
    IsMaxInf (Comparison.ge.over μ) m w ↔ μ w = m := by
  refine isMaxInf_iff.trans ⟨fun ⟨hmw, hent⟩ => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hm
    exact le_antisymm (hent (μ w) le_rfl le_rfl) hmw
  · rintro rfl
    exact ⟨le_rfl, fun _ hd _ hw' => le_trans hd hw'⟩

end

section
variable [LinearOrder α] (μ : W → α) {m : α} (w : W)

/-- On a dense scale every degree of which is realized, "more than `d`" has no maximally
informative degree ([fox-hackl-2006]). -/
theorem not_hasMaxInf_gt_over [DenselyOrdered α] (hSurj : Function.Surjective μ) :
    ¬ HasMaxInf (Comparison.gt.over μ) w :=
  (hasMaxInf_iff_isGreatest (Comparison.strictAnti_gt_over μ hSurj)).not.2 fun ⟨g, hg⟩ =>
    let ⟨y, hgy, hyw⟩ := exists_between (hg.1 : g < μ w)
    not_le.2 hgy (hg.2 (hyw : w ∈ Comparison.gt.over μ y))

/-- On a dense scale every degree of which is realized, "less than `d`" has no maximally
informative degree: `not_hasMaxInf_gt_over` on the dual scale. -/
theorem not_hasMaxInf_lt_over [DenselyOrdered α] (hSurj : Function.Surjective μ) :
    ¬ HasMaxInf (Comparison.lt.over μ) w :=
  not_hasMaxInf_gt_over (toDual ∘ μ) w (toDual.surjective.comp hSurj)

/-- "At most `d`" is maximally informative at the true measure: `hasMaxInf_ge_over` on the
dual scale. -/
theorem hasMaxInf_le_over : HasMaxInf (Comparison.le.over μ) w :=
  hasMaxInf_ge_over (toDual ∘ μ) w

/-- The maximally informative "at most" degree is the true measure ([rouillard-2026]'s
direction): `isMaxInf_ge_over_iff` on the dual scale. -/
theorem isMaxInf_le_over_iff (hm : m ∈ Set.range μ) :
    IsMaxInf (Comparison.le.over μ) m w ↔ μ w = m :=
  isMaxInf_ge_over_iff (toDual ∘ μ) (m := toDual m) w hm

end

/-- On `ℕ`, "more than `d`" has a maximally informative degree, `μ w - 1`: the discrete
scale rescues what density forbids. -/
theorem hasMaxInf_gt_over_nat (μ : W → ℕ) (w : W) (hw : w ∈ Comparison.gt.over μ 0) :
    HasMaxInf (Comparison.gt.over μ) w :=
  ⟨μ w - 1, isMaxInf_iff.2 ⟨by have : μ w > 0 := hw; show μ w > μ w - 1; omega,
    fun d hd w' hw' => by
      have : μ w' > μ w - 1 := hw'; have : μ w > d := hd; show μ w' > d; omega⟩⟩

end Alternatives
