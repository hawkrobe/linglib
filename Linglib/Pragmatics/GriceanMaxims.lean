import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Insert
import Linglib.Core.Order.Minimal

/-!
# The Gricean maxim of Quantity

[grice-1975]'s maxim of Quantity asks a speaker to make the contribution as informative as
required and no more. This file states both submaxims for a referring expression, whose
required information is the identity of its referent. A description `d` with extension
`ext d` *distinguishes* the referent `r` from a contrast set `C` when it holds of `r` and of
no member of `C`, the first submaxim; it is not more informative than required when it is
`Minimal` among the distinguishing descriptions under an order on descriptions that the
consumer supplies, the second. `quantityViolation` classifies a description as
under-informative, over-informative or neither.

## Implementation notes

* The order on descriptions is content, not extension: every distinguishing description of
  `r` against `C` has the same extension on `insert r C`, so the second submaxim cannot be
  read off extensions. [dale-reiter-1995] orders attribute–value sets by inclusion and
  [engelhardt-etal-2006] a bare noun below its modified forms.
* `Distinguishes.mono` records the coherence a consumer's order should have with the
  extension: when more content means a smaller extension, adding content to a distinguishing
  description that still holds of the referent cannot lose it.

## References

* [grice-1975]
* [dale-reiter-1995]
* [engelhardt-etal-2006]
-/

namespace Pragmatics.GriceanMaxims

variable {D E : Type*}

section Distinguishes

variable (ext : D → Set E) (C : Finset E) (r : E) (d : D)

/-- `d` distinguishes `r` from the contrast set `C`: it holds of `r` and of no member of
`C`. -/
def Distinguishes : Prop := r ∈ ext d ∧ ∀ c ∈ C, c ∉ ext d

instance [∀ d, DecidablePred (· ∈ ext d)] : Decidable (Distinguishes ext C r d) := by
  unfold Distinguishes; infer_instance

variable {ext C r d}

theorem distinguishes_iff_disjoint :
    Distinguishes ext C r d ↔ r ∈ ext d ∧ Disjoint (ext d) C := by
  simp [Distinguishes, Set.disjoint_right]

/-- Against every other member of a finite domain, a description distinguishes `r` exactly
when `r` is its whole extension. -/
theorem distinguishes_univ_erase_iff [Fintype E] [DecidableEq E] :
    Distinguishes ext (Finset.univ.erase r) r d ↔ ext d = {r} := by
  simp only [Distinguishes, Finset.mem_erase, Finset.mem_univ, and_true,
    Set.eq_singleton_iff_unique_mem]
  exact and_congr_right fun _ ↦ ⟨fun h x hx ↦ by_contra fun hxr ↦ h x hxr hx,
    fun h c hc hc' ↦ hc (h c hc')⟩

/-- A distinguishing description distinguishes against any smaller contrast set. -/
theorem Distinguishes.anti (h : Distinguishes ext C r d) {C' : Finset E} (hC : C' ⊆ C) :
    Distinguishes ext C' r d :=
  ⟨h.1, fun c hc ↦ h.2 c (hC hc)⟩

/-- When more content means a smaller extension, adding content to a distinguishing
description that still holds of the referent keeps it distinguishing. -/
theorem Distinguishes.mono [Preorder D] (hext : Antitone ext) (h : Distinguishes ext C r d)
    {d' : D} (hd : d ≤ d') (hr : r ∈ ext d') : Distinguishes ext C r d' :=
  ⟨hr, fun c hc hc' ↦ h.2 c hc (hext hd hc')⟩

end Distinguishes

/-! ### The two submaxims -/

/-- The direction in which a description violates Quantity: too little content to
distinguish its referent, or more than distinguishing it requires. -/
inductive QuantityViolation
  | underInformative
  | overInformative
  deriving DecidableEq, Repr

section Violation

variable [Preorder D] (ext : D → Set E) (C : Finset E) (r : E) (d : D)
  [DecidablePred (Distinguishes ext C r)] [DecidablePred (Minimal (Distinguishes ext C r))]

/-- The Quantity status of `d` as a description of `r` against `C`: under-informative when it
does not distinguish `r`, over-informative when a briefer description does, and neither when
it is a minimal distinguishing description. -/
def quantityViolation : Option QuantityViolation :=
  if Distinguishes ext C r d then
    if Minimal (Distinguishes ext C r) d then none else some .overInformative
  else some .underInformative

variable {ext C r d}

theorem quantityViolation_eq_none_iff :
    quantityViolation ext C r d = none ↔ Minimal (Distinguishes ext C r) d := by
  unfold quantityViolation
  split_ifs with h₁ h₂
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by simp) h₂
  · exact iff_of_false (by simp) fun h ↦ h₁ h.prop

theorem quantityViolation_eq_under_iff :
    quantityViolation ext C r d = some .underInformative ↔ ¬ Distinguishes ext C r d := by
  unfold quantityViolation
  split_ifs with h₁ h₂ <;> simp [h₁]

/-- A description is over-informative exactly when it distinguishes its referent and so does
a briefer one. -/
theorem quantityViolation_eq_over_iff :
    quantityViolation ext C r d = some .overInformative ↔
      Distinguishes ext C r d ∧ ∃ d' < d, Distinguishes ext C r d' := by
  unfold quantityViolation
  split_ifs with h₁ h₂
  · exact iff_of_false (by simp) fun ⟨_, _, hd', h'⟩ ↦ h₂.not_prop_of_lt hd' h'
  · exact iff_of_true rfl ⟨h₁, (not_minimal_iff_exists_lt h₁).mp h₂⟩
  · exact iff_of_false (by simp) fun h ↦ h₁ h.1

end Violation

end Pragmatics.GriceanMaxims
