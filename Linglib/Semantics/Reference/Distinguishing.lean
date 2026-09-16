import Mathlib.Data.Finset.Basic
import Linglib.Semantics.Reference.Iota

/-!
# Distinguishing descriptions

A description identifies its referent against a contrast set when it holds of the referent
and of no distractor, [dale-reiter-1995]'s distinguishing description and the first submaxim
of [grice-1975]'s Quantity as [engelhardt-etal-2006] reads it for referring expressions. It is
the Russellian uniqueness of `Reference.russellIota` over the domain the contrast set restricts
(`distinguishes_iff_russellIota`), stated here with a finite contrast set and a description's
extension so that it decides on a display.

## Main definitions

* `Reference.Distinguishes`: `d` holds of `r` and of no member of `C`.

## Main results

* `distinguishes_iff_russellIota`: identification against `C` is the definite's uniqueness on
  `insert r C`.
* `distinguishes_univ_erase_iff`: against every other individual, `r` is the whole extension.

## References

* [dale-reiter-1995]
* [grice-1975]
* [engelhardt-etal-2006]
-/

namespace Reference

variable {D E : Type*} (ext : D → Set E) (C : Finset E) (r : E) (d : D)

/-- `d` distinguishes `r` from the contrast set `C`: it holds of `r` and of no member of
`C`. -/
def Distinguishes : Prop := r ∈ ext d ∧ ∀ c ∈ C, c ∉ ext d

instance [∀ d, DecidablePred (· ∈ ext d)] : Decidable (Distinguishes ext C r d) := by
  unfold Distinguishes; infer_instance

variable {ext C r d}

theorem distinguishes_iff_disjoint :
    Distinguishes ext C r d ↔ r ∈ ext d ∧ Disjoint (ext d) C := by
  simp [Distinguishes, Set.disjoint_right]

/-- Identification against a contrast set that excludes the referent is the Russellian
uniqueness of the description on the domain `insert r C`. -/
theorem distinguishes_iff_russellIota [DecidableEq E] (hr : r ∉ C) :
    Distinguishes ext C r d ↔ russellIota (fun x ↦ x ∈ ext d ∧ x ∈ insert r C) = some r := by
  rw [russellIota_eq_some_iff]
  simp only [Distinguishes, Finset.mem_insert, true_or, and_true]
  exact and_congr_right fun _ ↦
    ⟨fun h x ⟨hx, hxr⟩ ↦ hxr.elim id fun hxC ↦ (h x hxC hx).elim,
      fun h c hc hc' ↦ hr (h c ⟨hc', .inr hc⟩ ▸ hc)⟩

/-- Against every other individual of a finite domain, a description distinguishes `r` exactly
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

end Reference
