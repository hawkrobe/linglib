import Linglib.Semantics.Modification.Classification

/-!
# Modification-time noun coercion (NVP + HPP)

Noun-extension widening under the Non-Vacuity and Head Primacy
Principles of [kamp-partee-1995], used by [partee-2010] to reanalyse
privative adjectives as subsective-after-coercion; both principles are
anticipated in [kamp-1975] § 7.

## Main definitions

* `isNonVacuous P w d`: NVP at world `w` within local domain `d`.
* `LicensedCoercion N adj w`: NVP-licensed widening of `N`.
* `SubsectiveReanalysis adjClassical`: reanalysis as
  subsective-after-coercion.

## Implementation notes

This models the fake-fur widening of [partee-2010] § 4 (its formulae
(18) and (20)); the constitutive-material case (stone lion) is bracketed
there. `isNonVacuous` states the NVP bivalently, simplifying
[kamp-partee-1995]'s partial setting. Not to be confused with complement
coercion (`Studies/Pustejovsky1995.lean`), NP type-shifting
(`Semantics/Composition/TypeShifting.lean`), or aspectual coercion
(`Semantics/Aspect/Composition.lean`).
-/

namespace Modification

variable {W E : Type*}

/-- Both the positive and the negative extension of `P` at `w` meet the
    local domain `d`. -/
def isNonVacuous (P : Property W E) (w : W) (d : E → Prop) : Prop :=
  (∃ x, d x ∧ P w x) ∧ (∃ x, d x ∧ ¬ P w x)

/-- `isNonVacuous` is monotone in the local domain. -/
theorem isNonVacuous.mono {P : Property W E} {w : W} {d d' : E → Prop}
    (h : isNonVacuous P w d) (hdd' : d ≤ d') : isNonVacuous P w d' :=
  ⟨h.1.imp fun x hx => ⟨hdd' x hx.1, hx.2⟩, h.2.imp fun x hx => ⟨hdd' x hx.1, hx.2⟩⟩

/-- The NVP is self-dual: a predicate and its complement are non-vacuous
    in the same local domains. -/
theorem isNonVacuous_compl {P : Property W E} {w : W} {d : E → Prop} :
    isNonVacuous (fun w x => ¬ P w x) w d ↔ isNonVacuous P w d := by
  unfold isNonVacuous
  simp only [not_not]
  exact and_comm

/-- A wider noun extension `shift ⊇ N` at `w` under which `adj shift`
    is non-vacuous in `shift`'s extension (the HPP local domain). The
    `shift` is a full intension although licensing holds at the single
    world `w`: a non-extensional `adj` reads its values at other worlds. -/
structure LicensedCoercion (N : Property W E) (adj : Modifier (Property W E)) (w : W) where
  shift : Property W E
  le_shift : N w ≤ shift w
  satisfies_nvp : isNonVacuous (adj shift) w (shift w)

/-- Reanalysis of `adjClassical` as subsective-after-coercion. The
    coercion is NVP-conditional — [partee-2010]'s coercion-as-last-resort:
    `shift_inert` forbids widening whenever direct application is already
    non-vacuous (`nounShift_eq_self` derives the identity). -/
structure SubsectiveReanalysis (adjClassical : Modifier (Property W E)) where
  nounShift : Property W E → Property W E
  adjSubsective : Modifier (Property W E)
  le_nounShift : ∀ N, N ≤ nounShift N
  is_subsective : Modifier.isSubsective adjSubsective
  shift_inert : ∀ (N : Property W E) (w : W),
    isNonVacuous (adjClassical N) w (N w) → nounShift N ≤ N

variable {adjClassical : Modifier (Property W E)}

/-- Where direct application is already non-vacuous, the shift is the
    identity. -/
theorem SubsectiveReanalysis.nounShift_eq_self (R : SubsectiveReanalysis adjClassical)
    {N : Property W E} {w : W} (h : isNonVacuous (adjClassical N) w (N w)) :
    R.nounShift N = N :=
  le_antisymm (R.shift_inert N w h) (R.le_nounShift N)

/-- A reanalysis licenses a coercion at every world where the shifted
    noun renders the reanalysed meaning non-vacuous — the positive
    counterpart of `Partee2010.isPrivative_no_LicensedCoercion`. -/
def SubsectiveReanalysis.licensedCoercion (R : SubsectiveReanalysis adjClassical)
    {N : Property W E} {w : W}
    (h : isNonVacuous (R.adjSubsective (R.nounShift N)) w (R.nounShift N w)) :
    LicensedCoercion N R.adjSubsective w :=
  ⟨R.nounShift N, R.le_nounShift N w, h⟩

end Modification
