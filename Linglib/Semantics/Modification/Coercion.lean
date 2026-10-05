module

public import Linglib.Semantics.Modification.Classification

/-!
# Noun coercion licensed by non-vacuity

Kamp and Partee's non-vacuity principle asks that a predicate have both a positive and a
negative extension in its local domain, and their head primacy principle makes the extension of
the head noun the local domain of its modifier. Partee uses the two to reanalyse privative
adjectives as subsective: where an adjective is vacuous on the literal noun, the noun is widened
until the adjective is not. Kamp anticipates both principles in his §7.

## Main definitions

* `IsNonVacuous P w d`: `P` has a positive and a negative extension within `d` at `w`.
* `LicensedCoercion N adj w`: a widening of `N` under which `adj` is non-vacuous in the
  widened noun at `w`.
* `SubsectiveReanalysis adj`: a reanalysis of `adj` as subsective after widening the noun.

## Implementation notes

This models Partee's widening of *fur* to real or fake fur in her §4, formulae (18) and (20).
`IsNonVacuous` is bivalent, simplifying the partial setting of Kamp and Partee. Complement
coercion (`Studies/Pustejovsky1995.lean`) and the type shifts of noun phrases
(`Semantics/Quantification/NP.lean`) are different notions.

## References

* [kamp-partee-1995]
* [partee-2010]
* [kamp-1975]
-/

@[expose] public section

namespace Modification

variable {W E : Type*}

/-- `P` is non-vacuous within `d` at `w` when both its positive and its negative extension at
`w` meet `d`. -/
def IsNonVacuous (P : Property W E) (w : W) (d : E → Prop) : Prop :=
  (∃ x, d x ∧ P w x) ∧ (∃ x, d x ∧ ¬ P w x)

/-- `IsNonVacuous` is monotone in the local domain. -/
theorem IsNonVacuous.mono {P : Property W E} {w : W} {d d' : E → Prop}
    (h : IsNonVacuous P w d) (hdd' : d ≤ d') : IsNonVacuous P w d' :=
  ⟨h.1.imp fun x hx ↦ ⟨hdd' x hx.1, hx.2⟩, h.2.imp fun x hx ↦ ⟨hdd' x hx.1, hx.2⟩⟩

/-- A predicate and its complement are non-vacuous in the same local domains. -/
theorem isNonVacuous_compl {P : Property W E} {w : W} {d : E → Prop} :
    IsNonVacuous (fun w x ↦ ¬ P w x) w d ↔ IsNonVacuous P w d := by
  unfold IsNonVacuous
  simp only [not_not]
  exact and_comm

/-- A predicate disjoint from `Q` is non-vacuous in any domain that holds an instance of it and
an instance of `Q`. -/
theorem isNonVacuous_of_disjoint {P Q : Property W E} {w : W} {d : E → Prop} (h : Disjoint P Q)
    (hP : ∃ x, d x ∧ P w x) (hQ : ∃ x, d x ∧ Q w x) : IsNonVacuous P w d :=
  ⟨hP, hQ.imp fun _ hx ↦ ⟨hx.1, fun hPx ↦ h.le_bot w _ ⟨hPx, hx.2⟩⟩⟩

/-- A privative modifier is never non-vacuous within the extension of its noun, the local domain
that head primacy assigns. -/
theorem not_isNonVacuous_of_isPrivative {adj : Modifier (Property W E)}
    (hp : Modifier.IsPrivative adj) (N : Property W E) (w : W) :
    ¬ IsNonVacuous (adj N) w (N w) :=
  fun h ↦ h.1.elim fun x hx ↦ isPrivative_iff.1 hp N w x hx.2 hx.1

/-- A coercion of `N` licensed at `w` is a wider noun meaning `shift` such that `adj shift` is
non-vacuous in the extension of `shift` at `w`, the local domain that head primacy assigns. The
`shift` is a full intension although licensing holds at the single world `w`, since a
non-extensional `adj` reads its values at other worlds. -/
structure LicensedCoercion (N : Property W E) (adj : Modifier (Property W E)) (w : W) where
  shift : Property W E
  le_shift : N w ≤ shift w
  satisfies_nvp : IsNonVacuous (adj shift) w (shift w)

/-- A subsective reanalysis of `adjClassical` widens each noun and interprets the adjective
subsectively. Coercion is a last resort for [partee-2010], so `shift_inert` forbids widening a
noun on which `adjClassical` is already non-vacuous. -/
structure SubsectiveReanalysis (adjClassical : Modifier (Property W E)) where
  nounShift : Property W E → Property W E
  adjSubsective : Modifier (Property W E)
  le_nounShift : ∀ N, N ≤ nounShift N
  is_subsective : Modifier.IsSubsective adjSubsective
  shift_inert : ∀ (N : Property W E) (w : W),
    IsNonVacuous (adjClassical N) w (N w) → nounShift N ≤ N

variable {adjClassical : Modifier (Property W E)}

/-- Where direct application is already non-vacuous, the shift is the identity. -/
theorem SubsectiveReanalysis.nounShift_eq_self (R : SubsectiveReanalysis adjClassical)
    {N : Property W E} {w : W} (h : IsNonVacuous (adjClassical N) w (N w)) :
    R.nounShift N = N :=
  le_antisymm (R.shift_inert N w h) (R.le_nounShift N)

/-- Where direct application is already non-vacuous, the reanalysed meaning applies only to
members of the literal noun. -/
theorem SubsectiveReanalysis.adjSubsective_nounShift_le (R : SubsectiveReanalysis adjClassical)
    {N : Property W E} {w : W} (h : IsNonVacuous (adjClassical N) w (N w)) :
    R.adjSubsective (R.nounShift N) ≤ N :=
  (congrArg R.adjSubsective (R.nounShift_eq_self h)).trans_le (R.is_subsective N)

/-- A reanalysis licenses a coercion at every world where the reanalysed meaning is non-vacuous
on the widened noun, unlike a privative adjective (`Partee2010.isPrivative_no_LicensedCoercion`). -/
def SubsectiveReanalysis.licensedCoercion (R : SubsectiveReanalysis adjClassical)
    {N : Property W E} {w : W}
    (h : IsNonVacuous (R.adjSubsective (R.nounShift N)) w (R.nounShift N w)) :
    LicensedCoercion N R.adjSubsective w :=
  ⟨R.nounShift N, R.le_nounShift N w, h⟩

end Modification
