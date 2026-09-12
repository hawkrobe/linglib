import Linglib.Logic.Duality
import Linglib.Core.Data.Trivalent
import Linglib.Semantics.Plurality.Basic

/-!
# Trivalent plural predication

The trivalent value of plural predication after [kriz-spector-2021]: "the Xs are P" is true
when every atom of the plurality satisfies `P`, false when none does, and undefined
otherwise (`pluralTruthValue`, the library's `Trivalent.dist`). The gap is symmetric under
negation (`homogeneity_gap_symmetric`, `pluralTruthValue_neg`), which is why a plural
sentence and its negation are undefined in the same worlds. A homogeneity parameter
`HomParam` selects a sub-plurality for each plurality, and universal quantification over
admissible parameters (`allViaForallH`) recovers the atom-wise universal reading
(`allViaForallH_iff_allSatisfy`).

## Implementation notes

`HomParam` is a single-argument, sub-plurality-valued simplification of the paper's
homogeneity parameter, which is indexed by argument positions and valued in generalised
quantifiers over convex candidate domains; the paper's own candidates, parameters, and
*all* are formalized in `Studies/KrizSpector2021.lean`.

## References

* [kriz-spector-2021]
* [van-fraassen-1966]
-/
namespace Plurality.Trivalent

open _root_.Plurality

variable {Atom W : Type*}

/-! ### Trivalent truth values -/

/-- The trivalent truth value for plural predication "the Xs are P".

- TRUE: all atoms satisfy `P` (vacuously on `∅`)
- FALSE: nonempty plurality with no atoms satisfying `P`
- GAP: witnesses on both sides

This is the core of [kriz-spector-2021]: predication on a plurality
is super-true iff the predicate holds at every atom, super-false iff it
fails at every atom, gap otherwise. The [van-fraassen-1966]
supervaluation framing (each atom as a specification point) is
documented by `Semantics.Supervaluation.superTrue_eq_dist`. -/
@[reducible] def pluralTruthValue (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) : _root_.Trivalent :=
  Trivalent.dist x (λ a => P a w)

@[simp]
theorem pluralTruthValue_eq_true_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .true ↔ allSatisfy P x w :=
  Trivalent.dist_eq_true_iff x _

@[simp]
theorem pluralTruthValue_eq_false_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .false ↔ x.Nonempty ∧ noneSatisfy P x w :=
  Trivalent.dist_eq_false_iff x _

@[simp]
theorem pluralTruthValue_eq_gap_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .indet ↔
    (∃ a ∈ x, P a w) ∧ (∃ a ∈ x, ¬ P a w) :=
  Trivalent.dist_eq_indet_iff x _

theorem allSatisfy_imp_noneSatisfy_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allSatisfy P x w → noneSatisfy (λ a w => ¬ P a w) x w := by
  intro h a ha hPa; exact hPa (h a ha)

theorem noneSatisfy_imp_allSatisfy_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    noneSatisfy P x w → allSatisfy (λ a w => ¬ P a w) x w := id

/-! ### The homogeneity theorem -/

/-- The gap condition: some but not all atoms satisfy `P`. -/
def inGap (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  (∃ a ∈ x, P a w) ∧ (∃ a ∈ x, ¬ P a w)

/-- **Homogeneity Theorem** ([kriz-spector-2021]). The gap is
    symmetric under negation: a world is in the gap for `P` iff it is
    in the gap for `¬P`. This explains why "the Xs are P" and "the Xs
    aren't P" are both undefined in exactly the same worlds. -/
theorem homogeneity_gap_symmetric (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    inGap P x w ↔ inGap (λ a w => ¬ P a w) x w := by
  unfold inGap
  refine ⟨λ ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ => ?_,
          λ ⟨⟨a, ha, hnPa⟩, ⟨b, hb, hnnPb⟩⟩ => ?_⟩
  · exact ⟨⟨b, hb, hPb⟩, ⟨a, ha, λ hnPa => hnPa hPa⟩⟩
  · refine ⟨⟨b, hb, ?_⟩, ⟨a, ha, hnPa⟩⟩
    by_contra hPb; exact hnnPb hPb

/-- Corollary: `pluralTruthValue` is gap iff the negated version is gap. -/
theorem pluralTruthValue_gap_iff_neg_gap (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (_hne : x.Nonempty) :
    pluralTruthValue P x w = .indet ↔
    pluralTruthValue (λ a w => ¬ P a w) x w = .indet := by
  rw [pluralTruthValue_eq_gap_iff, pluralTruthValue_eq_gap_iff]
  refine ⟨λ ⟨⟨a, ha, hPa⟩, ⟨b, hb, hnPb⟩⟩ => ?_,
          λ ⟨⟨a, ha, hnPa⟩, ⟨b, hb, hnnPb⟩⟩ => ?_⟩
  · exact ⟨⟨b, hb, hnPb⟩, ⟨a, ha, λ hnPa => hnPa hPa⟩⟩
  · refine ⟨⟨b, hb, ?_⟩, ⟨a, ha, hnPa⟩⟩
    by_contra hPb; exact hnnPb hPb

/-- **Homogeneity Polarity**: truth and falsity swap under negation
    on nonempty pluralities; the gap is preserved. Empty `x` makes both
    `allSatisfy P` and `allSatisfy ¬P` vacuously true, so the theorem
    requires `x.Nonempty`. -/
theorem pluralTruthValue_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    pluralTruthValue (λ a w => ¬ P a w) x w =
    match pluralTruthValue P x w with
    | .true => .false
    | .false => .true
    | .indet => .indet := by
  cases h : pluralTruthValue P x w
  · rw [pluralTruthValue_eq_true_iff] at h
    rw [pluralTruthValue_eq_false_iff]
    exact ⟨hne, λ a ha hnPa => hnPa (h a ha)⟩
  · rw [pluralTruthValue_eq_false_iff] at h
    rw [pluralTruthValue_eq_true_iff]
    intro a ha hPa; exact h.2 a ha hPa
  · rw [pluralTruthValue_eq_gap_iff] at h
    rw [pluralTruthValue_eq_gap_iff]
    obtain ⟨⟨a, ha, hPa⟩, ⟨b, hb, hnPb⟩⟩ := h
    exact ⟨⟨b, hb, hnPb⟩, ⟨a, ha, λ hnPa => hnPa hPa⟩⟩

/-! ### The homogeneity parameter H

K&S parameterise interpretation by `H`, mapping each argument position to a
candidate denotation. The formalisation here treats `H` as a
**single-argument** sub-plurality selector — a simplification of K&S's
multi-argument candidate-GQ-valued `H` (their H is morally
`ArgIdx × Plurality → Cand_x`, supporting their Desideratum B on
co-referential plural arguments). The reductive `allViaForallH_iff_allSatisfy`
below reflects this simplification: K&S's actual `H` does not collapse to
atom-universal in non-monotonic positions. -/

/-- A homogeneity parameter selects, for each plurality, a sub-plurality. -/
def HomParam (Atom : Type*) : Type _ := Finset Atom → Finset Atom

/-- An admissible homogeneity parameter maps `x` to a nonempty sub-plurality. -/
def isAdmissible (H : HomParam Atom) (x : Finset Atom) : Prop :=
  H x ⊆ x ∧ (H x).Nonempty

/-- The identity parameter `H(x) = x` (universal/maximal reading). -/
def HomParam.id : HomParam Atom := λ x => x

theorem isAdmissible_id (x : Finset Atom) (hne : x.Nonempty) :
    isAdmissible (HomParam.id (Atom := Atom)) x :=
  ⟨Finset.Subset.refl x, hne⟩

/-- Interpretation of a distributive predicate parameterised by `H`. -/
def interpWithH (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (H : HomParam Atom) (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ H x, P a w

instance (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (H : HomParam Atom) (x : Finset Atom) (w : W) :
    Decidable (interpWithH P H x w) :=
  inferInstanceAs (Decidable (∀ a ∈ H x, P a w))

/-- Universal quantification over admissible `H`. -/
def allViaForallH (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ H : HomParam Atom, isAdmissible H x → interpWithH P H x w

/-- Universal `H`-quantification reduces to atom-wise universal, in the
    file's simplified `H` typing. K&S's actual `H`, valued in candidate
    GQs, does not collapse this way in non-monotonic positions. -/
theorem allViaForallH_iff_allSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w := by
  refine ⟨λ hall a ha => ?_, λ hall H hAdm a ha => hall a (hAdm.1 ha)⟩
  have hAdm : isAdmissible (λ _ => ({a} : Finset Atom)) x :=
    ⟨Finset.singleton_subset_iff.mpr ha, ⟨a, Finset.mem_singleton.mpr rfl⟩⟩
  exact hall (λ _ => {a}) hAdm a (Finset.mem_singleton.mpr rfl)

/-- Trivalent truth via `H`-quantification matches `pluralTruthValue`. -/
theorem forallH_true_iff_pluralTrue (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ pluralTruthValue P x w = .true := by
  rw [allViaForallH_iff_allSatisfy, pluralTruthValue_eq_true_iff]

end Plurality.Trivalent
