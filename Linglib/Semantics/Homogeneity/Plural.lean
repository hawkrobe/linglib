import Linglib.Semantics.Homogeneity.Usable
import Linglib.Semantics.Plurality.Trivalent
import Linglib.Semantics.Supervaluation.Basic

/-!
# Homogeneity: the plural instantiation

Plural definite predication as the atoms-instantiation of the homogeneity
substrate, after [kriz-2016]: `barePlural P x` is the trivalent sentence
"the Xs are P" (supervaluation over the atoms of the plurality), and
`allPlural P x` is its gap removal — *all*'s semantic contribution.
Originates with [kriz-2016]; consumed by `Studies/Kriz2016.lean`,
`Studies/BarLev2021.lean`, and `Studies/KrizSpector2021.lean`.

## Main definitions

* `barePlural`: the bare plural sentence as a `Prop3`.
* `allPlural`: the *all*-sentence, `Prop3.metaAssert` of `barePlural`.

## Main results

* `allPlural_prevents_nonmax`, `allPlural_blocked_by_wide_issue`,
  `allPlural_exceptions_unmentionable`: *all* forces literal truth and
  blocks non-maximal use.
* `barePlural_eq_superTrue`: plural predication is supervaluation over
  atoms.

## References

* [M. Križ, *Homogeneity, Non-Maximality, and All*][kriz-2016]
-/

namespace Semantics.Homogeneity

open Trivalent (Prop3)
open Semantics.Plurality
open Semantics.Plurality.Trivalent

variable {Atom W : Type*} (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
  (x : Finset Atom)

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePlural : Prop3 W :=
  λ w => pluralTruthValue P x w

/-- The *all*-sentence "all the Xs are P". Per [kriz-2016] §3.1, *all*'s
    semantic contribution is gap removal, so the semantics is derived from
    the bare plural via `Prop3.metaAssert` rather than stipulated. -/
def allPlural : Prop3 W :=
  (barePlural P x).metaAssert

/-- *all* eliminates the extension gap. -/
theorem gapExt_allPlural : (allPlural P x).gapExt = ∅ :=
  Trivalent.Prop3.gapExt_metaAssert _

/-- An *all*-sentence is never homogeneous. -/
theorem not_isHomogeneous_allPlural : ¬isHomogeneous (allPlural P x) :=
  not_isHomogeneous_metaAssert _

/-- The bare plural and the *all*-sentence are true in the same worlds. -/
theorem posExt_allPlural : (allPlural P x).posExt = (barePlural P x).posExt :=
  Trivalent.Prop3.posExt_metaAssert _

/-- *all* absorbs the gap into the negative extension. -/
theorem negExt_allPlural :
    (allPlural P x).negExt = (barePlural P x).negExt ∪ (barePlural P x).gapExt :=
  Trivalent.Prop3.negExt_metaAssert _

/-- *all*-sentences are bivalent. -/
theorem isBivalent_allPlural : (allPlural P x).isBivalent :=
  Trivalent.Prop3.isBivalent_metaAssert _

/-- An *all*-sentence is true iff all atoms satisfy `P`. -/
theorem allPlural_eq_true_iff (w : W) :
    allPlural P x w = .true ↔ allSatisfy P x w := by
  rw [← pluralTruthValue_eq_true_iff]
  simp only [allPlural, barePlural, Trivalent.Prop3.metaAssert_apply]
  generalize pluralTruthValue P x w = t
  cases t <;> simp

/-- `bivalentPred` of an *all*-sentence is true iff `allSatisfy` holds.
    Cf. `KrizSpector2021.all_addressing_iff_relevant`. -/
theorem bivalentPred_allPlural_eq_allSatisfy (w : W) :
    bivalentPred (allPlural P x) w = true ↔ allSatisfy P x w := by
  simp only [bivalentPred, beq_iff_eq]
  exact allPlural_eq_true_iff P x w

/-- If an *all*-sentence is usable at `w`, all atoms satisfy `P` at `w`:
    bivalence turns usability's not-false clause into literal truth.
    Cf. `allPlural_blocked_by_wide_issue` for the complementary Addressing
    direction. -/
theorem allPlural_prevents_nonmax (q : QUD W) (w : W)
    (h : usable q (allPlural P x) w) : allSatisfy P x w :=
  (allPlural_eq_true_iff P x w).mp
    (((usable_iff_of_isBivalent (isBivalent_allPlural P x) q w).mp h).1)

/-- An *all*-sentence cannot address a "wide" issue — one with a cell
    straddling the *all*/not-*all* boundary ([kriz-2016] §3.4). -/
theorem allPlural_blocked_by_wide_issue (q : QUD W)
    (hWide : ∃ w₁ w₂, q.r w₁ w₂ ∧ allSatisfy P x w₁ ∧ ¬ allSatisfy P x w₂) :
    ¬ addressesIssue q (allPlural P x) := by
  intro hAddr
  obtain ⟨w₁, w₂, hEq, h1, h2⟩ := hWide
  have h2' : allPlural P x w₂ = .false := by
    cases isBivalent_allPlural P x w₂ with
    | inl h => exact absurd ((allPlural_eq_true_iff P x w₂).mp h) h2
    | inr h => exact h
  exact hAddr ⟨w₁, w₂, hEq, (allPlural_eq_true_iff P x w₁).mpr h1, h2'⟩

/-- A usable *all*-sentence leaves no exceptions to mention: "#Although all
    the professors smiled, Smith didn't" is contradictory. The bare-plural
    unmentionability result proper ([kriz-2016] §4.1) is
    `exception_unaddressable`. -/
theorem allPlural_exceptions_unmentionable (q : QUD W) (w : W) (a : Atom)
    (ha : a ∈ x) (h : usable q (allPlural P x) w) : P a w :=
  allPlural_prevents_nonmax P x q w h a ha

/-- The bare plural at `w` equals `superTrue` with atoms as specification
    points and `P(·, w)` as the evaluation function — plural predication is
    supervaluation over atoms ([fine-1975]). -/
theorem barePlural_eq_superTrue (hne : x.Nonempty) (w : W) :
    barePlural P x w =
    Semantics.Supervaluation.superTrue (fun a => P a w) ⟨x, hne⟩ := by
  simp only [barePlural, pluralTruthValue]
  rw [Semantics.Supervaluation.superTrue_eq_dist]

/-- An *all*-sentence is never indefinite. -/
theorem allPlural_ne_indet (w : W) : allPlural P x w ≠ .indet := by
  rcases isBivalent_allPlural P x w with h | h <;> simp [h]

end Semantics.Homogeneity
