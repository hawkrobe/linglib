import Linglib.Data.Examples.Kriz2015
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Studies.Magri2014
import Linglib.Semantics.Plurality.Homogeneity.Basic
import Linglib.Semantics.Plurality.Distributivity
import Linglib.Semantics.Plurality.Trivalent

/-!
# Križ (2016): homogeneity, non-maximality, and *all*

This file is the plural instantiation of the homogeneity substrate in
`Semantics.Homogeneity`, after [kriz-2016]: plural predication is trivalent
(`barePluralTV`, atoms as specification points), *all* is gap removal
(`allPluralTV`), and non-maximal readings arise pragmatically when a coarse
issue puts a gap-world in the same cell as a literally-true world (`usable`).
A five-world finite model checks the predictions end-to-end, including the
§4.2 sensitivity to what an exception does instead and the §4.1
unmentionability of exceptions. Closing sections connect the analysis to the
typed data in `Data.Examples.Kriz2015`, to supervaluation ([fine-1975]), and
to [magri-2014]'s rival gap derivation.

## Implementation notes

`QUD W` is the substrate partition type, not the [roberts-1996] QUD-stack:
§4.5 of the paper argues (examples (39)-(40)) that the current issue is an
overarching, not directly manipulable, property of the discourse, so
`coarseQ`/`fineQ` below are pedagogical constructions. Following §4.4, the
gap is trivalent but not presuppositional (contra [gajewski-2005]). The §4.6
numeral puzzle (*the ten professors smiled* resists non-maximality) is left
unaddressed, as in the paper.

## References

* [M. Križ, *Homogeneity, Non-Maximality, and All*][kriz-2016]
* [M. Križ, *Aspects of Homogeneity in the Semantics of Natural Language*][kriz-2015]
* [K. Fine, *Vagueness, Truth and Logic*][fine-1975]
-/

namespace Kriz2016

open Semantics.Plurality
open Semantics.Plurality.Distributivity
open Semantics.Plurality.Trivalent
open Semantics.Homogeneity

variable {Atom W : Type*} [DecidableEq Atom]
variable (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)

/-! ### Plural predication as sentence extension -/

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePluralTV : SentenceTV W :=
  λ w => pluralTruthValue P x w

/-- The *all*-sentence "all the Xs are P". Per §3.1, *all*'s semantic
    contribution is gap removal, so the semantics is derived from the bare
    plural via `removeGap` rather than stipulated. -/
def allPluralTV : SentenceTV W :=
  removeGap (barePluralTV P x)

omit [DecidableEq Atom] in
/-- *all* eliminates the extension gap. -/
theorem all_no_gap : gapExt (allPluralTV P x) = ∅ := by
  by_contra h
  exact removeGap_not_homogeneous (barePluralTV P x) h

omit [DecidableEq Atom] in
/-- An *all*-sentence is never homogeneous. -/
theorem all_not_homogeneous : ¬isHomogeneous (allPluralTV P x) :=
  removeGap_not_homogeneous (barePluralTV P x)

omit [DecidableEq Atom] in
/-- The bare plural and the *all*-sentence are true in the same worlds. -/
theorem all_posExt_eq : posExt (allPluralTV P x) = posExt (barePluralTV P x) :=
  removeGap_posExt_eq (barePluralTV P x)

omit [DecidableEq Atom] in
/-- *all* absorbs the gap into the negative extension. -/
theorem all_negExt_eq :
    negExt (barePluralTV P x) ∪ gapExt (barePluralTV P x) =
    negExt (allPluralTV P x) :=
  (removeGap_negExt_eq (barePluralTV P x)).symm

/-! ### The effect of *all* -/

omit [DecidableEq Atom] in
/-- *all*-sentences are bivalent. -/
theorem all_bivalent : isBivalent (allPluralTV P x) :=
  removeGap_bivalent (barePluralTV P x)

/-- Gap removal on a plural sentence is true iff all atoms satisfy `P`.
    Cf. `KrizSpector2021.removeGap_iff_forallH`. -/
theorem removeGap_plural_true_iff (w : W) :
    removeGap (fun w => pluralTruthValue P x w) w = .true ↔
    allSatisfy P x w := by
  rw [← pluralTruthValue_eq_true_iff]; simp only [removeGap]
  generalize pluralTruthValue P x w = t
  cases t <;> simp

/-- `bivalentPred` of an *all*-sentence is true iff `allSatisfy` holds.
    Cf. `KrizSpector2021.all_addressing_iff_relevant`. -/
theorem bivalentPred_allPluralTV_eq_allSatisfy (w : W) :
    bivalentPred (allPluralTV P x) w = true ↔ allSatisfy P x w := by
  simp only [bivalentPred, beq_iff_eq, allPluralTV]
  exact removeGap_plural_true_iff P x w

/-- If an *all*-sentence is usable at `w`, all atoms satisfy `P` at `w`:
    bivalence turns usability's not-false clause into literal truth.
    Cf. `all_blocked_by_wide_issue` for the complementary Addressing
    direction. -/
theorem all_prevents_nonmax (q : QUD W) (w : W)
    (h : usable q (allPluralTV P x) w) : allSatisfy P x w := by
  have hTrue : allPluralTV P x w = .true :=
    ((bivalent_usable_iff_true q _ (all_bivalent P x) w).mp h).1
  have hBareTrue : barePluralTV P x w = .true := by
    have hMem : w ∈ posExt (allPluralTV P x) := hTrue
    rw [all_posExt_eq P x] at hMem
    exact hMem
  exact (pluralTruthValue_eq_true_iff P x w).mp hBareTrue

/-- An *all*-sentence cannot address a "wide" issue — one with a cell
    straddling the *all*/not-*all* boundary (§3.4). -/
theorem all_blocked_by_wide_issue (q : QUD W)
    (hWide : ∃ w₁ w₂, q.r w₁ w₂ ∧ allSatisfy P x w₁ ∧ ¬ allSatisfy P x w₂) :
    ¬ addressesIssue q (allPluralTV P x) := by
  intro hAddr
  obtain ⟨w₁, w₂, hEq, h1, h2⟩ := hWide
  have h1' : allPluralTV P x w₁ = .true :=
    (removeGap_plural_true_iff P x w₁).mpr h1
  have h2' : allPluralTV P x w₂ = .false := by
    cases all_bivalent P x w₂ with
    | inl h =>
      have hAll : allSatisfy P x w₂ :=
        (removeGap_plural_true_iff P x w₂).mp h
      exact absurd hAll h2
    | inr h => exact h
  exact hAddr ⟨w₁, w₂, hEq, h1', h2'⟩

/-- A usable *all*-sentence leaves no exceptions to mention: "#Although all
    the professors smiled, Smith didn't" is contradictory. The bare-plural
    unmentionability result proper (§4.1) is `smith_exception_unaddressable`
    below. -/
theorem all_exceptions_unmentionable (q : QUD W) (w : W) (a : Atom) (ha : a ∈ x)
    (h : usable q (allPluralTV P x) w) : P a w := by
  have := all_prevents_nonmax P x q w h
  exact this a ha

/-! ### Finite model

Three professors attend Sue's talk; the predicate is "smiled".

| World          | Smith | Jones | Lee | Bare plural | All   |
|----------------|-------|-------|-----|-------------|-------|
| allSmiled      | ✓     | ✓     | ✓   | TRUE        | true  |
| smithNeutral   | ✗     | ✓     | ✓   | GAP         | false |
| smithAngry     | ✗     | ✓     | ✓   | GAP         | false |
| onlyLeeSmiled  | ✗     | ✗     | ✓   | GAP         | false |
| noneSmiled     | ✗     | ✗     | ✗   | FALSE       | false |

`smithNeutral` and `smithAngry` agree on who smiled but differ in what Smith
does instead, which the coarse QUD ("Was the talk well-received?") is
sensitive to (§4.2); the fine QUD ("Did every professor smile?") separates
all worlds. -/

section FiniteModel

/-- Worlds of the five-world model. In both `smithNeutral` and `smithAngry`
    Smith fails to smile; the worlds differ in whether his demeanour is
    relevant to the coarse issue (§4.2). -/
inductive ProfWorld where
  | allSmiled
  | smithNeutral   -- Smith neutral expression (irrelevant exception)
  | smithAngry     -- Smith visibly angry (relevant exception per §4.2)
  | onlyLeeSmiled
  | noneSmiled
  deriving DecidableEq, Repr, Fintype

inductive Prof where
  | smith | jones | lee
  deriving DecidableEq, Repr, Fintype

/-- Which professor smiled in which world. -/
def smiled : Prof → ProfWorld → Prop
  | .smith, .allSmiled      => True
  | .smith, .smithNeutral   => False
  | .smith, .smithAngry     => False
  | .smith, .onlyLeeSmiled  => False
  | .smith, .noneSmiled     => False
  | .jones, .allSmiled      => True
  | .jones, .smithNeutral   => True
  | .jones, .smithAngry     => True
  | .jones, .onlyLeeSmiled  => False
  | .jones, .noneSmiled     => False
  | .lee,   .allSmiled      => True
  | .lee,   .smithNeutral   => True
  | .lee,   .smithAngry     => True
  | .lee,   .onlyLeeSmiled  => True
  | .lee,   .noneSmiled     => False

instance smiled.instDecidable : ∀ p w, Decidable (smiled p w) := by
  intro p w; cases p <;> cases w <;> unfold smiled <;> infer_instance

/-- All three professors. -/
def profs : Finset Prof := Finset.univ

/-- Reception grades for the coarse QUD: Smith's anger pulls reception down
    to `mixed`, his neutrality leaves it `positive` (§4.2). -/
inductive Reception where | positive | mixed | negative
  deriving DecidableEq

def receptionGrade : ProfWorld → Reception
  | .allSmiled => .positive
  | .smithNeutral => .positive
  | .smithAngry => .mixed       -- §4.2: Smith's anger is relevant
  | .onlyLeeSmiled => .mixed
  | .noneSmiled => .negative

/-- Coarse QUD: "Was Sue's talk well-received?" -/
def coarseQ : QUD ProfWorld := QUD.ofDecEq receptionGrade

/-- Fine QUD: "Did every professor smile?" -/
def fineQ : QUD ProfWorld := QUD.ofDecEq id

/-! #### Trivalent values at each world -/

theorem bare_allSmiled :
    barePluralTV smiled profs .allSmiled = .true := by decide

theorem bare_smithNeutral :
    barePluralTV smiled profs .smithNeutral = .indet := by decide

theorem bare_onlyLeeSmiled :
    barePluralTV smiled profs .onlyLeeSmiled = .indet := by decide

theorem bare_noneSmiled :
    barePluralTV smiled profs .noneSmiled = .false := by decide

/-- The bare plural about the professors is homogeneous: `smithNeutral` is in
    the gap. -/
theorem bare_profs_homogeneous :
    isHomogeneous (barePluralTV smiled profs) :=
  isHomogeneous_of_gap (barePluralTV smiled profs) .smithNeutral (by decide)

/-! #### End-to-end predictions -/

/-- The bare plural is usable at `smithNeutral` under the coarse QUD: the
    non-maximal reading. -/
theorem smithNeutral_usable_coarse :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral := by decide

/-- The bare plural is not usable at `smithNeutral` under the fine QUD. -/
theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePluralTV smiled profs) .smithNeutral := by decide

/-- The *all*-sentence is not usable at `smithNeutral` under any QUD. -/
theorem all_not_usable_smithNeutral (q : QUD ProfWorld)
    (h : usable q (allPluralTV smiled profs) .smithNeutral) : False :=
  absurd (all_prevents_nonmax smiled profs q .smithNeutral h) (by decide)

/-- Wherever the *all*-sentence is usable, Smith smiled. -/
theorem smith_exception_unmentionable (q : QUD ProfWorld) (w : ProfWorld)
    (h : usable q (allPluralTV smiled profs) w) :
    smiled .smith w :=
  all_exceptions_unmentionable smiled profs q w .smith (by decide) h

/-- The coarse QUD communicates the gap-world `smithNeutral`. -/
theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePluralTV smiled profs) :=
  ⟨.allSmiled, by decide, by decide⟩

/-- The fine QUD does not communicate `smithNeutral`. -/
theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePluralTV smiled profs) := by
  intro ⟨w', hEq, hTrue⟩
  revert hEq hTrue; cases w' <;> decide

/-! #### Unmentionability of exceptions (§4.1)

"#The professors smiled, but one of them didn't" is infelicitous even where
the non-maximal reading is licensed — the paper's (25a-b), with the
*although* diagnostic traced to [kroch-1974] via [lasersohn-1999]. The
derivation is pure Addressing (the substrate's `exception_unaddressable`):
non-maximal use requires a cell containing both a true-world and the
gap-world, and the exception-mentioning continuation straddles it. -/

/-- "Smith didn't smile", the exception-mentioning continuation. -/
def smithDidntSmile : SentenceTV ProfWorld :=
  λ w => if smiled .smith w then .false else .true

/-- Under the coarse issue licensing the non-maximal use at `smithNeutral`,
    "…but Smith didn't" cannot address the issue (§4.1). -/
theorem smith_exception_unaddressable :
    ¬ addressesIssue coarseQ smithDidntSmile :=
  exception_unaddressable coarseQ (barePluralTV smiled profs) smithDidntSmile
    .smithNeutral smithNeutral_usable_coarse (by decide) (by decide)

/-! #### What exceptions do (§4.2)

Whether an exception is tolerated depends on what it does instead: Smith
looking neutral is irrelevant to reception, Smith looking angry is not. The
model places `smithNeutral` and `smithAngry` in different `coarseQ` cells,
so the same sentence under the same QUD is usable at one gap-world and not
the other — a contrast unavailable to accounts without an issue parameter
(restricted reference, alternative geometry). -/

theorem bare_smithAngry :
    barePluralTV smiled profs .smithAngry = .indet := by decide

/-- The bare plural is not usable at `smithAngry` under the coarse QUD:
    `smithAngry` shares its cell with `onlyLeeSmiled`, and neither is in the
    positive extension. -/
theorem bare_smithAngry_not_usable_coarse :
    ¬ usable coarseQ (barePluralTV smiled profs) .smithAngry := by decide

/-- The §4.2 contrast: same sentence, same QUD, opposite usability at the
    two gap-worlds. -/
theorem bare_usable_neutral_not_angry :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral ∧
    ¬ usable coarseQ (barePluralTV smiled profs) .smithAngry :=
  ⟨smithNeutral_usable_coarse, bare_smithAngry_not_usable_coarse⟩

end FiniteModel

/-! ### The typed switches data

The switches items of `Data.Examples.Kriz2015` show the model's pattern in
the wild: "Oh no, the switches are on!" is acceptable under the existential
issue and unacceptable under the universal one (cf.
`smithNeutral_usable_coarse` vs `smithNeutral_not_usable_fine`), and the
*all* variant is unacceptable even in the permissive context (cf.
`all_not_usable_smithNeutral`). The gap rows lift to `.indet` observations
in the pooled `Generalizations.HomogeneityGap` data. -/

open Generalizations.HomogeneityGap in
/-- Both switches gap rows (positive and negated) observe `.indet`: the gap
    is symmetric under negation. -/
theorem switches_gap_observed_indet :
    (fromExample Kriz2015.Examples.switches_pos_gap).map (·.observed) =
      some .indet ∧
    (fromExample Kriz2015.Examples.switches_neg_gap).map (·.observed) =
      some .indet := by
  decide

open Generalizations.HomogeneityGap in
/-- The model matches the data: the bare plural's value at the gap-world is
    the value the positive gap row observes. -/
theorem model_matches_gap_row :
    (fromExample Kriz2015.Examples.switches_pos_gap).map (·.observed) =
      some (barePluralTV smiled profs .smithNeutral) := by
  decide

/-! ### Supervaluation

Plural predication is supervaluation ([fine-1975]) with atoms as
specification points — the same shape as thresholds for vague predicates,
closest worlds for conditionals (`selectional_eq_dist`), and restrictor
precisifications for reciprocals
(`HaugDalrymple2020.quantifiedReciprocalTV_iff_supervaluation`). -/

open Semantics.Supervaluation (SpecSpace superTrue)

omit [DecidableEq Atom] in
/-- The bare plural at `w` equals `superTrue` with atoms as specification
    points and `P(·, w)` as the evaluation function. -/
theorem barePluralTV_eq_superTrue (hne : x.Nonempty) (w : W) :
    barePluralTV P x w = superTrue (fun a => P a w) ⟨x, hne⟩ := by
  simp only [barePluralTV, pluralTruthValue]
  rw [Semantics.Supervaluation.superTrue_eq_dist]

omit [DecidableEq Atom] in
/-- A homogeneity gap is supervaluation indefiniteness. -/
theorem homogeneity_gap_is_indefiniteness (hne : x.Nonempty) (w : W)
    (hgap : barePluralTV P x w = .indet) :
    superTrue (fun a => P a w) ⟨x, hne⟩ = Trivalent.indet := by
  rw [← barePluralTV_eq_superTrue P x hne w]; exact hgap

omit [DecidableEq Atom] in
/-- An *all*-sentence is never indefinite. -/
theorem all_removes_supervaluation_gap (w : W) :
    allPluralTV P x w ≠ .indet := by
  rcases all_bivalent P x w with h | h <;> simp [h]

/-! ### Conjunction overgeneration (§6.2)

Conjunctions of proper names are homogeneous (Szabolcsi & Haddican 2004,
[magri-2014]) yet generally resist non-maximal readings. Modelled as a
plural over its conjunct atoms, the machinery predicts non-maximal use at a
gap-world (`conj_modeled_as_plural_predicts_nonmax`); the paper's informal
response is that mentioning an individual prompts accommodation of a finer
issue on which no non-maximal reading survives, an accommodation step not
formalized here or in the paper. -/

section ConjunctionOvergeneration

inductive ConjAtom where | bert | claire | dora
  deriving DecidableEq, Repr, Fintype

inductive ConjWorld where | allWent | dorasMissing | onlyBert | noneWent
  deriving DecidableEq, Repr, Fintype

def wentThere : ConjAtom → ConjWorld → Prop
  | .bert,   .allWent       => True
  | .bert,   .dorasMissing  => True
  | .bert,   .onlyBert      => True
  | .bert,   .noneWent      => False
  | .claire, .allWent       => True
  | .claire, .dorasMissing  => True
  | .claire, .onlyBert      => False
  | .claire, .noneWent      => False
  | .dora,   .allWent       => True
  | .dora,   .dorasMissing  => False
  | .dora,   .onlyBert      => False
  | .dora,   .noneWent      => False

instance wentThere.instDecidable : ∀ a w, Decidable (wentThere a w) := by
  intro a w; cases a <;> cases w <;> unfold wentThere <;> infer_instance

def threeCoworkers : Finset ConjAtom := Finset.univ

/-- Cells of the coarse "did anyone go?" issue. -/
inductive ConjPartition where | someWent | noneWent
  deriving DecidableEq

def someWentPartition : ConjWorld → ConjPartition
  | .allWent => .someWent
  | .dorasMissing => .someWent
  | .onlyBert => .someWent
  | .noneWent => .noneWent

def coarseConjQ : QUD ConjWorld := QUD.ofDecEq someWentPartition

theorem conj_dorasMissing_gap :
    barePluralTV wentThere threeCoworkers .dorasMissing = .indet := by decide

/-- Modelled as a plural over {Bert, Claire, Dora}, the conjunction is
    predicted usable at the gap-world `dorasMissing` under the coarse issue —
    the overgenerated non-maximal reading. -/
theorem conj_modeled_as_plural_predicts_nonmax :
    usable coarseConjQ (barePluralTV wentThere threeCoworkers) .dorasMissing := by
  decide

end ConjunctionOvergeneration

/-! ### Križ vs Magri on the gap's value

[magri-2014] derives homogeneity from double exhaustification over
alternative geometry: on a gap scenario, `doubleExh .mystery` is
bivalent-false (`Magri2014.gap_positive_false`) — the gap collapses inside
the semantics. For Križ the same input is `.indet`, and the gap is
pragmatically recoverable under a coarse issue (`gap_enables_nonmax`). A
false sentence is unutterable on standard Gricean terms, so Magri's account
needs additional pragmatic machinery to license the non-maximal uses the
finite model exhibits. `Magri2014.fromPredicate` translates the model's
`(smiled, profs, smithNeutral)` into Magri's count abstraction, so both
operators run on the same input. -/

section MagriDivergence

open Magri2014

/-- A 3-atom Magri scenario where 2 of 3 atoms satisfy the predicate. -/
def magriGapScenario : Scenario :=
  { total := 3, satisfying := 2, valid := by omega }

/-- Counting satisfiers of `smiled` at `smithNeutral` yields the 2-of-3
    scenario: the divergence below is a same-input comparison. -/
theorem fromPredicate_smithNeutral :
    fromPredicate smiled profs .smithNeutral = magriGapScenario := rfl

theorem magriGapScenario_isGap : isGap magriGapScenario = true := by decide

/-- Magri's `doubleExh .mystery` is false on a 2-of-3 gap. -/
theorem magri_2of3_gap_is_bivalent_false :
    doubleExh .mystery magriGapScenario = false :=
  gap_positive_false magriGapScenario magriGapScenario_isGap

/-- On the same input, Magri's operator returns false while Križ's returns
    `.indet` and the sentence is usable under the coarse issue: the two
    accounts assign the gap incompatible statuses. -/
theorem kriz_vs_magri_alternative_geometry :
    doubleExh .mystery (fromPredicate smiled profs .smithNeutral) = false ∧
    barePluralTV smiled profs .smithNeutral = .indet ∧
    usable coarseQ (barePluralTV smiled profs) .smithNeutral :=
  ⟨fromPredicate_smithNeutral.symm ▸ magri_2of3_gap_is_bivalent_false,
   bare_smithNeutral, smithNeutral_usable_coarse⟩

end MagriDivergence

end Kriz2016
