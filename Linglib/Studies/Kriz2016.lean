import Linglib.Semantics.Homogeneity.Plural

/-!
# Križ (2016): Homogeneity, Non-Maximality, and All

This file formalizes [kriz-2016]'s account of non-maximal readings of definite plurals. *The
professors smiled* is neither true nor false when some but not all of them smiled, and the
sentence is nonetheless usable there whenever the current issue does not distinguish that
situation from one in which all smiled; *all* removes the gap and with it the non-maximal
reading. A five-world model of three professors runs the account end to end on the library's
homogeneity substrate (`barePlural`, `allPlural`, both originating with this paper): the
non-maximal use under a coarse issue and its absence under a fine one, the unusability of the
*all*-sentence at any gap world, the unmentionability of exceptions
(`smith_exception_unaddressable`), and the paper's prediction that what an exception does
instead matters, since a visibly angry
Smith falls into a different cell of the coarse issue than a neutral one
(`bare_usable_neutral_not_angry`). Conjunctions of names, modelled as plurals over their
conjuncts, are predicted to allow non-maximal readings they rarely have
(`conj_modeled_as_plural_predicts_nonmax`), which the paper answers with an accommodated finer
issue.

## Implementation notes

* `QUD W` is the substrate partition type, not the question stack of [roberts-1996]: the
  paper's §4.5 argues that the current issue is an overarching property of the discourse that
  is not directly manipulable, so `coarseQ` and `fineQ` are constructions for the model.
* Following §4.4, the gap is trivalent but not presuppositional (contra [gajewski-2005]).
* The §4.5 puzzle of numerals (*the ten professors smiled* resists non-maximality) is left open,
  as in the paper, and so is the accommodation step of §6.2.

## References

* [kriz-2016]
* [kriz-2015] — the dissertation the account develops
* [lasersohn-1999], [kroch-1974] — pragmatic halos and the unmentionability of exceptions
* [szabolcsi-haddican-2004], [magri-2014] — the homogeneity of conjunctions
-/

namespace Kriz2016

open Homogeneity

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
    barePlural smiled profs .allSmiled = .true := by decide

theorem bare_smithNeutral :
    barePlural smiled profs .smithNeutral = .indet := by decide

theorem bare_onlyLeeSmiled :
    barePlural smiled profs .onlyLeeSmiled = .indet := by decide

theorem bare_noneSmiled :
    barePlural smiled profs .noneSmiled = .false := by decide

/-- The bare plural about the professors is homogeneous: `smithNeutral` is in
    the gap. -/
theorem bare_profs_homogeneous :
    isHomogeneous (barePlural smiled profs) :=
  isHomogeneous_of_gap (barePlural smiled profs) .smithNeutral (by decide)

/-! #### End-to-end predictions -/

/-- The bare plural is usable at `smithNeutral` under the coarse QUD: the
    non-maximal reading. -/
theorem smithNeutral_usable_coarse :
    usable coarseQ (barePlural smiled profs) .smithNeutral := by decide

/-- The bare plural is not usable at `smithNeutral` under the fine QUD. -/
theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePlural smiled profs) .smithNeutral := by decide

/-- The *all*-sentence is not usable at `smithNeutral` under any QUD. -/
theorem all_not_usable_smithNeutral (q : QUD ProfWorld)
    (h : usable q (allPlural smiled profs) .smithNeutral) : False :=
  absurd (allPlural_prevents_nonmax smiled profs q .smithNeutral h) (by decide)

/-- Wherever the *all*-sentence is usable, Smith smiled. -/
theorem smith_exception_unmentionable (q : QUD ProfWorld) (w : ProfWorld)
    (h : usable q (allPlural smiled profs) w) :
    smiled .smith w :=
  allPlural_exceptions_unmentionable smiled profs q w .smith (by decide) h

/-- The coarse QUD communicates the gap-world `smithNeutral`. -/
theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePlural smiled profs) :=
  ⟨.allSmiled, by decide, by decide⟩

/-- The fine QUD does not communicate `smithNeutral`. -/
theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePlural smiled profs) := by
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
def smithDidntSmile : Trivalent.Prop3 ProfWorld :=
  λ w => if smiled .smith w then .false else .true

/-- Under the coarse issue licensing the non-maximal use at `smithNeutral`,
    "…but Smith didn't" cannot address the issue (§4.1). -/
theorem smith_exception_unaddressable :
    ¬ addressesIssue coarseQ smithDidntSmile :=
  exception_unaddressable coarseQ (barePlural smiled profs) smithDidntSmile
    .smithNeutral smithNeutral_usable_coarse (by decide) (by decide)

/-! #### What exceptions do (§4.2)

Whether an exception is tolerated depends on what it does instead: Smith
looking neutral is irrelevant to reception, Smith looking angry is not. The
model places `smithNeutral` and `smithAngry` in different `coarseQ` cells,
so the same sentence under the same QUD is usable at one gap-world and not
the other — a contrast unavailable to accounts without an issue parameter
(restricted reference, alternative geometry). -/

theorem bare_smithAngry :
    barePlural smiled profs .smithAngry = .indet := by decide

/-- The bare plural is not usable at `smithAngry` under the coarse QUD:
    `smithAngry` shares its cell with `onlyLeeSmiled`, and neither is in the
    positive extension. -/
theorem bare_smithAngry_not_usable_coarse :
    ¬ usable coarseQ (barePlural smiled profs) .smithAngry := by decide

/-- The §4.2 contrast: same sentence, same QUD, opposite usability at the
    two gap-worlds. -/
theorem bare_usable_neutral_not_angry :
    usable coarseQ (barePlural smiled profs) .smithNeutral ∧
    ¬ usable coarseQ (barePlural smiled profs) .smithAngry :=
  ⟨smithNeutral_usable_coarse, bare_smithAngry_not_usable_coarse⟩

end FiniteModel

/-! ### Conjunction overgeneration (§6.2)

Conjunctions of proper names are homogeneous ([szabolcsi-haddican-2004],
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
    barePlural wentThere threeCoworkers .dorasMissing = .indet := by decide

/-- Modelled as a plural over {Bert, Claire, Dora}, the conjunction is
    predicted usable at the gap-world `dorasMissing` under the coarse issue —
    the overgenerated non-maximal reading. -/
theorem conj_modeled_as_plural_predicts_nonmax :
    usable coarseConjQ (barePlural wentThere threeCoworkers) .dorasMissing := by
  decide

end ConjunctionOvergeneration

end Kriz2016
