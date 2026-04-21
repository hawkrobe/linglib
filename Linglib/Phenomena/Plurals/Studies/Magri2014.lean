import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Polarity
import Linglib.Phenomena.Plurals.Homogeneity
import Linglib.Phenomena.Plurals.Multiplicity
import Linglib.Theories.Semantics.Exhaustification.Innocent

/-!
# Magri (2014): Homogeneity Effects via Double Strengthening
@cite{magri-2014}

An account for the homogeneity effects triggered by plural definites and
conjunction based on double strengthening. In *Pragmatics, Semantics and
the Case of Scalar Implicatures*, ed. S. Pistoia Reda (Palgrave Macmillan),
99-145.

## Core Idea

Plural definites like *the boys* have a **plain existential semantics**,
equivalent to the indefinite *some boys*. Their universal reading arises
through *double strengthening* modeled on @cite{spector-2007}:

1. The indefinite *some boys* triggers the "only-some" scalar implicature
2. The definite *the boys* triggers the implicature that this "only-some"
   implicature is false
3. The universal reading thus arises as a "not-only-some" implicature

No strengthening occurs in DE environments, where definites reveal their
plain existential semantics --- producing homogeneity effects.

## Formal Structure

The theory reduces to a three-element alternative configuration:

- **MYSTERY**: the item displaying homogeneity (THE / PL / AND_unF)
- **WEAK**: its semantically equivalent alternative (SOME / SING / OR)
- **STRONG**: the stronger alternative (ALL / TWO / BOTH)

The crucial asymmetry: MYSTERY and WEAK are Horn-mates, WEAK and STRONG
are Horn-mates, but MYSTERY is NOT a Horn-mate of STRONG. Horn-mateness
is non-transitive.

## Double Exhaustification

The universal reading arises via two layers of EXH:

1. **Inner EXH**: SOME excludes ALL (standard SI), but THE has no
   excludable alternatives (ALL is not a Horn-mate, SOME is equivalent).
   So EXH(THE) = THE = SOME, EXH(SOME) = SOME AND NOT ALL.

2. **Outer EXH**: At the second level, EXH(SOME) = SOME AND NOT ALL is
   *strictly stronger* than EXH(THE) = SOME. Since SOME is a Horn-mate
   of THE, it becomes excludable at the outer level:
   EXH(EXH(THE)) = SOME AND NOT(SOME AND NOT ALL) = ALL.

## Primal vs Dual

- **Primal theory**: MYSTERY has weak plain meaning, strengthened to STRONG
  in UE. Applies to definites and plural morphology.
- **Dual theory**: MYSTERY has strong plain meaning, weakened to WEAK in DE.
  Applies to unfocused conjunction.

Both derive the same net result: MYSTERY behaves as STRONG in UE,
MYSTERY behaves as WEAK in DE.

## Relationship to @cite{spector-2007}

Magri extends Spector's exhaustivity-based account of plural morphology
(PL/SING/TWO) to plural definites (THE/SOME/ALL) and unfocused conjunction
(AND_unF/OR/BOTH). The key technical innovation is assumption (19): using
*iterated* exhaustification where the *strengthened* alternatives (not
just plain meanings) determine outer-level excludability. Spector's
single-EXH result `Max(P) = {Exhaust(P)}` is formalized in
`ScalarImplicatures/Studies/Spector2007.lean`.
-/

namespace Magri2014

open Core (Polarity)


-- ============================================================
-- SECTION 1: The Alternative Configuration
-- ============================================================

/--
The three items in a double-strengthening configuration.

Each concrete domain (definites, plural morphology, conjunction) provides
a different instantiation.
-/
inductive Role where
  | mystery  -- THE / PL / AND_unF
  | weak     -- SOME / SING / OR
  | strong   -- ALL / TWO / BOTH
  deriving Repr, DecidableEq, Inhabited

/--
Entailment structure between the three items.
STRONG asymmetrically entails both WEAK and MYSTERY.
MYSTERY and WEAK are semantically equivalent (mutual entailment).
-/
def entails : Role → Role → Bool
  | .strong, _         => true   -- STRONG entails everything
  | .mystery, .mystery => true
  | .mystery, .weak    => true   -- MYSTERY ≡ WEAK
  | .weak, .mystery    => true   -- WEAK ≡ MYSTERY
  | .weak, .weak       => true
  | _, _               => false

/-- MYSTERY and WEAK are semantically equivalent (mutual entailment). -/
theorem mystery_equiv_weak :
    entails .mystery .weak = true ∧ entails .weak .mystery = true := ⟨rfl, rfl⟩

/-- STRONG asymmetrically entails WEAK. -/
theorem strong_asymm_entails_weak :
    entails .strong .weak = true ∧ entails .weak .strong = false := ⟨rfl, rfl⟩

/-- STRONG asymmetrically entails MYSTERY. -/
theorem strong_asymm_entails_mystery :
    entails .strong .mystery = true ∧ entails .mystery .strong = false := ⟨rfl, rfl⟩

/--
Horn-mateness: the non-transitive relation that determines which
alternatives are relevant for exhaustification.

WEAK <-> STRONG: Horn-mates (standard scalar pair)
WEAK <-> MYSTERY: Horn-mates (the definite competes with the indefinite)
MYSTERY x STRONG: NOT Horn-mates (the crucial asymmetry!)
-/
def hornMates : Role → Role → Bool
  | .weak, .strong  => true
  | .strong, .weak  => true
  | .weak, .mystery => true
  | .mystery, .weak => true
  | _, _            => false

-- The key asymmetry: MYSTERY and STRONG are not Horn-mates
theorem mystery_not_mate_of_strong : hornMates .mystery .strong = false := rfl
theorem strong_not_mate_of_mystery : hornMates .strong .mystery = false := rfl

-- Sanity: the standard pairs are Horn-mates
theorem weak_strong_mates : hornMates .weak .strong = true := rfl
theorem weak_mystery_mates : hornMates .weak .mystery = true := rfl


/--
The set of excludable alternatives at the inner (first) EXH level.

An alternative psi is excludable w.r.t. prejacent phi when:
1. psi is a Horn-mate of phi
2. psi asymmetrically entails phi (i.e., psi entails phi but phi does not entail psi)
-/
def innerExcludable (prejacent alt : Role) : Bool :=
  hornMates prejacent alt && entails alt prejacent && !(entails prejacent alt)

-- SOME excludes STRONG (the standard "not all" implicature)
theorem some_excludes_all : innerExcludable .weak .strong = true := rfl

-- MYSTERY (THE) does NOT exclude STRONG (ALL) --- not Horn-mates
theorem the_does_not_exclude_all : innerExcludable .mystery .strong = false := rfl

-- MYSTERY (THE) does not exclude WEAK (SOME) --- equivalent, no asymmetric entailment
theorem the_does_not_exclude_some : innerExcludable .mystery .weak = false := rfl

-- WEAK (SOME) does not exclude MYSTERY (THE) --- equivalent, no asymmetric entailment
theorem some_does_not_exclude_the : innerExcludable .weak .mystery = false := rfl


-- ============================================================
-- SECTION 2: Exhaustification (EXH)
-- ============================================================

/--
The semantic value of an item, in an abstract Boolean domain.

We model the "world" as having `n` individuals in a plurality, and a
predicate P that holds of a given number of them. This lets us reason
about SOME (>= 1), ALL (= n), and THE (= SOME by assumption).
-/
structure Scenario where
  /-- Total number of individuals in the plurality -/
  total : Nat
  /-- Number satisfying the predicate -/
  satisfying : Nat
  /-- satisfying <= total -/
  valid : satisfying ≤ total
  deriving Repr

/-- SOME / MYSTERY: at least one satisfies (existential) -/
def someMeaning (s : Scenario) : Bool := s.satisfying ≥ 1

/-- ALL / STRONG: all satisfy (universal) -/
def allMeaning (s : Scenario) : Bool := s.satisfying == s.total

/-- Plain meanings for each role in the PRIMAL theory (definites) -/
def primalMeaning : Role → Scenario → Bool
  | .mystery => someMeaning  -- THE has existential plain meaning
  | .weak    => someMeaning  -- SOME has existential meaning
  | .strong  => allMeaning   -- ALL has universal meaning

/-- THE and SOME have the same plain meaning (the core assumption). -/
theorem mystery_eq_weak_meaning :
    primalMeaning .mystery = primalMeaning .weak := rfl

/-- ALL entails SOME (if all satisfy, then at least one satisfies). -/
theorem strong_entails_weak (s : Scenario) (hn : s.total ≥ 1) :
    allMeaning s = true → someMeaning s = true := by
  simp only [allMeaning, someMeaning, beq_iff_eq, decide_eq_true_eq]
  omega

/--
EXH applied to a prejacent: assert the prejacent and negate all
innerExcludable alternatives (@cite{spector-2007}, definition 18).

  EXH(phi) = phi AND AND{NOT psi : psi innerExcludable w.r.t. phi}
-/
def exh (prejacent : Role) (s : Scenario) : Bool :=
  primalMeaning prejacent s &&
  [Role.mystery, .weak, .strong].all (λ alt =>
    if innerExcludable prejacent alt then !primalMeaning alt s else true)

/--
EXH(SOME) = SOME AND NOT ALL

The standard "only some" scalar implicature: some but not all.
-/
theorem exh_some (s : Scenario) :
    exh .weak s = (someMeaning s && !allMeaning s) := by
  simp only [exh, innerExcludable, hornMates, entails, primalMeaning,
    List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.false_and,
    Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true]

/--
EXH(THE) = THE = SOME

The definite has no innerExcludable alternatives (STRONG is not a Horn-mate,
and WEAK is equivalent), so EXH is vacuous.
-/
theorem exh_the (s : Scenario) :
    exh .mystery s = someMeaning s := by
  simp only [exh, innerExcludable, hornMates, entails, primalMeaning,
    List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.false_and,
    Bool.not_true, Bool.not_false, ite_false, Bool.false_eq_true]


-- ============================================================
-- SECTION 3: Double Strengthening (the main result)
-- ============================================================

/--
At the outer (second) EXH level, excludability uses Horn-mateness but
checks entailment of STRENGTHENED meanings rather than plain meanings.

In the three-element configuration, the only outer-excludable pair is
(MYSTERY, WEAK): EXH(SOME) = SOME AND NOT ALL is strictly stronger than
EXH(THE) = SOME, and they are Horn-mates.

This is a derived fact, verified by `exh_weak_strictly_stronger`. -/
def outerExcludable : Role → Role → Bool
  | .mystery, .weak => true
  | _, _            => false

/-- EXH(WEAK) is strictly stronger than EXH(MYSTERY):
    EXH(SOME) = SOME ∧ ¬ALL entails EXH(THE) = SOME, but not vice versa.

    This justifies `outerExcludable .mystery .weak = true`. -/
theorem exh_weak_strictly_stronger :
    (∀ s : Scenario, exh .weak s = true → exh .mystery s = true) ∧
    (∃ s : Scenario, exh .mystery s = true ∧ exh .weak s = false) := by
  constructor
  · intro s h
    rw [exh_some] at h
    rw [exh_the]
    simp only [Bool.and_eq_true] at h
    exact h.1
  · exact ⟨⟨3, 3, by omega⟩, by native_decide⟩

/-- The outer excludability assignment is justified by Horn-mateness
    plus asymmetric strengthened entailment. -/
theorem outerExcludable_justified :
    hornMates .mystery .weak = true ∧
    (∀ s, exh .weak s = true → exh .mystery s = true) ∧
    (∃ s, exh .mystery s = true ∧ exh .weak s = false) :=
  ⟨rfl, exh_weak_strictly_stronger.1, exh_weak_strictly_stronger.2⟩

/--
Iterated EXH (assumption 19 in @cite{magri-2014}, extending
@cite{spector-2007}): the strengthened meaning is computed through
double exhaustification with outer-level excludability. The key
innovation over @cite{spector-2007}'s single EXH is that the
*strengthened* meanings of alternatives (not just plain meanings)
determine excludability at the outer level.

  doubleExh(phi) = EXH(phi) AND AND{NOT EXH(psi) : psi outerExcludable w.r.t. phi}
-/
def doubleExh (prejacent : Role) (s : Scenario) : Bool :=
  exh prejacent s &&
  [Role.mystery, .weak, .strong].all (λ alt =>
    if outerExcludable prejacent alt then !exh alt s else true)

/-- Boolean identity used in the main proof. -/
private theorem bool_core (a b : Bool) :
    (a && !(a && !b)) = (a && b) := by
  cases a <;> cases b <;> rfl

/-- Reduction: doubleExh .mystery s = someMeaning s AND allMeaning s. -/
private theorem doubleExh_mystery_eq (s : Scenario) :
    doubleExh .mystery s = (someMeaning s && allMeaning s) := by
  simp only [doubleExh, outerExcludable, exh, innerExcludable, hornMates, entails,
    primalMeaning, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
    Bool.false_and, Bool.not_true, Bool.not_false, ite_true, ite_false,
    Bool.false_eq_true]
  exact bool_core (someMeaning s) (allMeaning s)

/--
**The main theorem**: double exhaustification of THE yields ALL
(given a non-vacuous plurality).

  doubleExh(THE) = EXH(EXH(THE))
                 = EXH(THE) AND NOT EXH(SOME)         -- outer EXH negates the Horn-mate
                 = THE AND NOT(SOME AND NOT ALL)        -- unpack inner EXH
                 = SOME AND NOT(SOME AND NOT ALL)       -- THE = SOME
                 = SOME AND (NOT SOME OR ALL)           -- De Morgan
                 = ALL                                  -- since SOME is asserted

The hypothesis `s.total >= 1` excludes the vacuous case (empty plurality),
where `allMeaning` is vacuously true but `someMeaning` is false. Vacuous
definites ("the boys" when there are no boys) are presupposition failures.
-/
theorem double_strengthening_yields_universal (s : Scenario) (hn : s.total ≥ 1) :
    doubleExh .mystery s = allMeaning s := by
  rw [doubleExh_mystery_eq]
  simp only [someMeaning, allMeaning]
  cases h : (s.satisfying == s.total)
  · simp
  · simp only [beq_iff_eq] at h
    simp [decide_eq_true_eq]
    omega


-- ============================================================
-- SECTION 4: DE Environments (no strengthening)
-- ============================================================

/--
In DE environments (negation, restrictor of *every*, etc.), no
strengthening occurs. The definite reveals its plain existential semantics.

  NOT THE = NOT SOME

This is because in DE environments, the resulting matrix sentence already
has the strongest meaning, so EXH is vacuous.
-/
def notMeaning (meaning : Scenario → Bool) (s : Scenario) : Bool :=
  !meaning s

theorem de_no_strengthening (s : Scenario) :
    notMeaning (primalMeaning .mystery) s =
    notMeaning (primalMeaning .weak) s := by
  rfl


-- ============================================================
-- SECTION 5: Homogeneity Effects (derived)
-- ============================================================

/--
A GAP scenario: some but not all individuals satisfy the predicate.
-/
def isGap (s : Scenario) : Bool :=
  someMeaning s && !allMeaning s

/--
In a GAP scenario, the strengthened meaning of the positive sentence
(THE = ALL after double strengthening) is FALSE.
-/
theorem gap_positive_false (s : Scenario) (h : isGap s = true) :
    doubleExh .mystery s = false := by
  rw [doubleExh_mystery_eq]
  simp only [isGap, Bool.and_eq_true] at h
  obtain ⟨_, h2⟩ := h
  revert h2; cases allMeaning s <;> simp

/--
In a GAP scenario, the strengthened meaning of the negative sentence
(NOT THE = NOT SOME = NOT EXISTS) is also FALSE (since some DO satisfy).
-/
theorem gap_negative_false (s : Scenario) (h : isGap s = true) :
    notMeaning someMeaning s = false := by
  simp only [notMeaning, isGap, Bool.and_eq_true] at h ⊢
  simp [h.1]

/--
**Homogeneity derived**: In GAP scenarios, both the positive and negative
descriptions are false. The positive is false because ALL fails; the negative
is false because SOME succeeds. This non-complementarity IS the homogeneity
gap --- the definite is "neither clearly true nor clearly false."
-/
theorem homogeneity_from_double_strengthening (s : Scenario) (h : isGap s = true) :
    doubleExh .mystery s = false ∧ notMeaning someMeaning s = false :=
  ⟨gap_positive_false s h, gap_negative_false s h⟩


-- ============================================================
-- SECTION 6: Concrete Instances
-- ============================================================

/--
The three domains unified by the double strengthening account.
-/
inductive HomogeneityDomain where
  /-- Plural definites: THE <-> SOME, ALL (primal) -/
  | definites
  /-- Bare plural morphology: PL <-> SING, TWO (primal) -/
  | pluralMorphology
  /-- Unfocused conjunction: AND_unF <-> OR, BOTH (dual) -/
  | conjunction
  deriving Repr, DecidableEq

/--
The correspondence table from the paper: each domain instantiates the
same three-element alternative structure.

| MYSTERY       | WEAK          | STRONG              |
|---------------|---------------|---------------------|
| the boys      | some boys     | all/each of the boys|
| books (PL)    | a book (SING) | two books (TWO)     |
| Adam and Bill | Adam or Bill  | both Adam and Bill  |
-/
structure DomainLabels where
  domain : HomogeneityDomain
  mysteryLabel : String
  weakLabel : String
  strongLabel : String
  deriving Repr

def definiteLabels : DomainLabels :=
  { domain := .definites
  , mysteryLabel := "the boys"
  , weakLabel := "some (of the) boys"
  , strongLabel := "all/each of the boys" }

def pluralMorphLabels : DomainLabels :=
  { domain := .pluralMorphology
  , mysteryLabel := "books (plural morphology)"
  , weakLabel := "a book (singular)"
  , strongLabel := "two books (numerical)" }

def conjunctionLabels : DomainLabels :=
  { domain := .conjunction
  , mysteryLabel := "Adam and_unF Bill"
  , weakLabel := "Adam or Bill"
  , strongLabel := "(both) Adam and_F Bill" }

def allDomains : List DomainLabels :=
  [definiteLabels, pluralMorphLabels, conjunctionLabels]


-- ============================================================
-- SECTION 7: Primal vs Dual
-- ============================================================

/--
Whether the domain uses the primal or dual version of the theory.

- Primal: MYSTERY starts weak (existential), gets strengthened to STRONG in UE
- Dual: MYSTERY starts strong (conjunctive), gets weakened to WEAK in DE
-/
inductive TheoryVariant where
  | primal  -- definites, plural morphology
  | dual    -- unfocused conjunction
  deriving Repr, DecidableEq

def domainVariant : HomogeneityDomain → TheoryVariant
  | .definites        => .primal
  | .pluralMorphology => .primal
  | .conjunction      => .dual

/-- Plain meanings in the DUAL theory (conjunction).
    In the dual, MYSTERY (AND_unF) starts with strong (conjunctive) plain meaning. -/
def dualMeaning : Role → Scenario → Bool
  | .mystery => allMeaning   -- AND_unF has conjunctive plain meaning
  | .weak    => someMeaning  -- OR has disjunctive meaning
  | .strong  => allMeaning   -- BOTH/AND_F has conjunctive meaning

/-- In the primal, MYSTERY starts weak and requires double EXH to reach STRONG. -/
theorem primal_mystery_is_weak :
    primalMeaning .mystery = someMeaning := rfl

/-- In the dual, MYSTERY starts strong directly (no EXH needed in UE). -/
theorem dual_mystery_is_strong :
    dualMeaning .mystery = allMeaning := rfl

/-- The primal requires double exhaustification to reach ALL,
    while the dual starts there directly. Both agree on the UE result. -/
theorem primal_needs_exh_dual_doesnt (s : Scenario) (hn : s.total ≥ 1) :
    doubleExh .mystery s = allMeaning s ∧ dualMeaning .mystery s = allMeaning s :=
  ⟨double_strengthening_yields_universal s hn, rfl⟩

/--
The effective interpretation of MYSTERY in each polarity context.

In the **primal** theory (definites, plural morphology):
- UE: double strengthening yields STRONG (universal/plurality)
- DE: no strengthening, MYSTERY reveals WEAK (existential/singular)

In the **dual** theory (conjunction):
- UE: MYSTERY reveals STRONG (conjunctive) directly
- DE: double strengthening yields WEAK (disjunctive)
-/
def effectiveInterpretation (variant : TheoryVariant) (pol : Polarity) : Role :=
  match variant, pol with
  | .primal, .positive => .strong   -- strengthened to universal
  | .primal, .negative => .weak     -- reveals existential
  | .dual,   .positive => .strong   -- reveals conjunctive (= strong)
  | .dual,   .negative => .weak     -- weakened to disjunctive

/--
Both variants produce the same net result: MYSTERY behaves as STRONG in UE
and as WEAK in DE.
-/
theorem primal_dual_agree :
    effectiveInterpretation .primal = effectiveInterpretation .dual := by
  funext pol; cases pol <;> rfl


-- ============================================================
-- SECTION 8: Sloppy Existential Readings
-- ============================================================

/--
Magri's conjecture: a matrix plural definite has a universal
(existential) reading in a conversational context if and only if the
corresponding indefinite triggers (does not trigger) the "only-some"
scalar implicature.

  A matrix definite THE has universal force <-> the indefinite SOME triggers SI

When the indefinite triggers no "only-some" implicature, there is nothing
for the definite's second-order implicature to negate, so no strengthening
occurs and the definite reveals its plain existential meaning.
-/
structure SloppyExistentialPrediction where
  /-- Context description -/
  context : String
  /-- Does the indefinite trigger "only-some" in this context? -/
  indefiniteTriggersSI : Bool
  /-- Does the definite receive universal force? -/
  definiteUniversal : Bool
  deriving Repr

/-- The prediction: these always agree. -/
def sloppyPrediction (p : SloppyExistentialPrediction) : Bool :=
  p.indefiniteTriggersSI == p.definiteUniversal

/-- Classroom context: sloppy existential reading.
    Example attributed to Schlenker (p.c.) in @cite{gajewski-2005}. -/
def classroomExample : SloppyExistentialPrediction :=
  { context := "Three girls raise their hands. 'Wait, the girls have a question!'"
  , indefiniteTriggersSI := false  -- "some girls" would also be fine here
  , definiteUniversal := false }   -- sloppy existential: only 3 of 10

/-- Standard predication: universal reading. -/
def standardExample : SloppyExistentialPrediction :=
  { context := "Ten girls in a team each solve the problem. 'The girls solved the problem.'"
  , indefiniteTriggersSI := true   -- "some girls" would implicate not all
  , definiteUniversal := true }    -- universal: all of them

def sloppyExamples : List SloppyExistentialPrediction :=
  [classroomExample, standardExample]

theorem sloppy_prediction_holds :
    sloppyExamples.all sloppyPrediction = true := by native_decide


-- ============================================================
-- BRIDGE 1: Connection to Homogeneity.lean Empirical Data
-- ============================================================

open Phenomena.Plurals.Homogeneity (HomogeneityDatum switchesExample conjunctionExample)

/-- Concrete scenario instances for the switches example (10 switches). -/
def switchesAll : Scenario := ⟨10, 10, by omega⟩
def switchesNone : Scenario := ⟨10, 0, by omega⟩
def switchesGap : Scenario := ⟨10, 5, by omega⟩

/-- In the ALL scenario, double strengthening gives the universal reading. -/
theorem switches_all_true : doubleExh .mystery switchesAll = true := by native_decide

/-- In the NONE scenario, double strengthening fails (no individuals satisfy). -/
theorem switches_none_false : doubleExh .mystery switchesNone = false := by native_decide
/-- In the NONE scenario, negation of existential gives true (none satisfy). -/
theorem switches_none_neg_true : notMeaning someMeaning switchesNone = true := by native_decide

/-- In the GAP scenario, both positive (double-strengthened) and negative
    (plain existential under negation) are false --- the homogeneity gap. -/
theorem switches_gap_homogeneity :
    doubleExh .mystery switchesGap = false ∧
    notMeaning someMeaning switchesGap = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- The gap derivation matches the empirical judgments in `Homogeneity.lean`:
    in the gap scenario, both positive and negative sentences are judged
    "neither true nor false." -/
theorem gap_matches_switches_data :
    switchesExample.positiveInGap = .neitherTrueNorFalse ∧
    switchesExample.negativeInGap = .neitherTrueNorFalse := ⟨rfl, rfl⟩

/-- The conjunction domain also displays the same gap pattern. -/
theorem gap_matches_conjunction_data :
    conjunctionExample.positiveInGap = .neitherTrueNorFalse ∧
    conjunctionExample.negativeInGap = .neitherTrueNorFalse := ⟨rfl, rfl⟩

/-- Magri's theory accounts for the full truth-value pattern in the
    switches example: universal in ALL, denial in NONE, gap in between. -/
theorem full_pattern_matches_switches :
    -- ALL scenario: positive clearly true, negative clearly false
    switchesExample.positiveInAll = .clearlyTrue ∧
    switchesExample.negativeInAll = .clearlyFalse ∧
    -- NONE scenario: positive clearly false, negative clearly true
    switchesExample.positiveInNone = .clearlyFalse ∧
    switchesExample.negativeInNone = .clearlyTrue ∧
    -- GAP scenario: neither true nor false for both
    switchesExample.positiveInGap = .neitherTrueNorFalse ∧
    switchesExample.negativeInGap = .neitherTrueNorFalse := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


-- ============================================================
-- BRIDGE 2: Connection to Multiplicity.lean Parallels
-- ============================================================

open Phenomena.Plurals.Multiplicity (MonotonicityParallel pluralSingularParallel orAndParallel)

/-- Magri's primal theory predicts strengthening in UE but not DE,
    matching the monotonicity pattern documented in `Multiplicity.lean`:
    the inference arises in UE (positive) contexts but not DE (negative). -/
theorem primal_matches_monotonicity_pattern :
    effectiveInterpretation .primal .positive = .strong ∧
    effectiveInterpretation .primal .negative = .weak ∧
    pluralSingularParallel.arisesInUE = true ∧
    pluralSingularParallel.arisesInDE = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Magri's conjunction (dual) domain corresponds to the or/and
    monotonicity parallel in `Multiplicity.lean`. -/
theorem dual_matches_conjunction_parallel :
    effectiveInterpretation .dual .positive = .strong ∧
    effectiveInterpretation .dual .negative = .weak ∧
    orAndParallel.arisesInUE = true ∧
    orAndParallel.arisesInDE = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩


-- ============================================================
-- SECTION 9: Bridge to Fox's Computable exhB
-- ============================================================

/-!
## Connection to @cite{fox-2007}'s Computable Algorithm

The abstract three-role computation above uses hand-coded `innerExcludable`
and `outerExcludable`. Here we verify that Fox's computable innocent
exclusion algorithm (`exhB` from `InnocentExclusion.lean`) applied twice
produces the same result: double exhaustification yields the universal
reading.

The key subtlety: `exhB` treats all alternatives in its list uniformly,
so **non-transitive Horn-mateness** must be encoded in which alternatives
are *included in the list*. THE and SOME get different alternative lists:
- THE's alternatives: `[bSome]` (only SOME is a Horn-mate; ALL is not)
- SOME's alternatives: `[bSome, bAll]` (both THE and ALL are Horn-mates)
-/

section FoxBridge

open Exhaustification (innocent predToFinset altsFromPreds)

/-- Three worlds for a two-member plurality: none, one, or all satisfy. -/
inductive Sat where | none | one | all
  deriving Repr, DecidableEq, Fintype

/-- SOME meaning: at least one satisfies. -/
private def bSome : Sat → Bool | .one | .all => true | _ => false
/-- ALL meaning: all satisfy. -/
private def bAll : Sat → Bool | .all => true | _ => false

/-- THE's alternative list: only SOME is a Horn-mate (not ALL). -/
private def theAlts : List (Sat → Bool) := [bSome]

/-- SOME's alternative list: both THE (= SOME) and ALL are Horn-mates. -/
private def someAlts : List (Sat → Bool) := [bSome, bAll]

/-- Inner EXH(THE) = SOME: THE has no excludable alternatives because
    its only Horn-mate (SOME) is equivalent, not strictly stronger. -/
theorem fox_inner_exh_the :
    innocent.exh (altsFromPreds theAlts) (predToFinset bSome)
      = predToFinset bSome := by decide

/-- Inner EXH(SOME) = SOME ∧ ¬ALL: the standard "only some" SI. -/
theorem fox_inner_exh_some :
    innocent.exh (altsFromPreds someAlts) (predToFinset bSome)
      = predToFinset (fun w => bSome w && !bAll w) := by decide

/-- Inner results as named functions for the outer level. -/
private def innerThe : Sat → Bool :=
  fun w => decide (w ∈ innocent.exh (altsFromPreds theAlts) (predToFinset bSome))
private def innerSome : Sat → Bool :=
  fun w => decide (w ∈ innocent.exh (altsFromPreds someAlts) (predToFinset bSome))

/-- Outer-level alternative list for THE: [EXH(THE), EXH(SOME)].
    EXH(SOME) = SOME ∧ ¬ALL is strictly stronger than EXH(THE) = SOME,
    and SOME is a Horn-mate of THE, so it becomes excludable. -/
private def outerAltsForThe : List (Sat → Bool) := [innerThe, innerSome]

/-- **Bridge theorem**: Fox's exhaustification applied twice with the correct
    Horn-mate-restricted alternative sets yields the universal reading,
    matching `double_strengthening_yields_universal`.

    EXH(EXH(THE)) = EXH(THE) ∧ ¬EXH(SOME)
                   = SOME ∧ ¬(SOME ∧ ¬ALL)
                   = ALL -/
theorem fox_double_exh_yields_all :
    innocent.exh (altsFromPreds outerAltsForThe) (predToFinset innerThe)
      = predToFinset bAll := by decide

end FoxBridge


-- ============================================================
-- SECTION 10: Dual Theory — Inner EXH and DE Properties (§5.5)
-- ============================================================

/-!
## Dual Theory: UE Is Trivial, DE Reveals Weak Meaning

In the **dual** theory (§5.5.2), MYSTERY (AND_unF) has a *strong*
plain meaning (conjunction ≡ STRONG). In UE environments, the
strong meaning is already maximal — no strengthening occurs
(computation 55b: |||MYSTERY||| = [[MYSTERY]]).

In DE environments, the strong plain meaning under negation yields
a weak global meaning. The abstract computation (55a) shows that
double exhaustification of not·MYSTERY is vacuous:

  |||not·MYSTERY||| = EXH(EXH(not·MYSTERY))
                    = not·MYSTERY
                    = not·STRONG                     (since MYSTERY ≡ STRONG)

The vacuousness at the abstract level arises because MYSTERY ≡ STRONG
means not·MYSTERY ≡ not·STRONG — there is no strictly stronger
alternative to exclude. The *concrete* dual DE computation (61)/(72),
which enriches the alternative set with atomic conjuncts LEFT and RIGHT,
IS non-vacuous and derives not·OR. That computation is in Section 11.

This section verifies the abstract-level properties: inner EXH is
vacuous for the dual MYSTERY, and gap scenarios show the expected
pattern.
-/

section DualComputation

/-- Inner EXH in the dual theory.

    Note: This reuses `innerExcludable` from the primal theory. The
    abstract three-role `innerExcludable` uses primal entailment
    (MYSTERY ≡ WEAK), while in the dual MYSTERY ≡ STRONG. However,
    the inner EXH results are the same for both theories at the abstract
    level: MYSTERY has no excludable alternatives, and WEAK excludes
    STRONG. The primal `innerExcludable` gives the right answer because
    neither theory allows MYSTERY to exclude anything at the inner level. -/
def dualExh (prejacent : Role) (s : Scenario) : Bool :=
  dualMeaning prejacent s &&
  [Role.mystery, .weak, .strong].all (λ alt =>
    if innerExcludable prejacent alt then !dualMeaning alt s else true)

/-- In the dual, EXH is vacuous for MYSTERY: no alternative is
    both a Horn-mate and asymmetrically stronger. This matches
    computation (55b): |||MYSTERY||| = [[MYSTERY]] = ALL. -/
theorem dual_exh_mystery (s : Scenario) :
    dualExh .mystery s = allMeaning s := by
  simp only [dualExh, innerExcludable, hornMates, entails, dualMeaning,
    List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.false_and,
    Bool.not_true, Bool.not_false, ite_false, Bool.false_eq_true]

/-- In the dual, EXH(WEAK) = SOME ∧ ¬ALL (WEAK excludes STRONG).
    OR triggers "not-both" SI just as SOME triggers "not-all". -/
theorem dual_exh_weak (s : Scenario) :
    dualExh .weak s = (someMeaning s && !allMeaning s) := by
  simp only [dualExh, innerExcludable, hornMates, entails, dualMeaning,
    List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.false_and,
    Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true]

/-- NOT·MYSTERY in the dual = NOT·STRONG (since MYSTERY ≡ STRONG). -/
theorem dual_not_mystery_eq_not_strong (s : Scenario) :
    notMeaning (dualMeaning .mystery) s = notMeaning (dualMeaning .strong) s := rfl

/-- In a gap scenario, the dual DE reveals the weak meaning.
    not·MYSTERY = ¬ALL is true (not all satisfy), while
    not·SOME = ¬∃ is false (some do satisfy). -/
theorem dual_de_reveals_weak (s : Scenario)
    (_hn : s.total ≥ 1) (hgap : s.satisfying ≥ 1 ∧ s.satisfying < s.total) :
    notMeaning allMeaning s = true ∧ notMeaning someMeaning s = false := by
  unfold notMeaning allMeaning someMeaning
  have hne : s.satisfying ≠ s.total := by omega
  have hge : s.satisfying ≥ 1 := hgap.1
  simp [hne, hge]

end DualComputation


-- ============================================================
-- SECTION 11: Enriched Conjunction Alternatives (§A.7)
-- ============================================================

/-!
## Enriched Alternatives for Conjunction (§A.7)

§A.7 adds the atomic conjuncts LEFT and RIGHT to the alternative set
for unfocused conjunction, using @cite{fox-2007}'s definition of
excludable alternatives. The crucial asymmetry (69b): AND_F has OR
among its alternatives, but AND_unF does NOT. Non-transitive
Horn-mateness is encoded by giving each prejacent its own alternative list.

This derives computation (72): in DE environments, unfocused conjunction
behaves as disjunction: |||not·AND_unF||| = not·OR.
-/

section EnrichedConjunction

open Exhaustification (innocent predToFinset altsFromPreds)

/-- Four worlds for two atomic propositions (saw Adam, saw Bill). -/
inductive ConjW where
  | neither | onlyA | onlyB | both
  deriving Repr, DecidableEq, Fintype

def cLeft : ConjW → Bool | .onlyA | .both => true | _ => false
def cRight : ConjW → Bool | .onlyB | .both => true | _ => false
def cOr : ConjW → Bool | .neither => false | _ => true
def cAnd : ConjW → Bool | .both => true | _ => false

-- Per-prejacent alternative lists encoding non-transitive Horn-mateness (69b):
-- AND_unF's alts: {AND_F, LEFT, RIGHT} — NOT OR (the crucial asymmetry)
-- AND_F's alts: {AND_unF, OR, LEFT, RIGHT}
-- LEFT's alts: {AND_F, AND_unF, OR, RIGHT}
-- RIGHT's alts: {AND_F, AND_unF, OR, LEFT}

/-- AND_unF's alternatives: {AND_F, LEFT, RIGHT}. OR is NOT included. -/
private def andUnFAlts : List (ConjW → Bool) := [cAnd, cLeft, cRight]
/-- AND_F's alternatives: {AND_unF, OR, LEFT, RIGHT}. -/
private def andFAlts : List (ConjW → Bool) := [cAnd, cOr, cLeft, cRight]
/-- LEFT's alternatives: {AND_F, AND_unF, OR, RIGHT}.
    AND_F and AND_unF have the same denotation (`cAnd`), so the two
    copies are semantically redundant but reflect the paper's (69b). -/
private def leftAlts : List (ConjW → Bool) := [cAnd, cAnd, cOr, cRight]
/-- RIGHT's alternatives: {AND_F, AND_unF, OR, LEFT}.
    Same note: two `cAnd` copies for AND_F / AND_unF. -/
private def rightAlts : List (ConjW → Bool) := [cAnd, cAnd, cOr, cLeft]

-- Inner EXH for each item (with their own alternative lists)

/-- EXH(AND_unF) = AND (vacuous: all alts are entailed by AND). -/
theorem exh_andUnF :
    innocent.exh (altsFromPreds andUnFAlts) (predToFinset cAnd)
      = predToFinset cAnd := by decide

/-- EXH(AND_F) = AND (same: AND entails everything in its alt list). -/
theorem exh_andF :
    innocent.exh (altsFromPreds andFAlts) (predToFinset cAnd)
      = predToFinset cAnd := by decide

/-- EXH(LEFT) = LEFT ∧ ¬RIGHT (RIGHT is the only IE alternative). -/
theorem exh_left :
    innocent.exh (altsFromPreds leftAlts) (predToFinset cLeft)
      = predToFinset (fun w => cLeft w && !cRight w) := by decide

/-- EXH(RIGHT) = RIGHT ∧ ¬LEFT (symmetric). -/
theorem exh_right :
    innocent.exh (altsFromPreds rightAlts) (predToFinset cRight)
      = predToFinset (fun w => cRight w && !cLeft w) := by decide

-- DE computation: negated meanings with per-prejacent alternative lists

def nAnd : ConjW → Bool := fun w => !cAnd w
def nOr : ConjW → Bool := fun w => !cOr w
private def nLeft : ConjW → Bool := fun w => !cLeft w
private def nRight : ConjW → Bool := fun w => !cRight w

/-- not·AND_unF's alternatives: {not·AND_F, not·LEFT, not·RIGHT}. -/
private def nAndUnFAlts : List (ConjW → Bool) := [nAnd, nLeft, nRight]
/-- not·AND_F's alternatives: {not·AND_unF, not·OR, not·LEFT, not·RIGHT}. -/
private def nAndFAlts : List (ConjW → Bool) := [nAnd, nOr, nLeft, nRight]
/-- not·LEFT's alternatives: {not·AND_F, not·AND_unF, not·OR, not·RIGHT}. -/
private def nLeftAlts : List (ConjW → Bool) := [nAnd, nAnd, nOr, nRight]
/-- not·RIGHT's alternatives: {not·AND_F, not·AND_unF, not·OR, not·LEFT}. -/
private def nRightAlts : List (ConjW → Bool) := [nAnd, nAnd, nOr, nLeft]

/-- (71b) EXH(not·AND_unF) = not·AND (vacuous inner EXH).
    Neither not·LEFT nor not·RIGHT is IE: excluding one forces including
    the other, since ¬AND ∧ LEFT ∧ RIGHT is inconsistent. -/
theorem de_exh_notAndUnF :
    innocent.exh (altsFromPreds nAndUnFAlts) (predToFinset nAnd)
      = predToFinset nAnd := by decide

/-- (71a) EXH(not·AND_F) = not·AND ∧ ¬not·OR = not·AND ∧ OR.
    not·OR is IE (the only alternative not entailed by not·AND_F
    that can be consistently excluded). -/
theorem de_exh_notAndF :
    innocent.exh (altsFromPreds nAndFAlts) (predToFinset nAnd)
      = predToFinset (fun w => nAnd w && cOr w) := by decide

/-- (71c) EXH(not·LEFT) = not·LEFT ∧ OR ∧ RIGHT. -/
theorem de_exh_notLeft :
    innocent.exh (altsFromPreds nLeftAlts) (predToFinset nLeft)
      = predToFinset (fun w => nLeft w && cOr w && cRight w) := by decide

/-- (71d) EXH(not·RIGHT) = not·RIGHT ∧ OR ∧ LEFT. -/
theorem de_exh_notRight :
    innocent.exh (altsFromPreds nRightAlts) (predToFinset nRight)
      = predToFinset (fun w => nRight w && cOr w && cLeft w) := by decide

/-- Outer-level alternatives for not·AND_unF: the exhaustified forms
    of its Horn-mates {not·AND_F, not·LEFT, not·RIGHT}. -/
def outerNAndUnFAlts : List (ConjW → Bool) :=
  [ fun w => decide (w ∈ innocent.exh (altsFromPreds nAndUnFAlts) (predToFinset nAnd))
  , fun w => decide (w ∈ innocent.exh (altsFromPreds nAndFAlts) (predToFinset nAnd))
  , fun w => decide (w ∈ innocent.exh (altsFromPreds nLeftAlts) (predToFinset nLeft))
  , fun w => decide (w ∈ innocent.exh (altsFromPreds nRightAlts) (predToFinset nRight)) ]

/-- The inner EXH result for not·AND_unF (= not·AND, vacuous). -/
def innerNAndUnF : ConjW → Bool :=
  fun w => decide (w ∈ innocent.exh (altsFromPreds nAndUnFAlts) (predToFinset nAnd))

/-- **Computation (72)**: Double exhaustification of not·AND_unF yields not·OR.

    |||not·AND_unF||| = EXH(EXH(not·AND_unF))
                     = not·AND ∧ ¬EXH(not·AND_F) ∧ ¬EXH(not·LEFT)
                                                   ∧ ¬EXH(not·RIGHT)
                     = not·AND ∧ ¬(not·AND ∧ OR) ∧ ...
                     = not·AND ∧ (AND ∨ ¬OR)     ∧ ...
                     = not·AND ∧ ¬OR                  (since not·AND is asserted)
                     = not·OR

    Unfocused conjunction in DE environments behaves as disjunction. -/
theorem de_double_exh_conjunction :
    innocent.exh (altsFromPreds outerNAndUnFAlts) (predToFinset innerNAndUnF)
      = predToFinset nOr := by decide

end EnrichedConjunction


-- ============================================================
-- SECTION 12: Uniform Double Strengthening
-- ============================================================

/-!
## Uniform Double Strengthening over Theory Variants

The primal and dual theories share the same abstract mechanism — a
three-element alternative configuration with non-transitive
Horn-mateness. We unify them into a single `uniformResult`
function that takes a `TheoryVariant` and returns the effective
meaning in each polarity.
-/

section UniformStrengthening

/-- The effective meaning of MYSTERY in each polarity, parameterized
    by theory variant. Both variants produce the same result:
    STRONG (= ALL) in UE, WEAK (= SOME) in DE. -/
def uniformResult (v : TheoryVariant) (pol : Polarity) : Scenario → Bool :=
  match v, pol with
  | .primal, .positive => allMeaning    -- double-strengthened
  | .primal, .negative => someMeaning   -- revealed
  | .dual,   .positive => allMeaning    -- revealed
  | .dual,   .negative => someMeaning   -- double-weakened

/-- Primal and dual give the same effective meaning in both polarities. -/
theorem uniform_primal_dual_agree :
    ∀ (pol : Polarity), uniformResult .primal pol = uniformResult .dual pol := by
  intro pol; cases pol <;> rfl

/-- The primal UE result matches `double_strengthening_yields_universal`. -/
theorem uniform_primal_ue (s : Scenario) (hn : s.total ≥ 1) :
    uniformResult .primal .positive s = doubleExh .mystery s := by
  simp only [uniformResult]
  exact (double_strengthening_yields_universal s hn).symm

/-- The dual UE result matches the plain meaning of MYSTERY in the dual. -/
theorem uniform_dual_ue (s : Scenario) :
    uniformResult .dual .positive s = dualMeaning .mystery s := rfl

/-- The primal DE result matches the plain existential meaning. -/
theorem uniform_primal_de (s : Scenario) :
    uniformResult .primal .negative s = primalMeaning .mystery s := rfl

/-- The homogeneity pattern: in gap scenarios, MYSTERY is false under
    both polarities regardless of theory variant. -/
theorem uniform_gap (v : TheoryVariant) (s : Scenario) (_hn : s.total ≥ 1)
    (hgap : s.satisfying ≥ 1 ∧ s.satisfying < s.total) :
    uniformResult v .positive s = false ∧
    notMeaning (uniformResult v .negative) s = false := by
  have hne : s.satisfying ≠ s.total := by omega
  have hge : s.satisfying ≥ 1 := hgap.1
  cases v <;> simp [uniformResult, notMeaning, allMeaning, someMeaning, hne, hge]

end UniformStrengthening


-- ============================================================
-- SECTION 13: Questions Pull Apart Primal from Dual (§5.5.4)
-- ============================================================

/-!
## Questions: A Testable Distinction (§5.5.4)

Benjamin Spector (p.c., cited in §5.5.4) observes that **questions**
provide an environment where no strengthening occurs — they do not
license scalar implicatures. Under this assumption:

- **Primal** MYSTERY has weak plain meaning (existential) → questions
  should reveal existential force for definites.
- **Dual** MYSTERY has strong plain meaning (conjunctive) → questions
  should reveal conjunctive force for unfocused conjunction.

The paper offers preliminary data supporting this prediction: definites
in questions allow existential answers (62b), while unfocused conjunction
in questions resists disjunctive answers (63b).
-/

section QuestionPrediction

/-- In questions (no strengthening), the theory variant determines
    what force MYSTERY displays: primal → weak, dual → strong. -/
def mysteryInQuestions (v : TheoryVariant) : Role :=
  match v with
  | .primal => .weak     -- plain weak meaning revealed
  | .dual   => .strong   -- plain strong meaning revealed

/-- Questions differentiate the theories: primal MYSTERY shows WEAK,
    dual MYSTERY shows STRONG. -/
theorem questions_differentiate :
    mysteryInQuestions .primal ≠ mysteryInQuestions .dual := by
  decide

/-- Definites (primal) should have existential force in questions. -/
theorem definites_existential_in_questions :
    mysteryInQuestions (domainVariant .definites) = .weak := rfl

/-- Unfocused conjunction (dual) should have conjunctive force in questions. -/
theorem conjunction_conjunctive_in_questions :
    mysteryInQuestions (domainVariant .conjunction) = .strong := rfl

/-- Datum: "Did you talk to the students?" admits existential answer. -/
structure QuestionForceDatum where
  question : String
  domain : HomogeneityDomain
  variant : TheoryVariant
  predictedForce : Role
  /-- Data point: is the prediction borne out? -/
  supported : Bool
  deriving Repr

def definitesQuestion : QuestionForceDatum :=
  { question := "Did you talk to the students?"
  , domain := .definites
  , variant := .primal
  , predictedForce := .weak
  , supported := true }   -- (62b): existential answer felicitous

def conjunctionQuestion : QuestionForceDatum :=
  { question := "Did you talk to Adam and Bill?"
  , domain := .conjunction
  , variant := .dual
  , predictedForce := .strong
  , supported := true }   -- (63b): conjunctive answer degraded

/-- Both question data points support the primal/dual distinction. -/
theorem question_data_supports :
    [definitesQuestion, conjunctionQuestion].all (·.supported) = true := by
  native_decide

end QuestionPrediction


-- ============================================================
-- BRIDGE 3: Enriched Conjunction ↔ Empirical Data
-- ============================================================

/-!
## Connecting Enriched Conjunction to Empirical Data

The `de_double_exh_conjunction` theorem (Section 11) shows that
unfocused conjunction under negation behaves as disjunction on
the `ConjW` domain. Here we verify that this result matches the
gap pattern documented in `Homogeneity.lean`'s `conjunctionExample`:
in the gap scenario (Ann has red hair, Bert doesn't), both the
positive conjunction and its negation are "neither true nor false."
-/

section ConjunctionBridge

/-- The gap scenario for conjunction: one conjunct true, the other false. -/
private def conjGapWorlds : List ConjW := [.onlyA]

/-- In the gap, positive conjunction (AND) is false. -/
theorem conj_gap_positive_false :
    conjGapWorlds.all (λ w => cAnd w = false) = true := by
  decide

/-- In the gap, negative conjunction with enriched dual theory
    gives not·OR (= "saw neither"). This is FALSE in the gap
    (she DID see one of them), producing the homogeneity gap. -/
theorem conj_gap_dual_negative_false :
    conjGapWorlds.all (λ w => nOr w = false) = true := by
  decide

/-- This matches the empirical data: conjunction gap is
    neither-true-nor-false for both polarities. -/
theorem conj_gap_matches_empirical_data :
    conjunctionExample.positiveInGap = .neitherTrueNorFalse ∧
    conjunctionExample.negativeInGap = .neitherTrueNorFalse := ⟨rfl, rfl⟩

/-- Full end-to-end: the enriched conjunction computation produces
    truth values that correspond to the homogeneity gap pattern. -/
theorem enriched_conjunction_end_to_end :
    -- (1) Double EXH of not·AND_unF yields not·OR (Section 11)
    (Exhaustification.innocent.exh
        (Exhaustification.altsFromPreds outerNAndUnFAlts)
        (Exhaustification.predToFinset innerNAndUnF)
      = Exhaustification.predToFinset nOr) ∧
    -- (2) In gap world, AND (positive) is false
    cAnd .onlyA = false ∧
    -- (3) In gap world, not·OR (dual negative) is false
    nOr .onlyA = false ∧
    -- (4) Empirical data confirms the gap
    conjunctionExample.positiveInGap = .neitherTrueNorFalse ∧
    conjunctionExample.negativeInGap = .neitherTrueNorFalse := by
  exact ⟨de_double_exh_conjunction, rfl, rfl, rfl, rfl⟩

end ConjunctionBridge


end Magri2014
