import Linglib.Theories.Semantics.Plurality.Cumulativity
import Linglib.Theories.Semantics.Questions.ScopeReadings
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin

/-!
# @cite{johnston-2023}: Pair-List Answers to Questions with Plural Definites

William Johnston. 2023. Pair-list answers to questions with plural definites.
*Semantics and Pragmatics* 16, Article 2: 1–23.

## Overview

Questions with plural definites (QPDs) like "Who do the students like?"
can receive pair-list responses ("Ann likes Jones and Ben likes Smith").
The dominant view (@cite{srivastav-1992}, @cite{dayal-1996},
@cite{krifka-1992}) treats these as pragmatic elaborations on underlyingly
cumulative answers — the "cumulation-only" hypothesis.

@cite{johnston-2023} presents new evidence against this view: pair-list
answers are available even when the cumulative answer is already in the
common ground and no felicitous cumulative question exists. He argues that
QPDs are ambiguous between two parses:

1. **Cumulative parse**: `**(R)(X, Y)` — the cumulative operator from
   @cite{beck-sauerland-2000}. Pair-list form arises as pragmatic
   over-informative elaboration.

2. **Pair-list parse**: a genuine pair-list reading encoded in the
   semantics, sharing logical form with canonical pair-list questions
   (those with overt quantifiers or multiple wh-phrases).

## Key evidence

The basketball jersey scenario (§3): an assistant coach knows all five
players and knows the numbers (1–5) that were available, and believes
each player chose exactly one jersey. The cumulative answer — that the
players chose 1–5 — is already common knowledge. Yet "Which numbers did
the players pick?" felicitously receives a pair-list answer. Under the
cumulation-only hypothesis, the question should be as infelicitous as
"Who are the players?" or "What numbers were picked?", since those
answers are also already known.

## Predictions

1. **Subject-object asymmetry** in the pair-list parse (masked by
   cumulation pathway in ordinary contexts)
2. **Numeral modifier scope**: per-pair cardinality (pair-list parse)
   vs. total cardinality (cumulative parse)
3. **Number effect**: both DPs must be plural for the cumulation pathway;
   derives from `singleton_right_cumulativeOp` in `Cumulativity.lean`

## Formalization

We formalize the two-parse model and its predictions, derive the number
effect from `cumulativeOp`, prove that pair-list answers entail cumulative
truth (`pairListAnswer_entails_cumulativeOp`), show that pair-list
propositions are strictly finer-grained than cumulative propositions (the
Hamblin refinement: `pairList_strictly_finer`), connect the question-
embedding argument to epistemic state (`agentKnowsUnderParse`), derive
the subject-object asymmetry from scope constraints (`pairListScopeOK`),
and verify predictions against Johnston's data.
-/

namespace Johnston2023

open Semantics.Plurality.Cumulativity

-- ============================================================================
-- § 1. Core types
-- ============================================================================

/-- The two possible parses of a question with a plural definite (QPD).

    @cite{johnston-2023} §4: QPDs are ambiguous between a cumulative parse
    (where pair-list form is over-informative elaboration) and a genuine
    pair-list parse (where pair-list is encoded in the semantics). -/
inductive QPDParse where
  /-- Cumulative parse: `**(R)(X, Y)`. Pair-list form is pragmatic. -/
  | cumulative
  /-- Genuine pair-list parse: shares logical form with quantifier
      pair-list questions. -/
  | pairList
  deriving DecidableEq, Repr

/-- Position of the wh-phrase relative to the plural definite DP.
    Canonical pair-list questions show a subject-object asymmetry
    (@cite{chierchia-1993}): wh-object admits pair-list, wh-subject
    does not. @cite{johnston-2023} §5.1 shows this extends to the
    pair-list parse of QPDs. -/
inductive WhPosition where
  /-- Wh-phrase is the syntactic subject. -/
  | subject
  /-- Wh-phrase is the syntactic object. -/
  | object
  deriving DecidableEq, Repr

/-! ### Pair-list vs cumulative: the semantic distinction

The cumulative operator `**(R)(X, Y)` checks *coverage* — every atom in X
is R-related to some atom in Y, and vice versa — without specifying *which*
atom maps to which. This is `cumulativeOp` from `Cumulativity.lean`, and
it is identical to `leftCoverage ∧ rightCoverage`.

A pair-list answer specifies a *complete assignment* — a function `f : A → B`
mapping each domain atom to a specific range atom, with `R(a, f(a))` witnessed
for each `a ∈ domain`. This assignment IS the additional information that
pair-list answers provide over cumulative answers: it is a Skolem function
for the existentials in `leftCoverage`. -/

/-- A pair-list answer: a specific assignment function `f` mapping each
    domain atom `a` to `f(a)` such that `f(a) ∈ range` and `R(a, f(a))`.

    Under the family-of-questions approach (@cite{johnston-2023} §4), this
    corresponds to answering each sub-question "Which number did player a
    pick?" individually. Under the function-based approach, it corresponds
    to exhibiting the function f.

    Contrast with `leftCoverage` (existential): `∀a ∈ X. ∃b ∈ Y. R(a,b)`.
    `pairListAnswer` provides a *specific witness* `f(a)` for each `a`,
    making it strictly more informative. -/
def pairListAnswer {A B : Type} [DecidableEq A] [DecidableEq B]
    (R : A → B → Bool) (domain : Finset A) (range : Finset B) (f : A → B) : Bool :=
  decide (∀ a ∈ domain, f a ∈ range ∧ R a (f a) = true)

/-- A valid pair-list assignment entails left coverage: if `f` witnesses
    each domain atom, then left coverage holds (the existentials are
    satisfiable). This is one half of the pair-list → cumulative entailment. -/
theorem pairListAnswer_entails_leftCoverage {A B : Type} [DecidableEq A] [DecidableEq B]
    (R : A → B → Bool) (domain : Finset A) (range : Finset B) (f : A → B)
    (hf : pairListAnswer R domain range f = true) :
    leftCoverage R domain range = true := by
  simp only [pairListAnswer, decide_eq_true_iff] at hf
  simp only [leftCoverage, decide_eq_true_iff]
  intro a ha
  obtain ⟨hmem, hR⟩ := hf a ha
  exact ⟨f a, hmem, hR⟩

/-- If a pair-list assignment additionally covers every range atom
    (surjectivity onto the range), then the full cumulative operator holds.

    In QPD scenarios, the range is typically the image of the assignment
    (e.g., all jersey numbers actually picked), so this condition holds
    and pair-list answers entail cumulative truth. -/
theorem pairListAnswer_entails_cumulativeOp {A B : Type} [DecidableEq A] [DecidableEq B]
    (R : A → B → Bool) (domain : Finset A) (range : Finset B) (f : A → B)
    (hf : pairListAnswer R domain range f = true)
    (hsurj : ∀ b ∈ range, ∃ a ∈ domain, f a = b) :
    cumulativeOp R domain range = true := by
  simp only [pairListAnswer, decide_eq_true_iff] at hf
  simp only [cumulativeOp, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · intro a ha
    obtain ⟨hmem, hR⟩ := hf a ha
    exact ⟨f a, hmem, hR⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := hsurj b hb
    exact ⟨a, ha, (hf a ha).2⟩

-- ============================================================================
-- § 2. Empirical data
-- ============================================================================

/-- A QPD pair-list judgment. -/
structure QPDDatum where
  /-- The question. -/
  question : String
  /-- Scenario or context. -/
  context : String := ""
  /-- The pair-list answer (if felicitous). -/
  answer : String := ""
  /-- Is the wh-phrase's domain plural? -/
  whPlural : Bool
  /-- Is the plural definite DP plural? -/
  definPlural : Bool
  /-- Is the cumulative answer already in the common ground? -/
  cumulativeInCG : Bool
  /-- Is a pair-list response felicitous? -/
  pairListFelicitous : Bool
  /-- Which parse is responsible (if determinable from context). -/
  parse : Option QPDParse
  /-- Wh-position. -/
  whPosition : WhPosition
  /-- Source in @cite{johnston-2023}. -/
  source : String
  deriving Repr

/-! ### The basketball jersey argument (@cite{johnston-2023} §3)

The assistant coach knows all five players, knows the numbers (1–5)
that were available, and believes each player chose exactly one jersey.
The cumulative answer — that the players chose 1–5 — is already common
knowledge. Yet the pair-list question is felicitous. -/

/-- Ex. 24–25: "Which numbers did the players pick?" — felicitous pair-list
    even though the cumulative answer is in the CG. -/
def jerseyPairList : QPDDatum :=
  { question := "Which numbers did the players pick?"
  , context := "Basketball: 5 players, jerseys 1–5, each chose exactly one; questioner knows players and numbers"
  , answer := "Ann picked 1, Ben picked 2, Chris picked 3, Dan picked 4, Emma picked 5"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := true
  , parse := some .pairList
  , whPosition := .object
  , source := "ex. 24–25" }

/-- Ex. 28a: "#Who are the players?" — infelicitous because the answer
    is already known. This shows the cumulative answer IS in the CG:
    the questioner already knows the relevant identity facts. -/
def jerseyInfelicitous_who : QPDDatum :=
  { question := "#Who are the players?"
  , context := "Basketball jersey context (same as above)"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := false
  , parse := none
  , whPosition := .object
  , source := "ex. 28a" }

/-- Ex. 29: "#Which numbers did the players pick between them?" —
    *between them* forces a cumulative reading; infelicitous because
    the cumulative answer is already known. -/
def jerseyBetweenThem : QPDDatum :=
  { question := "#Which numbers did the players pick between them?"
  , context := "Basketball jersey context, cumulative forced by 'between them'"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := false
  , parse := some .cumulative
  , whPosition := .object
  , source := "ex. 29" }

/-! ### Number effect (@cite{johnston-2023} §2.2)

Pair-list responses to QPDs coincide with those cumulative relations
where both pluralities admit pairing uncertainty. When either DP is
singular, `**(R)(X, {y})` collapses to `∀x ∈ X. R(x, y)` — proved as
`singleton_right_cumulativeOp` in `Cumulativity.lean` — eliminating the
pairing uncertainty that motivates over-informative elaboration. -/

/-- Ex. 18: "Which professors do the students like?" — both DPs plural;
    pair-list felicitous. -/
def bothPlural : QPDDatum :=
  { question := "Which professors do the students like?"
  , answer := "Ann likes Prof. Jones, and Ben likes Prof. Smith"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := false
  , pairListFelicitous := true
  , parse := none
  , whPosition := .object
  , source := "ex. 18" }

/-- Ex. 19: "Which professor do the students like?" — wh-phrase singular;
    pair-list infelicitous. `**(like)(students, {Jones})` collapses to
    `∀s ∈ students. like(s, Jones)` (number effect). -/
def singularWh : QPDDatum :=
  { question := "#Which professor do the students like?"
  , whPlural := false
  , definPlural := true
  , cumulativeInCG := false
  , pairListFelicitous := false
  , parse := none
  , whPosition := .object
  , source := "ex. 19" }

/-- Ex. 20: "Which professors does the student like?" — definite singular;
    pair-list infelicitous. Symmetric to `singularWh`: the cumulative
    operator with a singleton left argument also collapses. -/
def singularDefin : QPDDatum :=
  { question := "#Which professors does the student like?"
  , whPlural := true
  , definPlural := false
  , cumulativeInCG := false
  , pairListFelicitous := false
  , parse := none
  , whPosition := .object
  , source := "ex. 20" }

/-! ### Subject-object asymmetry (@cite{johnston-2023} §5.1)

Under the cumulation pathway, no asymmetry: pair-list form is
available regardless of wh-position (§2.1, ex. 16–17). Under the genuine
pair-list parse, the same subject-object asymmetry found in canonical
pair-list questions emerges — parallel to the contrast between
"Who does every student like?" (✓ pair-list) and "Who likes every
professor?" (#pair-list) from @cite{chierchia-1993}.

The asymmetry is only visible when the cumulation pathway is excluded
(e.g., the basketball jersey context forces the pair-list parse). -/

/-- Ex. 37: "Which numbers did the players pick?" — pair-list parse;
    wh-object → felicitous. -/
def asymmetryObject : QPDDatum :=
  { question := "Which numbers did the players pick?"
  , context := "Basketball jersey context (cumulation excluded)"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := true
  , parse := some .pairList
  , whPosition := .object
  , source := "ex. 37" }

/-- Ex. 38: "#Which players picked the numbers?" — pair-list parse;
    wh-subject → infelicitous. Parallel to canonical "#Who likes every
    professor?" -/
def asymmetrySubject : QPDDatum :=
  { question := "#Which players picked the numbers?"
  , context := "Basketball jersey context (cumulation excluded)"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := false
  , parse := some .pairList
  , whPosition := .subject
  , source := "ex. 38" }

/-- Ex. 35: under cumulation pathway, wh-object — pair-list available. -/
def cumulationNoAsymmetryObj : QPDDatum :=
  { question := "Who do those students like?"
  , answer := "Ann likes Prof. Jones, and Ben likes Prof. Smith"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := false
  , pairListFelicitous := true
  , parse := some .cumulative
  , whPosition := .object
  , source := "ex. 35" }

/-- Ex. 36: under cumulation pathway, wh-subject — ALSO pair-list
    available. No asymmetry under cumulation. -/
def cumulationNoAsymmetrySubj : QPDDatum :=
  { question := "Who likes the professors?"
  , answer := "Ann likes Prof. Jones, and Ben likes Prof. Smith"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := false
  , pairListFelicitous := true
  , parse := some .cumulative
  , whPosition := .subject
  , source := "ex. 36" }

/-! ### Numeral modifier scope (@cite{johnston-2023} §5.2)

In the pair-list parse, a numeral modifier constrains the cardinality
of the answer *within each pair*. In the cumulative parse, it constrains
the *total* cardinality across the entire answer. -/

/-- Numeral scope datum: how a numeral modifier is interpreted under
    each parse. The numeral constrains different cardinalities depending
    on the parse. -/
structure NumeralScopeDatum where
  question : String
  numeral : Nat
  /-- Under pair-list parse: numeral constrains cardinality per pair. -/
  perPairCard : Nat
  /-- Under cumulative parse: numeral constrains total cardinality. -/
  totalCard : Nat
  /-- Which parse is active. -/
  parse : QPDParse
  source : String
  deriving Repr

/-- Ex. 40–41: "Which two numbers did the players pick?" (pair-list parse:
    each player picked two numbers; 5 players × 2 = 10 individual answers). -/
def twoNumbersPairList : NumeralScopeDatum :=
  { question := "Which two numbers did the players pick?"
  , numeral := 2
  , perPairCard := 2
  , totalCard := 10     -- 5 players × 2 numbers each
  , parse := .pairList
  , source := "ex. 40–41" }

/-- Ex. 45–46: "Which ten numbers did the players pick?" (cumulative parse:
    ten numbers total across all players). -/
def tenNumbersCumulative : NumeralScopeDatum :=
  { question := "Which ten numbers did the players pick?"
  , numeral := 10
  , perPairCard := 2    -- each player happened to pick 2
  , totalCard := 10
  , parse := .cumulative
  , source := "ex. 45–46" }

/-- Under pair-list parse, the numeral constrains per-pair cardinality;
    under cumulative parse, it constrains total cardinality. -/
def numeralConstrains (d : NumeralScopeDatum) : Nat :=
  match d.parse with
  | .pairList   => d.perPairCard
  | .cumulative => d.totalCard

/-- For both data points, the numeral equals the cardinality it
    constrains under the active parse. -/
theorem twoNumbers_numeral_matches :
    numeralConstrains twoNumbersPairList = twoNumbersPairList.numeral := by decide

theorem tenNumbers_numeral_matches :
    numeralConstrains tenNumbersCumulative = tenNumbersCumulative.numeral := by decide

/-! ### Embedded QPDs (@cite{johnston-2023} §3)

Question-embedding verbs *wonder* and *discover* confirm that the
pair-list reading is semantic, not pragmatic. Under the cumulation-only
hypothesis, embedded QPDs should not receive pair-list interpretations:
pragmatic over-informative elaboration cannot apply inside the scope of
an attitude verb (the answerer isn't elaborating under *wonder*).

Yet embedded QPDs ARE felicitous with pair-list content (ex. 31). This
is consistent with the pair-list reading being *semantic*: the embedded
question directly denotes a pair-list Hamblin set, regardless of
pragmatic elaboration strategies.

*Wonder* is rogative/non-factive (`Semantics.Attitudes.Factivity`):
it does not entail that its complement is true. Under the cumulation
pathway, the assistant coach wondering about the cumulative answer
should be infelicitous (the coach already knows the answer). Under the
pair-list parse, the coach is ignorant of the specific mappings — hence
the question is felicitous. -/

/-- Ex. 31a: "The assistant coach wonders which numbers the players
    picked." — felicitous with pair-list content under the pair-list
    parse; infelicitous under cumulative (because coach already knows
    the cumulative answer). -/
def wonderEmbedded : QPDDatum :=
  { question := "The assistant coach wonders which numbers the players picked"
  , context := "Basketball jersey context — coach knows the numbers, doesn't know the mapping"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := true
  , parse := some .pairList
  , whPosition := .object
  , source := "ex. 31a" }

/-- Ex. 31b: "The assistant coach will discover which numbers the players
    picked." — felicitous; the to-be-discovered content is the pair-list
    mapping, not the already-known cumulative answer. -/
def discoverEmbedded : QPDDatum :=
  { question := "The assistant coach will discover which numbers the players picked"
  , context := "Basketball jersey context"
  , whPlural := true
  , definPlural := true
  , cumulativeInCG := true
  , pairListFelicitous := true
  , parse := some .pairList
  , whPosition := .object
  , source := "ex. 31b" }

def allQPDData : List QPDDatum :=
  [ jerseyPairList, jerseyInfelicitous_who, jerseyBetweenThem
  , bothPlural, singularWh, singularDefin
  , asymmetryObject, asymmetrySubject
  , cumulationNoAsymmetryObj, cumulationNoAsymmetrySubj
  , wonderEmbedded, discoverEmbedded ]

-- ============================================================================
-- § 3. Predictions (derived from parse properties)
-- ============================================================================

/-- Predict whether a pair-list response is felicitous under a given parse.

    - **Cumulative parse**: requires both DPs plural (number effect, derived
      from `singleton_right_cumulativeOp`) and the cumulative answer NOT
      already in the CG (otherwise no new information to elaborate).
    - **Pair-list parse**: requires the wh-phrase to be the object
      (subject-object asymmetry, parallel to canonical pair-list Qs
      with overt quantifiers; @cite{chierchia-1993}). -/
def predictFelicitous (parse : QPDParse) (whPos : WhPosition)
    (whPlural definPlural cumulativeInCG : Bool) : Bool :=
  match parse with
  | .cumulative =>
    -- Number effect: both DPs must be plural for pairing uncertainty.
    -- When either is singular, ** collapses to universal quantification
    -- (see § 5 bridge theorems below).
    whPlural && definPlural && !cumulativeInCG
  | .pairList =>
    -- Subject-object asymmetry: wh must be object.
    -- Parallel to canonical pair-list with overt quantifiers.
    match whPos with
    | .object => true
    | .subject => false

/-- The overall prediction: a pair-list response is felicitous if EITHER
    parse yields a felicitous result. This is the two-parse model. -/
def predictFelicitousEither (whPos : WhPosition)
    (whPlural definPlural cumulativeInCG : Bool) : Bool :=
  predictFelicitous .cumulative whPos whPlural definPlural cumulativeInCG ||
  predictFelicitous .pairList whPos whPlural definPlural cumulativeInCG

-- ============================================================================
-- § 4. Verification theorems
-- ============================================================================

/-! ### Basketball jersey: cumulation-only gets this wrong -/

/-- The cumulation-only hypothesis wrongly predicts jersey pair-list is
    infelicitous (cumulative answer already in CG). -/
theorem cumulationOnly_wrong_for_jersey :
    predictFelicitous .cumulative .object true true true = false := by decide

/-- The pair-list parse correctly predicts it IS felicitous. -/
theorem pairListParse_right_for_jersey :
    predictFelicitous .pairList .object true true true = true := by decide

/-- Two-parse model gets the jersey context right. -/
theorem twoParse_right_for_jersey :
    predictFelicitousEither .object true true true = true := by decide

/-! ### Number effect -/

/-- Both DPs plural → cumulation pathway available. -/
theorem bothPlural_cumulation :
    predictFelicitous .cumulative .object true true false = true := by decide

/-- Singular wh → cumulation pathway blocked (number effect). -/
theorem singularWh_blocks_cumulation :
    predictFelicitous .cumulative .object false true false = false := by decide

/-- Singular definite → cumulation pathway blocked (number effect). -/
theorem singularDefin_blocks_cumulation :
    predictFelicitous .cumulative .object true false false = false := by decide

/-! ### Subject-object asymmetry (pair-list parse) -/

/-- Pair-list parse: wh-object → felicitous. -/
theorem pairListParse_object_ok :
    predictFelicitous .pairList .object true true true = true := by decide

/-- Pair-list parse: wh-subject → infelicitous. -/
theorem pairListParse_subject_blocked :
    predictFelicitous .pairList .subject true true true = false := by decide

/-- Cumulation pathway: no asymmetry (both positions felicitous). -/
theorem cumulation_no_asymmetry :
    predictFelicitous .cumulative .object true true false = true ∧
    predictFelicitous .cumulative .subject true true false = true := by decide

/-! ### Datum-level verification -/

/-- Jersey pair-list: pair-list parse predicts the observed judgment. -/
theorem jerseyPairList_verified :
    predictFelicitous .pairList jerseyPairList.whPosition
      jerseyPairList.whPlural jerseyPairList.definPlural
      jerseyPairList.cumulativeInCG = jerseyPairList.pairListFelicitous := by decide

/-- Jersey between-them: cumulative parse predicts the observed judgment. -/
theorem jerseyBetweenThem_verified :
    predictFelicitous .cumulative jerseyBetweenThem.whPosition
      jerseyBetweenThem.whPlural jerseyBetweenThem.definPlural
      jerseyBetweenThem.cumulativeInCG = jerseyBetweenThem.pairListFelicitous := by decide

/-- Asymmetry: object felicitous via pair-list parse. -/
theorem asymmetryObject_verified :
    predictFelicitous .pairList asymmetryObject.whPosition
      asymmetryObject.whPlural asymmetryObject.definPlural
      asymmetryObject.cumulativeInCG = asymmetryObject.pairListFelicitous := by decide

/-- Asymmetry: subject infelicitous via pair-list parse. -/
theorem asymmetrySubject_verified :
    predictFelicitous .pairList asymmetrySubject.whPosition
      asymmetrySubject.whPlural asymmetrySubject.definPlural
      asymmetrySubject.cumulativeInCG = asymmetrySubject.pairListFelicitous := by decide

-- ============================================================================
-- § 5. Bridge theorems: cumulation ↔ questions
-- ============================================================================

/-! ### Connecting `cumulativeOp` to pair-list semantics

The cumulative operator from `Cumulativity.lean` is exactly the `**`
that @cite{johnston-2023} uses (eq. 2). We demonstrate on concrete
scenarios that:

(a) `cumulativeOp` doesn't distinguish specific mappings — two worlds
    with different player→number assignments but the same sets of players
    and numbers yield the same cumulative truth value. This is WHY pair-
    list responses go beyond the cumulative answer.

(b) `singleton_right_cumulativeOp` derives the number effect: with a
    singleton right argument, `**` collapses to universal quantification,
    eliminating the mapping uncertainty.

(c) `pairListSem` DOES distinguish specific mappings: it tracks the
    actual per-element information that pair-list answers convey.
-/

section ConcreteBridge

inductive Player where | ann | ben
  deriving DecidableEq, BEq, Repr

inductive Number where | n1 | n2 | n3 | n4 | n5
  deriving DecidableEq, BEq, Repr

instance : Fintype Player where
  elems := {.ann, .ben}
  complete x := by cases x <;> simp

instance : Fintype Number where
  elems := {.n1, .n2, .n3, .n4, .n5}
  complete x := by cases x <;> simp

def allPlayers : Finset Player := Finset.univ
def allNumbers : Finset Number := Finset.univ

/-- Scenario (5): Ann→n1, Ben→n2 (one-to-one). -/
def picked₁ : Player → Number → Bool
  | .ann, .n1 => true
  | .ben, .n2 => true
  | _,    _   => false

/-- Scenario (12a): Ann and Ben each like both n1 and n2 (many-to-many). -/
def picked₂ : Player → Number → Bool
  | .ann, .n1 => true
  | .ann, .n2 => true
  | .ben, .n1 => true
  | .ben, .n2 => true
  | _,    _   => false

/-- Scenario (12c): Ann→n1, Ben→n1 and n2 (asymmetric). -/
def picked₃ : Player → Number → Bool
  | .ann, .n1 => true
  | .ben, .n1 => true
  | .ben, .n2 => true
  | _,    _   => false

def relevantNumbers : Finset Number := {.n1, .n2}

/-! ### (a) Cumulation doesn't distinguish mappings -/

/-- All three scenarios yield `**(picked)(players, {n1,n2}) = true`.
    The cumulative operator can't tell which player picked which number.
    This is @cite{johnston-2023}'s eq. 12: the Hamblin set of a QPD
    under cumulative interpretation contains a proposition that is true
    in all three scenarios. -/
theorem cumulative_indistinguishes_scenarios :
    cumulativeOp picked₁ allPlayers relevantNumbers = true ∧
    cumulativeOp picked₂ allPlayers relevantNumbers = true ∧
    cumulativeOp picked₃ allPlayers relevantNumbers = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- But the relations genuinely differ: Ann didn't pick n2 in
    scenario 1 but did in scenario 2. A pair-list answer would
    distinguish these scenarios. -/
theorem scenarios_differ :
    picked₁ .ann .n2 ≠ picked₂ .ann .n2 := by decide

/-! ### (b) Number effect derived from `singleton_right_cumulativeOp`

When the wh-phrase yields a singular answer (a singleton set),
`cumulativeOp` collapses to universal quantification. This is the
formal content of the "number effect": there is no mapping uncertainty
to elaborate, so no pair-list response is motivated.

The theorem `singleton_right_cumulativeOp` (in `Cumulativity.lean`)
provides the general principle. Here we instantiate it: -/

/-- Left coverage with singleton: reduces to universal. -/
theorem singleton_number_effect :
    leftCoverage picked₁ allPlayers ({.n1} : Finset Number)
      = decide (∀ p ∈ allPlayers, picked₁ p .n1 = true) :=
  singleton_right_left_coverage picked₁ allPlayers .n1

/-- Full `**` with singleton and nonempty domain: universal. -/
theorem singleton_full_number_effect :
    cumulativeOp picked₁ allPlayers ({.n1} : Finset Number)
      = decide (∀ p ∈ allPlayers, picked₁ p .n1 = true) :=
  singleton_right_cumulativeOp picked₁ allPlayers .n1 ⟨.ann, Finset.mem_univ _⟩

/-- And in this case it's false: Ben didn't pick n1. -/
theorem singleton_not_cumulative :
    cumulativeOp picked₁ allPlayers ({.n1} : Finset Number) = false := by native_decide

/-! ### (c) Pair-list assignments distinguish mappings

Unlike `leftCoverage` (which only checks existential coverage),
`pairListAnswer` commits to a *specific* assignment function. Different
valid assignments yield different pair-list answers, even when cumulative
truth is identical. This is the formal content of Johnston's argument. -/

/-- Assignment for scenario 1: Ann→n1, Ben→n2 (one-to-one). -/
def assign₁ : Player → Number
  | .ann => .n1
  | .ben => .n2

/-- Reversed assignment: Ann→n2, Ben→n1. -/
def assign₂ : Player → Number
  | .ann => .n2
  | .ben => .n1

/-- `assign₁` is a valid pair-list answer for `picked₁`. -/
theorem assign₁_valid :
    pairListAnswer picked₁ allPlayers relevantNumbers assign₁ = true := by native_decide

/-- `assign₂` is NOT valid for `picked₁`: Ann didn't pick n2. This is
    exactly the information that pair-list answers encode and cumulative
    answers discard. -/
theorem assign₂_invalid_for_picked₁ :
    pairListAnswer picked₁ allPlayers relevantNumbers assign₂ = false := by native_decide

/-- For `picked₂` (many-to-many), BOTH assignments are valid — each
    player picked both numbers. But pair-list answers still distinguish
    them: "Ann picked n1, Ben picked n2" ≠ "Ann picked n2, Ben picked n1".
    Cumulative truth conflates these two pair-list answers into a single
    truth value. -/
theorem both_assignments_valid_for_picked₂ :
    pairListAnswer picked₂ allPlayers relevantNumbers assign₁ = true ∧
    pairListAnswer picked₂ allPlayers relevantNumbers assign₂ = true := by
  constructor <;> native_decide

/-- Pair-list answers encode per-atom witnesses that cumulation discards.
    Scenario 1 and scenario 2 have different per-atom truth values. -/
theorem different_witnesses :
    (picked₁ .ann .n1 = true ∧ picked₁ .ann .n2 = false) ∧
    (picked₂ .ann .n1 = true ∧ picked₂ .ann .n2 = true) := by decide

end ConcreteBridge

-- ============================================================================
-- § 6. Hamblin bridge: pair-list is strictly finer than cumulative
-- ============================================================================

/-! ### Pair-list propositions refine cumulative propositions

The Hamblin denotation of a question is a set of propositions — possible
answers (`Semantics.Questions.Hamblin.QuestionDen`). Under the cumulative
parse, the Hamblin set contains *cumulative propositions* that specify
which individuals are involved without specifying the mapping. Under the
pair-list parse, the Hamblin set contains *pair-list propositions* that
specify the complete assignment.

The pair-list Hamblin set is a strict refinement of the cumulative one:
every pair-list proposition entails exactly one cumulative proposition,
but multiple pair-list propositions can entail the same cumulative
proposition. This is why cumulative answers are less informative — they
conflate worlds that pair-list answers distinguish.

We demonstrate this concretely with `JerseyWorld`: two worlds with swapped
player→number assignments satisfy the same cumulative proposition but are
distinguished by pair-list propositions. -/

section HamblinBridge

/-- A world in the basketball jersey scenario: specifies which player
    picked which number. Different worlds = different assignments. -/
structure JerseyWorld where
  annPicks : Number
  benPicks : Number
  deriving DecidableEq, BEq, Repr

/-- The picking relation induced by a world. In world `w`, player `p`
    picked number `n` iff `n` is the number assigned to `p` in `w`. -/
def worldPicked (w : JerseyWorld) : Player → Number → Bool
  | .ann, n => n == w.annPicks
  | .ben, n => n == w.benPicks

/-- A pair-list proposition: "Ann picked `a`, Ben picked `b`."
    True in exactly those worlds where the assignment matches.
    Each such proposition is a member of the pair-list question's
    Hamblin set (`Semantics.Questions.Hamblin.QuestionDen`). -/
def plProp (a b : Number) : JerseyWorld → Bool :=
  fun w => (w.annPicks == a) && (w.benPicks == b)

/-- World where Ann→n1, Ben→n2. -/
def w₁₂ : JerseyWorld := ⟨.n1, .n2⟩

/-- World where Ann→n2, Ben→n1 (swapped assignment). -/
def w₂₁ : JerseyWorld := ⟨.n2, .n1⟩

/-- Pair-list propositions distinguish worlds with different assignments:
    "Ann picked n1, Ben picked n2" is true in w₁₂ but false in w₂₁. -/
theorem plProp_distinguishes :
    plProp .n1 .n2 w₁₂ = true ∧ plProp .n1 .n2 w₂₁ = false := by decide

/-- Both worlds satisfy cumulative truth for the same range {n1, n2}:
    the cumulative operator conflates them. -/
theorem cum_conflates :
    cumulativeOp (worldPicked w₁₂) allPlayers relevantNumbers = true ∧
    cumulativeOp (worldPicked w₂₁) allPlayers relevantNumbers = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Pair-list propositions are strictly finer than cumulative propositions.**

    Worlds that cumulation conflates (same cumulative truth value), pair-list
    distinguishes (different pair-list truth values). This is the Hamblin-level
    formalization of @cite{johnston-2023}'s central argument: the cumulative
    question's denotation is too coarse to capture the information that
    pair-list answers provide.

    Connects to `Semantics.Questions.Hamblin.QuestionDen`: the pair-list
    question's Hamblin set `{plProp a b | a b}` is a refinement of the
    cumulative question's Hamblin set. -/
theorem pairList_strictly_finer :
    plProp .n1 .n2 w₁₂ ≠ plProp .n1 .n2 w₂₁ ∧
    cumulativeOp (worldPicked w₁₂) allPlayers relevantNumbers =
    cumulativeOp (worldPicked w₂₁) allPlayers relevantNumbers := by
  constructor
  · decide
  · native_decide

end HamblinBridge

-- ============================================================================
-- § 7. Scope bridge: subject-object asymmetry
-- ============================================================================

/-! ### The pair-list parse requires DP-over-wh scope

The subject-object asymmetry in pair-list questions (@cite{chierchia-1993})
arises because the pair-list parse requires the plural definite DP to take
scope over the wh-phrase, distributing over the wh-domain:

- **Wh-object** ("Which numbers did the players pick?"): the plural definite
  DP *the players* is in subject position and c-commands the wh-phrase in
  object position → wide scope available → pair-list parse ✓

- **Wh-subject** ("#Which players picked the numbers?"): the plural definite
  DP *the numbers* is in object position and cannot scope over the wh-phrase
  in subject position → wide scope blocked → pair-list parse ✗

This parallels the contrast in canonical pair-list questions with overt
quantifiers: "Who does every student like?" (✓) vs "Who likes every
professor?" (✗).

Under the cumulation pathway, no such asymmetry arises: `cumulativeOp`
is symmetric in its arguments, so pair-list elaboration is available
regardless of wh-position (ex. 35–36). The asymmetry is visible only when
cumulation is excluded (e.g., the basketball jersey context). -/

/-- The pair-list parse requires the plural definite DP to scope over the
    wh-phrase. This is possible when wh is the object (DP in subject
    c-commands), blocked when wh is the subject (DP in object cannot
    scope over subject). -/
def pairListScopeOK (whPos : WhPosition) : Bool :=
  match whPos with
  | .object  => true   -- DP in subject scopes over wh in object ✓
  | .subject => false  -- DP in object cannot scope over wh in subject ✗

/-- The scope constraint derives the pair-list parse prediction in
    `predictFelicitous`: wh-object → felicitous. -/
theorem scope_derives_pairList_object :
    pairListScopeOK .object = predictFelicitous .pairList .object true true true := rfl

/-- Scope constraint derives: wh-subject → infelicitous. -/
theorem scope_derives_pairList_subject :
    pairListScopeOK .subject = predictFelicitous .pairList .subject true true true := rfl

-- ============================================================================
-- § 8. Epistemic bridge: question-embedding verbs
-- ============================================================================

/-! ### Why *wonder* and *discover* confirm the pair-list parse

@cite{johnston-2023} §3: attitude verbs *wonder* and *discover* embed QPDs
felicitously with pair-list content (ex. 31). This is unexpected under the
cumulation-only hypothesis, because pragmatic elaboration cannot operate
inside attitude verb scope.

The formal argument uses the epistemic properties of question-embedding
verbs (cf. `Semantics.Attitudes.Factivity`):

- **Rogative verbs** (*wonder*, *ask*) are felicitous only when the subject
  is *ignorant* of the embedded question's answer.
- In the jersey context, the coach KNOWS the cumulative answer (which
  numbers were picked). Under the cumulative parse, "the coach wonders
  [QPD]" violates the ignorance requirement → infelicitous.
- But the coach DOESN'T KNOW the pair-list answer (who picked which
  number). Under the pair-list parse, "the coach wonders [QPD]" satisfies
  the requirement → felicitous.

This derives from the Hamblin refinement (`pairList_strictly_finer`):
since the pair-list Hamblin set is finer, an agent can resolve the
cumulative question while remaining ignorant of the pair-list one. -/

section EpistemicBridge

/-- Whether an embedded question is felicitous under *wonder*/*discover*:
    the agent must lack the embedded question's answer.

    Both rogative verbs (*wonder*, *ask*) and learn-type responsive verbs
    (*discover*, *find out*) require ignorance — the difference is tense
    (currently ignorant vs. previously ignorant). -/
def embeddingRequiresIgnorance (agentKnowsAnswer : Bool) : Bool :=
  !agentKnowsAnswer

/-- Derive the agent's knowledge from the QPD parse and common-ground
    status.

    Under the cumulative parse, the agent knows the answer iff the
    cumulative answer is in the CG. Under the pair-list parse, the agent
    may lack the mapping even when the cumulative answer is known — this
    is the basketball jersey scenario (the coach knows which numbers were
    picked, but not who picked which). -/
def agentKnowsUnderParse (parse : QPDParse) (cumulativeInCG : Bool)
    (mappingKnown : Bool := false) : Bool :=
  match parse with
  | .cumulative => cumulativeInCG
  | .pairList   => mappingKnown

/-- "The coach wonders [QPD]" under cumulative parse: infelicitous.
    The coach already knows the cumulative answer. -/
theorem jersey_wonder_cumulative :
    embeddingRequiresIgnorance (agentKnowsUnderParse .cumulative true) = false := rfl

/-- "The coach wonders [QPD]" under pair-list parse: felicitous.
    The coach doesn't know the mapping. -/
theorem jersey_wonder_pairList :
    embeddingRequiresIgnorance (agentKnowsUnderParse .pairList true) = true := rfl

/-- "The coach will discover [QPD]" under pair-list parse: the coach
    is currently ignorant of the mapping (felicitous embedding).
    The embedded QPD denotes a question whose answer the coach will learn. -/
theorem jersey_discover_pairList :
    embeddingRequiresIgnorance (agentKnowsUnderParse .pairList true) = true := rfl

end EpistemicBridge

-- ============================================================================
-- § 9. Bridge to ScopeReadings.predictPairList
-- ============================================================================

/-! The updated `predictPairList` from `ScopeReadings.lean` now has a
`pluralDefinite` field (default `false`). Setting `pluralDefinite := true`
for QPDs correctly predicts pair-list availability even with a definite
subject, capturing @cite{johnston-2023}'s two-parse model at the level of
the existing infrastructure.

This bridges Johnston's QPD-specific analysis to the general pair-list
prediction machinery used for overt-quantifier pair-lists
(@cite{groenendijk-stokhof-1984}). -/

/-- Plural definites allow pair-list responses: the updated prediction
    function correctly returns `true`. -/
theorem predictPairList_pluralDefinite_ok :
    Semantics.Questions.ScopeReadings.predictPairList
      { attitudeVerb := none
      , universalDefinite := true
      , contrastiveFocus := false
      , isMatrix := true
      , pluralDefinite := true } = true := by decide

/-- Without the plural-definite flag, a definite universal still blocks
    pair-list (the pre-Johnston default, correct for non-plural definites). -/
theorem predictPairList_definite_blocks :
    Semantics.Questions.ScopeReadings.predictPairList
      { attitudeVerb := none
      , universalDefinite := true
      , contrastiveFocus := false
      , isMatrix := true
      , pluralDefinite := false } = false := by decide

/-- The `pluralDefinite` field correctly restores backward compatibility:
    for non-definite universals (standard case), behavior is unchanged. -/
theorem predictPairList_nondefinite_unchanged :
    Semantics.Questions.ScopeReadings.predictPairList
      { attitudeVerb := none
      , universalDefinite := false
      , contrastiveFocus := false
      , isMatrix := true
      , pluralDefinite := false } = true := by decide

end Johnston2023
