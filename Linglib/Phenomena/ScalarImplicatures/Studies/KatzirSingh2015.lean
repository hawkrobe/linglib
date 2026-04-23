import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Features.FelicityTypes
import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.ScalarImplicatures.Studies.Magri2009
import Linglib.Theories.Semantics.Questions.Denotation.Partition

/-!
# Economy of Structure and Information
@cite{heim-1991} @cite{hurford-1974} @cite{katzir-2007} @cite{katzir-singh-2015} @cite{magri-2009} @cite{spector-2014}

@cite{katzir-singh-2015}. Proceedings of Sinn und Bedeutung 19, pp. 322–339.

Two felicity conditions on assertions:

1. **Question Condition** (def 8): An assertion must address a good question —
   one not trivially settled by the common ground.

2. **Answer Condition** (def 15): An assertion must not be needlessly inferior
   to any alternative — where inferiority combines structural complexity with semantic strength.

These two conditions unify:
- @cite{magri-2009} oddness (# Some Italians come from a warm country)
- @cite{spector-2014} oddness (# All Italians...; # John has one wife)
- Hurford's constraint (# John visited France or Paris)
- Maximize Presupposition! (# A sun is shining)
- DE reversal of oddness patterns

Open problem: oddness under embedding (K&S §4) — the conditions are
stated globally but oddness persists in embedded constituents.

-/

namespace KatzirSingh2015

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Core K&S Definitions
-- ═══════════════════════════════════════════════════════════════════════

/-- Discourse scenario packaging meaning, complexity, context, and QUD.

- `meaning`: interpretation of each utterance at each world
- `complexity`: structural complexity; lower = simpler
- `context`: common knowledge; `context w = true` iff w is CK-compatible
- `qud`: question under discussion (equivalence relation on worlds)
- `utterances`: speaker's available alternatives
- `worlds`: exhaustive world enumeration -/
structure Scenario (W U : Type*) where
  meaning    : U → W → Bool
  complexity : U → ℕ
  context    : W → Bool
  qud        : QUD W
  utterances : List U
  worlds     : List W

namespace Scenario

variable {W U : Type*} (s : Scenario W U)

/-- Context-compatible worlds. -/
def cWorlds : List W := s.worlds.filter s.context

/-- Question Condition violation (K&S def 7–8): the QUD is trivially settled
by CK — all context-compatible worlds give the same answer.

Each scenario defines its QUD via a content-specific projection function
(e.g., `warmthAnswer`, `gradeAnswer`) that maps worlds to semantically
meaningful answer types. For minimal world types, these projections happen
to be injective (each world encodes a distinct answer), but making the
question explicit ensures the model extends correctly to richer world
types where multiple worlds could give the same answer. -/
def badQuestion : Bool :=
  s.cWorlds.all λ w => s.cWorlds.all λ v => s.qud.sameAnswer w v

/-- Semantic entailment over ALL worlds: ⟦u⟧ ⊆ ⟦v⟧.
Uses all worlds (not just context), since the better-than relation
compares general semantic strength (K&S def 16a). -/
def semEntails (u v : U) : Bool :=
  s.worlds.all λ w => !s.meaning u w || s.meaning v w

/-- At-least-as-good-as (K&S def 16a): φ ≲ ψ iff
φ is at most as complex as ψ AND semantically at least as strong (⟦φ⟧ ⊆ ⟦ψ⟧). -/
def atLeastAsGood (u v : U) : Bool :=
  decide (s.complexity u ≤ s.complexity v) && s.semEntails u v

/-- Strictly better-than (K&S def 16b): φ ≺ ψ := φ ≲ ψ ∧ ¬(ψ ≲ φ). -/
def betterThan (u v : U) : Bool :=
  s.atLeastAsGood u v && !s.atLeastAsGood v u

/-- Answer Condition violation (K&S def 15): u is needlessly inferior —
there exists a strictly better alternative. -/
def needlesslyInferior (u : U) : Bool :=
  s.utterances.any λ v => s.betterThan v u

/-- K&S Oddness: violates Question Condition or Answer Condition. -/
def isOdd (u : U) : Bool :=
  s.badQuestion || s.needlesslyInferior u

/-- Contextual equivalence: same truth value at all CK-compatible worlds. -/
def contextEquiv (u v : U) : Bool :=
  s.cWorlds.all λ w => s.meaning u w == s.meaning v w

/-- Strengthened Answer Condition: also requires the dominating alternative
to be *compatible with the context* (true at some CK-world). This closes
a truth gap where `needlesslyInferior` could flag an utterance as odd
because a false-but-simpler alternative exists.

For all 5 K&S scenarios, this coincides with `needlesslyInferior`
(verified below). -/
def needlesslyInferiorStrict (u : U) : Bool :=
  s.utterances.any λ v =>
    s.betterThan v u && s.cWorlds.any (s.meaning v)

end Scenario

/-- Reusable semantic model: meaning, complexity, world enumeration, and
utterance alternatives. Factored out of `Scenario` so the same model
can be paired with different discourse contexts. -/
structure SemanticModel (W U : Type*) where
  meaning    : U → W → Bool
  complexity : U → ℕ
  worlds     : List W
  utterances : List U

/-- Discourse context: context set + QUD. Factored out so different
questions/contexts can be explored with the same semantic model. -/
structure DiscourseContext (W : Type*) where
  context : W → Bool
  qud     : QUD W

/-- Build a `Scenario` from composable pieces. -/
def Scenario.mk' {W U : Type*} (m : SemanticModel W U) (d : DiscourseContext W) : Scenario W U where
  meaning    := m.meaning
  complexity := m.complexity
  context    := d.context
  qud        := d.qud
  utterances := m.utterances
  worlds     := m.worlds

-- ═══════════════════════════════════════════════════════════════════════
-- §2  @cite{spector-2014} Triviality (for comparison / bridge)
-- ═══════════════════════════════════════════════════════════════════════

section Triviality

variable {W : Type*} (worlds : List W) (C : W → Bool)

/-- C-contradiction: incompatible with context. (@cite{spector-2014}, def 4a) -/
def isCContradiction (φ' : W → Bool) : Bool :=
  worlds.all λ w => !C w || !φ' w

/-- C-tautology: entailed by context. (@cite{spector-2014}, def 4b) -/
def isCTautology (φ' : W → Bool) : Bool :=
  worlds.all λ w => !C w || φ' w

/-- C-equivalent to φ: same truth value in context. (@cite{spector-2014}, def 4c) -/
def isCEquivalent (φ φ' : W → Bool) : Bool :=
  worlds.all λ w => !C w || (φ w == φ' w)

/-- Trivial in C given φ. (@cite{spector-2014}, def 4) -/
def isTrivialInC (φ φ' : W → Bool) : Bool :=
  isCContradiction worlds C φ' ||
  isCTautology worlds C φ' ||
  isCEquivalent worlds C φ φ'

/-- No Trivial Alternatives violation (@cite{spector-2014}, def 5):
ALL alternatives are trivial in C given φ. -/
def allAlternativesTrivial (φ : W → Bool) (alts : List (W → Bool)) : Bool :=
  alts.all λ φ' => isTrivialInC worlds C φ φ'

end Triviality

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Italian Warmth Oddness — Question Condition
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (1)–(2): "# Some/All Italians come from a warm country"

The example is due to @cite{magri-2009}, who explains the oddness via
blind mandatory scalar implicatures (see `Magri2009.lean`). K&S offer
an alternative explanation: the QUD is trivially settled by CK.

CK: Italy is a warm country. Since all Italians come from Italy,
the QUD "Do [some/all] Italians come from a warm country?" is
trivially settled → Question Condition violation.

Both K&S and @cite{spector-2014} predict oddness here (§1.2). -/

section ItalianWarmth

inductive ItalyWorld where
  | allWarm  | noneWarm
  deriving DecidableEq, Repr

inductive ItalyUtt where
  | some_ | all_
  deriving DecidableEq, Repr

/-- "Do Italians come from a warm country?" — a yes/no question. -/
def warmthAnswer : ItalyWorld → Bool
  | .allWarm => true | .noneWarm => false

open ItalyWorld ItalyUtt in
def italianWarmthScenario : Scenario ItalyWorld ItalyUtt where
  meaning
    | some_, allWarm => true  | some_, noneWarm => false
    | all_,  allWarm => true  | all_,  noneWarm => false
  complexity | some_ => 1 | all_ => 1
  context    | allWarm => true | noneWarm => false
  qud := QUD.ofDecEq warmthAnswer (name := "warm country?")
  utterances := [some_, all_]
  worlds     := [allWarm, noneWarm]

/-- Contextual equivalence: some ↔ all (CK makes them interchangeable). -/
theorem italianWarmth_contextEquiv :
    italianWarmthScenario.contextEquiv .some_ .all_ = true := by native_decide

/-- QUD trivially settled by CK → Question Condition violated. -/
theorem italianWarmth_badQuestion :
    italianWarmthScenario.badQuestion = true := by native_decide

/-- K&S prediction: "some" is odd. -/
theorem italianWarmth_some_odd :
    italianWarmthScenario.isOdd .some_ = true := by native_decide

/-- K&S prediction: "all" is odd. -/
theorem italianWarmth_all_odd :
    italianWarmthScenario.isOdd .all_ = true := by native_decide

/-- Bridge: @cite{spector-2014} makes the same prediction (all alternatives trivial). -/
theorem spector_agrees_italianWarmth :
    allAlternativesTrivial [ItalyWorld.allWarm, .noneWarm]
      (λ w => w == .allWarm)
      (italianWarmthScenario.meaning .some_)
      [italianWarmthScenario.meaning .all_] = true := by native_decide

end ItalianWarmth

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Needlessly Weak Answers — Answer Condition
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (14)/(17): "In this department, every professor gives the same
grade to all of his students. Kim is a professor."
  (a) # This year, Kim assigned an A to some of his students — ODD
  (b) This year, Kim assigned an A to all of his students — OK

The QUD is good (we don't know Kim's grade). But "some" is needlessly
weak: "all" is equally complex and semantically stronger.

Connects to Core.Scale: the ⟦all⟧ ⊆ ⟦some⟧ entailment that drives
the Answer Condition is the same relationship captured by
`Alternatives.Quantifiers.entails.all.some_ = true`. -/

section NeedlesslyWeak

inductive GradeWorld where
  | allA | someNotAll | noneA
  deriving DecidableEq, Repr

inductive GradeUtt where
  | some_ | all_
  deriving DecidableEq, Repr

/-- "How many of Kim's students got an A?" — answer encoded as
(some-got-A, all-got-A) truth values on the ⟨some, all⟩ scale. -/
def gradeAnswer : GradeWorld → Bool × Bool
  | .allA => (true, true) | .someNotAll => (true, false) | .noneA => (false, false)

open GradeWorld GradeUtt in
def gradeScenario : Scenario GradeWorld GradeUtt where
  meaning
    | some_, allA => true | some_, someNotAll => true | some_, noneA => false
    | all_,  allA => true | all_,  someNotAll => false | all_,  noneA => false
  complexity | some_ => 1 | all_ => 1
  context | allA => true | someNotAll => false | noneA => true
  qud := QUD.ofDecEq gradeAnswer (name := "what grade did Kim give?")
  utterances := [some_, all_]
  worlds     := [allA, someNotAll, noneA]

/-- QUD is NOT trivially settled (Kim might or might not have given A). -/
theorem grade_goodQuestion :
    gradeScenario.badQuestion = false := by native_decide

/-- "all" entails "some" (semantically stronger in all worlds). -/
theorem grade_all_entails_some :
    gradeScenario.semEntails .all_ .some_ = true := by native_decide

/-- "some" does NOT entail "all" (true at someNotAll where "all" is false). -/
theorem grade_some_not_entails_all :
    gradeScenario.semEntails .some_ .all_ = false := by native_decide

/-- "all" ≺ "some" (equally complex, strictly stronger). -/
theorem grade_all_better_than_some :
    gradeScenario.betterThan .all_ .some_ = true := by native_decide

/-- K&S prediction: "some" is odd (needlessly weak). -/
theorem grade_some_odd :
    gradeScenario.isOdd .some_ = true := by native_decide

/-- K&S prediction: "all" is fine (best available answer). -/
theorem grade_all_ok :
    gradeScenario.isOdd .all_ = false := by native_decide

/-- Contextual equivalence despite general non-equivalence. -/
theorem grade_contextEquiv :
    gradeScenario.contextEquiv .some_ .all_ = true := by native_decide

end NeedlesslyWeak

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Hurford Disjunctions — Needlessly Complex
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (22): "# John visited France or Paris"

Since Paris ⊆ France, "France or Paris" ≡ "France" semantically.
But the disjunction is structurally more complex (complexity 2 vs 1).
So "France" ≺ "France or Paris" → disjunction is needlessly complex.

Connects to RSA/ScalarImplicatures/Hurford.lean which models
Hurford's constraint via speaker rationality. K&S derive the same
prediction from economy, without RSA machinery. -/

section Hurford

inductive VisitWorld where
  | parisOnly | franceNotParis | neither
  deriving DecidableEq, Repr

inductive VisitUtt where
  | france | franceOrParis
  deriving DecidableEq, Repr

/-- "Did John visit France?" — a yes/no question. Genuinely coarser than
identity: `parisOnly` and `franceNotParis` collapse (both → visited). -/
def visitAnswer : VisitWorld → Bool
  | .parisOnly => true | .franceNotParis => true | .neither => false

open VisitWorld VisitUtt in
/-- Hurford alternatives: the disjunction vs. its simple equivalent.
"Paris" is excluded from utterance alternatives because the Hurford
comparison is between a complex form and its semantically equivalent
simpler form, not between independently informative expressions. -/
def hurfordScenario : Scenario VisitWorld VisitUtt where
  meaning
    | france,        parisOnly => true  | france,        franceNotParis => true
    | france,        neither   => false
    | franceOrParis, parisOnly => true  | franceOrParis, franceNotParis => true
    | franceOrParis, neither   => false
  complexity | france => 1 | franceOrParis => 2
  context := λ _ => true
  qud := QUD.ofDecEq visitAnswer (name := "visited France?")
  utterances := [france, franceOrParis]
  worlds     := [parisOnly, franceNotParis, neither]

/-- "France" and "France or Paris" are semantically equivalent
(Paris ⊆ France, so the disjunction adds nothing). -/
theorem hurford_equiv :
    hurfordScenario.semEntails .france .franceOrParis = true ∧
    hurfordScenario.semEntails .franceOrParis .france = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- "France" ≺ "France or Paris" (simpler + equally strong). -/
theorem hurford_france_better :
    hurfordScenario.betterThan .france .franceOrParis = true := by native_decide

/-- K&S prediction: "France or Paris" is odd (needlessly complex). -/
theorem hurford_disjunction_odd :
    hurfordScenario.isOdd .franceOrParis = true := by native_decide

/-- K&S prediction: "France" is fine (no better alternative available). -/
theorem hurford_france_ok :
    hurfordScenario.isOdd .france = false := by native_decide

end Hurford

-- ═══════════════════════════════════════════════════════════════════════
-- §6  DE Reversal — Monotonicity Flips Oddness
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (18): "Every prof who assigned an A to [some/all] got a raise"

In DE restrictor, "some" picks out MORE professors → stronger universal.
The entailment direction reverses: ⟦some⟧_DE ⊆ ⟦all⟧_DE.
So "all" becomes needlessly weak (opposite of UE).

Connects to Semantics.Montague/Sentence/Entailment/Monotonicity.lean:
the reversal here is the same phenomenon as `every_restr_DE`. -/

section DEReversal

inductive DEWorld where
  | w1 | w2 | w3
  deriving DecidableEq, Repr

inductive DEUtt where
  | some_ | all_
  deriving DecidableEq, Repr

/-- "A to some or all?" in DE — answer encoded as
(some_DE, all_DE) truth values. -/
def deAnswer : DEWorld → Bool × Bool
  | .w1 => (true, true) | .w2 => (false, true) | .w3 => (false, false)

open DEWorld DEUtt in
/-- DE scenario: "some" version is stronger (narrower truth set).
In UE, ⟦all⟧ ⊆ ⟦some⟧; in DE, this reverses to ⟦some⟧_DE ⊆ ⟦all⟧_DE. -/
def deScenario : Scenario DEWorld DEUtt where
  meaning
    -- DE: "some" is STRONGER (true in fewer worlds)
    | some_, w1 => true  | some_, w2 => false | some_, w3 => false
    -- DE: "all" is WEAKER (true in more worlds)
    | all_,  w1 => true  | all_,  w2 => true  | all_,  w3 => false
  complexity | some_ => 1 | all_ => 1
  -- CK rules out w2 (same as grade: CK makes some/all equivalent)
  context | w1 => true | w2 => false | w3 => true
  qud := QUD.ofDecEq deAnswer (name := "A to some or all?")
  utterances := [some_, all_]
  worlds     := [w1, w2, w3]

/-- DE reversal: "some" entails "all" (opposite of UE). -/
theorem de_some_entails_all :
    deScenario.semEntails .some_ .all_ = true := by native_decide

/-- "all" does NOT entail "some" in DE. -/
theorem de_all_not_entails_some :
    deScenario.semEntails .all_ .some_ = false := by native_decide

/-- DE: "some" ≺ "all" (reversed from UE where "all" ≺ "some"). -/
theorem de_some_better_than_all :
    deScenario.betterThan .some_ .all_ = true := by native_decide

/-- K&S prediction in DE: "all" is odd (needlessly weak). -/
theorem de_all_odd :
    deScenario.isOdd .all_ = true := by native_decide

/-- K&S prediction in DE: "some" is fine (the stronger answer). -/
theorem de_some_ok :
    deScenario.isOdd .some_ = false := by native_decide

/-- Cross-scenario bridge: UE and DE have opposite entailment directions. -/
theorem ue_de_reversal :
    -- UE: all entails some
    gradeScenario.semEntails .all_ .some_ = true ∧
    -- DE: some entails all (reversed!)
    deScenario.semEntails .some_ .all_ = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- Cross-scenario bridge: UE and DE have opposite oddness verdicts. -/
theorem ue_de_oddness_flips :
    -- UE: "some" odd, "all" ok
    gradeScenario.isOdd .some_ = true ∧
    gradeScenario.isOdd .all_ = false ∧
    -- DE: "all" odd, "some" ok (flipped!)
    deScenario.isOdd .all_ = true ∧
    deScenario.isOdd .some_ = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end DEReversal

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Maximize Presupposition — Answer Condition
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (21): "# A sun is shining" vs. "The sun is shining"

CK: there is exactly one sun. Both utterances are contextually equivalent.
But "the sun" presupposes uniqueness, making it semantically stronger
(⟦the sun is shining⟧ ⊂ ⟦a sun is shining⟧). So "a sun" is needlessly
weak → Maximize Presupposition falls out as Answer Condition.

Connects to Core/Presupposition.lean: the definite's stronger presupposition
is what gives "the" its semantic advantage under K&S's ordering. -/

section MaxPresup

inductive SunWorld where
  | oneShining | oneNotShining | manySuns
  deriving DecidableEq, Repr

inductive SunUtt where
  | aSun | theSun
  deriving DecidableEq, Repr

/-- "Is the sun shining?" — presupposition-sensitive answer.
`manySuns` is a presupposition failure (uniqueness violated), distinct
from both yes and no. -/
def sunAnswer : SunWorld → Option Bool
  | .oneShining => some true | .oneNotShining => some false | .manySuns => none

open SunWorld SunUtt in
def maxPresupScenario : Scenario SunWorld SunUtt where
  meaning
    | aSun,   oneShining    => true  | aSun,   oneNotShining => false
    | aSun,   manySuns      => true   -- ∃ sun shining
    | theSun, oneShining    => true   -- unique sun + shining
    | theSun, oneNotShining => false
    | theSun, manySuns      => false  -- presup failure (not unique)
  complexity | aSun => 1 | theSun => 1
  -- CK: exactly one sun
  context | oneShining => true | oneNotShining => true | manySuns => false
  qud := QUD.ofDecEq sunAnswer (name := "is the sun shining?")
  utterances := [aSun, theSun]
  worlds     := [oneShining, oneNotShining, manySuns]

/-- "the sun" entails "a sun" (presuppositional strength). -/
theorem maxPresup_the_entails_a :
    maxPresupScenario.semEntails .theSun .aSun = true := by native_decide

/-- "a sun" does NOT entail "the sun" (true at manySuns where "the" fails). -/
theorem maxPresup_a_not_entails_the :
    maxPresupScenario.semEntails .aSun .theSun = false := by native_decide

/-- "the sun" ≺ "a sun" (equally complex, strictly stronger). -/
theorem maxPresup_the_better :
    maxPresupScenario.betterThan .theSun .aSun = true := by native_decide

/-- K&S prediction: "a sun" is odd (= Maximize Presupposition!). -/
theorem maxPresup_indefinite_odd :
    maxPresupScenario.isOdd .aSun = true := by native_decide

/-- K&S prediction: "the sun" is fine. -/
theorem maxPresup_definite_ok :
    maxPresupScenario.isOdd .theSun = false := by native_decide

/-- Contextual equivalence: CK (unique sun) makes a/the equivalent. -/
theorem maxPresup_contextEquiv :
    maxPresupScenario.contextEquiv .aSun .theSun = true := by native_decide

end MaxPresup

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Independence of the Two Conditions
-- ═══════════════════════════════════════════════════════════════════════

/-- The Question Condition and Answer Condition are independent:
- Italian warmth: Question Condition violated, Answer Condition irrelevant
- Grade: Question Condition satisfied, Answer Condition violated
This shows neither condition subsumes the other. -/
theorem conditions_independent :
    -- Question Condition violated (Italian warmth)
    italianWarmthScenario.badQuestion = true ∧
    -- Question Condition satisfied (Grade)
    gradeScenario.badQuestion = false ∧
    -- Answer Condition violated (Grade: "some" needlessly weak)
    gradeScenario.needlesslyInferior .some_ = true ∧
    -- Answer Condition satisfied (Italian warmth: neither is inferior)
    italianWarmthScenario.needlesslyInferior .some_ = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §9  needlesslyInferiorStrict Verification
-- ═══════════════════════════════════════════════════════════════════════

/-! Verify that `needlesslyInferiorStrict` (context-aware) coincides with
`needlesslyInferior` on all 5 scenarios. This confirms the truth gap
doesn't affect the existing examples. -/

theorem strict_agrees_italianWarmth :
    italianWarmthScenario.needlesslyInferiorStrict .some_ =
    italianWarmthScenario.needlesslyInferior .some_ := by native_decide

theorem strict_agrees_grade :
    gradeScenario.needlesslyInferiorStrict .some_ =
    gradeScenario.needlesslyInferior .some_ := by native_decide

theorem strict_agrees_hurford :
    hurfordScenario.needlesslyInferiorStrict .franceOrParis =
    hurfordScenario.needlesslyInferior .franceOrParis := by native_decide

theorem strict_agrees_de :
    deScenario.needlesslyInferiorStrict .all_ =
    deScenario.needlesslyInferior .all_ := by native_decide

theorem strict_agrees_maxPresup :
    maxPresupScenario.needlesslyInferiorStrict .aSun =
    maxPresupScenario.needlesslyInferior .aSun := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §10  Scenario Composability — SemanticModel × DiscourseContext
-- ═══════════════════════════════════════════════════════════════════════

/-! Demonstrate that `SemanticModel` + `DiscourseContext` can be composed
via `Scenario.mk'`. The DE scenario's semantic model is reused with a
different discourse context (all worlds CK-compatible). -/

section Composability

open DEWorld DEUtt in
/-- DE scenario's semantic model, factored out for reuse. -/
def deModel : SemanticModel DEWorld DEUtt where
  meaning
    | some_, w1 => true  | some_, w2 => false | some_, w3 => false
    | all_,  w1 => true  | all_,  w2 => true  | all_,  w3 => false
  complexity | some_ => 1 | all_ => 1
  worlds     := [w1, w2, w3]
  utterances := [some_, all_]

open DEWorld in
/-- Original DE discourse context (w2 ruled out by CK). -/
def deDiscourseOriginal : DiscourseContext DEWorld where
  context | w1 => true | w2 => false | w3 => true
  qud     := QUD.ofDecEq deAnswer (name := "A to some or all? (DE)")

open DEWorld in
/-- Alternative discourse context: all worlds CK-compatible. -/
def deDiscourseOpen : DiscourseContext DEWorld where
  context := λ _ => true
  qud     := QUD.ofDecEq deAnswer (name := "A to some or all? (open CK)")

/-- The composed scenario matches the original `deScenario`. -/
theorem compose_matches_de :
    let s := Scenario.mk' deModel deDiscourseOriginal
    s.isOdd .all_ = true ∧ s.isOdd .some_ = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- With open context (w2 now CK-compatible), "all" is still odd:
"some" still entails "all" in the DE model, so the Answer Condition
is unchanged. But the context change demonstrates reuse of the
semantic model with a different discourse context. -/
theorem compose_open_context :
    let s := Scenario.mk' deModel deDiscourseOpen
    s.isOdd .all_ = true ∧ s.isOdd .some_ = false := by
  exact ⟨by native_decide, by native_decide⟩

end Composability

-- ═══════════════════════════════════════════════════════════════════════
-- §12  Explicit Question Rescue (K&S §2.2)
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S predict that an explicit question neutralizes the Question Condition.

(3a)  # John has one wife — odd (no explicit question)
(11a) (How many wives does John have?) John has one wife — OK

The explicit question makes the QUD a "good question" (K&S (7))
regardless of whether CK settles it. Oddness then depends solely on
the Answer Condition. Since "one wife" is not needlessly inferior
(all alternatives are CK-incompatible), the sentence is felicitous.

This is a genuine prediction difference with @cite{spector-2014}:
Spector predicts oddness persists because the triviality of alternatives
is unchanged by the explicit question (K&S §2.2, p. 327). -/

section ExplicitQuestionRescue

inductive WifeWorld where
  | oneWife | twoWives | noWife
  deriving DecidableEq, Repr

inductive WifeUtt where
  | one | two | zero
  deriving DecidableEq, Repr

open WifeWorld WifeUtt in
/-- Semantic model for "John has N wives" (shared across discourse contexts). -/
def wifeModel : SemanticModel WifeWorld WifeUtt where
  meaning
    | one,  oneWife => true  | one,  twoWives => false | one,  noWife => false
    | two,  oneWife => false | two,  twoWives => true  | two,  noWife => false
    | zero, oneWife => false | zero, twoWives => false | zero, noWife => true
  complexity | one => 1 | two => 1 | zero => 1
  worlds := [oneWife, twoWives, noWife]
  utterances := [one, two, zero]

/-- "How many wives does John have?" — answer is a count. -/
def wifeCount : WifeWorld → Nat
  | .oneWife => 1 | .twoWives => 2 | .noWife => 0

open WifeWorld in
/-- Discourse context: CK = monogamous society (John has exactly one wife). -/
def wifeContextCK : DiscourseContext WifeWorld where
  context | oneWife => true | twoWives => false | noWife => false
  qud := QUD.ofDecEq wifeCount (name := "how many wives?")

def wifeScenario : Scenario WifeWorld WifeUtt :=
  Scenario.mk' wifeModel wifeContextCK

/-- QUD trivially settled by CK (everyone knows John has one wife). -/
theorem wife_badQuestion :
    wifeScenario.badQuestion = true := by native_decide

/-- "One wife" is NOT needlessly inferior: the alternatives ("two wives",
"zero wives") are CK-incompatible and semantically independent, so
neither is strictly better. -/
theorem wife_one_not_inferior :
    wifeScenario.needlesslyInferior .one = false := by native_decide

/-- Without explicit question: "John has one wife" is odd.
K&S (3a): the QUD is trivially settled → Question Condition violated. -/
theorem wife_one_odd :
    wifeScenario.isOdd .one = true := by native_decide

/-- K&S prediction with explicit question (K&S (11a)):

When "How many wives does John have?" is explicitly asked, the Question
Condition is satisfied (the question is good by K&S (7) — all participants
are committed to settling it). Oddness depends solely on the Answer
Condition. Since "one wife" is not needlessly inferior, the sentence
becomes felicitous.

Formally: `isOdd = badQuestion ∨ needlesslyInferior`. The explicit
question eliminates `badQuestion`, leaving only `needlesslyInferior`,
which is `false`. -/
theorem wife_rescue_answer_condition :
    wifeScenario.needlesslyInferior .one = false := by native_decide

/-- @cite{spector-2014} disagrees: "John has one wife" remains odd even
with the explicit question. All alternatives are trivial in CK:
- "two wives" is a C-contradiction (incompatible with CK)
- "zero wives" is a C-contradiction (incompatible with CK)
Since ALL alternatives are trivial, Spector's No Trivial Alternatives
condition (K&S (5)) is violated regardless of whether a question was asked.
Triviality is a property of the alternatives in context, not of the discourse. -/
theorem spector_wife_still_odd :
    allAlternativesTrivial [WifeWorld.oneWife, .twoWives, .noWife]
      (λ w => w == .oneWife)
      (wifeScenario.meaning .one)
      [wifeScenario.meaning .two, wifeScenario.meaning .zero] = true := by native_decide

/-- K&S vs Spector divergence on explicit question rescue:
- K&S: Answer Condition alone → "one wife" is fine (not needlessly inferior)
- Spector: all alternatives trivial → still odd (explicit question irrelevant)
This is the core empirical test case between the two theories. -/
theorem ks_spector_diverge_wife :
    wifeScenario.needlesslyInferior .one = false ∧
    allAlternativesTrivial [WifeWorld.oneWife, .twoWives, .noWife]
      (λ w => w == .oneWife)
      (wifeScenario.meaning .one)
      [wifeScenario.meaning .two, wifeScenario.meaning .zero] = true := by
  exact ⟨by native_decide, by native_decide⟩

end ExplicitQuestionRescue

-- ═══════════════════════════════════════════════════════════════════════
-- §14  Bridge to Empirical Hurford Data
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S's Hurford scenario (§5, K&S (22)) models entailing disjunctions
as needlessly complex answers. This bridges to the empirical Hurford
data in `ScalarImplicatures.Basic`, showing the theory accounts for
the observed infelicity judgments.

The rescue cases (K&S (24): "some or all", "possible or necessary") require
embedded exhaustification + a grammatical knowledge operator (K&S §3.3.2,
citing Meyer 2013). This additional machinery is beyond the scope of the
current formalization. -/

open Phenomena.ScalarImplicatures in
/-- K&S's theoretical prediction matches the empirical Hurford data:
- Theory: entailing disjunctions are needlessly complex → odd
- Data: `hurfordViolations` are all infelicitous

The theoretical mechanism (Answer Condition: `betterThan .france .franceOrParis`)
produces the same verdict as the empirical observation. -/
theorem ks_hurford_matches_empirical :
    -- Theory: "France or Paris" is odd (needlessly complex)
    hurfordScenario.isOdd .franceOrParis = true ∧
    -- Data: all empirical Hurford violations are infelicitous
    hurfordViolations.all (·.felicitous == false) = true := by
  exact ⟨by native_decide, by native_decide⟩

open Phenomena.ScalarImplicatures in
/-- The theoretical mechanism: "France" ≺ "France or Paris" because
"France" is simpler (complexity 1 < 2) and semantically equivalent
(Paris ⊆ France). This is the same entailment pattern observed in
the empirical Hurford data: each violation has B ⊆ A or A ⊆ B. -/
theorem ks_hurford_mechanism :
    -- Semantic equivalence
    hurfordScenario.semEntails .france .franceOrParis = true ∧
    hurfordScenario.semEntails .franceOrParis .france = true ∧
    -- "France" is strictly better (simpler + equivalent)
    hurfordScenario.betterThan .france .franceOrParis = true ∧
    -- The simpler form is fine
    hurfordScenario.isOdd .france = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

open Phenomena.ScalarImplicatures in
/-- Empirical prediction: rescued Hurford cases are felicitous.
K&S argues rescue requires embedded exhaustification (K&S §3.3.2, (24)):
exh(some) breaks the entailment, so "some or all" ≠ "all" semantically.
The data confirms this: all rescued cases are felicitous. -/
theorem hurford_rescued_match_data :
    hurfordRescuedCases.all (·.felicitous == true) = true := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §15  Three-Way Comparison: K&S ↔ Magri ↔ Spector
-- ═══════════════════════════════════════════════════════════════════════

/-! Three competing theories of oddness on the Italian warmth example:

| Sentence                  | Magri 2009 | K&S 2015 | Spector 2014 |
|---------------------------|:----------:|:--------:|:------------:|
| # Some Italians…          | ODD        | ODD      | ODD          |
| All Italians…             | ok         | ODD      | ODD          |

All three agree on "some". The disagreement on "all" reveals:
- **@cite{magri-2009}** is the most targeted: only oddness when a blind
  implicature contradicts CK. "All" generates no implicature, so it's fine.
- **K&S** casts the widest net via the Question Condition: ANY utterance
  addressing a trivially settled QUD is odd.
- **@cite{spector-2014}** predicts oddness via triviality: "all" is a
  C-tautology (entailed by CK), so the only alternative is trivial → odd. -/

section ThreeWayComparison

open Magri2009

/-- Three-way agreement on "some Italians come from a warm country":
all three theories predict oddness, via different mechanisms. -/
theorem three_way_agree_some :
    -- Magri: odd (blind implicature ¬all contradicts CK)
    italianScenario.blindOdd .some_ = true ∧
    -- K&S: odd (QUD trivially settled by CK)
    italianWarmthScenario.isOdd .some_ = true ∧
    -- Spector: odd (sole alternative is trivial)
    allAlternativesTrivial
      [Magri2009.ItalyWorld₃.allWarm, .someNotAll, .noneWarm]
      (λ w => w == .allWarm)
      (italianScenario.meaning .all_)
      [italianScenario.meaning .some_] = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Three-way comparison on "all Italians come from a warm country":
Magri says fine; K&S and Spector both say odd. -/
theorem three_way_disagree_all :
    -- Magri: fine (no implicature generated)
    italianScenario.blindOdd .all_ = false ∧
    -- K&S: odd (Question Condition violated)
    italianWarmthScenario.isOdd .all_ = true ∧
    -- Spector: odd (sole alternative is trivial)
    allAlternativesTrivial
      [Magri2009.ItalyWorld₃.allWarm, .someNotAll, .noneWarm]
      (λ w => w == .allWarm)
      (italianScenario.meaning .all_)
      [italianScenario.meaning .some_] = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

end ThreeWayComparison

end KatzirSingh2015
