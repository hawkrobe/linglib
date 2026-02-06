import Linglib.Core.QUD
import Linglib.Core.Proposition
import Linglib.Theories.QuestionSemantics.Partition

/-!
# Economy of Structure and Information

Katzir & Singh (2015). Proceedings of Sinn und Bedeutung 19, pp. 322–339.

Two felicity conditions on assertions:

1. **Question Condition** (def 8): An assertion must address a good question —
   one not trivially settled by the common ground.

2. **Answer Condition** (def 15): An assertion must not be needlessly inferior
   to any alternative — where inferiority combines structural complexity
   (Katzir 2007) with semantic strength.

These two conditions unify:
- Magri (2009) oddness (# Some Italians come from a warm country)
- Spector (2014) oddness (# All Italians...; # John has one wife)
- Hurford's constraint (# John visited France or Paris)
- Maximize Presupposition! (# A sun is shining)
- DE reversal of oddness patterns (Magri 2011)

Open problem: oddness under embedding (K&S §4) — the conditions are
stated globally but oddness persists in embedded constituents.

## References

- Katzir, R. & Singh, R. (2015). Economy of structure and information.
- Spector, B. (2014). Scalar implicatures, blindness and common knowledge.
- Magri, G. (2009). Individual-level predicates and mandatory scalar implicatures.
- Magri, G. (2011). Another argument for embedded scalar implicatures.
- Katzir, R. (2007). Structurally-defined alternatives.
- Hurford, J. R. (1974). Exclusive or inclusive disjunction.
- Heim, I. (1991). Artikel und Definitheit.
-/

namespace QuestionSemantics.EconomyOddness

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Core K&S Definitions
-- ═══════════════════════════════════════════════════════════════════════

/-- Discourse scenario packaging meaning, complexity, context, and QUD.

- `meaning`: interpretation of each utterance at each world
- `complexity`: structural complexity (Katzir 2007); lower = simpler
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
by CK — all context-compatible worlds give the same answer. -/
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
-- §2  Spector (2014) Triviality (for comparison / bridge)
-- ═══════════════════════════════════════════════════════════════════════

section Triviality

variable {W : Type*} (worlds : List W) (C : W → Bool)

/-- C-contradiction: incompatible with context. (Spector 2014, def 4a) -/
def isCContradiction (φ' : W → Bool) : Bool :=
  worlds.all λ w => !C w || !φ' w

/-- C-tautology: entailed by context. (Spector 2014, def 4b) -/
def isCTautology (φ' : W → Bool) : Bool :=
  worlds.all λ w => !C w || φ' w

/-- C-equivalent to φ: same truth value in context. (Spector 2014, def 4c) -/
def isCEquivalent (φ φ' : W → Bool) : Bool :=
  worlds.all λ w => !C w || (φ w == φ' w)

/-- Trivial in C given φ. (Spector 2014, def 4) -/
def isTrivialInC (φ φ' : W → Bool) : Bool :=
  isCContradiction worlds C φ' ||
  isCTautology worlds C φ' ||
  isCEquivalent worlds C φ φ'

/-- No Trivial Alternatives violation (Spector 2014, def 5):
ALL alternatives are trivial in C given φ. -/
def allAlternativesTrivial (φ : W → Bool) (alts : List (W → Bool)) : Bool :=
  alts.all λ φ' => isTrivialInC worlds C φ φ'

end Triviality

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Magri/Spector Oddness — Question Condition
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (1)–(2): "# Some/All Italians come from a warm country"

CK: Italy is a warm country. Since all Italians come from Italy,
the QUD "Do [some/all] Italians come from a warm country?" is
trivially settled → Question Condition violation.

Both K&S and Spector (2014) predict oddness here (§1.2). -/

section MagriSpector

inductive ItalyWorld where
  | allWarm  | noneWarm
  deriving DecidableEq, BEq, Repr

inductive ItalyUtt where
  | some_ | all_
  deriving DecidableEq, BEq, Repr

open ItalyWorld ItalyUtt in
def magriScenario : Scenario ItalyWorld ItalyUtt where
  meaning
    | some_, allWarm => true  | some_, noneWarm => false
    | all_,  allWarm => true  | all_,  noneWarm => false
  complexity | some_ => 1 | all_ => 1
  context    | allWarm => true | noneWarm => false
  qud := QUD.ofDecEq id
  utterances := [some_, all_]
  worlds     := [allWarm, noneWarm]

/-- Contextual equivalence: some ↔ all (CK makes them interchangeable). -/
theorem magri_contextEquiv :
    magriScenario.contextEquiv .some_ .all_ = true := by native_decide

/-- QUD trivially settled by CK → Question Condition violated. -/
theorem magri_badQuestion :
    magriScenario.badQuestion = true := by native_decide

/-- K&S prediction: "some" is odd. -/
theorem magri_some_odd :
    magriScenario.isOdd .some_ = true := by native_decide

/-- K&S prediction: "all" is odd. -/
theorem magri_all_odd :
    magriScenario.isOdd .all_ = true := by native_decide

/-- Bridge: Spector (2014) makes the same prediction (all alternatives trivial). -/
theorem spector_agrees_magri :
    allAlternativesTrivial [ItalyWorld.allWarm, .noneWarm]
      (λ w => w == .allWarm)
      (magriScenario.meaning .some_)
      [magriScenario.meaning .all_] = true := by native_decide

end MagriSpector

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Needlessly Weak Answers — Answer Condition
-- ═══════════════════════════════════════════════════════════════════════

/-! K&S ex. (14)/(17): "In this department, every professor gives the same
grade to all of his students. Kim is a professor."
  (a) # This year, Kim assigned an A to some of his students  — ODD
  (b)   This year, Kim assigned an A to all of his students  — OK

The QUD is good (we don't know Kim's grade). But "some" is needlessly
weak: "all" is equally complex and semantically stronger.

Connects to Core.Scales: the ⟦all⟧ ⊆ ⟦some⟧ entailment that drives
the Answer Condition is the same relationship captured by
`Core.Scales.Quantifiers.entails .all .some_ = true`. -/

section NeedlesslyWeak

inductive GradeWorld where
  | allA | someNotAll | noneA
  deriving DecidableEq, BEq, Repr

inductive GradeUtt where
  | some_ | all_
  deriving DecidableEq, BEq, Repr

open GradeWorld GradeUtt in
def gradeScenario : Scenario GradeWorld GradeUtt where
  meaning
    | some_, allA => true | some_, someNotAll => true | some_, noneA => false
    | all_,  allA => true | all_,  someNotAll => false | all_,  noneA => false
  complexity | some_ => 1 | all_ => 1
  context | allA => true | someNotAll => false | noneA => true
  qud := QUD.ofDecEq id
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
  deriving DecidableEq, BEq, Repr

inductive VisitUtt where
  | france | franceOrParis
  deriving DecidableEq, BEq, Repr

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
  qud := QUD.ofDecEq id
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

Connects to TruthConditional/Sentence/Entailment/Monotonicity.lean:
the reversal here is the same phenomenon as `every_restr_DE`. -/

section DEReversal

inductive DEWorld where
  | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr

inductive DEUtt where
  | some_ | all_
  deriving DecidableEq, BEq, Repr

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
  qud := QUD.ofDecEq id
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
  deriving DecidableEq, BEq, Repr

inductive SunUtt where
  | aSun | theSun
  deriving DecidableEq, BEq, Repr

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
  qud := QUD.ofDecEq id
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
- Magri: Question Condition violated, Answer Condition irrelevant
- Grade: Question Condition satisfied, Answer Condition violated
This shows neither condition subsumes the other. -/
theorem conditions_independent :
    -- Question Condition violated (Magri)
    magriScenario.badQuestion = true ∧
    -- Question Condition satisfied (Grade)
    gradeScenario.badQuestion = false ∧
    -- Answer Condition violated (Grade: "some" needlessly weak)
    gradeScenario.needlesslyInferior .some_ = true ∧
    -- Answer Condition satisfied (Magri: neither is inferior to the other)
    magriScenario.needlesslyInferior .some_ = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §9  needlesslyInferiorStrict Verification
-- ═══════════════════════════════════════════════════════════════════════

/-! Verify that `needlesslyInferiorStrict` (context-aware) coincides with
`needlesslyInferior` on all 5 scenarios. This confirms the truth gap
doesn't affect the existing examples. -/

theorem strict_agrees_magri :
    magriScenario.needlesslyInferiorStrict .some_ =
    magriScenario.needlesslyInferior .some_ := by native_decide

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
  qud     := QUD.ofDecEq id

open DEWorld in
/-- Alternative discourse context: all worlds CK-compatible. -/
def deDiscourseOpen : DiscourseContext DEWorld where
  context := λ _ => true
  qud     := QUD.ofDecEq id

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

end QuestionSemantics.EconomyOddness
