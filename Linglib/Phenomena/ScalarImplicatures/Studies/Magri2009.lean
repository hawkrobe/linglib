import Linglib.Core.Interfaces.Felicity
import Mathlib.Tactic.TypeStar

/-!
# Blind Mandatory Scalar Implicatures
@cite{magri-2009}

@cite{magri-2009}. Natural Language Semantics 17(3): 245–297.

Two hypotheses form the core of the paper:

1. **Blindness Hypothesis (BH)** (§3.2.2): The exhaustivity operator EXH
   computes the strengthened meaning using *logical* entailment (→_W),
   not entailment given common knowledge (→_{W_ck}). That is, whether
   an alternative is excludable is determined without consulting CK.

2. **Mismatch Hypothesis (MH)** (§3.2.5): If the blind strengthened meaning
   EXH(φ) is a contradiction given common knowledge (EXH(φ) ∩ W_ck = ∅),
   then φ sounds odd.

## Introductory Example

"# Some Italians come from a warm country" (ex. (2))
- Literal: some Italians come from a warm country
- Strengthened (blind, via BH): some BUT NOT ALL Italians come from a warm country
- CK: Italy is warm → all Italians come from a warm country
- Strengthened ∩ CK = ∅ → odd (via MH)

## Application to Individual-Level Predicates

The paper's main contribution (§4) derives properties of individual-level
predicates (ILPs) from BH + MH via assumption (70): ILPs are
**homogeneous** — if an i-predicate holds at any time in W_ck, it holds at
all times. This homogeneity makes blind strengthening systematically
contradict CK for i-predicate constructions.

Key applications: "#Sometimes, John is tall" (§4.1), bare plural subject
restrictions (§4.2), embedding under universal quantifiers (§4.3), and
German word order (§4.5). See §5 below for the Q-adverb formalization.

The ILP/SLP distinction connects to `PredicateLevel` in
`Semantics.Lexical.Noun.Kind.Carlson1977`.
-/

namespace Phenomena.ScalarImplicatures.Studies.Magri2009

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Blind Strengthening Framework
-- ═══════════════════════════════════════════════════════════════════════

/-- A scenario for blind scalar implicature computation.

@cite{magri-2009}'s mechanism needs only literal meanings, scalar
alternatives, and common knowledge — no QUD or complexity ordering. -/
structure BlindScenario (W U : Type*) where
  /-- Literal meaning of each utterance at each world. -/
  meaning : U → W → Bool
  /-- Stronger scalar alternatives for each utterance.
      For ⟨some, all⟩: strongerAlts(some) = [all], strongerAlts(all) = [].

      This is a simplification of @cite{fox-2007}'s innocently excludable
      alternatives Excl(φ, Alt). For the ⟨some, all⟩ scale, Excl reduces to
      the set of logically stronger alternatives, so `strongerAlts` is
      equivalent. For richer alternative sets (e.g., with disjunction),
      Excl involves a maximal-consistency computation that this field
      does not capture. -/
  strongerAlts : U → List U
  /-- Common knowledge: which worlds are CK-compatible. -/
  context : W → Bool
  /-- Exhaustive world enumeration. -/
  worlds : List W

namespace BlindScenario

variable {W U : Type*} (s : BlindScenario W U)

/-- CK-compatible worlds. -/
def cWorlds : List W := s.worlds.filter s.context

/-- Strengthened meaning: literal ∧ negation of all stronger alternatives.

Implements the **Blindness Hypothesis** (BH): EXH computes the
strengthened meaning using logical entailment over W, not entailment
given common knowledge W_ck. The grammar strengthens automatically,
even when the result contradicts what speaker and hearer both know. -/
def strengthened (u : U) (w : W) : Bool :=
  s.meaning u w && (s.strongerAlts u).all (λ a => !s.meaning a w)

/-- Blind oddness: the utterance has scalar alternatives and the
strengthened meaning is false at every CK-compatible world.

Implements the **Mismatch Hypothesis** (MH): if EXH(φ) ∩ W_ck = ∅
(the blind strengthened meaning contradicts common knowledge), then
φ sounds odd. -/
def blindOdd (u : U) : Bool :=
  !(s.strongerAlts u).isEmpty &&
  s.cWorlds.all (λ w => !s.strengthened u w)

end BlindScenario

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Italian Warmth Example
-- ═══════════════════════════════════════════════════════════════════════

/-! "# Some Italians come from a warm country" (@cite{magri-2009})

Three worlds are needed because the strengthened meaning "some but not
all" requires a world where some but not all Italians come from a warm
country.

CK: Italy is a warm country → all Italians come from a warm country.
Only `allWarm` is CK-compatible. -/

inductive ItalyWorld₃ where
  | allWarm     -- all Italians come from a warm country (CK-compatible)
  | someNotAll  -- some but not all (not CK-compatible)
  | noneWarm    -- none do (not CK-compatible)
  deriving DecidableEq, BEq, Repr

inductive ItalyUtt where
  | some_ | all_
  deriving DecidableEq, BEq, Repr

open ItalyWorld₃ ItalyUtt in
def italianScenario : BlindScenario ItalyWorld₃ ItalyUtt where
  meaning
    | some_, allWarm => true  | some_, someNotAll => true  | some_, noneWarm => false
    | all_,  allWarm => true  | all_,  someNotAll => false | all_,  noneWarm => false
  strongerAlts
    | some_ => [all_]  -- "all" is the stronger scalar alternative
    | all_  => []      -- no stronger alternative on the ⟨some, all⟩ scale
  context
    | allWarm => true | someNotAll => false | noneWarm => false
  worlds := [allWarm, someNotAll, noneWarm]

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Core Predictions
-- ═══════════════════════════════════════════════════════════════════════

/-- Strengthened "some" at allWarm is false:
some(allWarm) ∧ ¬all(allWarm) = true ∧ false = false.
The blind implicature "not all" kills the literal meaning at the CK world. -/
theorem some_strengthened_false_at_ck :
    italianScenario.strengthened .some_ .allWarm = false := by native_decide

/-- Strengthened "some" at someNotAll is true:
some(someNotAll) ∧ ¬all(someNotAll) = true ∧ true = true.
But someNotAll is ruled out by CK — no help. -/
theorem some_strengthened_true_at_nonck :
    italianScenario.strengthened .some_ .someNotAll = true := by native_decide

/-- @cite{magri-2009} prediction: "some Italians" is odd.
The blind implicature "not all" contradicts CK (Italy is warm). -/
theorem italian_some_blind_odd :
    italianScenario.blindOdd .some_ = true := by native_decide

/-- "all Italians" is not odd: no stronger alternative to negate,
so no blind implicature is generated. -/
theorem italian_all_not_odd :
    italianScenario.blindOdd .all_ = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §4  FelicityCondition Instance
-- ═══════════════════════════════════════════════════════════════════════

/-- Input for @cite{magri-2009} felicity checking. -/
structure MagriInput (W U : Type*) where
  scenario : BlindScenario W U
  utterance : U

open Interfaces in
/-- @cite{magri-2009} as a `FelicityCondition`: an utterance is odd when
its blind strengthened meaning contradicts common knowledge. -/
instance {W U : Type*} : FelicityCondition (MagriInput W U) where
  name := "Magri 2009"
  check := λ ⟨s, u⟩ =>
    if s.blindOdd u then
      { status := .odd, source := some .unspecified }
    else
      { status := .felicitous }

/-- Magri predicts "some Italians" is odd. -/
theorem magri_italian_some_odd :
    Interfaces.isOdd (MagriInput.mk italianScenario .some_) = true := by native_decide

/-- Magri predicts "all Italians" is fine. -/
theorem magri_italian_all_ok :
    Interfaces.isOdd (MagriInput.mk italianScenario .all_) = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Individual-Level Predicates: Q-Adverbs (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

/-! @cite{magri-2009} ex. (3)/(72b): "# Sometimes, John is tall"

The paper's main contribution derives oddness of Q-adverbs with
individual-level predicates (ILPs) from BH + MH. The key assumption
is **ILP homogeneity** (assumption (70)): if an i-predicate holds of
an individual at any time in W_ck, it holds at all times. This rules
out mixed worlds (tall at some times but not all) from the common
ground.

- Literal: at some times, John is tall
- Strengthened (blind, via BH): at some but NOT ALL times, John is tall
- CK: "tall" is an ILP → homogeneity → John is either always tall
  or never tall. The "sometimes but not always" world is CK-incompatible.
- Strengthened ∩ CK = ∅ → odd (via MH)

Contrast with the stage-level predicate "# Sometimes, John is available":
since availability can genuinely vary over time, the "sometimes but not
always" world is CK-compatible → strengthened meaning is satisfiable → OK.

The ILP/SLP distinction is formalized in `PredicateLevel` from
`Semantics.Lexical.Noun.Kind.Carlson1977`. -/

section QAdverb

inductive TallWorld where
  | alwaysTall   -- tall at all times (CK-compatible: ILP homogeneity)
  | sometimesOnly -- tall at some but not all times (NOT CK-compatible)
  | neverTall    -- tall at no time (CK-compatible: ILP homogeneity)
  deriving DecidableEq, BEq, Repr

inductive QAdvUtt where
  | sometimes_ | always_
  deriving DecidableEq, BEq, Repr

open TallWorld QAdvUtt in
/-- @cite{magri-2009} §4.1: Q-adverbs with individual-level predicates.

"Sometimes" and "always" form a ⟨sometimes, always⟩ scale analogous to
⟨some, all⟩. ILP homogeneity (assumption (70)) rules out `sometimesOnly`
from the common ground. -/
def tallScenario : BlindScenario TallWorld QAdvUtt where
  meaning
    | sometimes_, alwaysTall => true   -- at some times = yes (all ⊆ some)
    | sometimes_, sometimesOnly => true
    | sometimes_, neverTall => false
    | always_,    alwaysTall => true
    | always_,    sometimesOnly => false
    | always_,    neverTall => false
  strongerAlts
    | sometimes_ => [always_]  -- "always" is stronger on the ⟨sometimes, always⟩ scale
    | always_    => []
  -- ILP homogeneity: only homogeneous worlds are CK-compatible
  context
    | alwaysTall => true | sometimesOnly => false | neverTall => true
  worlds := [alwaysTall, sometimesOnly, neverTall]

/-- Strengthened "sometimes" at alwaysTall is false:
sometimes(alwaysTall) ∧ ¬always(alwaysTall) = true ∧ false = false. -/
theorem tall_sometimes_strengthened_false :
    tallScenario.strengthened .sometimes_ .alwaysTall = false := by native_decide

/-- Strengthened "sometimes" at neverTall is also false:
sometimes(neverTall) = false. -/
theorem tall_sometimes_strengthened_false_never :
    tallScenario.strengthened .sometimes_ .neverTall = false := by native_decide

/-- @cite{magri-2009} prediction: "# Sometimes, John is tall" is odd.
The blind implicature "not always" contradicts ILP homogeneity. -/
theorem tall_sometimes_blind_odd :
    tallScenario.blindOdd .sometimes_ = true := by native_decide

/-- "Always, John is tall" is fine: no stronger alternative exists. -/
theorem tall_always_not_odd :
    tallScenario.blindOdd .always_ = false := by native_decide

/-- FelicityCondition prediction: "sometimes tall" is odd. -/
theorem magri_tall_sometimes_odd :
    Interfaces.isOdd (MagriInput.mk tallScenario .sometimes_) = true := by native_decide

/-- FelicityCondition prediction: "always tall" is fine. -/
theorem magri_tall_always_ok :
    Interfaces.isOdd (MagriInput.mk tallScenario .always_) = false := by native_decide

end QAdverb

end Phenomena.ScalarImplicatures.Studies.Magri2009
