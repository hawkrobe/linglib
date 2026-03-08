import Linglib.Core.Interfaces.Felicity
import Linglib.Phenomena.ScalarImplicatures.Studies.KatzirSingh2015

/-!
# Blind Mandatory Scalar Implicatures
@cite{magri-2009}

@cite{magri-2009}. Natural Language Semantics 17(3): 245–297.

The grammar computes scalar implicatures **blindly** — without access to
common knowledge (CK). When the strengthened meaning (literal + negation of
stronger alternatives) contradicts CK, the utterance is odd.

## Core Mechanism

1. Compute strengthened meaning: ⟦S⟧_str = ⟦S⟧ ∧ ∀a ∈ ALT, ¬⟦a⟧
2. Check CK compatibility: is ⟦S⟧_str true at any CK-compatible world?
3. If no → oddness (blind implicature contradicts common knowledge)

## Key Example

"# Some Italians come from a warm country"
- Literal: some Italians come from a warm country
- Strengthened (blind): some BUT NOT ALL Italians come from a warm country
- CK: Italy is warm → all Italians come from a warm country
- Strengthened ∩ CK = ∅ → odd

## Comparison with @cite{katzir-singh-2015}

K&S explain the same oddness via Question Condition (QUD trivially settled
by CK). Both theories predict "some" is odd. They **disagree** on "all":
K&S predicts "all" is odd too (QUD trivially settled for all utterances),
while Magri predicts "all" is fine (no stronger alternative to negate).

## Connection to Individual-Level Predicates

@cite{magri-2009}'s key insight: individual-level predicates (ILPs) like
"come from a warm country" systematically trigger this pattern because
their truth is stable across times/situations, making blind strengthening
more likely to contradict CK. This connects to the ILP/SLP distinction
formalized in `Semantics.Lexical.Noun.Kind.Carlson1977`.
-/

namespace Phenomena.ScalarImplicatures.Studies.Magri2009

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Blind Strengthening Framework
-- ═══════════════════════════════════════════════════════════════════════

/-- A scenario for blind scalar implicature computation.

Unlike K&S's `Scenario` (which uses a QUD and complexity ordering),
Magri's mechanism only needs literal meanings, scalar alternatives,
and common knowledge. No question-based or economy-based reasoning. -/
structure BlindScenario (W U : Type*) where
  /-- Literal meaning of each utterance at each world. -/
  meaning : U → W → Bool
  /-- Stronger scalar alternatives for each utterance.
      For ⟨some, all⟩: strongerAlts(some) = [all], strongerAlts(all) = []. -/
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

Computed **blindly** — without consulting common knowledge. This is the
core of @cite{magri-2009}: the grammar strengthens automatically,
even when the result contradicts what speaker and hearer both know. -/
def strengthened (u : U) (w : W) : Bool :=
  s.meaning u w && (s.strongerAlts u).all (λ a => !s.meaning a w)

/-- Blind oddness: the utterance has scalar alternatives and the
strengthened meaning is false at every CK-compatible world.

The blind implicature (¬alt) combined with the literal meaning
yields a proposition incompatible with common knowledge → oddness. -/
def blindOdd (u : U) : Bool :=
  !(s.strongerAlts u).isEmpty &&
  s.cWorlds.all (λ w => !s.strengthened u w)

end BlindScenario

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Italian Warmth Example
-- ═══════════════════════════════════════════════════════════════════════

/-! "# Some Italians come from a warm country" (@cite{magri-2009})

Three worlds are needed (unlike K&S's two-world model) because the
strengthened meaning "some but not all" requires a world where some
but not all Italians come from a warm country.

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
-- §5  Bridge: Magri ↔ K&S
-- ═══════════════════════════════════════════════════════════════════════

/-! @cite{magri-2009} and @cite{katzir-singh-2015} make different
predictions for the Italian warmth scenario. They agree that "some"
is odd, but disagree about "all". -/

/-- Both theories agree: "some Italians come from a warm country" is odd. -/
theorem magri_ks_agree_some_odd :
    italianScenario.blindOdd .some_ = true ∧
    KatzirSingh2015.italianWarmthScenario.isOdd .some_ = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- The theories **disagree** on "all Italians come from a warm country":

- **Magri**: NOT odd — "all" has no stronger alternative, so no blind
  implicature is generated, and the literal meaning is CK-compatible.
- **K&S**: Odd — the QUD "Do all Italians come from a warm country?"
  is trivially settled by CK, so ANY assertion addressing it is odd.

This is a genuine empirical prediction difference. Intuitively, "All
Italians come from a warm country" is uninformative but not # odd in
the way "Some Italians come from a warm country" is, which favors
Magri's more targeted mechanism. -/
theorem magri_ks_disagree_all :
    italianScenario.blindOdd .all_ = false ∧
    KatzirSingh2015.italianWarmthScenario.isOdd .all_ = true := by
  exact ⟨by native_decide, by native_decide⟩

end Phenomena.ScalarImplicatures.Studies.Magri2009
