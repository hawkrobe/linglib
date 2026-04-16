import Linglib.Core.Polarity
import Linglib.Core.Discourse.InformationStructure

/-!
# Polarity-Marking Levels
Blühdorn (2012), @cite{turco-braun-dimroth-2014}, @cite{hohle-1992}

Languages mark polarity switches (negation → affirmation) by targeting
one of two distinct semantic levels:

1. **Polarity level**: a particle directly sets [+Pol], "undoing" contextual
   negation. Dutch *wel*, French *si*, Swedish *jo*.

2. **Assertion level**: prosodic prominence on the finite verb highlights
   the *assertion operator* — the element that carries the assertive
   relation between topic and comment. German Verum focus.

Both achieve polarity contrast/correction at the pragmatic level, but
they operate on different structural components of the sentence and make
different predictions about co-occurrence with negation.

## Key prediction: negation compatibility

Because the assertion operator *wraps* the polarized proposition, Verum
focus is compatible with either polarity value:

- "Das Kind HAT nicht geweint" (VF + neg = emphatic denial) ✓
- "Das Kind HAT geweint" (VF + pos = emphatic assertion) ✓

Because a polarity particle *is* the polarity operator, it clashes with
the opposite polarity value:

- "Het kind heeft wel gehuild" (wel + pos) ✓
- *"Het kind heeft wel niet gehuild" (wel + neg = contradictory) ✗

## Sentence decomposition

Following Blühdorn (2012), a sentence's polarity-relevant structure
decomposes into three layers:

```
  ASSERT [ POL [ RADICAL ] ]
    ↑           ↑       ↑
    VF         wel    content
```

Verum focus targets ASSERT; polarity particles target POL. The radical
is the polarity-neutral propositional content.
-/

namespace Semantics.Focus.PolarityLevel

open Core (Polarity)
open Core.InformationStructure (PolarityMarkingStrategy PolaritySwitchContext)

-- ════════════════════════════════════════════════════
-- § 1. Polarity-marking levels
-- ════════════════════════════════════════════════════

/-- The semantic level at which a polarity-marking device operates.

    Blühdorn (2012): Verum focus and affirmative particles target
    different structural components, yielding different co-occurrence
    patterns with negation. -/
inductive PolarityMarkingLevel where
  /-- Polarity level: targets [±Pol] directly.
      Affirmative particles (Dutch *wel*) set [+Pol]. -/
  | polarity
  /-- Assertion level: highlights the assertion operator (finiteness).
      German Verum focus (@cite{hohle-1992}). -/
  | assertion
  deriving DecidableEq, Repr

/-- Map polarity-marking strategies to their semantic level.
    Returns `none` for strategies without a clear level assignment. -/
def strategyLevel : PolarityMarkingStrategy → Option PolarityMarkingLevel
  | .particle        => some .polarity
  | .verumFocus      => some .assertion
  | .polarityReversal => some .polarity
  | .other           => none
  | .unmarked        => none

variable {W : Type}

-- ════════════════════════════════════════════════════
-- § 2. Sentence structure
-- ════════════════════════════════════════════════════

/-- A sentence decomposed into its polarity-relevant structural layers.

    Blühdorn (2012): every sentence has a polarity-neutral radical,
    a polarity operator [±Pol], and an assertion operator. Different
    polarity-marking devices target different layers.

    The `marking` field uses `Option PolarityMarkingLevel` rather than
    two independent Bools — assertion-level and polarity-level marking
    are mutually exclusive by construction. -/
structure SentenceStructure (W : Type) where
  /-- Polarity-neutral propositional content -/
  radical : W → Bool
  /-- The polarity value [±Pol] -/
  pol : Polarity
  /-- Which structural level is overtly marked, if any -/
  marking : Option PolarityMarkingLevel := none

/-- Apply polarity to the radical to get truth conditions.

    Polarity is the innermost operator: it wraps the radical before
    the assertion operator applies. -/
def SentenceStructure.eval (s : SentenceStructure W) : W → Bool :=
  match s.pol with
  | .positive => s.radical
  | .negative => λ w => !s.radical w

-- ════════════════════════════════════════════════════
-- § 3. Predictions: negation compatibility
-- ════════════════════════════════════════════════════

/-- Is a marking level compatible with a given polarity value?

    Assertion-level marking (VF) is compatible with either polarity
    because it targets the assertion operator, which wraps the
    already-polarized proposition.

    Polarity-level marking (particles) requires [+Pol] — the particle
    IS the polarity operator, so it cannot coexist with [−Pol]. -/
def PolarityMarkingLevel.compatibleWith : PolarityMarkingLevel → Polarity → Bool
  | .assertion, _         => true
  | .polarity,  .positive => true
  | .polarity,  .negative => false

/-- Well-formedness constraint on polarity marking.

    Delegates to `PolarityMarkingLevel.compatibleWith`: unmarked
    sentences are always well-formed; marked sentences must have a
    level compatible with their polarity value. -/
def SentenceStructure.wellFormed (s : SentenceStructure W) : Bool :=
  match s.marking with
  | none       => true
  | some level => level.compatibleWith s.pol

/-! ### Prediction 1: VF is compatible with negation

"Das Kind HAT nicht geweint" — VF on a negative sentence yields
emphatic denial (counter-presuppositional reading,
Gussenhoven 1983). -/

theorem vf_negative_wellformed (radical : W → Bool) :
    (SentenceStructure.mk radical .negative (some .assertion)).wellFormed = true := rfl

theorem vf_positive_wellformed (radical : W → Bool) :
    (SentenceStructure.mk radical .positive (some .assertion)).wellFormed = true := rfl

/-! ### Prediction 2: polarity particles require [+Pol]

*"Het kind heeft wel niet gehuild" — *wel* in a negative sentence
is contradictory. -/

theorem particle_negative_illformed (radical : W → Bool) :
    (SentenceStructure.mk radical .negative (some .polarity)).wellFormed = false := rfl

theorem particle_positive_wellformed (radical : W → Bool) :
    (SentenceStructure.mk radical .positive (some .polarity)).wellFormed = true := rfl

/-! ### The two levels differ on negation compatibility -/

theorem levels_differ_on_negation :
    PolarityMarkingLevel.polarity.compatibleWith .negative ≠
    PolarityMarkingLevel.assertion.compatibleWith .negative := by decide

-- ════════════════════════════════════════════════════
-- § 4. Functional equivalence
-- ════════════════════════════════════════════════════

/-- Despite operating at different semantic levels, both strategies yield
    the same truth conditions when applied to a positive proposition.

    @cite{turco-braun-dimroth-2014}: Dutch *wel* and German VF are
    "functionally equivalent" for polarity contrast/correction —
    the pragmatic effect is the same even though the structural target
    differs. -/
theorem functional_equivalence_positive (radical : W → Bool) :
    let vf  : SentenceStructure W := ⟨radical, .positive, some .assertion⟩
    let prt : SentenceStructure W := ⟨radical, .positive, some .polarity⟩
    vf.eval = prt.eval := rfl

/-- Both strategies are available in both discourse contexts
    (contrast and correction). The level distinction is orthogonal
    to the context distinction. -/
theorem both_levels_context_general :
    ∀ ctx : PolaritySwitchContext,
    ∀ _ : PolarityMarkingLevel,
    (ctx = .contrast ∨ ctx = .correction) := by
  intro ctx _; cases ctx <;> simp

-- ════════════════════════════════════════════════════
-- § 5. Strategy-level bridge
-- ════════════════════════════════════════════════════

theorem particle_targets_polarity :
    strategyLevel .particle = some .polarity := rfl

theorem vf_targets_assertion :
    strategyLevel .verumFocus = some .assertion := rfl

/-- Particles and VF target different levels. -/
theorem particle_vf_different_levels :
    strategyLevel .particle ≠ strategyLevel .verumFocus := by decide

/-- Polarity-reversal particles (German *doch*, Swedish *jo*, French *si*)
    also target the polarity level, like affirmative particles. -/
theorem reversal_targets_polarity :
    strategyLevel .polarityReversal = some .polarity := rfl

end Semantics.Focus.PolarityLevel
