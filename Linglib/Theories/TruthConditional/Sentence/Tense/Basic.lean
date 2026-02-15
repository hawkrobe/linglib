/-
# Tense Semantics

Semantic operators for grammatical tense (PAST, PRES, FUT).

## Core Idea

Tense operators impose temporal constraints on propositions:
- **PAST**: Event time precedes reference time (τ(s) < τ(s'))
- **PRES**: Event time equals reference time (τ(s) = τ(s'))
- **FUT**: Event time follows reference time (τ(s) > τ(s'))

Following Kratzer (1998), tenses are like pronouns for times:
they introduce or retrieve temporal reference points.

## Two Frameworks

1. **Reichenbach-style**: Tense relates R to S
   - PAST: R < S
   - PRESENT: R = S (or R ◦ S)
   - FUTURE: S < R

2. **Situation-semantic** (Kratzer/Mendes):
   - Tense operators take a situation argument and constrain its time
   - τ(s) is the temporal trace of situation s

## References

- Reichenbach, H. (1947). Elements of Symbolic Logic.
- Partee, B. (1973). Some structural analogies between tenses and pronouns.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
- Klein, W. (1994). Time in Language.
- Mendes, A. (2025). Indefiniteness in future reference. S&P 18(10).
-/

import Linglib.Core.Time
import Linglib.Core.Reichenbach

namespace TruthConditional.Sentence.Tense

open Core.Time
open Core.Reichenbach


/--
Grammatical tense: a temporal relation imposed by tense morphology.

Following the Reichenbach/Klein tradition:
- PAST: reference time before speech time
- PRESENT: reference time overlaps speech time
- FUTURE: reference time after speech time
-/
inductive GramTense where
  | past
  | present
  | future
  deriving DecidableEq, Repr, BEq, Inhabited

namespace GramTense

/-- Convert tense to its corresponding temporal relation -/
def toRelation : GramTense → TemporalRelation
  | .past => .before
  | .present => .overlapping
  | .future => .after

/-- The inverse relation (for "backwards" reference) -/
def inverseRelation : GramTense → TemporalRelation
  | .past => .after
  | .present => .overlapping
  | .future => .before

end GramTense


/--
Type of situation-level propositions.

A temporal predicate takes a situation and returns truth value.
This is what tense operators modify.
-/
abbrev SitProp (W Time : Type*) := Situation W Time → Prop

/--
Type of tense operators.

A tense operator takes:
- A temporal predicate P : (s, s') → Prop
- Two situations: the "now" situation s and evaluation situation s'
- Returns whether P holds with the tense constraint
-/
abbrev TenseOp (W Time : Type*) := SitProp W Time → Situation W Time → Situation W Time → Prop

/--
PAST operator (Mendes 2025 style)

⟦PAST⟧ = λP.λs.λs'. τ(s) < τ(s') ∧ P(s)

The PAST operator:
1. Requires the event situation s to precede reference situation s'
2. Evaluates P at the past situation s
-/
def PAST {W Time : Type*} [LT Time] : TenseOp W Time :=
  λ P s s' => s.time < s'.time ∧ P s

/--
PRES operator (Mendes 2025 style)

⟦PRES⟧ = λP.λs.λs'. τ(s) = τ(s') ∧ P(s)

The PRESENT operator:
1. Requires the event situation s to be contemporaneous with s'
2. Evaluates P at situation s
-/
def PRES {W Time : Type*} : TenseOp W Time :=
  λ P s s' => s.time = s'.time ∧ P s

/--
FUT operator (Mendes 2025 style)

⟦FUT⟧ = λP.λs.λs'. τ(s) > τ(s') ∧ P(s)

The FUTURE operator:
1. Requires the event situation s to follow reference situation s'
2. Evaluates P at the future situation s
-/
def FUT {W Time : Type*} [LT Time] : TenseOp W Time :=
  λ P s s' => s.time > s'.time ∧ P s


/-
For simpler analyses, tense can modify a predicate relative to a fixed
speech time, without threading through two situations.

These are the "traditional" tense operators.
-/

/--
Simple PAST: Event time precedes speech time.

⟦PAST⟧ₛᵢₘₚₗₑ = λP.λt.λt_s. t < t_s ∧ P(t)
-/
def pastSimple {Time : Type*} [LT Time] (P : Time → Prop) (eventTime speechTime : Time) : Prop :=
  eventTime < speechTime ∧ P eventTime

/--
Simple PRESENT: Event time equals speech time.
-/
def presSimple {Time : Type*} (P : Time → Prop) (eventTime speechTime : Time) : Prop :=
  eventTime = speechTime ∧ P eventTime

/--
Simple FUTURE: Event time follows speech time.
-/
def futSimple {Time : Type*} [LT Time] (P : Time → Prop) (eventTime speechTime : Time) : Prop :=
  eventTime > speechTime ∧ P eventTime


/--
Apply a tense to a Reichenbach frame, constraining R relative to P.
Tense locates reference time relative to perspective time (Kiparsky 2002),
not speech time. In root clauses P = S, so this reduces to the standard
Reichenbach analysis. In SOT languages, embedded P shifts to the matrix
event time, making the embedded tense relative.
-/
def applyTense {Time : Type*} [LinearOrder Time] (t : GramTense) (f : ReichenbachFrame Time) : Prop :=
  match t with
  | .past => f.referenceTime < f.perspectiveTime
  | .present => f.referenceTime = f.perspectiveTime
  | .future => f.referenceTime > f.perspectiveTime

/--
Check if a Reichenbach frame satisfies a given tense.
Tense locates R relative to P (perspective time).
-/
def satisfiesTense {Time : Type*} [LinearOrder Time] [DecidableEq Time]
    [DecidableRel (α := Time) (· < ·)]
    (t : GramTense) (f : ReichenbachFrame Time) : Bool :=
  match t with
  | .past => f.referenceTime < f.perspectiveTime
  | .present => f.referenceTime == f.perspectiveTime
  | .future => f.referenceTime > f.perspectiveTime


/--
Sequence of tenses (for embedded tense in reported speech, etc.)

"John said that Mary left" - past under past
-/
def composeTense : GramTense → GramTense → GramTense
  | .past, .past => .past      -- Past of past is past (in English)
  | .past, .present => .past   -- Present of past is past
  | .past, .future => .past    -- Future of past... complex (would)
  | .present, t => t           -- Present is transparent
  | .future, .past => .future  -- Past of future... complex
  | .future, .present => .future
  | .future, .future => .future

/--
Sequence of Tenses (SOT) parameter.

Languages differ in how embedded tense interacts with matrix tense:
- **SOT languages** (English): Embedded tense is relative to matrix
- **Non-SOT languages** (Japanese): Embedded tense is absolute
-/
inductive SOTParameter where
  | relative  -- English: embedded tense relative to matrix
  | absolute  -- Japanese: embedded tense absolute (to utterance time)
  deriving DecidableEq, Repr, BEq


/--
PAST requires temporal precedence.
-/
theorem past_requires_precedence {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : Situation W Time) :
    PAST P s s' → s.time < s'.time := by
  intro ⟨h, _⟩
  exact h

/--
FUT requires temporal succession.
-/
theorem fut_requires_succession {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : Situation W Time) :
    FUT P s s' → s.time > s'.time := by
  intro ⟨h, _⟩
  exact h

/--
PRES requires contemporaneity.
-/
theorem pres_requires_contemporaneity {W Time : Type*}
    (P : SitProp W Time) (s s' : Situation W Time) :
    PRES P s s' → s.time = s'.time := by
  intro ⟨h, _⟩
  exact h

/--
Tense preserves the predicate.

If TENSE(P)(s, s'), then P(s).
-/
theorem past_preserves_pred {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : Situation W Time) :
    PAST P s s' → P s := by
  intro ⟨_, h⟩
  exact h

theorem pres_preserves_pred {W Time : Type*}
    (P : SitProp W Time) (s s' : Situation W Time) :
    PRES P s s' → P s := by
  intro ⟨_, h⟩
  exact h

theorem fut_preserves_pred {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : Situation W Time) :
    FUT P s s' → P s := by
  intro ⟨_, h⟩
  exact h


section Examples

/-- Example predicate: "rain at situation s" -/
def raining (W : Type*) : SitProp W ℤ := λ _s => True  -- placeholder

/-- "It rained" is true iff there's a past situation where it rained -/
example : PAST (raining Unit) ⟨(), -1⟩ ⟨(), 0⟩ := by
  constructor
  · -- -1 < 0
    decide
  · -- raining holds (trivially true)
    trivial

/-- "It will rain" is true iff there's a future situation where it rains -/
example : FUT (raining Unit) ⟨(), 1⟩ ⟨(), 0⟩ := by
  constructor
  · -- 1 > 0
    decide
  · trivial

end Examples

-- ════════════════════════════════════════════════════════════════
-- § composeTense Properties
-- ════════════════════════════════════════════════════════════════

/-!
### composeTense Properties

`composeTense` is a stipulative function defining how surface tenses compose
under embedding. The following theorems establish its algebraic properties.

For the DERIVED version — showing that composeTense matches the Reichenbach
analysis with perspective shifting — see
`TruthConditional.Sentence.Tense.SequenceOfTense`.
-/

/-- Present is transparent under composition (left):
    composing with matrix present always yields the embedded tense.
    This reflects present's semantics: R = P, so tense relative to
    a present perspective is unchanged. -/
theorem composeTense_present_left (t : GramTense) :
    composeTense .present t = t := by cases t <;> rfl

/-- Present is transparent under composition (right):
    embedding present under any tense yields the matrix tense.
    Embedded present = "at the matrix event time" = same tense
    relative to speech time. -/
theorem composeTense_present_right (t : GramTense) :
    composeTense t .present = t := by cases t <;> rfl

/-- Tense composition is idempotent for past: embedding past
    arbitrarily deep under past still yields past. -/
theorem composeTense_past_idempotent :
    composeTense .past .past = .past := rfl

/-- Tense composition is idempotent for future. -/
theorem composeTense_future_idempotent :
    composeTense .future .future = .future := rfl

end TruthConditional.Sentence.Tense
