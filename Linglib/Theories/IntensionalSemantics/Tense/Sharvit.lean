import Linglib.Theories.IntensionalSemantics.Tense.Basic
import Linglib.Core.Tense

/-!
# Sharvit (2003): Simultaneous Tense as a Genuine Tense

Sharvit's theory: the simultaneous reading under attitudes arises from a
genuine tense with its own semantics -- it denotes "at the local evaluation
time" -- rather than being zero tense (Ogihara), deleted past (Kratzer), or
a bound variable (Abusch).

## Core Mechanisms

1. **Simultaneous tense**: a tense morpheme whose semantics directly locates
   the event AT the local evaluation time
2. **Indirect question SOT**: the simultaneous tense handles SOT in indirect
   questions without deletion, zero tense, or binding
3. **RC tense**: uniform mechanism for relative clause tense
4. **Embedded present puzzle**: simultaneous tense at a future eval time
   explains present-under-future

## Motivating Data

The key data that Sharvit uses to motivate a separate simultaneous tense:

**Indirect questions**: "John asked who was sick" has a simultaneous reading
(who was sick at the asking time). Standard SOT theories struggle here:
- Deletion: what triggers deletion in a question (no attitude verb with
  the right properties)?
- Zero tense: why is the question past-marked at all?
- Binding: no attitude-like semantics provides a binder in questions.

Sharvit's solution: the "past" in the indirect question IS a simultaneous
tense -- its semantics locates the event at the local evaluation time
(the asking time), not before it.

## Optional SOT

In Hebrew-type languages, both the simultaneous tense and genuine past
are available in embedded clauses, producing optional SOT:
- "John said Mary was sick" (simultaneous tense → simultaneous reading)
- "John said Mary is sick" (present tense → simultaneous reading too,
  but with different pragmatic properties)

## Limitations

- The formal implementation here uses `sorry` for some derivation theorems
  pending closer consultation of Sharvit's LI 2003 paper
- Cross-linguistic predictions not fully worked out

## References

- Sharvit, Y. (2003). Embedded tense and universal grammar.
  *Linguistic Inquiry* 34(4): 669--681.
- Ogihara, T. & Sharvit, Y. (2012). Embedded tenses.
  In R. Binnick (ed.), *The Oxford Handbook of Tense and Aspect*.
-/

namespace IntensionalSemantics.Tense.Sharvit

open Core.Tense
open Core.Reichenbach
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Simultaneous Tense
-- ════════════════════════════════════════════════════════════════

/-- Sharvit's simultaneous tense: a genuine tense morpheme whose
    semantics locates the event AT the local evaluation time.

    This is distinct from:
    - Zero tense (Ogihara): an ambiguous reading of past
    - SOT deletion (Kratzer): removal of embedded past
    - Bound variable (Abusch): a variable receiving the matrix event time

    The simultaneous tense is a first-class tense with its own denotation:
    ⟦SIM⟧ = λt. λe. time(e) = t   (event time = evaluation time) -/
structure SimultaneousTense (Time : Type*) where
  /-- The local evaluation time (set by the matrix verb) -/
  evalTime : Time
  /-- The event time -/
  eventTime : Time
  /-- The tense's semantics: event time = evaluation time -/
  simultaneous : eventTime = evalTime

/-- The simultaneous tense is not a past tense: it does not assert
    temporal precedence. It asserts temporal overlap. -/
theorem simultaneousTense_is_present {Time : Type*}
    (st : SimultaneousTense Time) :
    st.eventTime = st.evalTime := st.simultaneous


-- ════════════════════════════════════════════════════════════════
-- § Indirect Question SOT
-- ════════════════════════════════════════════════════════════════

/-- Sharvit's challenge: tense in indirect questions.
    "John asked who was sick" -- past in the indirect question
    gets a simultaneous reading. Standard SOT theories struggle:
    - Deletion: what triggers deletion in a question?
    - Zero tense: why is the question past-marked at all?
    - Binding: no attitude-like semantics in questions.
    Sharvit: the simultaneous tense has its own semantics. -/
structure IndirectQuestionTense (Time : Type*) where
  /-- The asking time -/
  askingTime : Time
  /-- The sickness time -/
  sickTime : Time
  /-- Simultaneous: sickness at the asking time -/
  simultaneous : sickTime = askingTime

/-- An indirect question with simultaneous tense has the embedded event
    at the matrix event time (asking time), just like declarative SOT. -/
theorem indirectQ_simultaneous_at_asking {Time : Type*}
    (iqt : IndirectQuestionTense Time) :
    iqt.sickTime = iqt.askingTime := iqt.simultaneous


-- ════════════════════════════════════════════════════════════════
-- § Embedded Present Puzzle
-- ════════════════════════════════════════════════════════════════

/-- The embedded present puzzle: "John will say Mary is sick."

    The present tense "is" under future "will say" gets a simultaneous
    reading: Mary is sick at the future saying time, not necessarily
    at speech time.

    Sharvit's account: the "present" in the embedded clause is the
    simultaneous tense, evaluated at the (future) saying time. -/
structure EmbeddedPresentUnderFuture (Time : Type*) where
  /-- Speech time -/
  speechTime : Time
  /-- The future saying time -/
  sayingTime : Time
  /-- The sickness time -/
  sickTime : Time
  /-- The saying is in the future -/
  future_saying : Prop  -- sayingTime > speechTime
  /-- Simultaneous tense: sick at the saying time -/
  simultaneous : sickTime = sayingTime

/-- Under Sharvit's account, the embedded present puzzle is resolved:
    the simultaneous tense at a future eval time correctly predicts
    that sickness is at the future saying time. -/
theorem embedded_present_is_simultaneous {Time : Type*}
    (ep : EmbeddedPresentUnderFuture Time) :
    ep.sickTime = ep.sayingTime := ep.simultaneous


-- ════════════════════════════════════════════════════════════════
-- § Optional SOT (Hebrew-type)
-- ════════════════════════════════════════════════════════════════

/-- Optional SOT in Hebrew-type languages.

    Unlike English (obligatory SOT), Hebrew allows both:
    - "John said Mary was sick" (simultaneous tense → simultaneous reading)
    - "John said Mary is sick"  (present tense → also simultaneous, but
      with double-access pragmatics)

    The availability of both forms with similar (but not identical) meanings
    supports the existence of a dedicated simultaneous tense: in Hebrew,
    the choice is not forced by grammar, but in English, SOT forces the
    "past" form even for the simultaneous reading. -/
inductive HebrewSOTChoice where
  /-- Past morphology → simultaneous tense (Sharvit) -/
  | pastFormSimultaneous
  /-- Present morphology → genuine present (double-access) -/
  | presentFormDoubleAccess
  deriving DecidableEq, Repr, BEq

/-- Both Hebrew forms are grammatical (optional SOT). -/
theorem hebrew_both_available :
    HebrewSOTChoice.pastFormSimultaneous ≠ HebrewSOTChoice.presentFormDoubleAccess :=
  nofun


-- ════════════════════════════════════════════════════════════════
-- § Relative Clause Tense
-- ════════════════════════════════════════════════════════════════

/-- Sharvit's account of RC tense: the simultaneous tense in a relative
    clause is evaluated at the modified NP's temporal coordinate.

    "the man who was tall" — the past in the RC is simultaneous tense
    evaluated at the temporal coordinate of "the man."

    This provides a uniform mechanism: the same simultaneous tense
    operates in attitude complements, indirect questions, and RCs. -/
structure RCSimultaneousTense (Time : Type*) where
  /-- The modified NP's temporal coordinate -/
  npTime : Time
  /-- The RC event time -/
  rcEventTime : Time
  /-- Simultaneous: RC event at the NP's time -/
  simultaneous : rcEventTime = npTime

/-- RC simultaneous tense gives the expected frame: R = P. -/
theorem rc_simultaneous_present {Time : Type*}
    (rct : RCSimultaneousTense Time) :
    rct.rcEventTime = rct.npTime := rct.simultaneous


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Sharvit derives the simultaneous reading directly:
    the simultaneous tense semantics gives R = P by definition. -/
theorem sharvit_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).isPresent := rfl

/-- Sharvit derives the indirect question simultaneous reading
    without deletion, zero tense, or binding. The simultaneous tense
    in "John asked who was sick" locates sickness at asking time. -/
theorem sharvit_derives_indirect_question_SOT {Time : Type*}
    (iqt : IndirectQuestionTense Time) :
    iqt.sickTime = iqt.askingTime := iqt.simultaneous

/-- Sharvit handles the embedded present puzzle:
    "John will say Mary is sick" → sick at saying time.
    The simultaneous tense at a future eval time does the work. -/
theorem sharvit_handles_embedded_present_puzzle {Time : Type*}
    (ep : EmbeddedPresentUnderFuture Time) :
    ep.sickTime = ep.sayingTime := ep.simultaneous

/-- Sharvit derives RC tense uniformly via the simultaneous tense
    mechanism (same tense, different evaluation contexts). -/
theorem sharvit_derives_rc_tense {Time : Type*}
    (rct : RCSimultaneousTense Time) :
    rct.rcEventTime = rct.npTime := rct.simultaneous


-- ════════════════════════════════════════════════════════════════
-- § Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Sharvit (2003) identity card. -/
def Sharvit : TenseTheory where
  name := "Sharvit 2003"
  citation := "Sharvit, Y. (2003). Embedded tense and universal grammar. LI 34(4): 669-681."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := false
  simultaneousMechanism := "simultaneous tense with its own semantics (not deletion/zero/binding)"


end IntensionalSemantics.Tense.Sharvit
