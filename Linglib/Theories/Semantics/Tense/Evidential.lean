import Linglib.Theories.Semantics.Tense.Compositional
import Linglib.Core.Evidence
import Linglib.Core.Presupposition
import Linglib.Theories.Semantics.Mood.Basic

/-!
# Tense and Evidence (Cumming 2026)

Cumming (2026, *Linguistics and Philosophy* 49:153–175) argues that English
nonfuture tenses encode an evidential constraint: the speaker's evidence must
be causally downstream of the described event. The formal backbone is a triple
(S, A, T) — speech time, evidence-acquisition time, topic-event time — with
language-specific ordering constraints on these parameters.

## The (S, A, T) System

Extending Reichenbach's (S, R, E), Cumming adds **A** (evidence-acquisition
time): the time at which the speaker acquires the evidence grounding the
assertion. Nonfuture tenses (past, present) impose T ≤ A — evidence is
*downstream* of the event. Future tense lifts this constraint.

## Cross-linguistic Data

The paper's tables (17)–(22) show that Korean (-te, -ney) and Bulgarian (-l)
tense morphology systematically interacts with evidential perspective. Paradigm
data is in `Fragments/{English/Tense, Korean/Evidentials, Bulgarian/Evidentials}`;
verification theorems are in `Phenomena/Cumming2026/Bridge.lean`.

## EP/UP Constraint Enums

`EPCondition` and `UPCondition` enumerate the distinct constraint shapes
attested across the three languages. Each has a `toConstraint` method that
recovers the predicate over `EvidentialFrame ℤ`. This replaces the earlier
design where paradigm entries stored opaque lambdas.

## Connection to Modal Evidentiality

The tense evidential constraint parallels von Fintel & Gillies's (2010)
`kernelMust` presupposition: both require non-direct evidence. The bridge
between these two phenomena is formalized in `Comparisons/TenseModalEvidentiality.lean`.

## Connection to Core.Evidence

`EPCondition.toEvidentialPerspective` maps the five EP constraint shapes to
the canonical `EvidentialPerspective` classification in `Core.Evidence`.

## References

- Cumming, S. (2026). Tense and evidence. *Linguistics and Philosophy* 49:153–175.
- Ninan, D. (2022). Tense and temporal evidence. *L&P* 45:941–969.
- Reichenbach, H. (1947). *Elements of Symbolic Logic*.
-/

namespace Semantics.Tense.Evidential

open Core.Time
open Core.Reichenbach
open Semantics.Tense
open Core.Evidence
open Core.Presupposition

-- ════════════════════════════════════════════════════
-- § 1. Evidential Frame
-- ════════════════════════════════════════════════════

/-- Cumming's (S, A, T) frame. Extends Reichenbach with an evidence-acquisition
    time A. S = speechTime, T = eventTime, A = acquisitionTime. The existing
    referenceTime (R) stays — it governs utterance perspective independently. -/
structure EvidentialFrame (Time : Type*) extends ReichenbachFrame Time where
  /-- Evidence-acquisition time (A): when the speaker acquires the evidence
      grounding the assertion. -/
  acquisitionTime : Time

-- ════════════════════════════════════════════════════
-- § 2. EP Constraint Enum
-- ════════════════════════════════════════════════════

/-- Evidential perspective constraint shapes attested across English, Korean,
    and Bulgarian (Cumming 2026, Tables 17–22). Each value corresponds to a
    distinct ordering on T vs A. -/
inductive EPCondition where
  /-- T ≤ A: evidence downstream of event (English past/progressive, Bulgarian NFUT). -/
  | downstream
  /-- T < A: strict downstream (Korean -te PAST, -ney PAST). -/
  | strictDownstream
  /-- T = A: contemporaneous evidence (Korean -te PRES, -ney PRES). -/
  | contemporaneous
  /-- A < T: prospective evidence (Korean -te FUT, -ney FUT, English will-have/will-now, Bulgarian FUT). -/
  | prospective
  /-- No EP constraint (English bare future/will). -/
  | unconstrained
  deriving DecidableEq, Repr, BEq

/-- Recover the predicate over `EvidentialFrame ℤ` from an `EPCondition`. -/
def EPCondition.toConstraint : EPCondition → EvidentialFrame ℤ → Prop
  | .downstream => λ f => f.eventTime ≤ f.acquisitionTime
  | .strictDownstream => λ f => f.eventTime < f.acquisitionTime
  | .contemporaneous => λ f => f.eventTime = f.acquisitionTime
  | .prospective => λ f => f.acquisitionTime < f.eventTime
  | .unconstrained => λ _ => True

/-- Is this EP constraint nonfuture? Downstream, strict downstream, and
    contemporaneous all entail T ≤ A; prospective and unconstrained do not. -/
def EPCondition.isNonfuture : EPCondition → Bool
  | .downstream => true
  | .strictDownstream => true
  | .contemporaneous => true
  | .prospective => false
  | .unconstrained => false

/-- Map EP constraint shapes to `EvidentialPerspective` where applicable.
    Unconstrained has no single perspective. -/
def EPCondition.toEvidentialPerspective : EPCondition → Option EvidentialPerspective
  | .downstream => some .retrospective
  | .strictDownstream => some .retrospective
  | .contemporaneous => some .contemporaneous
  | .prospective => some .prospective
  | .unconstrained => none

-- ════════════════════════════════════════════════════
-- § 3. UP Constraint Enum
-- ════════════════════════════════════════════════════

/-- Utterance perspective constraint shapes attested across the three
    languages (Cumming 2026). Each value corresponds to a distinct ordering
    on T vs S. -/
inductive UPCondition where
  /-- T < S: past. -/
  | past
  /-- T = S: present. -/
  | present
  /-- S < T: future. -/
  | future
  /-- T ≤ S: nonfuture (Bulgarian NFUT). -/
  | nonfuture
  /-- No UP constraint. -/
  | unconstrained
  deriving DecidableEq, Repr, BEq

/-- Recover the predicate over `EvidentialFrame ℤ` from a `UPCondition`. -/
def UPCondition.toConstraint : UPCondition → EvidentialFrame ℤ → Prop
  | .past => λ f => f.eventTime < f.speechTime
  | .present => λ f => f.eventTime = f.speechTime
  | .future => λ f => f.speechTime < f.eventTime
  | .nonfuture => λ f => f.eventTime ≤ f.speechTime
  | .unconstrained => λ _ => True

-- ════════════════════════════════════════════════════
-- § 4. Tense-Evidential Paradigm
-- ════════════════════════════════════════════════════

/-- A row in a tense-aspect-mood-evidentiality paradigm table.
    Generalizes Cumming's (2026) tense-evidential paradigm (Tables 17–22)
    with optional mood and mirativity fields, enabling unified TAME
    fragment entries. Existing `{ label, ep, up }` constructions still
    work because `mood` and `mirative` have default values (`none`). -/
structure TAMEEntry where
  /-- Morphological label (e.g., "simple past", "-te PAST") -/
  label : String
  /-- Evidential perspective constraint: T vs A -/
  ep : EPCondition
  /-- Utterance perspective constraint: T vs S -/
  up : UPCondition
  /-- Grammatical mood (indicative, subjunctive), if specified -/
  mood : Option Semantics.Mood.GramMood := none
  /-- Mirativity value (expected, unexpected, neutral), if specified -/
  mirative : Option Core.Evidence.MirativityValue := none

/-- Is this a nonfuture tense? Derived from the EP constraint. -/
def TAMEEntry.isNonfuture (p : TAMEEntry) : Bool :=
  p.ep.isNonfuture

/-- The EP constraint as a predicate over `EvidentialFrame ℤ`. -/
def TAMEEntry.epConstraint (p : TAMEEntry) :
    EvidentialFrame ℤ → Prop :=
  p.ep.toConstraint

/-- The UP constraint as a predicate over `EvidentialFrame ℤ`. -/
def TAMEEntry.upConstraint (p : TAMEEntry) :
    EvidentialFrame ℤ → Prop :=
  p.up.toConstraint

-- ════════════════════════════════════════════════════
-- § 5. Core Predicates
-- ════════════════════════════════════════════════════

/-- Cumming's constraint (10): evidence is downstream of the event.
    T ≤ A — the event precedes (or coincides with) evidence acquisition. -/
def downstreamEvidence (f : EvidentialFrame ℤ) : Prop :=
  f.eventTime ≤ f.acquisitionTime

-- ════════════════════════════════════════════════════
-- § 6. Generic Downstream Lemma
-- ════════════════════════════════════════════════════

/-- Any nonfuture EP constraint entails downstream evidence (T ≤ A).
    One proof, five cases — the three nonfuture cases follow from ≤, <, =
    respectively; the two non-nonfuture cases are eliminated by `h_nf`. -/
theorem EPCondition.nonfuture_implies_downstream
    (ep : EPCondition) (f : EvidentialFrame ℤ)
    (h_nf : ep.isNonfuture = true) (h_ep : ep.toConstraint f) :
    downstreamEvidence f := by
  cases ep with
  | downstream => exact h_ep
  | strictDownstream => exact le_of_lt h_ep
  | contemporaneous => exact le_of_eq h_ep
  | prospective => simp [isNonfuture] at h_nf
  | unconstrained => simp [isNonfuture] at h_nf

-- ════════════════════════════════════════════════════
-- § 7. Presuppositional Nonfuture Meaning
-- ════════════════════════════════════════════════════

/-- Nonfuture meaning as a presuppositional proposition (Cumming 2026, §5):
    the presupposition is that evidence is downstream (T ≤ A); the assertion
    is the bare propositional content p.

    This captures the non-truth-conditional status of the evidential
    constraint: it is a felicity condition (presupposition), not part
    of what is asserted. Parameterized over an arbitrary world type `W`. -/
def nonfutureMeaning {W : Type*} (f : EvidentialFrame ℤ) (p : Bool) : PrProp W where
  presup := λ _ => decide (f.eventTime ≤ f.acquisitionTime)
  assertion := λ _ => p

/-- The presupposition of nonfutureMeaning checks downstream evidence. -/
theorem nonfutureMeaning_presup {W : Type*} (f : EvidentialFrame ℤ) (p : Bool) (w : W) :
    (nonfutureMeaning f p).presup w = decide (f.eventTime ≤ f.acquisitionTime) := rfl

end Semantics.Tense.Evidential
