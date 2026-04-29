import Linglib.Theories.Pragmatics.Dialogue.KOS.Basic
import Linglib.Theories.Pragmatics.Dialogue.KOS.Rules

/-!
# The Reprise Content Hypothesis (RCH)

@cite{purver-ginzburg-2004}, @cite{ginzburg-2012}

The Reprise Content Hypothesis is a methodological criterion linking
fragment-reprise data to denotational adequacy. It comes in two strengths
(@cite{ginzburg-2012} ex. 98):

- **Weak RCH**: a fragment reprise question queries *a part of* the standard
  semantic content of the fragment being reprised.
- **Strong RCH**: a fragment reprise question queries *exactly* the standard
  semantic content of the fragment being reprised.

RCH operates per **reading type** — fragment reprises admit multiple readings
(Clausal Confirmation, Intended Content, Repetition, Correction;
@cite{ginzburg-2012} Ch. 6 §6.2.1, Table 6.1). A `reprisedContent` operation
returns the *type* at which each licensed query operates, parameterized by
reading.

## Architectural role

RCH is **not** a load-bearing constraint inside the dialogue grammar — nothing
in KOS *needs* RCH to function. It is a meta-theoretic predicate over
denotation assignments: given a function from fragments to LocProps, RCH asks
whether the q-params structure on each LocProp licenses *exactly* (or *at
least*) the queries that a reprise empirically generates. RCH is therefore a
`Prop` predicate over assignment functions; specific denotation proposals
become theorems about whether they satisfy or violate it.

## What this file provides

- `RFReading` — the four reading types for reprise fragments
- `QueryType` — the semantic type at which a reprise query operates (individual,
  property, functional, repetition)
- `reprisedContent` — the set of query types observed for a (host, sub, reading)
- `RechPredictor` — the denotation-side function a theory must supply
- `WeakRCH` / `StrongRCH` — Prop predicates over predictors

The GQ-violation theorem and the q-params/dgb-params satisfaction theorem live
in `Phenomena/Dialogue/Studies/PurverGinzburg2004.lean`, which consumes this
file.
-/

namespace Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. Reprise readings (@cite{ginzburg-2012} Ch. 6 §6.2.1, Table 6.1)
-- ════════════════════════════════════════════════════

/-- The four reading types for a fragment reprise.

@cite{ginzburg-2012} Ch. 6 §6.2.1: empirical CR-corpus work establishes
that any single reprise fragment admits up to four readings, distinguished
by what they query.

This enum mirrors the `CRReading` enum in
`Phenomena/Dialogue/Studies/Ginzburg2012.lean`. We declare it here so that
`KOS/RepriseContent.lean` does not depend downstream on any Phenomena file. -/
inductive RFReading where
  /-- "Are you asking/saying that p?" — confirms propositional content -/
  | clausalConfirmation
  /-- "What do you mean by X?" — requests intended referent / predicate -/
  | intendedContent
  /-- "Can you repeat X?" — requests phonological repetition -/
  | repetition
  /-- "Did you say X or Y?" — corrective alternative -/
  | correction
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 2. QueryType — semantic type at which a reprise queries
-- ════════════════════════════════════════════════════

/-- The semantic type at which a fragment-reprise query operates.

@cite{ginzburg-2012} §8.5.1's argument against generalized-quantifier
denotations turns on a *type-mismatch*: GQ denotations predict reprise
queries at functional type `(e → t) → t`, while the empirical record shows
reprises operating only at individual / property type. We reify the relevant
type distinctions as a finite enum so that the GQ-violation theorem in
`PurverGinzburg2004.lean` can be a structural disagreement between predicted
and observed `QueryType` sets, not a numerical mismatch on probability
values. -/
inductive QueryType where
  /-- Query at type `e` — "what individual?" (witness for an `IND`-typed q-param) -/
  | individual
  /-- Query at type `e → t` — "what property/restriction?" -/
  | property : String → QueryType
  /-- Query at type `(e → t) → t` — generalized-quantifier-typed -/
  | functional
  /-- Query at the phonological form — "what string?" -/
  | repetition
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 3. Observed reprise content
-- ════════════════════════════════════════════════════

/-- Query types observed for a reprise of `sub` in host LocProp under `reading`.

@cite{ginzburg-2012} Ch. 6 §6.2.1, Table 6.1 + §8.5.1:

- `repetition` queries the phonological form (always `.repetition`).
- `intendedContent` queries the *q-params record* of the sub-utterance —
  one `.individual` query per index, plus a `.property` query per restrictor.
  When the host's `qcparams` is empty (referential NP), the only intended-
  content query is a `.property` over the sub-utterance's content string.
- `clausalConfirmation` confirms propositional content — a single
  `.individual` query about the witness.
- `correction` is ad-hoc and not characterized in §8.5; we return `[]`. -/
def reprisedContent {Cont : Type} (host : LocProp Cont) (sub : SubUtterance) :
    RFReading → List QueryType
  | .repetition           => [.repetition]
  | .intendedContent      =>
      if host.qcparams.isEmpty then
        [.property sub.cont]
      else
        .individual :: host.qcparams.map (fun p => QueryType.property p.restriction)
  | .clausalConfirmation  => [.individual]
  | .correction           => []

-- ════════════════════════════════════════════════════
-- § 4. RCH as a Prop predicate over predictors
-- ════════════════════════════════════════════════════

/-- A reprise scenario: a host utterance, a sub-utterance fragment within it,
and a reading type. -/
structure RepriseEvent (Cont : Type) where
  host : LocProp Cont
  sub : SubUtterance
  reading : RFReading

/-- A predictor maps a reprise event to the query types its denotation theory
*predicts* should be licensed. Different denotation proposals (GQ, q-params
split, HOU, ...) yield different predictors; RCH judges them. -/
abbrev RchPredictor (Cont : Type) := RepriseEvent Cont → List QueryType

/-- The q-params/dgb-params predictor (@cite{ginzburg-2012} §8.5.1).

For each reprise event, this predictor licenses exactly the query types that
the q-params record on the host's LocProp would expose — namely
`.individual` (witness) plus a `.property` per restrictor — plus the
reading-specific queries (`.repetition` for phonological echoes). -/
def qParamsPredictor {Cont : Type} : RchPredictor Cont :=
  fun ev => reprisedContent ev.host ev.sub ev.reading

/-- **Weak RCH** (@cite{ginzburg-2012} ex. 98a, p. 323):
every observed reprise query type is *predicted* by the denotation theory.

Read as: the theory does not under-generate. It may predict more than is
observed, but it covers everything that is observed. -/
def WeakRCH {Cont : Type} (predict : RchPredictor Cont) : Prop :=
  ∀ ev : RepriseEvent Cont, ∀ qt ∈ reprisedContent ev.host ev.sub ev.reading,
    qt ∈ predict ev

/-- **Strong RCH** (@cite{ginzburg-2012} ex. 98b, p. 323):
predicted and observed query type sets coincide.

Read as: the theory neither under- nor over-generates. Strong RCH is *too
strong* to hold of arbitrary fragments — Ginzburg himself documents
exceptions (the multi-reading phenomenon in Table 6.1). It is included for
completeness because Ginzburg states both versions. Theorems about it are
typically refutations. -/
def StrongRCH {Cont : Type} (predict : RchPredictor Cont) : Prop :=
  ∀ ev : RepriseEvent Cont,
    (∀ qt, qt ∈ reprisedContent ev.host ev.sub ev.reading ↔ qt ∈ predict ev)

-- ════════════════════════════════════════════════════
-- § 5. Structural facts
-- ════════════════════════════════════════════════════

/-- Strong RCH implies Weak RCH — the predicted set is a superset of the
observed set under either reading. -/
theorem strongRCH_implies_weakRCH {Cont : Type} (predict : RchPredictor Cont)
    (h : StrongRCH predict) : WeakRCH predict := by
  intro ev qt hqt
  exact ((h ev) qt).mp hqt

/-- The q-params predictor satisfies Weak RCH by construction:
it predicts exactly what `reprisedContent` reports. -/
theorem qParamsPredictor_satisfies_weakRCH {Cont : Type} :
    WeakRCH (qParamsPredictor : RchPredictor Cont) := by
  intro ev qt hqt
  exact hqt

/-- The q-params predictor satisfies Strong RCH for the same reason. -/
theorem qParamsPredictor_satisfies_strongRCH {Cont : Type} :
    StrongRCH (qParamsPredictor : RchPredictor Cont) := by
  intro ev qt
  exact Iff.rfl

end Pragmatics.Dialogue.KOS
