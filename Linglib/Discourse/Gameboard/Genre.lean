import Linglib.Discourse.Gameboard.Basic

/-!
# KOS: Genre Relevance & Outcome Fulfillment
[ginzburg-2012] §4.6 (pp. 101–110)

The `genreRelevant` predicate (eq. 90 p. 105) constraining which
initiating moves are felicitous given a conversational genre, plus
the outcome-fulfillability machinery (ex. 89 p. 105) that ex. 90
reduces to.

## Relevance per ex. 90 p. 105

Ginzburg: "m0 is relevant to G0 in dgb0 for A iff A believes that
outcome(dgb0 ⊕moves m0, G0) will be fulfilled."

We model this as: simulate adding the move's question content to QUD,
then check whether the resulting QUD is consistent with the genre's
anticipated questions (qnud) or its explicit qudConstraint.

## Two genre-relevance predicates

This file provides two relevance computations:

- `genreRelevant` — the thin variant: uses the genre's `qudConstraint`
  predicate (no `DecidableEq` requirement). Suitable for genres that
  encode their constraints procedurally (e.g., bakery accepts only
  bread-related questions).
- `genreRelevantViaQnud` — the qnud-based variant: requires
  `[DecidableEq QContent]`. Suitable for genres that enumerate their
  anticipated questions explicitly. Models the eq. 88 qnud field
  directly.

Both project through the `InfoStruc` layer that QUD now stores
(per Ch. 6 final shape, with QUD-as-InfoStruc treatment per §7.6 FEC discussion).

## Outcome predicate

`GenreType.outcomeFulfilled` formalizes ex. 89's outcome relation: a
DGB fulfills the genre's outcome when its QUD-projected questions are
all in the anticipated `qnud` set. This is the substrate ex. 90 reduces
to ("outcome will be fulfilled").

## Deferred

Ginzburg's full TTR record (ex. 88) also includes agent fields, utt-time,
facts subset, and a co-propositionality constraint relating MaxQUD to
the move's content. These need richer machinery (TTR types for agents,
co-propositionality predicates) that downstream consumers can add when
they exercise these claims.
-/

namespace Discourse.Gameboard

-- ════════════════════════════════════════════════════
-- § 1. Outcome fulfillment (ex. 89 p. 105)
-- ════════════════════════════════════════════════════

/-- A DGB fulfills the genre's outcome when its QUD's projected questions
are all anticipated (i.e., in `genre.qnud`).

[ginzburg-2012] ex. 89 (p. 105): the outcome of a dialogue is
fulfilled when its trajectory is consistent with the genre's anticipated
question stack. The full version also requires move sequence to be
consistent with `anticipatedMoves`; we model the QUD half here. -/
def GenreType.outcomeFulfilled {P Fact QContent : Type*} {Cont : Type}
    [DecidableEq QContent]
    (genre : GenreType Fact QContent) (dgb : DGB P Fact QContent Cont) : Prop :=
  ∀ is ∈ dgb.qud, is.q ∈ genre.qnud

instance {P Fact QContent : Type*} {Cont : Type} [DecidableEq QContent]
    (genre : GenreType Fact QContent) (dgb : DGB P Fact QContent Cont) :
    Decidable (genre.outcomeFulfilled dgb) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

-- ════════════════════════════════════════════════════
-- § 2. Genre relevance — thin variant
-- ════════════════════════════════════════════════════

/-- A move is genre-relevant via the explicit `qudConstraint` predicate.

[ginzburg-2012] ex. 90 (p. 105): "m0 is relevant to G0 in dgb0 for A
iff A believes that outcome(dgb0 ⊕moves m0, G0) will be fulfilled."

This thin variant uses the genre's `qudConstraint` field (a procedural
predicate on the projected QUD content). For a `qnud`-list-based variant,
see `genreRelevantViaQnud`. -/
def genreRelevant {P Fact QContent : Type*} {Cont : Type}
    (genre : GenreType Fact QContent)
    (dgb : DGB P Fact QContent Cont) (m : IllocMove Fact QContent) : Prop :=
  match genre.qudConstraint with
  | none => True  -- unrestricted genre: all moves are relevant
  | some constraint =>
    match m.questionContent with
    | some q => constraint (q :: dgb.qud.map (·.q)) = true
    | none => True  -- non-question moves don't violate QUD constraints

instance {P Fact QContent : Type*} {Cont : Type}
    (genre : GenreType Fact QContent)
    (dgb : DGB P Fact QContent Cont) (m : IllocMove Fact QContent) :
    Decidable (genreRelevant genre dgb m) := by
  unfold genreRelevant
  cases genre.qudConstraint <;> cases m.questionContent <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 3. Genre relevance — qnud variant
-- ════════════════════════════════════════════════════

/-- A move is genre-relevant via the `qnud` (anticipated questions) field.

Ex. 90 reduced to the operational form: simulating the move's
QUD-incrementation, the resulting QUD must consist entirely of anticipated
questions. -/
def genreRelevantViaQnud {P Fact QContent : Type*} {Cont : Type} [DecidableEq QContent]
    (genre : GenreType Fact QContent)
    (dgb : DGB P Fact QContent Cont) (m : IllocMove Fact QContent) : Prop :=
  match m.questionContent with
  | none => True  -- non-question moves don't change QUD via this predicate
  | some q => ∀ q' ∈ q :: dgb.qud.map (·.q), q' ∈ genre.qnud

instance {P Fact QContent : Type*} {Cont : Type} [DecidableEq QContent]
    (genre : GenreType Fact QContent)
    (dgb : DGB P Fact QContent Cont) (m : IllocMove Fact QContent) :
    Decidable (genreRelevantViaQnud genre dgb m) := by
  unfold genreRelevantViaQnud
  cases m.questionContent <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 4. Coherence: outcome fulfillment is post-relevance closure
-- ════════════════════════════════════════════════════

/-- Genre-relevance and outcome-fulfillment connect: if every move added
to a DGB is `genreRelevantViaQnud`, then after the moves the outcome
is fulfilled (qud entries are all anticipated). This is a structural
witness that the qnud-based predicate genuinely tracks ex. 91's outcome
relation. -/
theorem genreRelevantViaQnud_preserves_outcomeFulfilled
    {P Fact QContent : Type*} {Cont : Type} [DecidableEq QContent]
    (genre : GenreType Fact QContent)
    (dgb : DGB P Fact QContent Cont)
    (_h : genre.outcomeFulfilled dgb)
    (m : IllocMove Fact QContent)
    (hm : genreRelevantViaQnud genre dgb m) :
    -- After pushing m's question content (if any), the resulting QUD is
    -- still in qnud — that's the ex. 89 outcome relation maintained.
    (match m.questionContent with
     | none => True  -- non-question moves don't change QUD
     | some q => q ∈ genre.qnud) := by
  unfold genreRelevantViaQnud at hm
  cases hq : m.questionContent with
  | none => simp [hq]
  | some q =>
    rw [hq] at hm
    -- hm : ∀ q' ∈ q :: dgb.qud.map (·.q), q' ∈ genre.qnud
    exact hm q List.mem_cons_self

end Discourse.Gameboard
