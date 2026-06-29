import Linglib.Discourse.Gameboard.Basic
import Linglib.Semantics.Questions.Support

/-!
# KOS: Conversational Rules on the TIS
[ginzburg-2012] Ch. 4

The TIS-level conversational rules: ask, assert, accept, qspec, check,
confirm, qcoord, factUpdateQudDowndate, greet. Each rule is a
function `TIS → … → TIS` matching [ginzburg-2012]'s precondition/
effect shape (the precondition is implicit in the input TIS state;
the effect is the output TIS state).

Plus the M-Coherence apparatus (ex. 70 p. 96) that lifts a list of
conversational rules into a relation on (DGB, move) pairs.

## Core Rules

1. **Greeting / CounterGreeting** — conversation initialization (pp. 74–76, ex. 17/20b)
2. **Ask QUD-incrementation** — question pushes onto QUD (p. 95, ex. 66)
3. **Assert QUD-incrementation** — assertion pushes About(p) onto QUD (p. 95, ex. 66)
4. **QSPEC** — subquestion accommodation (p. 95, ex. 66)
5. **QCoord** — successive question coordination (p. 99, ex. 77)
6. **Accept** — addressee grounds an assertion (p. 95, ex. 66)
7. **Check** — addressee requests confirmation (p. 95, ex. 68)
8. **Confirm** — speaker confirms in response to check (p. 95, ex. 68)
9. **Fact update/QUD-downdate** — accept triggers fact addition + QUD removal (p. 95; p. 103, ex. 85)

## Genre relevance

`genreRelevant` (eq. 90 p. 105) lives in the sibling `Gameboard/Genre.lean`.

## Grounding

The LocProp grounding/CRification protocol (Ch. 6 §6.5–6.7) lives in
the sibling `Gameboard/Grounding.lean`.
-/

namespace Discourse.Gameboard

open Question

-- ════════════════════════════════════════════════════
-- § 1. TIS Conversational Rules
-- ════════════════════════════════════════════════════

/-- **Ask rule**: a question utterance pushes onto QUD and records the move.

Ch. 4, "Ask QUD-incrementation" (p. 95, ex. 66). -/
def TIS.ask {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (q : QContent) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := (tis.dgb.pushQud q).recordMove (.ask q) }

/-- **Assert rule** (simplified): assertion adds to FACTS and downdates.

This version does not push About(p) onto QUD. For the full
Assert protocol with QUD-incrementation,
use `TIS.assertWithQUD`. -/
def TIS.assertRule {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := (tis.dgb.assertFact p).recordMove (.assert p) }

/-- **Assert QUD-incrementation**: the full Assert protocol.

Ch. 4 (p. 95, ex. 66): when A asserts p:
1. p is added to FACTS
2. About(p) — a polar question "whether p" — is pushed onto QUD
3. QUD is downdated (resolved questions removed)

The `aboutP` parameter converts the asserted fact to its corresponding
question, since this conversion is domain-specific. -/
def TIS.assertWithQUD {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (tis : TIS P Fact QContent Cont) (p : Fact) (aboutP : QContent) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := ((tis.dgb.addFact p).pushQud aboutP).downdateQud
            |>.recordMove (.assert p) }

/-- **Accept rule**: addressee grounds an assertion — adds fact to own FACTS.

Ch. 4, "Accept" (p. 95, ex. 66 step 4a).

**Known simplification**: the book's Accept rule (ex. 42) swaps spkr/addr
in the effects (the acceptor becomes the new speaker). We don't model
this because our worked examples don't track individual participants. -/
def TIS.accept {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    TIS P Fact QContent Cont :=
  { tis with dgb := (tis.dgb.addFact p).recordMove (.accept p) }

/-- **Check rule**: addressee requests confirmation of an assertion.

Ch. 4 (p. 95, ex. 68): a Check move pushes
a polar question about the asserted content onto QUD. -/
def TIS.check {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (p : Fact) (aboutP : QContent) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := (tis.dgb.pushQud aboutP).recordMove (.check p) }

/-- **Confirm rule**: speaker confirms in response to a check.

Ch. 4 (p. 95, ex. 68 step 2).

**Known simplification**: the book's Confirm rule (ex. 43) swaps spkr/addr,
as with Accept. See `TIS.accept` for details. -/
def TIS.confirm {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := (tis.dgb.assertFact p).recordMove (.confirm p) }

/-- **QCoord rule**: successive question coordination.

Ch. 4, ex. 77 (p. 99): allows a speaker to follow
up an initial question with a non-influencing question, where the initial
question remains QUD-maximal.

Effect: push q onto QUD without displacing the current maximal question. -/
def TIS.qcoord {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (q : QContent) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := { tis.dgb with
      qud := tis.dgb.qud ++ [.fromQuestion q]
      moves := tis.dgb.moves ++ [.ask q] } }

/-- **Fact update/QUD-downdate**: combined rule.

Ch. 4, ex. 85 (p. 103): when Accept occurs,
FACTS is updated and resolved questions are downdated from QUD. -/
def TIS.factUpdateQudDowndate {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent]
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    TIS P Fact QContent Cont :=
  { tis with dgb := (tis.dgb.addFact p).downdateQud }

/-- **Greeting**: conversation initialization.

Ch. 4 (p. 75, ex. 17): precondition is MOVES = ⟨⟩. -/
def TIS.greet {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) :
    TIS P Fact QContent Cont :=
  { tis with dgb := tis.dgb.recordMove .greet }

-- ════════════════════════════════════════════════════
-- § 2. TIS Theorems
-- ════════════════════════════════════════════════════

/-- Ask pushes exactly one question onto QUD (wrapped in InfoStruc). -/
theorem ask_pushes_qud {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (q : QContent) :
    (tis.ask q).dgb.qud = (.fromQuestion q : InfoStruc QContent Cont) :: tis.dgb.qud := rfl

/-- Ask does not modify FACTS. -/
theorem ask_preserves_facts {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (q : QContent) :
    (tis.ask q).dgb.facts = tis.dgb.facts := rfl

/-- Ask records the move. -/
theorem ask_records_move {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (q : QContent) :
    (tis.ask q).dgb.moves = tis.dgb.moves ++ [.ask q] := rfl

/-- Assert adds the fact to FACTS. -/
theorem assert_adds_fact {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    p ∈ (tis.assertRule p).dgb.facts := by
  simp [TIS.assertRule, DGB.assertFact, DGB.downdateQud, DGB.addFact, DGB.recordMove]

/-- assertWithQUD adds the fact to FACTS. -/
theorem assertWithQUD_adds_fact {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent]
    (tis : TIS P Fact QContent Cont) (p : Fact) (aboutP : QContent) :
    p ∈ (tis.assertWithQUD p aboutP).dgb.facts := by
  simp [TIS.assertWithQUD, DGB.downdateQud, DGB.pushQud, DGB.addFact, DGB.recordMove]

/-- Accept adds a fact without changing QUD. -/
theorem accept_preserves_qud {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    (tis.accept p).dgb.qud = tis.dgb.qud := rfl

/-- Accept adds the fact to FACTS. -/
theorem accept_adds_fact {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (p : Fact) :
    (tis.accept p).dgb.facts = p :: tis.dgb.facts := rfl

/-- Check pushes a question onto QUD. -/
theorem check_pushes_qud {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (p : Fact) (aboutP : QContent) :
    (tis.check p aboutP).dgb.qud =
      (.fromQuestion aboutP : InfoStruc QContent Cont) :: tis.dgb.qud := rfl

/-- Greeting requires empty moves (precondition check). -/
theorem greet_precond_empty_moves {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (h : tis.dgb.moves = []) :
    (tis.greet).dgb.moves = [.greet] := by
  simp [TIS.greet, DGB.recordMove, h]

-- ════════════════════════════════════════════════════
-- § 3. M-Coherence
-- ════════════════════════════════════════════════════

/-! ## Move Coherence

[ginzburg-2012] ex. 70 (p. 96) defines M(ove)-Coherence: a move m₁
is coherent with respect to a DGB dgb₀ iff there exists a conversational
rule c₁ mapping dgb₀ to dgb₁ such that dgb₁.LatestMove = m₁.

Pairwise and sequential M-Coherence extend this to move pairs and sequences. -/

/-- A conversational rule: a function from DGB to DGB.

Ch. 4 summary (p. 112): "a mapping that indicates
how one DGB can be modified by a conversationally related action." -/
abbrev ConvRule (P Fact QContent : Type*) (Cont : Type) :=
  DGB P Fact QContent Cont → DGB P Fact QContent Cont

/-- A move is M-Coherent with respect to a DGB if some conversational rule
produces a DGB whose latest move is that move.

ex. 70a (p. 96). -/
def mCoherent {P Fact QContent : Type*} {Cont : Type}
    (rules : List (ConvRule P Fact QContent Cont))
    (dgb₀ : DGB P Fact QContent Cont) (m : IllocMove Fact QContent) : Prop :=
  ∃ rule, rule ∈ rules ∧ (rule dgb₀).latestMove = some m

end Discourse.Gameboard
