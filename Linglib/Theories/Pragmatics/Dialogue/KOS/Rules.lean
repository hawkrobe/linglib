import Linglib.Theories.Pragmatics.Dialogue.KOS.Basic
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Core.QUD.Basic
import Linglib.Core.QUD.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy

/-!
# KOS Conversational Rules
@cite{ginzburg-2012} Ch. 4

Conversational rules govern how dialogue gameboards evolve during
conversation. @cite{ginzburg-2012} Ch. 4 defines these as precondition/effect
pairs (record types with `pre` and `effects` fields).

## Core Rules (@cite{ginzburg-2012} Ch. 4, pp. 72–112)

1. **Greeting / CounterGreeting** — conversation initialization (pp. 74–76, ex. 17/20b)
2. **Initiating Move** — refined Free Speech with genre relevance (p. 108, ex. 94)
3. **Ask QUD-incrementation** — question pushes onto QUD (p. 95, ex. 66)
4. **Assert QUD-incrementation** — assertion pushes About(p) onto QUD (p. 95, ex. 66)
5. **QSPEC** — subquestion accommodation (p. 95, ex. 66)
6. **QCoord** — successive question coordination (p. 99, ex. 77)
7. **Accept** — addressee grounds an assertion (p. 95, ex. 66)
8. **Check** — addressee requests confirmation (p. 95, ex. 68)
9. **Confirm** — speaker confirms in response to check (p. 95, ex. 68)
10. **Fact update/QUD-downdate** — accept triggers fact addition + QUD removal (p. 95; p. 103, ex. 85)

## Answerhood

The `Answerhood` typeclass abstracts the resolves-relation between facts
and questions — connecting to partition-based `QUD W` from `Core/Discourse/QUD.lean`
and to inquisitive `Issue W`.

## Genre (@cite{ginzburg-2012} §4.6)

Genres are TTR record types classifying conversations by their characteristic
structure. Activity relevance (`GenreRelevant`, p. 105, ex. 90) constrains
which initiating moves are felicitous.
-/

namespace Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. Answerhood
-- ════════════════════════════════════════════════════

/-- Whether a fact resolves a question.

This abstracts the answerhood relation between accumulated facts
and QUD entries. Concrete instances connect to:
- Partition-based answerhood (`QUD M`): a fact determines a unique cell
- String-based answerhood: pattern matching on content strings
- Propositional answerhood (`Prop' W`): a fact entails a question's answer

Ch. 4: "q is resolved relative to a DGB dgb iff
the FACTS in dgb contextually entail an answer to q." -/
class Answerhood (Fact QContent : Type) where
  resolves : Fact → QContent → Bool

/-- Whether all questions in a QUD stack are resolved by the current facts. -/
def allResolved {Fact QContent : Type} [Answerhood Fact QContent]
    (facts : List Fact) (qud : List QContent) : Bool :=
  qud.all fun q => facts.any fun f => Answerhood.resolves f q

-- ════════════════════════════════════════════════════
-- § 2. DGB Update Operations
-- ════════════════════════════════════════════════════

/-- Push a question onto the QUD stack.

Ch. 4: when a question is asked, it becomes
the maximal element of QUD. -/
def DGB.pushQud {P Fact QContent : Type}
    (dgb : DGB P Fact QContent) (q : QContent) : DGB P Fact QContent :=
  { dgb with qud := q :: dgb.qud }

/-- Remove resolved questions from QUD.

Ch. 4: QUD-downdate removes a question q
from QUD when FACTS contextually entail an answer to q. -/
def DGB.downdateQud {P Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB P Fact QContent) : DGB P Fact QContent :=
  { dgb with
    qud := dgb.qud.filter fun q => !dgb.facts.any fun f => Answerhood.resolves f q }

/-- Add a fact to the DGB's FACTS. -/
def DGB.addFact {P Fact QContent : Type}
    (dgb : DGB P Fact QContent) (p : Fact) : DGB P Fact QContent :=
  { dgb with facts := p :: dgb.facts }

/-- Record a move in the DGB's MOVES list. -/
def DGB.recordMove {P Fact QContent : Type}
    (dgb : DGB P Fact QContent) (m : IllocMove Fact QContent) :
    DGB P Fact QContent :=
  { dgb with moves := dgb.moves ++ [m] }

/-- Assert: add fact to FACTS, record the move, and downdate QUD.

Ch. 4 (p. 95, ex. 66): assertion adds content to
FACTS, pushes About(p,?) onto QUD, and any resolved question is removed. -/
def DGB.assertFact {P Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB P Fact QContent) (p : Fact) : DGB P Fact QContent :=
  (dgb.addFact p).downdateQud

-- ════════════════════════════════════════════════════
-- § 3. Conversational Rules on TIS
-- ════════════════════════════════════════════════════

/-- **Ask rule**: a question utterance pushes onto QUD and records the move.

Ch. 4, "Ask QUD-incrementation" (p. 95, ex. 66). -/
def TIS.ask {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) :
    TIS P Fact QContent :=
  { tis with
    dgb := (tis.dgb.pushQud q).recordMove (.ask q) }

/-- **Assert rule** (simplified): assertion adds to FACTS and downdates.

This version does not push About(p) onto QUD. For the full
Assert protocol with QUD-incrementation,
use `TIS.assertWithQUD`. -/
def TIS.assertRule {P Fact QContent : Type} [Answerhood Fact QContent]
    (tis : TIS P Fact QContent) (p : Fact) :
    TIS P Fact QContent :=
  { tis with
    dgb := (tis.dgb.assertFact p).recordMove (.assert p) }

/-- **Assert QUD-incrementation**: the full Assert protocol.

Ch. 4 (p. 95, ex. 66): when A asserts p:
1. p is added to FACTS
2. About(p) — a polar question "whether p" — is pushed onto QUD
3. QUD is downdated (resolved questions removed)

The `aboutP` parameter converts the asserted fact to its corresponding
question, since this conversion is domain-specific. -/
def TIS.assertWithQUD {P Fact QContent : Type} [Answerhood Fact QContent]
    (tis : TIS P Fact QContent) (p : Fact) (aboutP : QContent) :
    TIS P Fact QContent :=
  { tis with
    dgb := ((tis.dgb.addFact p).pushQud aboutP).downdateQud
            |>.recordMove (.assert p) }

/-- **Accept rule**: addressee grounds an assertion — adds fact to own FACTS.

Ch. 4, "Accept" (p. 95, ex. 66 step 4a).

**Known simplification**: the book's Accept rule (ex. 42) swaps spkr/addr
in the effects (the acceptor becomes the new speaker). We don't model
this because our worked examples don't track individual participants. -/
def TIS.accept {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (p : Fact) : TIS P Fact QContent :=
  { tis with dgb := (tis.dgb.addFact p).recordMove (.accept p) }

/-- **QSPEC rule**: a subquestion refines a QUD entry.

Precondition: q₂ influences some q₁ on QUD (q₂ is a subquestion).
Effect: push q₂ onto QUD (it becomes the new MaxQud).

Ch. 4, "QSPEC" (p. 95, ex. 66 step 2). -/
def TIS.qspec {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) : TIS P Fact QContent :=
  { tis with
    dgb := (tis.dgb.pushQud q).recordMove (.ask q) }

/-- **Check rule**: addressee requests confirmation of an assertion.

Ch. 4 (p. 95, ex. 68): a Check move pushes
a polar question about the asserted content onto QUD. -/
def TIS.check {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (p : Fact) (aboutP : QContent) :
    TIS P Fact QContent :=
  { tis with
    dgb := (tis.dgb.pushQud aboutP).recordMove (.check p) }

/-- **Confirm rule**: speaker confirms in response to a check.

Ch. 4 (p. 95, ex. 68 step 2).

**Known simplification**: the book's Confirm rule (ex. 43) swaps spkr/addr,
as with Accept. See `TIS.accept` for details. -/
def TIS.confirm {P Fact QContent : Type} [Answerhood Fact QContent]
    (tis : TIS P Fact QContent) (p : Fact) : TIS P Fact QContent :=
  { tis with
    dgb := (tis.dgb.assertFact p).recordMove (.confirm p) }

/-- **QCoord rule**: successive question coordination.

Ch. 4, ex. 77 (p. 99): allows a speaker to follow
up an initial question with a non-influencing question, where the initial
question remains QUD-maximal.

Effect: push q onto QUD without displacing the current maximal question. -/
def TIS.qcoord {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) : TIS P Fact QContent :=
  { tis with
    dgb := { tis.dgb with
      qud := tis.dgb.qud ++ [q]
      moves := tis.dgb.moves ++ [.ask q] } }

/-- **Fact update/QUD-downdate**: combined rule.

Ch. 4, ex. 85 (p. 103): when Accept occurs,
FACTS is updated and resolved questions are downdated from QUD. -/
def TIS.factUpdateQudDowndate {P Fact QContent : Type} [Answerhood Fact QContent]
    (tis : TIS P Fact QContent) (p : Fact) : TIS P Fact QContent :=
  { tis with dgb := (tis.dgb.addFact p).downdateQud }

/-- **Greeting**: conversation initialization.

Ch. 4 (p. 75, ex. 17): precondition is MOVES = ⟨⟩. -/
def TIS.greet {P Fact QContent : Type}
    (tis : TIS P Fact QContent) : TIS P Fact QContent :=
  { tis with dgb := tis.dgb.recordMove .greet }

-- ════════════════════════════════════════════════════
-- § 4. Structural Theorems
-- ════════════════════════════════════════════════════

/-- Ask pushes exactly one question onto QUD. -/
theorem ask_pushes_qud {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) :
    (tis.ask q).dgb.qud = q :: tis.dgb.qud := rfl

/-- Ask does not modify FACTS. -/
theorem ask_preserves_facts {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) :
    (tis.ask q).dgb.facts = tis.dgb.facts := rfl

/-- Ask records the move. -/
theorem ask_records_move {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) :
    (tis.ask q).dgb.moves = tis.dgb.moves ++ [.ask q] := rfl

/-- Assert adds the fact to FACTS. -/
theorem assert_adds_fact {P Fact QContent : Type} [Answerhood Fact QContent]
    (tis : TIS P Fact QContent) (p : Fact) :
    p ∈ (tis.assertRule p).dgb.facts := by
  simp [TIS.assertRule, DGB.assertFact, DGB.downdateQud, DGB.addFact, DGB.recordMove]

/-- assertWithQUD adds the fact to FACTS. -/
theorem assertWithQUD_adds_fact {P Fact QContent : Type} [Answerhood Fact QContent]
    (tis : TIS P Fact QContent) (p : Fact) (aboutP : QContent) :
    p ∈ (tis.assertWithQUD p aboutP).dgb.facts := by
  simp [TIS.assertWithQUD, DGB.downdateQud, DGB.pushQud, DGB.addFact, DGB.recordMove]

/-- Accept adds a fact without changing QUD. -/
theorem accept_preserves_qud {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (p : Fact) :
    (tis.accept p).dgb.qud = tis.dgb.qud := rfl

/-- Accept adds the fact to FACTS. -/
theorem accept_adds_fact {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (p : Fact) :
    (tis.accept p).dgb.facts = p :: tis.dgb.facts := rfl

/-- QSPEC pushes a subquestion. -/
theorem qspec_pushes {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (q : QContent) :
    (tis.qspec q).dgb.qud = q :: tis.dgb.qud := rfl

/-- Check pushes a question onto QUD. -/
theorem check_pushes_qud {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (p : Fact) (aboutP : QContent) :
    (tis.check p aboutP).dgb.qud = aboutP :: tis.dgb.qud := rfl

/-- Greeting requires empty moves (precondition check). -/
theorem greet_precond_empty_moves {P Fact QContent : Type}
    (tis : TIS P Fact QContent) (h : tis.dgb.moves = []) :
    (tis.greet).dgb.moves = [.greet] := by
  simp [TIS.greet, DGB.recordMove, h]

-- ════════════════════════════════════════════════════
-- § 5. QUD Downdate Properties
-- ════════════════════════════════════════════════════

/-- Downdate never increases QUD size. -/
theorem downdateQud_length_le {P Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB P Fact QContent) :
    dgb.downdateQud.qud.length ≤ dgb.qud.length := by
  simp only [DGB.downdateQud]
  exact List.length_filter_le _ _

/-- If a fact resolves the only question on QUD, downdate removes it. -/
theorem downdateQud_removes_resolved {P Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB P Fact QContent) (q : QContent) (f : Fact)
    (hq : dgb.qud = [q]) (hf : f ∈ dgb.facts) (hr : Answerhood.resolves f q = true) :
    dgb.downdateQud.qud = [] := by
  unfold DGB.downdateQud
  rw [hq]
  simp only [List.filter_cons, List.filter_nil]
  have : dgb.facts.any (fun f => Answerhood.resolves f q) = true :=
    List.any_eq_true.mpr ⟨f, hf, hr⟩
  simp [this]

-- ════════════════════════════════════════════════════
-- § 6. M-Coherence (ex. 70, p. 96)
-- ════════════════════════════════════════════════════

/-! ## Move Coherence

ex. 70 (p. 96) defines M(ove)-Coherence: a move m₁
is coherent with respect to a DGB dgb₀ iff there exists a conversational
rule c₁ mapping dgb₀ to dgb₁ such that dgb₁.LatestMove = m₁.

Pairwise and sequential M-Coherence extend this to move pairs and sequences. -/

/-- A conversational rule: a function from DGB to DGB.

Ch. 4 summary (p. 112): "a mapping that indicates
how one DGB can be modified by a conversationally related action." -/
abbrev ConvRule (P Fact QContent : Type) :=
  DGB P Fact QContent → DGB P Fact QContent

/-- A move is M-Coherent with respect to a DGB if some conversational rule
produces a DGB whose latest move is that move.

ex. 70a (p. 96). -/
def mCoherent {P Fact QContent : Type}
    (rules : List (ConvRule P Fact QContent))
    (dgb₀ : DGB P Fact QContent) (m : IllocMove Fact QContent) : Prop :=
  ∃ rule, rule ∈ rules ∧ (rule dgb₀).latestMove = some m

-- ════════════════════════════════════════════════════
-- § 7. Activity Relevance (ex. 90, p. 105)
-- ════════════════════════════════════════════════════

/-- A move is genre-relevant if the outcome of adding it to the DGB
can be anticipated to conclude as a conversation of the genre type.

ex. 90 (p. 105): "m0 is relevant to G0 in dgb0 for A
iff A believes that outcome(dgb0 ⊕ₘₒᵥₑₛ m0, G0) will be fulfilled." -/
def genreRelevant {P Fact QContent : Type}
    (genre : GenreType QContent)
    (dgb : DGB P Fact QContent) (m : IllocMove Fact QContent) : Bool :=
  match genre.qudConstraint with
  | none => true  -- unrestricted genre: all moves are relevant
  | some constraint =>
    match m.questionContent with
    | some q => constraint (q :: dgb.qud)
    | none => true  -- non-question moves don't violate QUD constraints

-- ════════════════════════════════════════════════════
-- § 8. Worked Example: Inquiry Cycle
-- ════════════════════════════════════════════════════

section InquiryExample

/-- String-based answerhood: a fact resolves a question if they match. -/
instance : Answerhood String String where
  resolves fact question := fact == question

/-- Start: empty TIS. -/
private def tis₀ : TIS String String String := TIS.initial

/-- Step 1: A asks "Is Bo here?" -/
private def tis₁ : TIS String String String := tis₀.ask "Bo is here"

/-- Step 2: B asserts "Bo is here." -/
private def tis₂ : TIS String String String := tis₁.assertRule "Bo is here"

/-- Step 3: A accepts B's assertion. -/
private def tis₃ : TIS String String String := tis₂.accept "Bo is here"

-- Verification

/-- After Ask, QUD contains the question. -/
theorem inquiry_step1_qud : tis₁.dgb.qud = ["Bo is here"] := rfl

/-- After Ask, FACTS are unchanged. -/
theorem inquiry_step1_facts : tis₁.dgb.facts = [] := rfl

/-- After Ask, the move is recorded. -/
theorem inquiry_step1_moves : tis₁.dgb.moves = [.ask "Bo is here"] := rfl

/-- After Assert, the fact is in FACTS. -/
theorem inquiry_step2_has_fact : "Bo is here" ∈ tis₂.dgb.facts := by
  simp [tis₂, TIS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud, DGB.recordMove]

/-- After Assert, QUD is empty (the question was resolved). -/
theorem inquiry_step2_qud_empty : tis₂.dgb.qud = [] := by native_decide

/-- After Accept, the fact appears twice (once from assert, once from accept). -/
theorem inquiry_step3_facts : tis₃.dgb.facts = ["Bo is here", "Bo is here"] := by
  native_decide

/-- The full inquiry cycle: QUD starts empty, gets a question, then empties. -/
theorem inquiry_cycle_qud :
    tis₀.dgb.qud = [] ∧ tis₁.dgb.qud = ["Bo is here"] ∧ tis₂.dgb.qud = [] := by
  native_decide

/-- Moves accumulate through the inquiry cycle. -/
theorem inquiry_cycle_moves :
    tis₃.dgb.moves = [.ask "Bo is here", .assert "Bo is here", .accept "Bo is here"] := by
  native_decide

end InquiryExample

-- ════════════════════════════════════════════════════
-- § 9. Check/Confirm Example (ex. 68, p. 95)
-- ════════════════════════════════════════════════════

section CheckExample

instance : Answerhood String String where
  resolves fact question := fact == question

/-- A(1): Bo is in Essen. (Assert) -/
private def checkTIS₀ : TIS String String String := TIS.initial
private def checkTIS₁ : TIS String String String :=
  checkTIS₀.assertRule "Bo is in Essen"

/-- B(1b): Is he? (Check) -/
private def checkTIS₂ : TIS String String String :=
  checkTIS₁.check "Bo is in Essen" "Bo is in Essen"

/-- A(2): Confirm. -/
private def checkTIS₃ : TIS String String String :=
  checkTIS₂.confirm "Bo is in Essen"

/-- After Check, QUD has the polar question. -/
theorem check_pushes : checkTIS₂.dgb.qud = ["Bo is in Essen"] := by native_decide

/-- After Confirm, the fact is in FACTS and QUD is resolved. -/
theorem confirm_resolves : checkTIS₃.dgb.qud = [] := by native_decide

end CheckExample

-- ════════════════════════════════════════════════════
-- § 10. Bridge: Answerhood ↔ QUD Partitions
-- ════════════════════════════════════════════════════

/-! ## Partition-Based Answerhood

Ch. 4 defines QUD-downdate in terms of FACTS
resolving questions. The `Answerhood` typeclass above abstracts this.
Here we connect it to the partition-based `QUD W` from
`Core/Discourse/QUD.lean` (@cite{groenendijk-stokhof-1984}):

A `Prop' W` fact resolves a `QUD W` question when the fact determines
a unique cell — all worlds where the fact holds are in the same
partition cell. -/

/-- A `Prop' W` resolves a `QUD W` if all fact-worlds are in the same
partition cell. -/
def propResolvesQUD {W : Type} [BEq W] (worlds : List W)
    (fact : Set W) [DecidablePred fact] (q : QUD W) : Bool :=
  let factWorlds := worlds.filter (fun w => decide (fact w))
  factWorlds.all fun w₁ =>
    factWorlds.all fun w₂ =>
      q.sameAnswer w₁ w₂

/-- Answerhood instance: `Prop' W` resolves `QUD W` over a fixed world list.
Decidability of each fact is obtained classically. -/
@[reducible] noncomputable def answerhoodFromPartition {W : Type} [BEq W] (worlds : List W) :
    Answerhood (Set W) (QUD W) where
  resolves fact q :=
    have : DecidablePred fact := Classical.decPred fact
    propResolvesQUD worlds fact q

-- ════════════════════════════════════════════════════
-- § 11. Partition Answerhood Example
-- ════════════════════════════════════════════════════

section PartitionExample

/-- Three-world scenario: is it raining? -/
inductive RainWorld where
  | sunny | rainy | cloudy
  deriving Repr, DecidableEq

/-- "Is it raining?" — partition into rainy vs non-rainy. -/
def isRainingQ : QUD RainWorld :=
  QUD.ofProject (fun w => match w with | .rainy => true | _ => false) "raining?"

/-- A tagged proposition for the rain example: pairs a `Prop' RainWorld`
    with a tag enabling decidable equality and Bool-valued resolution. -/
inductive RainProp where
  | raining
  | sunny
  deriving DecidableEq, Repr

def RainProp.toProp : RainProp → Set RainWorld
  | .raining => fun w => w = .rainy
  | .sunny   => fun w => w = .sunny

instance (rp : RainProp) : DecidablePred rp.toProp := fun w => by
  cases rp <;> simp only [RainProp.toProp] <;> exact inferInstance

/-- "It is raining" — true only in the rainy world. -/
def itIsRaining : Set RainWorld := fun w => w = .rainy

instance : DecidablePred itIsRaining := fun w => by
  unfold itIsRaining; exact inferInstance

/-- "It is sunny" — true only in the sunny world. -/
def itIsSunny : Set RainWorld := fun w => w = .sunny

instance : DecidablePred itIsSunny := fun w => by
  unfold itIsSunny; exact inferInstance

private def rainWorlds : List RainWorld := [.sunny, .rainy, .cloudy]

/-- "It is raining" resolves "Is it raining?" -/
theorem raining_resolves_raining :
    propResolvesQUD rainWorlds itIsRaining isRainingQ = true := by
  unfold propResolvesQUD itIsRaining
  decide

/-- "It is sunny" also resolves "Is it raining?" -/
theorem sunny_resolves_raining :
    propResolvesQUD rainWorlds itIsSunny isRainingQ = true := by
  unfold propResolvesQUD itIsSunny
  decide

/-- Full inquiry cycle with partition-based answerhood (via `RainProp` tags). -/
private def rainTIS₀ : TIS String RainProp (QUD RainWorld) := TIS.initial

instance rainAnswerhood : Answerhood RainProp (QUD RainWorld) where
  resolves rp q := propResolvesQUD rainWorlds rp.toProp q

private def rainTIS₁ : TIS String RainProp (QUD RainWorld) :=
  rainTIS₀.ask isRainingQ

/-- After asking, QUD has the partition question. -/
theorem rain_ask_qud : rainTIS₁.dgb.qud = [isRainingQ] := rfl

private def rainTIS₂ : TIS String RainProp (QUD RainWorld) :=
  rainTIS₁.assertRule .raining

/-- After asserting "It is raining", QUD is empty (resolved). -/
theorem rain_assert_resolves : rainTIS₂.dgb.qud = [] := by
  unfold rainTIS₂ rainTIS₁ rainTIS₀ TIS.assertRule TIS.ask DGB.assertFact
    DGB.addFact DGB.downdateQud DGB.recordMove DGB.pushQud
  simp only [List.filter, List.any]
  decide

end PartitionExample

-- ════════════════════════════════════════════════════
-- § 12. assertWithQUD Inquiry Cycle
-- ════════════════════════════════════════════════════

section AssertWithQUDExample

instance : Answerhood String String where
  resolves fact question := fact == question

/-- Full inquiry cycle using the Ginzburg 2012 Assert protocol.

A: "Is Bo here?"  (Ask)
B: "Bo is here."  (AssertWithQUD — pushes About("Bo is here") onto QUD)
A: accepts         (Accept + factUpdateQudDowndate) -/
private def awq₀ : TIS String String String := TIS.initial
private def awq₁ := awq₀.ask "Bo is here"
private def awq₂ := awq₁.assertWithQUD "Bo is here" "Bo is here"

/-- After assertWithQUD, the question from Ask is resolved (fact matches). -/
theorem awq_resolves_original_question : awq₂.dgb.qud = [] := by native_decide

/-- The fact is in FACTS after assertWithQUD. -/
theorem awq_has_fact : "Bo is here" ∈ awq₂.dgb.facts := by
  simp [awq₂, awq₁, awq₀, TIS.assertWithQUD, TIS.ask, DGB.addFact, DGB.pushQud,
    DGB.downdateQud, DGB.recordMove]

end AssertWithQUDExample

-- ════════════════════════════════════════════════════
-- § 13. Searle–KOS Direction-of-Fit Coherence
-- ════════════════════════════════════════════════════

/-- All assertive-class moves (assert, accept, confirm) share mind-to-world fit:
the speaker takes responsibility for truth. -/
theorem assertive_moves_mind_to_world {Fact QContent : Type} (p : Fact) :
    (IllocMove.assert (QContent := QContent) p).directionOfFit = .mindToWorld ∧
    (IllocMove.accept (QContent := QContent) p).directionOfFit = .mindToWorld ∧
    (IllocMove.confirm (QContent := QContent) p).directionOfFit = .mindToWorld :=
  ⟨rfl, rfl, rfl⟩

/-- Directive moves (ask, check) share world-to-mind fit:
the speaker wants the addressee to act. -/
theorem directive_moves_world_to_mind {Fact QContent : Type}
    (q : QContent) (p : Fact) :
    (IllocMove.ask (Fact := Fact) q).directionOfFit = .worldToMind ∧
    (IllocMove.check (QContent := QContent) p).directionOfFit = .worldToMind :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 14. Grounding Protocol (@cite{ginzburg-2012} Ch. 6, §6.5–6.7)
-- ════════════════════════════════════════════════════

/-! ## Utterance Integration: Grounding vs CRification

@cite{ginzburg-2012} Ch. 6 (§6.5–6.7): when an utterance enters Pending,
the addressee either *grounds* it (all contextual parameters resolved →
content enters FACTS) or *CRifies* it (some parameter unresolved →
a clarification request question is pushed onto QUD).

This is the LocProp-level protocol that replaces the string-based
`IS.integrateUtterance` from @cite{ginzburg-cooper-2004}. -/

/-- Whether a LocProp has all contextual parameters resolved.
A fully resolved LocProp can be grounded directly. -/
def LocProp.isFullyResolved {Cont : Type} (lp : LocProp Cont) : Bool :=
  lp.cparams.isEmpty

/-- Whether a LocProp can be grounded (= fully resolved). -/
def LocProp.canGround {Cont : Type} (lp : LocProp Cont) : Bool :=
  lp.isFullyResolved

/-- The result of integrating a LocProp into a DGB.
Either grounded (content → FACTS) or CRified (CR question → QUD). -/
inductive IntegrationResult (Cont QContent : Type) where
  /-- All cparams resolved: content enters FACTS. -/
  | grounded (content : Cont)
  /-- Some cparam unresolved: CR question pushed onto QUD. -/
  | crification (crQuestion : QContent) (unresolvedParam : CParam)
  deriving Repr

/-- Is this integration result a grounding? -/
def IntegrationResult.isGrounded {Cont QContent : Type} :
    IntegrationResult Cont QContent → Bool
  | .grounded _ => true
  | .crification _ _ => false

/-- Integrate a LocProp: ground if resolved, CRify otherwise.

The `toCR` function converts an unresolved parameter to a clarification
question — this is domain-specific (e.g., "Who do you mean by 'Bo'?"). -/
def integrateLocProp {Cont QContent : Type}
    (lp : LocProp Cont) (toCR : CParam → QContent) :
    IntegrationResult Cont QContent :=
  match lp.cparams with
  | [] => .grounded lp.cont
  | p :: _ => .crification (toCR p) p

/-- A fully resolved LocProp always grounds. -/
theorem resolved_always_grounds {Cont QContent : Type}
    (lp : LocProp Cont) (toCR : CParam → QContent)
    (h : lp.isFullyResolved = true) :
    (integrateLocProp lp toCR).isGrounded = true := by
  simp only [LocProp.isFullyResolved, List.isEmpty_iff] at h
  simp only [integrateLocProp, h, IntegrationResult.isGrounded]

/-- If there are no coercion options and the LocProp has unresolved params,
integration produces a CRification — there is no silent fallback. -/
theorem no_coercion_fallback {Cont QContent : Type}
    (lp : LocProp Cont) (toCR : CParam → QContent) (p : CParam) (ps : CParamSet)
    (h : lp.cparams = p :: ps) :
    (integrateLocProp lp toCR).isGrounded = false := by
  simp only [integrateLocProp, h, IntegrationResult.isGrounded]

-- ════════════════════════════════════════════════════
-- § 15. Non-Resolve-Cond (@cite{ginzburg-2012} ex. 100, p. 111)
-- ════════════════════════════════════════════════════

/-! ## DGB Well-Formedness: Non-Resolve-Cond

@cite{ginzburg-2012} ex. 100 (p. 111): the DGB includes a well-formedness
constraint `non-resolve-cond` requiring that no question on QUD is already
resolved by FACTS. This prevents trivially answered questions from lingering
on QUD — they should be downdated. -/

/-- The non-resolve-cond: no question on QUD is resolved by FACTS.
@cite{ginzburg-2012} ex. 100 (p. 111). -/
def DGB.nonResolveCond {P Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB P Fact QContent) : Bool :=
  dgb.qud.all fun q => !(dgb.facts.any fun f => Answerhood.resolves f q)

/-- An empty DGB trivially satisfies non-resolve-cond. -/
theorem DGB.initial_nonResolveCond {P Fact QContent : Type} [Answerhood Fact QContent] :
    (DGB.initial : DGB P Fact QContent).nonResolveCond = true := rfl

/-- Filtering by p then checking all satisfy p is trivially true. -/
private theorem all_filter_self {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).all p = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold List.filter
    cases hx : p x with
    | true => simp only [List.all_cons, hx, Bool.true_and, ih]
    | false => exact ih

/-- After QUD-downdate, non-resolve-cond holds: all remaining questions
are unresolved by FACTS. -/
theorem downdateQud_restores_nonResolveCond
    {P Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB P Fact QContent) :
    dgb.downdateQud.nonResolveCond = true := by
  simp only [DGB.nonResolveCond, DGB.downdateQud]
  exact all_filter_self _ _

end Pragmatics.Dialogue.KOS
