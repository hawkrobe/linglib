import Linglib.Theories.Pragmatics.Dialogue.KOS.Rules
import Linglib.Theories.Semantics.TypeTheoretic.Discourse

/-!
# KOS ↔ TTR Bridge
@cite{ginzburg-2012} @cite{cooper-2023}

Connects the KOS dialogue framework (DGB, TIS, conversational rules) to
TTR's type-theoretic content representations (CheckableAustinian propositions,
TTRQuestions). This closes the loop between:

- `Theories/Pragmatics/Dialogue/KOS/` — dialogue structure
- `Theories/Semantics/TypeTheoretic/` — content types

## Key Instantiations

1. **DGB with Austinian facts**: `DGB String (BCheckableAustinian S) (TTRQuestion R)`
2. **Answerhood**: a `BCheckableAustinian S` resolves a `TTRQuestion R` when the
   situation witnesses the question body
3. **TIS ↔ InfoState genealogy**: `TIS` (Ginzburg 2012) is a refinement of
   `InfoState` (Cooper 2023) — the public/private split is a record extension

-/

namespace Pragmatics.Dialogue.KOS.TTRBridge

open Semantics.TypeTheoretic (BCheckableAustinian TTRQuestion TTRAnswer CheckableAustinian
  InfoState IsTrue IsFalse SubtypeOf)

-- ════════════════════════════════════════════════════
-- § 1. Bool-Valued TTR Questions
-- ════════════════════════════════════════════════════

/-- A Bool-valued TTR question: stays in `Type 0` for DGB compatibility.

`TTRQuestion R` (from TypeTheoretic/Discourse.lean) has `body : R → Type`,
placing it in `Type 1`. Since `DGB` requires `QContent : Type`, we provide
a decidable variant where the question body is Bool-valued.

The correspondence: `TTRQuestionB R` is to `TTRQuestion R` as `Prop' W` is
to `Prop' W` — the decidable/computable variant of the same concept. -/
structure TTRQuestionB (R : Type) where
  /-- The decidable question body -/
  body : R → Bool
  /-- Name for display -/
  name : String := ""

/-- A polar Bool-question: is P true? -/
def TTRQuestionB.polar (p : Bool) (name : String := "") : TTRQuestionB Unit where
  body := fun _ => p
  name := name

/-- A wh-question: which x satisfies P? -/
def TTRQuestionB.wh {R : Type} (body : R → Bool) (name : String := "") : TTRQuestionB R where
  body := body
  name := name

/-- A Bool-question is resolved when some element satisfies the body. -/
def TTRQuestionB.isResolved {R : Type} (q : TTRQuestionB R) (domain : List R) : Bool :=
  domain.any q.body

-- ════════════════════════════════════════════════════
-- § 2. Austinian-Fact DGB
-- ════════════════════════════════════════════════════

/-- A DGB whose facts are checkable Austinian propositions and whose
QUD entries are Bool-valued TTR questions.

@cite{ginzburg-2012} Ch. 4: FACTS is a set of Austinian propositions
`[sit = s, sit-type = T]`. QUD is a poset of questions. -/
abbrev AustinianDGB (S R : Type) := DGB String (BCheckableAustinian S) (TTRQuestionB R)

/-- A TIS with Austinian content types. -/
abbrev AustinianTIS (S R : Type) := TIS String (BCheckableAustinian S) (TTRQuestionB R)

-- ════════════════════════════════════════════════════
-- § 3. Support: Austinian Facts Resolve TTR Questions
-- ════════════════════════════════════════════════════

/-- A `BCheckableAustinian S` resolves a `TTRQuestionB S` when the
Austinian proposition is true at a situation that satisfies the question body.

@cite{ginzburg-2012} Ch. 4: "q is resolved relative to a DGB dgb iff the
FACTS in dgb contextually entail an answer to q."

For a fact `⟨s, T⟩` and question `Q`: the fact resolves Q when T(s) is true
AND Q.body(s) is true — the situation that makes the fact true also answers
the question. -/
instance austinianSupport (S : Type) :
    Core.Question.DecidableSupport (BCheckableAustinian S) (TTRQuestionB S) where
  supports fact question := fact.isTrue = true ∧ question.body fact.sit = true
  decSupports fact question := inferInstanceAs (Decidable (_ ∧ _))

-- ════════════════════════════════════════════════════
-- § 3. TIS ↔ InfoState Genealogy
-- ════════════════════════════════════════════════════

/-! ## The TIS → InfoState Projection

@cite{cooper-2023}'s `InfoState` (§2.6) is a simplified version of
@cite{ginzburg-2012}'s `TIS`. The correspondence:

| TIS (Ginzburg 2012)        | InfoState (Cooper 2023)      |
|----------------------------|------------------------------|
| `private_.agenda`          | `agenda`                     |
| `dgb.moves.getLast?`       | `latestUtterance`            |
| `dgb.facts`                | `commitments`                |
| `dgb.qud`                  | *(not represented)*          |
| `dgb.pending`              | *(not represented)*          |
| `private_.genre`           | *(not represented)*          |

TIS is a record extension of InfoState: it adds QUD, Pending, genre,
and separates public from private. -/

/-- Project a TIS to a Cooper-style InfoState.

The projection loses QUD, Pending, and genre information — these are
the components that @cite{ginzburg-2012} adds beyond @cite{cooper-2023}. -/
def tisToInfoState {P Fact QContent SignT : Type}
    (tis : TIS P Fact QContent)
    (moveToSign : IllocMove Fact QContent → SignT) :
    InfoState SignT (List Fact) where
  agenda := tis.private_.agenda.map moveToSign
  latestUtterance := tis.dgb.latestMove.map moveToSign
  commitments := tis.dgb.facts

/-- The projection preserves commitments (= FACTS). -/
theorem tisToInfoState_commitments {P Fact QContent SignT : Type}
    (tis : TIS P Fact QContent) (f : IllocMove Fact QContent → SignT) :
    (tisToInfoState tis f).commitments = tis.dgb.facts := rfl

-- ════════════════════════════════════════════════════
-- § 4. Worked Example: Austinian Inquiry
-- ════════════════════════════════════════════════════

section AustinianExample

/-- A simple situation type for the example. -/
inductive Weather where
  | sunny | rainy | cloudy
  deriving Repr, DecidableEq

/-- "It is raining" as an Austinian proposition: situation = rainy, type = isRainy. -/
def itIsRaining : BCheckableAustinian Weather where
  sit := .rainy
  sitType := fun w => match w with | .rainy => true | _ => false

/-- The Austinian proposition "it is raining" is true (rainy satisfies isRainy). -/
theorem itIsRaining_true : itIsRaining.isTrue = true := rfl

/-- "Is it raining?" as a Bool-valued TTR question. -/
def isItRaining : TTRQuestionB Weather where
  body := fun w => match w with | .rainy => true | _ => false
  name := "raining?"

/-- The fact "it is raining" resolves the question "is it raining?":
the situation (rainy) makes both the fact true and the question body true. -/
theorem raining_resolves :
    Core.Question.Support.supports
      (self := (austinianSupport Weather).toSupport)
      itIsRaining isItRaining := ⟨rfl, rfl⟩

/-- "It is sunny" — an Austinian proposition that does NOT resolve "is it raining?". -/
def itIsSunny : BCheckableAustinian Weather where
  sit := .sunny
  sitType := fun w => match w with | .sunny => true | _ => false

/-- A true fact about a different situation does not resolve the raining question. -/
theorem sunny_does_not_resolve_raining :
    ¬ Core.Question.Support.supports
      (self := (austinianSupport Weather).toSupport)
      itIsSunny isItRaining := by
  rintro ⟨_, h⟩; cases h

/-- An empty Austinian DGB. -/
private def adgb₀ : AustinianDGB Weather Weather := DGB.initial

/-- After asking "Is it raining?", QUD has the question. -/
private def atis₁ : AustinianTIS Weather Weather :=
  { dgb := (adgb₀.pushQud isItRaining).recordMove (.ask isItRaining) }

theorem atis_ask_qud : atis₁.dgb.qud = [isItRaining] := rfl

/-- After asserting "it is raining", the fact resolves the question and QUD empties. -/
private def atis₂ : AustinianTIS Weather Weather :=
  @TIS.assertRule _ _ _ (austinianSupport Weather) atis₁ itIsRaining

theorem atis_assert_resolves : atis₂.dgb.qud = [] := by
  simp [atis₂, TIS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud,
    DGB.recordMove, Core.Question.Support.supports, austinianSupport,
    BCheckableAustinian.isTrue, itIsRaining, isItRaining, atis₁, adgb₀,
    DGB.initial, DGB.pushQud]

/-- The fact is in FACTS after assertion. -/
theorem atis_has_fact : itIsRaining ∈ atis₂.dgb.facts := by
  simp [atis₂, TIS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud, DGB.recordMove]

end AustinianExample

end Pragmatics.Dialogue.KOS.TTRBridge
