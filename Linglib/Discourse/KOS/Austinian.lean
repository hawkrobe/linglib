import Linglib.Discourse.KOS.InquiryCycle
import Linglib.Semantics.TypeTheoretic.Discourse

/-!
# KOS over Austinian Propositions
[ginzburg-2012] [cooper-2023]

The TTR-typed instantiation of KOS substrate. `LocProp ⊐ TTRSign` is
already structural in `KOS/Defs.lean` (via `LocProp.toTTRSign` and the
`Coe` instance) — this file is not a "bridge" but a worked
instantiation pattern: how do we exercise the KOS conversational rules
when facts are TTR Austinian propositions and questions are TTR
question-bodies?

## Contents

- §1. `TTRQuestionB` — a Bool-valued TTR question (decidable variant of
   the `Type 1` `TTRQuestion`), needed because `DGB` requires `QContent : Type`.
- §2. Austinian-fact DGB/TIS aliases (`AustinianDGB`, `AustinianTIS`).
- §3. The `austinianSupport` instance — a `BCheckableAustinian` resolves
   a `TTRQuestionB` when the situation that makes the fact true also
   satisfies the question body (Ch. 4).
- §4. A worked Austinian inquiry-cycle example over a tiny
   `Weather` situation type.
-/

namespace Discourse.KOS.Austinian

open Semantics.TypeTheoretic (BCheckableAustinian CheckableAustinian
  IsTrue IsFalse)

-- ════════════════════════════════════════════════════
-- § 1. Bool-Valued TTR Questions
-- ════════════════════════════════════════════════════

/-- A Bool-valued TTR question: stays in `Type 0` for DGB compatibility.

`TTRQuestion R` (from TypeTheoretic/Discourse.lean) has `body : R → Type`,
placing it in `Type 1`. Since `DGB` requires `QContent : Type`, we provide
a decidable variant where the question body is Bool-valued.

The correspondence: `TTRQuestionB R` is to `TTRQuestion R` as `Prop' W` is
to `W → Prop` — the decidable/computable variant of the same concept. -/
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

-- ════════════════════════════════════════════════════
-- § 2. Austinian-Fact DGB
-- ════════════════════════════════════════════════════

/-- A DGB whose facts are checkable Austinian propositions and whose
QUD entries are Bool-valued TTR questions. The `Cont` parameter governs
the LocProp content type for `pending` and `qud` (use `Unit` if Pending
is unused; use `BCheckableAustinian S` for full TTR-typed CRification).

[ginzburg-2012] Ch. 4: FACTS is a set of Austinian propositions
`[sit = s, sit-type = T]`. QUD is a poset of questions. -/
abbrev AustinianDGB (S R : Type) (Cont : Type) :=
  DGB String (BCheckableAustinian S) (TTRQuestionB R) Cont

/-- A TIS with Austinian content types. -/
abbrev AustinianTIS (S R : Type) (Cont : Type) :=
  TIS String (BCheckableAustinian S) (TTRQuestionB R) Cont

-- ════════════════════════════════════════════════════
-- § 3. Support: Austinian Facts Resolve TTR Questions
-- ════════════════════════════════════════════════════

/-- A `BCheckableAustinian S` resolves a `TTRQuestionB S` when the
Austinian proposition is true at a situation that satisfies the question body.

[ginzburg-2012] Ch. 4: "q is resolved relative to a DGB dgb iff the
FACTS in dgb contextually entail an answer to q."

For a fact `⟨s, T⟩` and question `Q`: the fact resolves Q when T(s) is true
AND Q.body(s) is true — the situation that makes the fact true also answers
the question. -/
instance austinianSupport (S : Type) :
    Question.DecidableSupport (BCheckableAustinian S) (TTRQuestionB S) where
  supports fact question := fact.isTrue = true ∧ question.body fact.sit = true
  decSupports fact question := inferInstanceAs (Decidable (_ ∧ _))

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
    Question.Support.supports
      (self := (austinianSupport Weather).toSupport)
      itIsRaining isItRaining := ⟨rfl, rfl⟩

/-- "It is sunny" — an Austinian proposition that does NOT resolve "is it raining?". -/
def itIsSunny : BCheckableAustinian Weather where
  sit := .sunny
  sitType := fun w => match w with | .sunny => true | _ => false

/-- A true fact about a different situation does not resolve the raining question. -/
theorem sunny_does_not_resolve_raining :
    ¬ Question.Support.supports
      (self := (austinianSupport Weather).toSupport)
      itIsSunny isItRaining := by
  rintro ⟨_, h⟩; cases h

/-- An empty Austinian DGB. We use `Unit` for the LocProp content type
since this worked example exercises only QUD and FACTS, not the
Pending/CRification pipeline. -/
def adgb₀ : AustinianDGB Weather Weather Unit := DGB.initial

/-- After asking "Is it raining?", QUD has the question (wrapped in `InfoStruc`). -/
def atis₁ : AustinianTIS Weather Weather Unit :=
  { dgb := (adgb₀.pushQud isItRaining).recordMove (.ask isItRaining) }

theorem atis_ask_qud :
    atis₁.dgb.qud =
      [(InfoStruc.fromQuestion isItRaining : InfoStruc (TTRQuestionB Weather) Unit)] := rfl

/-- After asserting "it is raining", the fact resolves the question and QUD empties. -/
def atis₂ : AustinianTIS Weather Weather Unit :=
  @TIS.assertRule _ _ _ _ (austinianSupport Weather) atis₁ itIsRaining

theorem atis_assert_resolves : atis₂.dgb.qud = [] := by
  simp [atis₂, TIS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud,
    DGB.recordMove, Question.Support.supports,
    BCheckableAustinian.isTrue, itIsRaining, isItRaining, atis₁, adgb₀,
    DGB.initial, DGB.pushQud, InfoStruc.fromQuestion]

/-- The fact is in FACTS after assertion. -/
theorem atis_has_fact : itIsRaining ∈ atis₂.dgb.facts := by
  simp [atis₂, TIS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud, DGB.recordMove]

end AustinianExample

end Discourse.KOS.Austinian
