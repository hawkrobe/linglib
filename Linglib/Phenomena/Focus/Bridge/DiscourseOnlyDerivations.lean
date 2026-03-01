import Linglib.Theories.Semantics.Lexical.Particle.DiscourseOnly
import Linglib.Phenomena.Focus.DiscourseOnly

/-!
# End-to-End Derivation Chains for Discourse *only*

Concrete instantiations of the discourse *only* theory (IKW 2025 Def. 16)
that derive the acceptability of specific cross-linguistic examples.

## Architecture

The discourse *only* theory (in `Lexical/Particle/DiscourseOnly.lean`) defines
`isDefined` and `ciContent` as computable `Bool` functions over abstract types.
This file instantiates those functions with a concrete 8-world model of the
house-buying scenario used throughout IKW §7, then proves that the theory's
predictions match the empirical data in `Phenomena/Focus/DiscourseOnly.lean`.

## The House Model

8 worlds varying on three binary properties: beautiful, expensive, renovated.
The QUD "Should we buy the house?" is answered affirmatively only when the house
is beautiful, affordable, AND renovated (w₀). This ensures:
- "beautiful" supports buying (P(buy|beautiful) > P(buy))
- "expensive" anti-supports buying (P(buy|expensive) = 0)
- "renovated" is relevant to buying (P(buy|renovated) > P(buy))

## Derivation Chains

Each derivation theorem proves:
1. `isDefined` = true (the presupposition is satisfied)
2. `ciContent` = true (the CI holds: S supports α but S' doesn't)
3. These match the datum's `felicitous = true`

For interrogative S' examples (30a, 31a, etc.), the derivation shows that
the speaker's uncertainty about the answer blocks `fullSupport` for S' on
all QUD answers, trivially satisfying the CI's condition (ii).

## References

- Ippolito, Kiss & Williams (2025). Discourse *only*. WCCFL 41.
-/

namespace Phenomena.Focus.Bridge.DiscourseOnlyDerivations

open Discourse
open Semantics.Questions.ProbabilisticAnswerhood
open Semantics.Questions.Support
open Semantics.Lexical.Particle.DiscourseOnly
open Phenomena.Focus.DiscourseOnly

-- ============================================================================
-- World Type and Propositions
-- ============================================================================

/-- 8-world model for the house-buying scenario.

Encoding: w = 4b + 2e + r where
- b ∈ {0,1}: beauty (0 = beautiful)
- e ∈ {0,1}: expense (0 = affordable)
- r ∈ {0,1}: renovation (0 = renovated)

| World | Beautiful | Expensive | Renovated | Buy? |
|-------|-----------|-----------|-----------|------|
| w₀    | ✓         |           | ✓         | ✓    |
| w₁    | ✓         |           |           |      |
| w₂    | ✓         | ✓         | ✓         |      |
| w₃    | ✓         | ✓         |           |      |
| w₄    |           |           | ✓         |      |
| w₅    |           |           |           |      |
| w₆    |           | ✓         | ✓         |      |
| w₇    |           | ✓         |           |      |
-/
abbrev W := Fin 8

/-- The house is beautiful (w₀–w₃). -/
def beautiful : W → Bool := fun w => w.val < 4

/-- The house is expensive (w₂, w₃, w₆, w₇). -/
def expensive : W → Bool := fun w => (w.val / 2) % 2 == 1

/-- The house has been renovated (w₀, w₂, w₄, w₆). -/
def renovated : W → Bool := fun w => w.val % 2 == 0

/-- Should we buy the house? Only if beautiful, affordable, and renovated (w₀). -/
def buy : W → Bool := fun w => w.val == 0

/-- Uniform prior: P(w) = 1/8 for each world. -/
def prior : Prior W := fun _ => 1 / 8

/-- All worlds for doxastic subset checks. -/
def worlds : List W := List.finRange 8

-- ============================================================================
-- QUD and Denotations
-- ============================================================================

/-- QUD: "Should we buy the house?" — binary issue. -/
def qud : Issue W := Issue.polar buy

/-- Declarative S: "The house is beautiful" — one alternative. -/
def sBeautiful : Issue W := ⟨[beautiful]⟩

/-- Declarative S': "It's (very) expensive" — one alternative. -/
def s'Expensive : Issue W := ⟨[expensive]⟩

/-- Polar Q S': "Has it been renovated?" — two alternatives. -/
def s'RenovatedQ : Issue W := Issue.polar renovated

-- ============================================================================
-- Doxastic States
-- ============================================================================

/-- Speaker who asserts "beautiful" and "expensive": believes both.
DOX_sp = {w₂, w₃} (beautiful ∧ expensive). -/
def doxBE : InfoState W := fun w => beautiful w && expensive w

/-- Speaker who asserts "beautiful" but asks about renovation: believes
beautiful, uncertain about expense and renovation.
DOX_sp = {w₀, w₁, w₂, w₃} (beautiful). -/
def doxB : InfoState W := fun w => beautiful w

-- ============================================================================
-- Contexts
-- ============================================================================

/-- Context for core examples: S = "beautiful", S' = "expensive".
No prior partial answers — fresh discourse.

Subquestions per IKW §5.1: "Answering this question requires answering
its plausible subquestions, such as *Is the house beautiful?
Is the house expensive?*" We also include renovation since it
appears in the polar Q examples. -/
def coreCtx : Context W :=
  { qud := qud
  , prior := prior
  , dox := doxBE
  , worlds := worlds
  , partialAnswers := []
  , subquestions := [Issue.polar beautiful, Issue.polar expensive,
                     Issue.polar renovated] }

/-- Context for clause-type examples: S = "beautiful", S' = interrogative.
Speaker believes S but doesn't know the answer to S'. Same subquestions
as core context — the QUD structure doesn't change with clause type. -/
def clauseTypeCtx : Context W :=
  { qud := qud
  , prior := prior
  , dox := doxB
  , worlds := worlds
  , partialAnswers := []
  , subquestions := [Issue.polar beautiful, Issue.polar expensive,
                     Issue.polar renovated] }

-- ============================================================================
-- Sentences
-- ============================================================================

/-- "The house is beautiful, only it's expensive" (core declarative-declarative). -/
def declSentence : Sentence W :=
  { sDen := sBeautiful
  , s'Den := s'Expensive }

/-- "The house is beautiful, only has it been renovated?" (polar Q as S'). -/
def polarQSentence : Sentence W :=
  { sDen := sBeautiful
  , s'Den := s'RenovatedQ }

-- ============================================================================
-- Core Derivation: Declarative S + Declarative S'
-- ============================================================================

section CoreDerivation

/-- The presupposition is satisfied: S' is relevant and S supports an answer. -/
theorem core_isDefined : declSentence.isDefined coreCtx = true := by native_decide

/-- The CI holds: ∃α (= buy) s.t. all partial answers support α (vacuous),
S supports α, and S' does not support α. -/
theorem core_ciContent : declSentence.ciContent coreCtx = true := by native_decide

/-- The at-issue content is non-trivial: there exist worlds where both
S and S' hold (e.g., w₂: beautiful ∧ expensive). -/
theorem core_atIssue_nonempty :
    declSentence.atIssueContent (2 : W) = true := by native_decide

/-- S and S' disagree w.r.t. the QUD: S supports "buy" but S' supports
"don't buy", and they don't agree on any single answer. -/
theorem core_disagree : declSentence.disagree coreCtx = true := by native_decide

/-- Per-datum connection: the theory predicts felicitous for the core examples.

Each core example (Italian 29a, Russian 29b, Hungarian 29c, Mandarin 29d,
English 2) instantiates this same semantic scenario. -/
theorem core_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    italian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem russian_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    russian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem hungarian_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    hungarian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem mandarin_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    mandarin_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem english_house_predicted :
    declSentence.isDefined coreCtx = true ∧
    declSentence.ciContent coreCtx = true ∧
    english_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

end CoreDerivation

-- ============================================================================
-- Clause-Type Derivation: Declarative S + Polar Q S'
-- ============================================================================

section PolarQDerivation

/-- The presupposition is satisfied even with interrogative S': the polar Q
"has it been renovated?" has alternatives [renovated, ¬renovated], and
knowing whether the house is renovated is relevant to buying. -/
theorem polarQ_isDefined : polarQSentence.isDefined clauseTypeCtx = true := by
  native_decide

/-- The CI holds: the speaker believes the house is beautiful, so S supports
"buy". But the speaker doesn't know the answer to "has it been renovated?",
so the doxastic condition of fullSupport fails for S' on every QUD answer.
S' trivially fails to support the buying direction. -/
theorem polarQ_ciContent : polarQSentence.ciContent clauseTypeCtx = true := by
  native_decide

/-- Per-datum: predicts felicitous for all polar Q S' examples.

Russian 30a, Hungarian 31a, and Mandarin 32a all instantiate this scenario. -/
theorem russian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx = true ∧
    polarQSentence.ciContent clauseTypeCtx = true ∧
    russian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem hungarian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx = true ∧
    polarQSentence.ciContent clauseTypeCtx = true ∧
    hungarian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem mandarin_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx = true ∧
    polarQSentence.ciContent clauseTypeCtx = true ∧
    mandarin_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

end PolarQDerivation

-- ============================================================================
-- Abstract Theorem: Any Interrogative S' Where Speaker Doesn't Know Answer
-- ============================================================================

/-- For any context where S supports some QUD answer and S' is an interrogative
whose answer the speaker doesn't know, the CI's condition (ii) is satisfied:
S' trivially fails to support any answer because fullSupport requires the
doxastic condition (DOX_sp ⊆ q), which fails when the speaker doesn't
believe any alternative of S'.

This generalizes the polar Q derivation to all interrogative S' examples
(30a-d, 31a-d, 32a-d): the specific content of the question doesn't matter
for the CI — only that the speaker doesn't know the answer. -/
theorem interrogative_s'_ci_satisfied {W' : Type*} [Fintype W']
    (sent : Sentence W') (ctx : Context W')
    -- S supports some answer
    (hSsupports : ctx.qud.alternatives.any (fun α =>
      fullSupport ctx.dox sent.sDen ctx.prior α ctx.worlds) = true)
    -- Speaker doesn't believe any alternative of S'
    (hNoBelief : ∀ q, q ∈ sent.s'Den.alternatives →
      Discourse.supports ctx.dox q ctx.worlds = false)
    -- No prior partial answers that fail to support (vacuous when empty)
    (hPartial : ctx.partialAnswers = []) :
    sent.ciContent ctx = true := by
  unfold Sentence.ciContent
  rw [List.any_eq_true] at hSsupports ⊢
  obtain ⟨α, hMem, hSupp⟩ := hSsupports
  refine ⟨α, hMem, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', hPartial, List.all_nil,
    true_and]
  constructor
  · exact hSupp
  · exact fullSupport_fails_unbelieved ctx.dox sent.s'Den ctx.prior α
      ctx.worlds hNoBelief

end Phenomena.Focus.Bridge.DiscourseOnlyDerivations
