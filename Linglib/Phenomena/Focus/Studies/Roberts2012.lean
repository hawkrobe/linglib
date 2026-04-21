import Linglib.Core.Question.Hamblin
import Linglib.Core.Question.Relevance
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
# @cite{roberts-2012} — Information Structure in Discourse

@cite{roberts-2012} "Information structure in discourse: Towards an integrated
formal theory of pragmatics" (Semantics & Pragmatics 5(6): 1–69).

## Core Contributions Formalized

1. **QUD stack** — discourse state is an ordered stack of accepted, unanswered
   questions (`QUDStack`), not a single QUD.
2. **Strategy of inquiry** — recursive question decomposition (`Strategy`):
   answering all subquestions answers the parent.
3. **Negative partial answerhood** — a proposition partially answers a question
   by ruling out an alternative, not just confirming one (`partiallyAnswers`).
4. **Q-A congruence** — the focus alternatives of an answer equal the QUD
   alternatives (grounded by the Rooth–Hamblin type identity).

## D₀ Worked Example (Roberts §1.2)

The Big Question: "What did each person eat?"

- 4 Boolean dimensions: Hannah-beans, Hannah-tofu, Roger-beans, Roger-tofu
- 16 possible worlds
- 7 questions forming a strategy tree

```
         q₁ (What did everyone eat?)
        /                            \
    q_a (What did Hannah eat?)    q_b (What did Roger eat?)
    /        \                    /        \
q_ai (H beans?) q_aii (H tofu?) q_bi (R beans?) q_bii (R tofu?)
```

## Representation

This file uses `Core.Question` (Set-based, with `Prop` + `Decidable` Roberts QUD
predicates from `Core/Question/Relevance.lean`). Non-polar issues are built via
`Question.ofList` and `⊓`; entailment for these uses the `HasAltList` infrastructure
from `Core/Question/Hamblin.lean`. Set-based partitions live in
`Core/Question/Partition.lean` (`Core.Question.IsPartition`, backed by
`Setoid.IsPartition`).
-/

namespace Roberts2012

open Core
open Core.Question
open Discourse (QUDStack Strategy moveRelevantToStrategy)

-- ════════════════════════════════════════════════════
-- § D₀ World Space
-- ════════════════════════════════════════════════════

/-- A world in the D₀ scenario: 4 independent Boolean facts. -/
structure D0World where
  hb : Bool   -- Hannah ate beans
  ht : Bool   -- Hannah ate tofu
  rb : Bool   -- Roger ate beans
  rt : Bool   -- Roger ate tofu
  deriving DecidableEq, BEq, Repr

/-- Finite enumeration of D0World via the canonical equivalence with
    `Bool × Bool × Bool × Bool`. -/
instance : Fintype D0World :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool)
    { toFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      invFun := fun w => (w.hb, w.ht, w.rb, w.rt)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_D0World : Fintype.card D0World = 16 := by decide

-- ════════════════════════════════════════════════════
-- § Atomic Propositions (as Sets)
-- ════════════════════════════════════════════════════

/-- Hannah ate the beans. -/
def hannahBeans : Set D0World := {w | w.hb = true}
/-- Hannah ate the tofu. -/
def hannahTofu : Set D0World := {w | w.ht = true}
/-- Roger ate the beans. -/
def rogerBeans : Set D0World := {w | w.rb = true}
/-- Roger ate the tofu. -/
def rogerTofu : Set D0World := {w | w.rt = true}

instance : DecidablePred (· ∈ hannahBeans) :=
  fun w => show Decidable (w.hb = true) from inferInstance
instance : DecidablePred (· ∈ (hannahBeansᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ hannahBeans) from inferInstance
instance : DecidablePred (· ∈ hannahTofu) :=
  fun w => show Decidable (w.ht = true) from inferInstance
instance : DecidablePred (· ∈ (hannahTofuᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ hannahTofu) from inferInstance
instance : DecidablePred (· ∈ rogerBeans) :=
  fun w => show Decidable (w.rb = true) from inferInstance
instance : DecidablePred (· ∈ (rogerBeansᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ rogerBeans) from inferInstance
instance : DecidablePred (· ∈ rogerTofu) :=
  fun w => show Decidable (w.rt = true) from inferInstance
instance : DecidablePred (· ∈ (rogerTofuᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ rogerTofu) from inferInstance

/-! ### Nontriviality lemmas (manual, one per atomic proposition) -/

theorem hb_ne_empty : hannahBeans ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨true, false, false, false⟩ : D0World) ∈ hannahBeans := rfl
  rw [h] at hmem; exact hmem.elim

theorem hb_ne_univ : hannahBeans ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ hannahBeans :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

theorem ht_ne_empty : hannahTofu ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨false, true, false, false⟩ : D0World) ∈ hannahTofu := rfl
  rw [h] at hmem; exact hmem.elim

theorem ht_ne_univ : hannahTofu ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ hannahTofu :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

theorem rb_ne_empty : rogerBeans ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨false, false, true, false⟩ : D0World) ∈ rogerBeans := rfl
  rw [h] at hmem; exact hmem.elim

theorem rb_ne_univ : rogerBeans ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ rogerBeans :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

theorem rt_ne_empty : rogerTofu ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨false, false, false, true⟩ : D0World) ∈ rogerTofu := rfl
  rw [h] at hmem; exact hmem.elim

theorem rt_ne_univ : rogerTofu ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ rogerTofu :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

-- ════════════════════════════════════════════════════
-- § Polar Questions (via `Question.polar`)
-- ════════════════════════════════════════════════════

/-- "Did Hannah eat the beans?" -/
abbrev q_ai : Question D0World := Question.polar hannahBeans

/-- "Did Hannah eat the tofu?" -/
abbrev q_aii : Question D0World := Question.polar hannahTofu

/-- "Did Roger eat the beans?" -/
abbrev q_bi : Question D0World := Question.polar rogerBeans

/-- "Did Roger eat the tofu?" -/
abbrev q_bii : Question D0World := Question.polar rogerTofu

-- ════════════════════════════════════════════════════
-- § Wh-Questions (via `Question.ofList`)
-- ════════════════════════════════════════════════════

/-- "What did Hannah eat?" — partition into 4 cells by ⟨hb, ht⟩.
    Beans-only, tofu-only, both, neither. -/
def q_a : Question D0World := Question.ofList [
  {w | w.hb = true ∧ w.ht = false},
  {w | w.hb = false ∧ w.ht = true},
  {w | w.hb = true ∧ w.ht = true},
  {w | w.hb = false ∧ w.ht = false}
]

/-- "What did Roger eat?" — partition by ⟨rb, rt⟩. -/
def q_b : Question D0World := Question.ofList [
  {w | w.rb = true ∧ w.rt = false},
  {w | w.rb = false ∧ w.rt = true},
  {w | w.rb = true ∧ w.rt = true},
  {w | w.rb = false ∧ w.rt = false}
]

/-- "What did everyone eat?" — the Big Question, the lattice meet of
    `q_a` and `q_b` (knowing what everyone ate = knowing what Hannah ate
    AND what Roger ate). -/
def q_1 : Question D0World := q_a ⊓ q_b

-- ════════════════════════════════════════════════════
-- § Internal: per-cell alternatives of q_a, q_b, q_1
-- (Shared infrastructure for negative-entailment, partial-answer,
--  and relevance theorems below.)
-- ════════════════════════════════════════════════════

/-- Hannah-beans-only cell, the canonical witness in `alt q_a`. -/
private abbrev qa_c1 : Set D0World := {w | w.hb = true ∧ w.ht = false}

/-- Hannah-neither cell — used to construct atomic singletons of `alt q_1`. -/
private abbrev qa_c4 : Set D0World := {w | w.hb = false ∧ w.ht = false}

/-- Roger-neither cell — paired with `qa_c4` to give the singleton
    `{⟨false, false, false, false⟩}`. -/
private abbrev qb_c4 : Set D0World := {w | w.rb = false ∧ w.rt = false}

/-- The "all-false" world — atomic alternative of `q_1`. -/
private abbrev w_zero : D0World := ⟨false, false, false, false⟩

private theorem qa_c1_in_alt : qa_c1 ∈ alt q_a := by
  apply Question.mem_alt_ofList_of_disjoint_others
  · simp [qa_c1]
  · intro h
    have : (⟨true, false, false, false⟩ : D0World) ∈ qa_c1 := ⟨rfl, rfl⟩
    rw [h] at this; exact this.elim
  · intro p hp hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [Set.disjoint_left]
    rcases hp with rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · intro w h1 h2; exact Bool.false_ne_true (h2.1.symm.trans h1.1)
    · intro w h1 h2; exact Bool.false_ne_true (h1.2.symm.trans h2.2)
    · intro w h1 h2; exact Bool.false_ne_true (h2.1.symm.trans h1.1)

/-- The all-false singleton is an alternative of `q_1`. Maximal because
    every q_1-resolving state ⊇ {w_zero} must lie in both `qa_c4` and
    `qb_c4`, whose intersection is exactly `{w_zero}`. -/
private theorem singleton_w_zero_in_alt_q1 :
    ({w_zero} : Set D0World) ∈ alt q_1 := by
  show ({w_zero} : Set D0World) ∈ alt (q_a ⊓ q_b)
  rw [Question.mem_alt_inf_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- {w_zero} ∈ q_a.props (subset of qa_c4)
    rw [show (q_a : Question D0World).props = (Question.ofList _).props from rfl]
    show ({w_zero} : Set D0World) ∈ Question.ofList _
    rw [Question.mem_ofList]
    refine Or.inr ⟨qa_c4, ?_, ?_⟩
    · simp [qa_c4]
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, rfl⟩
  · -- {w_zero} ∈ q_b.props (subset of qb_c4)
    rw [show (q_b : Question D0World).props = (Question.ofList _).props from rfl]
    show ({w_zero} : Set D0World) ∈ Question.ofList _
    rw [Question.mem_ofList]
    refine Or.inr ⟨qb_c4, ?_, ?_⟩
    · simp [qb_c4]
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, rfl⟩
  · -- maximality: any q ⊇ {w_zero} in both q_a.props and q_b.props
    -- must equal {w_zero}.
    intro q ⟨hqa, hqb⟩ hsub
    have hqa' : q ∈ Question.ofList (W := D0World)
        [{w | w.hb = true ∧ w.ht = false}, {w | w.hb = false ∧ w.ht = true},
         {w | w.hb = true ∧ w.ht = true}, {w | w.hb = false ∧ w.ht = false}] := hqa
    have hqb' : q ∈ Question.ofList (W := D0World)
        [{w | w.rb = true ∧ w.rt = false}, {w | w.rb = false ∧ w.rt = true},
         {w | w.rb = true ∧ w.rt = true}, {w | w.rb = false ∧ w.rt = false}] := hqb
    rw [Question.mem_ofList] at hqa' hqb'
    -- q ⊇ {w_zero} so q nonempty; pick the cell of q_a / q_b containing w_zero
    have hwq : w_zero ∈ q := hsub rfl
    have hqne : q ≠ ∅ := fun h => by rw [h] at hwq; exact hwq.elim
    rcases hqa' with rfl | ⟨ca, hcaL, hqca⟩
    · exact (hqne rfl).elim
    rcases hqb' with rfl | ⟨cb, hcbL, hqcb⟩
    · exact (hqne rfl).elim
    -- ca contains w_zero (hb=false, ht=false), so ca = qa_c4
    have hwca : w_zero ∈ ca := hqca hwq
    have hca_eq : ca = qa_c4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcaL
      rcases hcaL with rfl | rfl | rfl | rfl
      · exact (Bool.false_ne_true hwca.1).elim
      · exact (Bool.false_ne_true hwca.2).elim
      · exact (Bool.false_ne_true hwca.1).elim
      · rfl
    have hwcb : w_zero ∈ cb := hqcb hwq
    have hcb_eq : cb = qb_c4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcbL
      rcases hcbL with rfl | rfl | rfl | rfl
      · exact (Bool.false_ne_true hwcb.1).elim
      · exact (Bool.false_ne_true hwcb.2).elim
      · exact (Bool.false_ne_true hwcb.1).elim
      · rfl
    -- q ⊆ qa_c4 ∩ qb_c4 = {w_zero}
    intro w hw
    have hwa : w ∈ qa_c4 := hca_eq ▸ hqca hw
    have hwb : w ∈ qb_c4 := hcb_eq ▸ hqcb hw
    rw [Set.mem_singleton_iff]
    cases w with
    | mk hb ht rb rt =>
      obtain ⟨hhb, hht⟩ := hwa
      obtain ⟨hrb, hrt⟩ := hwb
      simp only at hhb hht hrb hrt
      subst hhb; subst hht; subst hrb; subst hrt
      rfl

-- ════════════════════════════════════════════════════
-- § Question Entailment (@cite{roberts-2012} Def. 8)
-- ════════════════════════════════════════════════════

-- Polar→polar entailment decides via `questionEntails_polar_polar_iff`.

/-- `q_ai` entails itself (sanity check). -/
theorem qai_entails_qai : questionEntails q_ai q_ai :=
  questionEntails_refl _

/-- `q_ai` does NOT entail `q_bi`: knowing whether Hannah ate beans tells
    you nothing about whether Roger ate beans (orthogonal polar questions). -/
theorem qai_not_entails_qbi : ¬ questionEntails q_ai q_bi := by
  rw [questionEntails_polar_polar_iff hb_ne_empty hb_ne_univ
        rb_ne_empty rb_ne_univ]
  decide

-- Wh→polar entailments now decide via `ofList_le_polar_of_classified`
-- (each cell of the wh-partition lies in `p` or `pᶜ` of the polar
-- question) composed with `questionEntails_of_le'` (lattice → Roberts).
-- The Big-Question entailments use `inf_le_left`/`inf_le_right`.

/-- The Big Question entails "What did Hannah eat?" -/
theorem q1_entails_qa : questionEntails q_1 q_a :=
  questionEntails_of_le' inf_le_left

/-- The Big Question entails "What did Roger eat?" -/
theorem q1_entails_qb : questionEntails q_1 q_b :=
  questionEntails_of_le' inf_le_right

/-- "What did Hannah eat?" entails "Did Hannah eat the beans?" -/
theorem qa_entails_qai : questionEntails q_a q_ai := by
  apply questionEntails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwhb => Bool.false_ne_true (hw.1.symm.trans hwhb))
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwhb => Bool.false_ne_true (hw.1.symm.trans hwhb))

/-- "What did Hannah eat?" entails "Did Hannah eat the tofu?" -/
theorem qa_entails_qaii : questionEntails q_a q_aii := by
  apply questionEntails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (fun w hw hwht => Bool.false_ne_true (hw.2.symm.trans hwht))
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inr (fun w hw hwht => Bool.false_ne_true (hw.2.symm.trans hwht))

/-- "What did Roger eat?" entails "Did Roger eat the beans?" -/
theorem qb_entails_qbi : questionEntails q_b q_bi := by
  apply questionEntails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwrb => Bool.false_ne_true (hw.1.symm.trans hwrb))
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwrb => Bool.false_ne_true (hw.1.symm.trans hwrb))

/-- "What did Roger eat?" entails "Did Roger eat the tofu?" -/
theorem qb_entails_qbii : questionEntails q_b q_bii := by
  apply questionEntails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (fun w hw hwrt => Bool.false_ne_true (hw.2.symm.trans hwrt))
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inr (fun w hw hwrt => Bool.false_ne_true (hw.2.symm.trans hwrt))

-- Entailment is asymmetric: subquestions do NOT entail their parents.

/-- q_a does NOT entail q_1. The witness `qa_c1 ∈ alt q_a` (Hannah-beans-only)
    contains worlds with all four (rb, rt) combinations; no single q_b cell
    contains them all, so no `alt q_1` (which lies in some q_b cell) can
    extend `qa_c1`. -/
theorem qa_not_entails_q1 : ¬ questionEntails q_a q_1 := by
  intro h
  obtain ⟨q, hq, hsub⟩ := h qa_c1 qa_c1_in_alt
  -- q ∈ alt q_1 = alt (q_a ⊓ q_b); extract membership in q_b.props
  obtain ⟨⟨_, hqb⟩, _⟩ := hq
  have hqb' : q ∈ Question.ofList (W := D0World)
      [{w | w.rb = true ∧ w.rt = false}, {w | w.rb = false ∧ w.rt = true},
       {w | w.rb = true ∧ w.rt = true}, {w | w.rb = false ∧ w.rt = false}] := hqb
  rw [mem_ofList] at hqb'
  -- Two witness worlds in qa_c1 with conflicting (rb, rt)
  have hw1q : (⟨true, false, true, false⟩ : D0World) ∈ q := hsub ⟨rfl, rfl⟩
  have hw2q : (⟨true, false, false, true⟩ : D0World) ∈ q := hsub ⟨rfl, rfl⟩
  rcases hqb' with rfl | ⟨c, hcL, hqc⟩
  · exact hw1q.elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcL
  rcases hcL with rfl | rfl | rfl | rfl
  · exact Bool.false_ne_true (hqc hw2q).1
  · exact Bool.false_ne_true (hqc hw1q).1.symm
  · exact Bool.false_ne_true (hqc hw1q).2
  · exact Bool.false_ne_true (hqc hw1q).1.symm

/-- q_ai does NOT entail q_a. The witness `hannahBeans ∈ alt q_ai` contains
    worlds with both `ht = true` and `ht = false`; no q_a cell (each fixing
    `ht`) can extend `hannahBeans`. -/
theorem qai_not_entails_qa : ¬ questionEntails q_ai q_a := by
  intro h
  have halt : hannahBeans ∈ alt q_ai := by
    rw [show q_ai = Question.polar hannahBeans from rfl,
        alt_polar_of_nontrivial hb_ne_empty hb_ne_univ]
    left; rfl
  obtain ⟨q, hq, hsub⟩ := h hannahBeans halt
  have hq_props : q ∈ q_a.props := alt_subset_props _ hq
  have hq' : q ∈ Question.ofList (W := D0World)
      [{w | w.hb = true ∧ w.ht = false}, {w | w.hb = false ∧ w.ht = true},
       {w | w.hb = true ∧ w.ht = true}, {w | w.hb = false ∧ w.ht = false}] := hq_props
  rw [mem_ofList] at hq'
  have hw1q : (⟨true, true, false, false⟩ : D0World) ∈ q := hsub rfl
  have hw2q : (⟨true, false, false, false⟩ : D0World) ∈ q := hsub rfl
  rcases hq' with rfl | ⟨c, hcL, hqc⟩
  · exact hw1q.elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcL
  rcases hcL with rfl | rfl | rfl | rfl
  · exact Bool.false_ne_true (hqc hw1q).2.symm
  · exact Bool.false_ne_true (hqc hw1q).1.symm
  · exact Bool.false_ne_true (hqc hw2q).2
  · exact Bool.false_ne_true (hqc hw1q).1.symm

-- ════════════════════════════════════════════════════
-- § Subquestions (@cite{roberts-2012} Def. 8–9)
-- ════════════════════════════════════════════════════

/-- q_a is a subquestion of q_1. -/
theorem qa_sub_q1 : isSubquestion q_a q_1 := q1_entails_qa

/-- q_b is a subquestion of q_1. -/
theorem qb_sub_q1 : isSubquestion q_b q_1 := q1_entails_qb

-- ════════════════════════════════════════════════════
-- § Strategy of Inquiry (@cite{roberts-2012} Def. 12)
-- ════════════════════════════════════════════════════

/-- Roberts' strategy for the D₀ scenario:
    Answer q_1 by answering q_a and q_b;
    answer q_a by answering q_ai and q_aii;
    answer q_b by answering q_bi and q_bii. -/
def strat_1 : Strategy D0World :=
  .branch q_1 [
    .branch q_a [.leaf q_ai, .leaf q_aii],
    .branch q_b [.leaf q_bi, .leaf q_bii]
  ]

/-- The strategy has 7 questions total. -/
theorem strat_1_count : strat_1.allQuestions.length = 7 := by
  simp [strat_1, Strategy.allQuestions, List.flatMap]

/-- The root of the strategy is complete: answering "What did Hannah eat?"
    and "What did Roger eat?" answers "What did everyone eat?" Reduces
    by `top_inf_eq` to `questionEntails (q_a ⊓ q_b) q_1` = reflexivity. -/
theorem strat_1_root_complete : strat_1.isComplete := by
  show questionEntails ((⊤ ⊓ q_a) ⊓ q_b) q_1
  rw [top_inf_eq]
  exact questionEntails_refl _

/-- The q_a sub-strategy is complete: pursuing both polar subquestions
    `q_ai` and `q_aii` resolves the wh-question `q_a` they jointly
    partition. Closes via `polar_inf_polar_le_ofList_of_corners`: the
    four corners (Hannah's beans × tofu) are exactly the cells of `q_a`. -/
theorem strat_1_qa_complete :
    (Strategy.branch q_a [.leaf q_ai, .leaf q_aii] : Strategy D0World).isComplete := by
  show questionEntails ((⊤ ⊓ q_ai) ⊓ q_aii) q_a
  rw [top_inf_eq]
  apply questionEntails_of_le'
  show Question.polar hannahBeans ⊓ Question.polar hannahTofu ≤ q_a
  apply Question.polar_inf_polar_le_ofList_of_corners
  · exact ⟨{w | w.hb = true ∧ w.ht = true}, by simp, fun _ hw => hw⟩
  · refine ⟨{w | w.hb = true ∧ w.ht = false}, by simp, fun w hw => ⟨hw.1, ?_⟩⟩
    cases h : w.ht
    · rfl
    · exact (hw.2 h).elim
  · refine ⟨{w | w.hb = false ∧ w.ht = true}, by simp, fun w hw => ⟨?_, hw.2⟩⟩
    cases h : w.hb
    · rfl
    · exact (hw.1 h).elim
  · refine ⟨{w | w.hb = false ∧ w.ht = false}, by simp, fun w hw => ⟨?_, ?_⟩⟩
    · cases h : w.hb
      · rfl
      · exact (hw.1 h).elim
    · cases h : w.ht
      · rfl
      · exact (hw.2 h).elim

/-- The q_b sub-strategy is complete (mirror of `strat_1_qa_complete`
    for Roger). -/
theorem strat_1_qb_complete :
    (Strategy.branch q_b [.leaf q_bi, .leaf q_bii] : Strategy D0World).isComplete := by
  show questionEntails ((⊤ ⊓ q_bi) ⊓ q_bii) q_b
  rw [top_inf_eq]
  apply questionEntails_of_le'
  show Question.polar rogerBeans ⊓ Question.polar rogerTofu ≤ q_b
  apply Question.polar_inf_polar_le_ofList_of_corners
  · exact ⟨{w | w.rb = true ∧ w.rt = true}, by simp, fun _ hw => hw⟩
  · refine ⟨{w | w.rb = true ∧ w.rt = false}, by simp, fun w hw => ⟨hw.1, ?_⟩⟩
    cases h : w.rt
    · rfl
    · exact (hw.2 h).elim
  · refine ⟨{w | w.rb = false ∧ w.rt = true}, by simp, fun w hw => ⟨?_, hw.2⟩⟩
    cases h : w.rb
    · rfl
    · exact (hw.1 h).elim
  · refine ⟨{w | w.rb = false ∧ w.rt = false}, by simp, fun w hw => ⟨?_, ?_⟩⟩
    · cases h : w.rb
      · rfl
      · exact (hw.1 h).elim
    · cases h : w.rt
      · rfl
      · exact (hw.2 h).elim

-- ════════════════════════════════════════════════════
-- § QUD Stack Traces
-- ════════════════════════════════════════════════════

/-- Initial state: push the Big Question. -/
def stack_0 : QUDStack D0World := QUDStack.empty.push q_1

/-- Pursue Hannah's food: push q_a. -/
def stack_1 : QUDStack D0World := stack_0.push q_a

/-- Pursue Hannah+beans: push q_ai. -/
def stack_2 : QUDStack D0World := stack_1.push q_ai

/-- "Hannah ate the beans" answers q_ai: pop. -/
def stack_3 : QUDStack D0World := stack_2.pop

/-- Stack depths trace the discourse. -/
theorem stack_depths :
    stack_0.depth = 1 ∧ stack_1.depth = 2 ∧
    stack_2.depth = 3 ∧ stack_3.depth = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- After popping q_ai, the immediate QUD is q_a. -/
theorem stack_3_qud : stack_3.immediateQUD = some q_a := rfl

-- ════════════════════════════════════════════════════
-- § Negative Partial Answerhood
-- ════════════════════════════════════════════════════

/-- "Hannah didn't eat beans" (`hannahBeansᶜ`) negatively partially answers
    "Did Hannah eat beans?" — it rules out the `hannahBeans` alternative. -/
theorem neg_hb_partially_answers_qai :
    partiallyAnswers q_ai (hannahBeansᶜ : Set D0World) := by
  rw [partiallyAnswers_polar_iff hb_ne_empty hb_ne_univ]
  decide

/-- "Hannah didn't eat beans" also partially answers "What did Hannah eat?" —
    it rules out the `qa_c1` (Hannah-beans-only) alternative. -/
theorem neg_hb_partially_answers_qa :
    partiallyAnswers q_a (hannahBeansᶜ : Set D0World) := by
  refine ⟨qa_c1, qa_c1_in_alt, Or.inr ?_⟩
  intro w hw hw'
  exact hw hw'.1

-- ════════════════════════════════════════════════════
-- § Positive Partial Answerhood
-- ════════════════════════════════════════════════════

/-- "Hannah ate beans" positively partially answers q_ai. -/
theorem hb_partially_answers_qai :
    partiallyAnswers q_ai hannahBeans := by
  rw [partiallyAnswers_polar_iff hb_ne_empty hb_ne_univ]
  decide

/-- "Hannah ate beans" partially answers the Big Question — it rules out
    the `{w_zero}` (all-false) alternative. -/
theorem hb_partially_answers_q1 :
    partiallyAnswers q_1 hannahBeans := by
  refine ⟨{w_zero}, singleton_w_zero_in_alt_q1, Or.inr ?_⟩
  intro w hw hw'
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  exact Bool.false_ne_true hw

-- ════════════════════════════════════════════════════
-- § Relevance (@cite{roberts-2012} Def. 15)
-- ════════════════════════════════════════════════════

/-- "Hannah ate beans" as a single-alternative declarative issue. -/
def hannahBeans_assertion : Core.Question D0World := Question.declarative hannahBeans

/-- "Hannah ate beans" is relevant to q_1 (the Big Question). -/
theorem hannahBeans_relevant_to_q1 :
    moveRelevant hannahBeans_assertion q_1 [] := by
  refine ⟨hannahBeans, ?_, Or.inl hb_partially_answers_q1⟩
  show hannahBeans ∈ alt (Question.declarative hannahBeans)
  rw [alt_declarative]
  rfl

/-- q_a is relevant to q_1 as a subquestion: the `qa_c1` alternative
    rules out the `{w_zero}` alternative of q_1 (since `w_zero ∉ qa_c1`). -/
theorem qa_relevant_to_q1 :
    moveRelevant q_a q_1 [] := by
  refine ⟨qa_c1, qa_c1_in_alt, Or.inl ?_⟩
  refine ⟨{w_zero}, singleton_w_zero_in_alt_q1, Or.inr ?_⟩
  intro w hw hw'
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  exact Bool.false_ne_true hw.1

/-- "Hannah ate beans" is relevant to the entire D₀ strategy: it partially
    answers `q_1` (the strategy's root). -/
theorem hannahBeans_relevant_to_strategy :
    moveRelevantToStrategy hannahBeans_assertion strat_1 := by
  refine ⟨hannahBeans, ?_, q_1, ?_, hb_partially_answers_q1⟩
  · show hannahBeans ∈ alt (Question.declarative hannahBeans)
    rw [alt_declarative]; rfl
  · -- strat_1 = .branch q_1 [...]; q_1 is the head of allQuestions
    simp [strat_1, Strategy.allQuestions]

-- ════════════════════════════════════════════════════
-- § Q-A Congruence / Focus Type Identity
-- ════════════════════════════════════════════════════

/-- The Rooth–Hamblin type identity grounds Q-A congruence:
    propositional focus values and Hamblin question denotations are the
    same type. @cite{rooth-1992}, @cite{roberts-2012} Def. 25. -/
theorem focus_question_type_identity :
    Semantics.FocusInterpretation.PropFocusValue D0World =
    Semantics.Questions.Hamblin.QuestionDen D0World := rfl

end Roberts2012
