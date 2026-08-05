import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Entailment
import Linglib.Semantics.Questions.Resolution
import Linglib.Core.Data.Fintype.Sets
import Linglib.Discourse.QUD.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# [roberts-2012] — Information Structure in Discourse

[roberts-2012] "Information structure in discourse: Towards an integrated
formal theory of pragmatics" (Semantics & Pragmatics 5(6): 1–69), her
worked discourse D₀: two individuals (Hilary, Robin), two foods (bagels,
tofu), 16 worlds, 7 questions forming a strategy tree. The file traces
the QUD stack through the discourse, verifies her (10g.iii)
well-formedness invariant, and proves her entailment table and
strategy-completeness observations.

```
         q₁ (Who ate what?)
        /                            \
    q_a (What did Hilary eat?)    q_b (What did Robin eat?)
    /        \                    /        \
q_ai (H bagels?) q_aii (H tofu?) q_bi (R bagels?) q_bii (R tofu?)
```

## Representation

A world is the `Finset` of eating events that occurred in it. Questions
are joins of their answers ([hamblin-1973b]): the yes/no questions are
`Question.ofSet` of a single eating event — the `{|α|}` q-alternative
Roberts specifies (the substrate's inquisitive `Question.polar`, with
alternatives `{p, pᶜ}`, is the rival convention) — and the wh-questions
are `⨆` over the open index, her (1)'s q-alternatives by wh-abstraction:
`q_a` joins over foods (her (7)), `q_1` over person–food pairs (her
(45)).
Her derived complete-answer partition (4) is the theorem
`mentionAll_wh_iff`. Question entailment (8) is rendered as
complete-answer transmission — `MentionAll σ q₁ → MentionAll σ q₂` —
because the alt-witnessed `Question.Entails` coincides with (8) only for
partition-shaped alternatives (see the fidelity note in
`Semantics/Questions/Entailment.lean`); answerhood (3) is
`Question.PartiallyAnswers`/`Question.MentionAll` verbatim.
-/

namespace Roberts2012

open Question
open Discourse (QUDStack Strategy)

-- `decide` on `Set`-subset goals over the finite world space.
attribute [local instance] Set.decidableSubsetOfFintype

/-! ### D₀ world space -/

/-- The two individuals of D₀. -/
inductive Person | hilary | robin
  deriving DecidableEq, Fintype, Inhabited

/-- The two foods of D₀. -/
inductive Food | bagels | tofu
  deriving DecidableEq, Fintype, Inhabited

private theorem Person.forall_person {p : Person → Prop} :
    (∀ u, p u) ↔ p .hilary ∧ p .robin :=
  ⟨fun h => ⟨h _, h _⟩, fun ⟨h1, h2⟩ u => by cases u <;> assumption⟩

private theorem Food.forall_food {p : Food → Prop} :
    (∀ f, p f) ↔ p .bagels ∧ p .tofu :=
  ⟨fun h => ⟨h _, h _⟩, fun ⟨h1, h2⟩ f => by cases f <;> assumption⟩

/-- A world of Roberts' D₀ scenario: the set of eating events that
    occurred in it. -/
abbrev World := Finset (Person × Food)

/-- `u` ate `f` — the worlds containing the event, i.e. the principal
    up-set of its minimal world `{(u, f)}`. -/
abbrev ate (u : Person) (f : Food) : Set World := Set.Ici {(u, f)}

/-- Distinct eating events are ⊆-incomparable. -/
private theorem ate_subset_ate_iff {u u' : Person} {f f' : Food} :
    ate u f ⊆ ate u' f' ↔ u = u' ∧ f = f' := by
  simp [ate, Prod.ext_iff, eq_comm]

/-! ### Questions as q-alternative sets ((1), (2), (7)) -/

/-- Hilary ate the bagels. -/
abbrev hilaryBagels : Set World := ate .hilary .bagels
/-- Hilary ate the tofu. -/
abbrev hilaryTofu : Set World := ate .hilary .tofu
/-- Robin ate the bagels. -/
abbrev robinBagels : Set World := ate .robin .bagels
/-- Robin ate the tofu. -/
abbrev robinTofu : Set World := ate .robin .tofu

/-- "Did Hilary eat the bagels?" -/
abbrev q_ai : Question World := Question.ofSet hilaryBagels
/-- "Did Hilary eat the tofu?" -/
abbrev q_aii : Question World := Question.ofSet hilaryTofu
/-- "Did Robin eat the bagels?" -/
abbrev q_bi : Question World := Question.ofSet robinBagels
/-- "Did Robin eat the tofu?" -/
abbrev q_bii : Question World := Question.ofSet robinTofu
/-- "What did Hilary eat?" — the join of its answers. -/
abbrev q_a : Question World := ⨆ f, Question.ofSet (ate .hilary f)
/-- "What did Robin eat?" -/
abbrev q_b : Question World := ⨆ f, Question.ofSet (ate .robin f)
/-- "Who ate what?" — D₀'s move 1, joining answers over person–food
    pairs. -/
abbrev q_1 : Question World :=
  ⨆ uf : Person × Food, Question.ofSet (ate uf.1 uf.2)

/-! ### Alternative enumerations -/

private theorem ate_antichain (uf uf' : Person × Food)
    (h : ate uf.1 uf.2 ⊆ ate uf'.1 uf'.2) :
    ate uf.1 uf.2 = ate uf'.1 uf'.2 := by
  obtain ⟨h1, h2⟩ := ate_subset_ate_iff.mp h
  rw [h1, h2]

private theorem alt_wh (u : Person) :
    alt (⨆ f, Question.ofSet (ate u f)) = Set.range (ate u) :=
  alt_iSup_ofSet (fun _ => Set.nonempty_Ici)
    (fun f f' h => ate_antichain (u, f) (u, f') h)

private theorem alt_q_1 :
    alt q_1 = Set.range fun uf : Person × Food => ate uf.1 uf.2 :=
  alt_iSup_ofSet (fun _ => Set.nonempty_Ici) ate_antichain

private theorem mem_alt_wh (u : Person) (f : Food) :
    ate u f ∈ alt (⨆ f', Question.ofSet (ate u f')) := by
  rw [alt_wh]; exact Set.mem_range_self f

private theorem mem_alt_q1 (u : Person) (f : Food) :
    ate u f ∈ alt q_1 := by
  rw [alt_q_1]; exact Set.mem_range_self (u, f)

/-! ### The complete-answer partition ((4)), derived -/

/-- Deciding two propositions is lying in one of the four Boolean
    corners. -/
private theorem subset_corners_iff {σ A B : Set World} :
    (σ ⊆ A ∨ σ ⊆ Aᶜ) ∧ (σ ⊆ B ∨ σ ⊆ Bᶜ) ↔
      σ ⊆ A ∩ B ∨ σ ⊆ A ∩ Bᶜ ∨ σ ⊆ Aᶜ ∩ B ∨ σ ⊆ Aᶜ ∩ Bᶜ := by
  simp only [Set.subset_inter_iff]
  tauto

/-- A state completely answers "What did `u` eat?" iff it lies within
    one cell of the partition the q-alternatives induce. -/
theorem mentionAll_wh_iff {σ : Set World} {u : Person} :
    MentionAll σ (⨆ f', Question.ofSet (ate u f')) ↔
      σ ⊆ ate u .bagels ∩ ate u .tofu ∨
      σ ⊆ ate u .bagels ∩ (ate u .tofu)ᶜ ∨
      σ ⊆ (ate u .bagels)ᶜ ∩ ate u .tofu ∨
      σ ⊆ (ate u .bagels)ᶜ ∩ (ate u .tofu)ᶜ := by
  rw [mentionAll_iff_of_alt_eq_range (alt_wh u), Food.forall_food]
  exact subset_corners_iff

/-! ### Question entailment ((3), (8))

Her (8) — answering `q₁` yields a complete answer to `q₂` — is
`completeAnswers q₁ ⊆ completeAnswers q₂`; the î(1) table lists the
entailments among D₀'s seven questions. -/

/-- "Who ate what?" entails "What did `u` eat?". -/
theorem q1_entails_wh (u : Person) :
    completeAnswers q_1 ⊆ completeAnswers (⨆ f', Question.ofSet (ate u f')) :=
  completeAnswers_anti (by
    rw [alt_wh, alt_q_1]
    exact Set.range_comp_subset_range (Prod.mk u) fun uf => ate uf.1 uf.2)

/-- "What did `u` eat?" entails "Did `u` eat `f`?". -/
theorem wh_entails_polar (u : Person) (f : Food) :
    completeAnswers (⨆ f', Question.ofSet (ate u f')) ⊆
      completeAnswers (Question.ofSet (ate u f)) :=
  completeAnswers_anti (by
    rw [alt_ofSet, alt_wh]
    exact Set.singleton_subset_iff.mpr (Set.mem_range_self f))

/-- "Who ate what?" entails every polar subquestion. -/
theorem q1_entails_polar (u : Person) (f : Food) :
    completeAnswers q_1 ⊆ completeAnswers (Question.ofSet (ate u f)) :=
  (q1_entails_wh u).trans (wh_entails_polar u f)

/-- Subquestions do not entail their superquestions: "Hilary ate both"
    completely answers `q_a` but decides nothing about Robin. -/
theorem qa_not_entails_q1 :
    ¬ completeAnswers q_a ⊆ completeAnswers q_1 := fun h => by
  have := h (mentionAll_wh_iff.mpr (Or.inl subset_rfl)) _
    (mem_alt_q1 .robin .bagels)
  rcases this with h' | h' <;> exact absurd h' (by decide)

/-- "Did Hilary eat the bagels?" does not entail "What did Hilary eat?":
    the positive answer leaves the tofu alternative open. -/
theorem qai_not_entails_qa :
    ¬ completeAnswers q_ai ⊆ completeAnswers q_a := fun h => by
  have hma : MentionAll (hilaryBagels : Set World) q_ai := fun p hp => by
    rw [alt_ofSet, Set.mem_singleton_iff] at hp
    subst hp
    exact Or.inl subset_rfl
  have := h hma _ (mem_alt_wh .hilary .tofu)
  rcases this with h' | h' <;> exact absurd h' (by decide)

/-! ### Answer composition ((11))

Her `Ans(aᵢ) ∩ Ans(aᵢᵢ) = Ans(a)` and `Ans(a) ∩ Ans(b) = Ans(1)`, as
set equations over `completeAnswers`. Partial answerhood is *not*
transitive in general (chaining loses completeness at the middle link),
which is why the stack invariant proofs below go direct rather than
composing. -/

/-- Jointly answering the polar subquestions is exactly answering "What
    did `u` eat?". -/
theorem completeAnswers_polar_inter (u : Person) :
    completeAnswers (Question.ofSet (ate u .bagels)) ∩
        completeAnswers (Question.ofSet (ate u .tofu))
      = completeAnswers (⨆ f', Question.ofSet (ate u f')) :=
  Set.ext fun σ => by
    simp only [Set.mem_inter_iff, mem_completeAnswers, mentionAll_ofSet_iff,
      mentionAll_iff_of_alt_eq_range (alt_wh u), Food.forall_food]

/-- Jointly answering "What did Hilary eat?" and "What did Robin eat?"
    is exactly answering "Who ate what?". -/
theorem completeAnswers_wh_inter :
    completeAnswers (⨆ f', Question.ofSet (ate .hilary f')) ∩
        completeAnswers (⨆ f', Question.ofSet (ate .robin f'))
      = completeAnswers q_1 :=
  Set.ext fun σ => by
    simp only [Set.mem_inter_iff, mem_completeAnswers,
      mentionAll_iff_of_alt_eq_range (alt_wh .hilary),
      mentionAll_iff_of_alt_eq_range (alt_wh .robin),
      mentionAll_iff_of_alt_eq_range alt_q_1, Prod.forall,
      Person.forall_person, Food.forall_food]

/-! ### Strategy of inquiry ((12)) -/

/-- Substrategy for `q_a`: pursue both polar subquestions about Hilary. -/
def strat_a : Strategy World := .node q_a [.leaf q_ai, .leaf q_aii]

/-- Substrategy for `q_b`: pursue both polar subquestions about Robin. -/
def strat_b : Strategy World := .node q_b [.leaf q_bi, .leaf q_bii]

/-- Roberts' strategy for the D₀ scenario:
    answer q_1 by answering q_a and q_b;
    answer q_a by answering q_ai and q_aii;
    answer q_b by answering q_bi and q_bii. -/
def strat_1 : Strategy World := .node q_1 [strat_a, strat_b]

/-- The strategy has 7 questions total. -/
theorem strat_1_numNodes : strat_1.numNodes = 7 := rfl

private theorem meet_ofSet_entails {p p' : Set World} {Q : Question World}
    (hQ : p ∈ alt Q) : (Question.ofSet p ⊓ Question.ofSet p').Entails Q := by
  intro r hr
  have hr' : r ⊆ p :=
    Question.mem_ofSet.mp
      (Question.mem_inf.mp (Question.mem_props.mp (alt_subset_props _ hr))).1
  exact ⟨p, hQ, hr'⟩

/-- The Hilary substrategy is complete: jointly resolving `q_ai` and
    `q_aii` resolves `q_a`. -/
theorem strat_a_complete : strat_a.IsComplete :=
  .node_pair (meet_ofSet_entails (mem_alt_wh .hilary .bagels))
    (.leaf _) (.leaf _)

/-- The Robin substrategy is complete. -/
theorem strat_b_complete : strat_b.IsComplete :=
  .node_pair (meet_ofSet_entails (mem_alt_wh .robin .bagels))
    (.leaf _) (.leaf _)

/-- The whole D₀ strategy is complete: any joint resolution of `q_a` and
    `q_b` yields an alternative of `q_1`. -/
theorem strat_1_complete : strat_1.IsComplete := by
  refine .node_pair ?_ strat_a_complete strat_b_complete
  intro r hr
  have hr' : r ∈ (⨆ f', Question.ofSet (ate .hilary f')) :=
    (Question.mem_inf.mp (Question.mem_props.mp (alt_subset_props _ hr))).1
  rcases Question.mem_iSup_ofSet.mp hr' with rfl | ⟨f, hrf⟩
  · exact ⟨hilaryBagels, mem_alt_q1 .hilary .bagels, Set.empty_subset _⟩
  · exact ⟨ate .hilary f, mem_alt_q1 .hilary f, hrf⟩

/-! ### QUD stack traces ((10g), (17)) -/

/-- Initial state: accept move 1, "Who ate what?". -/
def stack_0 : QUDStack World := [q_1]

/-- Pursue Hilary's food: accept q_a. -/
def stack_1 : QUDStack World := q_a :: stack_0

/-- Pursue Hilary+bagels: accept q_ai. -/
def stack_2 : QUDStack World := q_ai :: stack_1

/-- "Hilary ate the bagels" answers q_ai: retire it. -/
def stack_3 : QUDStack World := stack_2.tail

/-- Stack depths trace the discourse. -/
theorem stack_depths :
    stack_0.length = 1 ∧ stack_1.length = 2 ∧
    stack_2.length = 3 ∧ stack_3.length = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- After retiring q_ai, the immediate QUD is q_a. -/
theorem stack_3_qud : stack_3.head? = some q_a := rfl

/-! ### Stack well-formedness ((10g.iii)) -/

private theorem wh_alts_partially_answer_q1 (u : Person) :
    ∀ a ∈ alt (⨆ f', Question.ofSet (ate u f')), PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_wh] at ha
  obtain ⟨f, -, rfl⟩ := ha
  exact ⟨ate u f, mem_alt_q1 u f, Or.inl subset_rfl⟩

private theorem polar_alts_partially_answer_wh (u : Person) (f : Food) :
    ∀ a ∈ alt (Question.ofSet (ate u f)),
      PartiallyAnswers a (⨆ f', Question.ofSet (ate u f')) := by
  intro a ha
  rw [alt_ofSet, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨ate u f, mem_alt_wh u f, Or.inl subset_rfl⟩

private theorem polar_alts_partially_answer_q1 (u : Person) (f : Food) :
    ∀ a ∈ alt (Question.ofSet (ate u f)), PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_ofSet, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨ate u f, mem_alt_q1 u f, Or.inl subset_rfl⟩

/-- The stack `[q_a, q_1]` is well-formed in the trivial common ground:
    every complete answer to the subquestion partially answers the
    question below it. -/
theorem stack_1_wellFormed : QUDStack.WellFormed Set.univ stack_1 := by
  show QUDStack.WellFormed Set.univ (q_a :: stack_0)
  rw [QUDStack.wellFormed_cons]
  refine ⟨?_, QUDStack.wellFormed_singleton ..⟩
  intro lower hlow a ha
  simp only [stack_0, List.mem_singleton] at hlow
  subst hlow
  rw [Set.univ_inter]
  exact wh_alts_partially_answer_q1 .hilary a ha

/-- The full three-question stack `[q_ai, q_a, q_1]` is well-formed. -/
theorem stack_2_wellFormed : QUDStack.WellFormed Set.univ stack_2 := by
  show QUDStack.WellFormed Set.univ (q_ai :: stack_1)
  rw [QUDStack.wellFormed_cons]
  refine ⟨?_, stack_1_wellFormed⟩
  intro lower hlow a ha
  rw [Set.univ_inter]
  rcases List.mem_cons.mp hlow with rfl | hlow
  · exact polar_alts_partially_answer_wh .hilary .bagels a ha
  · simp only [stack_0, List.mem_singleton] at hlow
    subst hlow
    exact polar_alts_partially_answer_q1 .hilary .bagels a ha

/-- Retiring the answered `q_ai` preserves well-formedness. -/
theorem stack_3_wellFormed : QUDStack.WellFormed Set.univ stack_3 :=
  stack_2_wellFormed.tail

/-! ### Answerhood ((3))

A partial answer evaluates at least one q-alternative, positively or
negatively; the negative direction — ruling an alternative out — is her
point against confirm-only answerhood. -/

/-- "Hilary didn't eat bagels" negatively answers "Did Hilary eat the
    bagels?" — it falsifies its sole alternative. -/
theorem neg_hilaryBagels_partiallyAnswers_qai :
    PartiallyAnswers (hilaryBagelsᶜ : Set World) q_ai :=
  partiallyAnswers_compl_of_mem_alt (self_mem_alt_ofSet (ate .hilary .bagels))

/-- "Hilary didn't eat bagels" partially answers "What did Hilary eat?" —
    it rules out the bagels alternative. -/
theorem neg_hilaryBagels_partiallyAnswers_qa :
    PartiallyAnswers (hilaryBagelsᶜ : Set World) q_a :=
  partiallyAnswers_compl_of_mem_alt (mem_alt_wh .hilary .bagels)

/-- "Hilary ate bagels" positively answers "Did Hilary eat the bagels?". -/
theorem hilaryBagels_partiallyAnswers_qai :
    PartiallyAnswers (hilaryBagels : Set World) q_ai :=
  partiallyAnswers_of_mem_alt (self_mem_alt_ofSet (ate .hilary .bagels))

/-- "Hilary ate bagels" partially answers "Who ate what?" — it confirms
    one of its four alternatives. -/
theorem hilaryBagels_partiallyAnswers_q1 :
    PartiallyAnswers (hilaryBagels : Set World) q_1 :=
  partiallyAnswers_of_mem_alt (mem_alt_q1 .hilary .bagels)

/-! ### Relevance ((15))

Assertion-clause relevance throughout; Roberts' clause for interrogative
moves is strategy membership, which `qa_relevant_to_q1` proxies by
partial answerhood. -/

/-- The assertion "Hilary ate bagels": a declarative's q-alternative
    set is the singleton of its content. -/
def hilaryBagels_assertion : Question World :=
  Question.ofSet hilaryBagels

/-- "Hilary ate bagels" is relevant to move 1, "Who ate what?". -/
theorem hilaryBagels_relevant_to_q1 :
    hilaryBagels_assertion.IsRelevantTo {q_1} :=
  ⟨hilaryBagels, self_mem_alt_ofSet _, q_1, rfl,
    hilaryBagels_partiallyAnswers_q1⟩

/-- The question `q_a` is relevant to `q_1` under the assertion-clause
    proxy: its bagels alternative confirms an alternative of `q_1`. -/
theorem qa_relevant_to_q1 : q_a.IsRelevantTo {q_1} :=
  ⟨hilaryBagels, mem_alt_wh .hilary .bagels, q_1, rfl,
    hilaryBagels_partiallyAnswers_q1⟩

/-- "Hilary ate bagels" is relevant to the entire D₀ strategy: it
    partially answers `q_1` (the strategy's root). -/
theorem hilaryBagels_relevant_to_strategy :
    hilaryBagels_assertion.IsRelevantTo {q | q ∈ strat_1.values} :=
  ⟨hilaryBagels, self_mem_alt_ofSet _, q_1,
    by simp [strat_1, strat_a, strat_b], hilaryBagels_partiallyAnswers_q1⟩

end Roberts2012
