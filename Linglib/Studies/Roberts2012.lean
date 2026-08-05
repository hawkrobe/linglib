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

A world is the `Finset` of eating events that occurred in it, and every
question is `Question.which` applied to the indexed family `ate` — her
(1)'s q-alternatives by wh-abstraction over a domain, verbatim: `whAte
u` abstracts over foods (her (7)), `q_1` over person–food pairs (her
(45)), and the yes/no questions use the singleton domain, giving the
`{|α|}` q-alternative she specifies (the substrate's inquisitive
`Question.polar`, with alternatives `{p, pᶜ}`, is the rival convention).
Her derived complete-answer partition (4) is the theorem
`mentionAll_whAte_iff`. Question entailment (8) is rendered as
complete-answer transmission — `MentionAll σ q₁ → MentionAll σ q₂` —
because the alt-witnessed `Question.Entails` coincides with (8) only for
partition-shaped alternatives (see the fidelity note in
`Semantics/Questions/Entailment.lean`); answerhood (3) is
`Question.PartiallyAnswers`/`Question.MentionAll` verbatim.
-/

namespace Roberts2012

open Question
open Discourse (QUDStack Strategy Relevant)

-- `decide` on `Set`-subset goals over the finite world space.
attribute [local instance] Set.decidableSubsetOfFintype

/-! ### D₀ world space -/

/-- The two individuals of D₀. -/
inductive Person | hilary | robin
  deriving DecidableEq, Fintype

/-- The two foods of D₀. -/
inductive Food | bagels | tofu
  deriving DecidableEq, Fintype

/-- A world is the set of eating events that occurred in it. -/
abbrev D0World := Finset (Person × Food)

/-- `u` ate `f`. -/
abbrev ate (u : Person) (f : Food) : Set D0World := {w | (u, f) ∈ w}

private theorem ate_nonempty (u : Person) (f : Food) : (ate u f).Nonempty :=
  ⟨{(u, f)}, Finset.mem_singleton_self _⟩

/-- Distinct eating events are ⊆-incomparable: the singleton world
    `{(u, f)}` witnesses. -/
private theorem ate_subset_ate_iff {u u' : Person} {f f' : Food} :
    ate u f ⊆ ate u' f' ↔ u = u' ∧ f = f' := by
  constructor
  · intro h
    have h2 : (u', f') = (u, f) :=
      Finset.mem_singleton.mp
        (h (show ({(u, f)} : D0World) ∈ ate u f from Finset.mem_singleton_self _))
    exact ⟨(congrArg Prod.fst h2).symm, (congrArg Prod.snd h2).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact subset_rfl

/-! ### Questions as q-alternative sets ((1), (2), (7)) -/

/-- "Did `u` eat `f`?" — singleton q-alternative `{|α|}` per Roberts'
    yes/no convention. -/
def polarAte (u : Person) (f : Food) : Question D0World :=
  Question.which {f} (ate u)

/-- "What did `u` eat?" — q-alternatives by abstraction over foods. -/
def whAte (u : Person) : Question D0World :=
  Question.which Set.univ (ate u)

/-- "Who ate what?" — D₀'s move 1, abstracting over person–food pairs
    (her (45)). -/
def q_1 : Question D0World :=
  Question.which Set.univ fun uf : Person × Food => ate uf.1 uf.2

/-- "Did Hilary eat the bagels?" -/
abbrev q_ai : Question D0World := polarAte .hilary .bagels
/-- "Did Hilary eat the tofu?" -/
abbrev q_aii : Question D0World := polarAte .hilary .tofu
/-- "Did Robin eat the bagels?" -/
abbrev q_bi : Question D0World := polarAte .robin .bagels
/-- "Did Robin eat the tofu?" -/
abbrev q_bii : Question D0World := polarAte .robin .tofu
/-- "What did Hilary eat?" -/
abbrev q_a : Question D0World := whAte .hilary
/-- "What did Robin eat?" -/
abbrev q_b : Question D0World := whAte .robin

/-- Hilary ate the bagels. -/
abbrev hilaryBagels : Set D0World := ate .hilary .bagels
/-- Hilary ate the tofu. -/
abbrev hilaryTofu : Set D0World := ate .hilary .tofu
/-- Robin ate the bagels. -/
abbrev robinBagels : Set D0World := ate .robin .bagels
/-- Robin ate the tofu. -/
abbrev robinTofu : Set D0World := ate .robin .tofu

/-! ### Alternative enumerations -/

private theorem alt_polarAte (u : Person) (f : Food) :
    alt (polarAte u f) = {ate u f} := by
  rw [polarAte, alt_which_of_antichain (Set.singleton_nonempty f)
    (fun e _ => ate_nonempty u e)
    (by rintro _ ⟨f₁, -, rfl⟩ _ ⟨f₂, -, rfl⟩ hne hsub
        obtain ⟨-, h2⟩ := ate_subset_ate_iff.mp hsub
        exact hne (h2 ▸ rfl))]
  exact Set.image_singleton

private theorem alt_whAte (u : Person) :
    alt (whAte u) = ate u '' Set.univ :=
  alt_which_of_antichain ⟨.bagels, trivial⟩ (fun e _ => ate_nonempty u e)
    (by rintro _ ⟨f₁, -, rfl⟩ _ ⟨f₂, -, rfl⟩ hne hsub
        obtain ⟨-, h2⟩ := ate_subset_ate_iff.mp hsub
        exact hne (h2 ▸ rfl))

private theorem alt_q_1 :
    alt q_1 = (fun uf : Person × Food => ate uf.1 uf.2) '' Set.univ :=
  alt_which_of_antichain ⟨(.hilary, .bagels), trivial⟩
    (fun uf _ => ate_nonempty uf.1 uf.2)
    (by rintro _ ⟨uf₁, -, rfl⟩ _ ⟨uf₂, -, rfl⟩ hne hsub
        obtain ⟨h1, h2⟩ := ate_subset_ate_iff.mp hsub
        exact hne (congrArg (fun uf : Person × Food => ate uf.1 uf.2)
          (Prod.ext h1 h2)))

private theorem ate_mem_alt_polar (u : Person) (f : Food) :
    ate u f ∈ alt (polarAte u f) := by
  rw [alt_polarAte]; rfl

private theorem ate_mem_alt_whAte (u : Person) (f : Food) :
    ate u f ∈ alt (whAte u) := by
  rw [alt_whAte]; exact ⟨f, trivial, rfl⟩

private theorem ate_mem_alt_q1 (u : Person) (f : Food) :
    ate u f ∈ alt q_1 := by
  rw [alt_q_1]; exact ⟨(u, f), trivial, rfl⟩

/-! ### The complete-answer partition ((4)), derived -/

/-- Deciding two propositions is lying in one of the four Boolean
    corners — the engine of her (4). -/
private theorem subset_corners_iff {σ A B : Set D0World} :
    (σ ⊆ A ∨ σ ⊆ Aᶜ) ∧ (σ ⊆ B ∨ σ ⊆ Bᶜ) ↔
      σ ⊆ A ∩ B ∨ σ ⊆ A ∩ Bᶜ ∨ σ ⊆ Aᶜ ∩ B ∨ σ ⊆ Aᶜ ∩ Bᶜ := by
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact Or.inl (Set.subset_inter h1 h2)
    · exact Or.inr (Or.inl (Set.subset_inter h1 h2))
    · exact Or.inr (Or.inr (Or.inl (Set.subset_inter h1 h2)))
    · exact Or.inr (Or.inr (Or.inr (Set.subset_inter h1 h2)))
  · rintro (h | h | h | h) <;>
      exact ⟨by first
          | exact Or.inl (h.trans Set.inter_subset_left)
          | exact Or.inr (h.trans Set.inter_subset_left),
        by first
          | exact Or.inl (h.trans Set.inter_subset_right)
          | exact Or.inr (h.trans Set.inter_subset_right)⟩

/-- Her (4): the complete answers to "What did `u` eat?" are exactly the
    states lying within one cell of the partition the q-alternatives
    induce. -/
theorem mentionAll_whAte_iff {σ : Set D0World} {u : Person} :
    MentionAll σ (whAte u) ↔
      σ ⊆ ate u .bagels ∩ ate u .tofu ∨
      σ ⊆ ate u .bagels ∩ (ate u .tofu)ᶜ ∨
      σ ⊆ (ate u .bagels)ᶜ ∩ ate u .tofu ∨
      σ ⊆ (ate u .bagels)ᶜ ∩ (ate u .tofu)ᶜ := by
  constructor
  · intro h
    exact subset_corners_iff.mp
      ⟨h _ (ate_mem_alt_whAte u .bagels), h _ (ate_mem_alt_whAte u .tofu)⟩
  · intro h p hp
    rw [alt_whAte] at hp
    obtain ⟨f, -, rfl⟩ := hp
    obtain ⟨h1, h2⟩ := subset_corners_iff.mpr h
    cases f
    exacts [h1, h2]

/-! ### Question entailment ((3), (8))

Her (8) — answering `q₁` yields a complete answer to `q₂` — rendered as
complete-answer transmission over the (3b) answerhood predicate. -/

private theorem mentionAll_mono {σ : Set D0World} {P Q : Question D0World}
    (h : alt Q ⊆ alt P) (hP : MentionAll σ P) : MentionAll σ Q :=
  fun p hp => hP p (h hp)

/-- "Who ate what?" entails "What did `u` eat?" (her î(1) table, first
    level). -/
theorem q1_entails_whAte {σ : Set D0World} (u : Person)
    (h : MentionAll σ q_1) : MentionAll σ (whAte u) :=
  mentionAll_mono
    (by rw [alt_whAte, alt_q_1]
        rintro _ ⟨f, -, rfl⟩
        exact ⟨(u, f), trivial, rfl⟩) h

/-- "What did `u` eat?" entails "Did `u` eat `f`?". -/
theorem whAte_entails_polar {σ : Set D0World} (u : Person) (f : Food)
    (h : MentionAll σ (whAte u)) : MentionAll σ (polarAte u f) :=
  mentionAll_mono
    (by rw [alt_polarAte, alt_whAte]
        rintro _ rfl
        exact ⟨f, trivial, rfl⟩) h

/-- "Who ate what?" entails every polar subquestion (her î(1) table,
    completed). -/
theorem q1_entails_polar {σ : Set D0World} (u : Person) (f : Food)
    (h : MentionAll σ q_1) : MentionAll σ (polarAte u f) :=
  whAte_entails_polar u f (q1_entails_whAte u h)

/-- Subquestions do not entail their superquestions: "Hilary ate both"
    completely answers `q_a` but decides nothing about Robin. -/
theorem qa_not_entails_q1 :
    ¬ ∀ σ : Set D0World, MentionAll σ q_a → MentionAll σ q_1 := by
  intro h
  have hma : MentionAll (hilaryBagels ∩ hilaryTofu : Set D0World) q_a :=
    mentionAll_whAte_iff.mpr (Or.inl subset_rfl)
  have := h _ hma _ (ate_mem_alt_q1 .robin .bagels)
  rcases this with h' | h' <;> exact absurd h' (by decide)

/-- "Did Hilary eat the bagels?" does not entail "What did Hilary eat?":
    the positive answer leaves the tofu alternative open. -/
theorem qai_not_entails_qa :
    ¬ ∀ σ : Set D0World, MentionAll σ q_ai → MentionAll σ q_a := by
  intro h
  have hma : MentionAll (hilaryBagels : Set D0World) q_ai := fun p hp => by
    rw [alt_polarAte, Set.mem_singleton_iff] at hp
    subst hp
    exact Or.inl subset_rfl
  have := h _ hma _ (ate_mem_alt_whAte .hilary .tofu)
  rcases this with h' | h' <;> exact absurd h' (by decide)

/-! ### Her (11): joint answers compose

The complete answers to the subquestions jointly are exactly the
complete answers to the parent. Partial answerhood is *not* transitive
in general (chaining loses completeness at the middle link), which is
why the stack invariant proofs below go direct rather than composing. -/

/-- Her (11a)/(11b): jointly answering the polar subquestions answers
    "What did `u` eat?". -/
theorem mentionAll_polar_pair_iff {σ : Set D0World} {u : Person} :
    MentionAll σ (polarAte u .bagels) ∧ MentionAll σ (polarAte u .tofu) ↔
      MentionAll σ (whAte u) := by
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [alt_whAte] at hp
    obtain ⟨f, -, rfl⟩ := hp
    cases f
    exacts [h1 _ (ate_mem_alt_polar u .bagels),
      h2 _ (ate_mem_alt_polar u .tofu)]
  · exact fun h => ⟨whAte_entails_polar u .bagels h,
      whAte_entails_polar u .tofu h⟩

/-- Her (11c): jointly answering "What did Hilary eat?" and "What did
    Robin eat?" answers "Who ate what?". -/
theorem mentionAll_whAte_pair_iff {σ : Set D0World} :
    MentionAll σ (whAte .hilary) ∧ MentionAll σ (whAte .robin) ↔
      MentionAll σ q_1 := by
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [alt_q_1] at hp
    obtain ⟨⟨u, f⟩, -, rfl⟩ := hp
    cases u
    exacts [h1 _ (ate_mem_alt_whAte .hilary f),
      h2 _ (ate_mem_alt_whAte .robin f)]
  · exact fun h => ⟨q1_entails_whAte .hilary h, q1_entails_whAte .robin h⟩

/-! ### Strategy of inquiry ((12)) -/

/-- Substrategy for `q_a`: pursue both polar subquestions about Hilary. -/
def strat_a : Strategy D0World := .node q_a [.leaf q_ai, .leaf q_aii]

/-- Substrategy for `q_b`: pursue both polar subquestions about Robin. -/
def strat_b : Strategy D0World := .node q_b [.leaf q_bi, .leaf q_bii]

/-- Roberts' strategy for the D₀ scenario:
    answer q_1 by answering q_a and q_b;
    answer q_a by answering q_ai and q_aii;
    answer q_b by answering q_bi and q_bii. -/
def strat_1 : Strategy D0World := .node q_1 [strat_a, strat_b]

/-- The strategy has 7 questions total. -/
theorem strat_1_numNodes : strat_1.numNodes = 7 := rfl

private theorem meet_polar_entails {u : Person} {f f' : Food}
    {Q : Question D0World} (hQ : ate u f ∈ alt Q) :
    (polarAte u f ⊓ polarAte u f').Entails Q := by
  intro r hr
  have hr' : r ∈ polarAte u f :=
    (Question.mem_inf.mp (Question.mem_props.mp (alt_subset_props _ hr))).1
  rcases Question.mem_which.mp hr' with rfl | ⟨e, he, hre⟩
  · exact ⟨ate u f, hQ, Set.empty_subset _⟩
  · rw [Set.mem_singleton_iff] at he
    exact ⟨ate u f, hQ, he ▸ hre⟩

/-- The Hilary substrategy is complete: jointly resolving `q_ai` and
    `q_aii` resolves `q_a`. -/
theorem strat_a_complete : strat_a.IsComplete :=
  .node_pair (meet_polar_entails (ate_mem_alt_whAte .hilary .bagels))
    (.leaf _) (.leaf _)

/-- The Robin substrategy is complete. -/
theorem strat_b_complete : strat_b.IsComplete :=
  .node_pair (meet_polar_entails (ate_mem_alt_whAte .robin .bagels))
    (.leaf _) (.leaf _)

/-- The whole D₀ strategy is complete: any joint resolution of `q_a` and
    `q_b` yields an alternative of `q_1` — the strategy-level face of her
    (11c). -/
theorem strat_1_complete : strat_1.IsComplete := by
  refine .node_pair ?_ strat_a_complete strat_b_complete
  intro r hr
  have hr' : r ∈ whAte .hilary :=
    (Question.mem_inf.mp (Question.mem_props.mp (alt_subset_props _ hr))).1
  rcases Question.mem_which.mp hr' with rfl | ⟨f, -, hrf⟩
  · exact ⟨hilaryBagels, ate_mem_alt_q1 .hilary .bagels, Set.empty_subset _⟩
  · exact ⟨ate .hilary f, ate_mem_alt_q1 .hilary f, hrf⟩

/-! ### QUD stack traces ((10g), (17)) -/

/-- Initial state: accept move 1, "Who ate what?". -/
def stack_0 : QUDStack D0World := [q_1]

/-- Pursue Hilary's food: accept q_a. -/
def stack_1 : QUDStack D0World := q_a :: stack_0

/-- Pursue Hilary+bagels: accept q_ai. -/
def stack_2 : QUDStack D0World := q_ai :: stack_1

/-- "Hilary ate the bagels" answers q_ai: retire it. -/
def stack_3 : QUDStack D0World := stack_2.tail

/-- Stack depths trace the discourse. -/
theorem stack_depths :
    stack_0.length = 1 ∧ stack_1.length = 2 ∧
    stack_2.length = 3 ∧ stack_3.length = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- After retiring q_ai, the immediate QUD is q_a. -/
theorem stack_3_qud : stack_3.head? = some q_a := rfl

/-! ### Stack well-formedness ((10g.iii)) -/

private theorem whAte_alts_partially_answer_q1 (u : Person) :
    ∀ a ∈ alt (whAte u), PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_whAte] at ha
  obtain ⟨f, -, rfl⟩ := ha
  exact ⟨ate u f, ate_mem_alt_q1 u f, Or.inl subset_rfl⟩

private theorem polar_alts_partially_answer_whAte (u : Person) (f : Food) :
    ∀ a ∈ alt (polarAte u f), PartiallyAnswers a (whAte u) := by
  intro a ha
  rw [alt_polarAte, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨ate u f, ate_mem_alt_whAte u f, Or.inl subset_rfl⟩

private theorem polar_alts_partially_answer_q1 (u : Person) (f : Food) :
    ∀ a ∈ alt (polarAte u f), PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_polarAte, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨ate u f, ate_mem_alt_q1 u f, Or.inl subset_rfl⟩

/-- The stack `[q_a, q_1]` satisfies Roberts' (10g.iii) in the trivial
    common ground: every complete answer to the subquestion partially
    answers the question below it. -/
theorem stack_1_wellFormed : QUDStack.WellFormed Set.univ stack_1 := by
  show QUDStack.WellFormed Set.univ (q_a :: stack_0)
  rw [QUDStack.wellFormed_cons]
  refine ⟨?_, QUDStack.wellFormed_singleton ..⟩
  intro lower hlow a ha
  simp only [stack_0, List.mem_singleton] at hlow
  subst hlow
  rw [Set.univ_inter]
  exact whAte_alts_partially_answer_q1 .hilary a ha

/-- The full three-question stack `[q_ai, q_a, q_1]` is well-formed. -/
theorem stack_2_wellFormed : QUDStack.WellFormed Set.univ stack_2 := by
  show QUDStack.WellFormed Set.univ (q_ai :: stack_1)
  rw [QUDStack.wellFormed_cons]
  refine ⟨?_, stack_1_wellFormed⟩
  intro lower hlow a ha
  rw [Set.univ_inter]
  rcases List.mem_cons.mp hlow with rfl | hlow
  · exact polar_alts_partially_answer_whAte .hilary .bagels a ha
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
    PartiallyAnswers (hilaryBagelsᶜ : Set D0World) q_ai :=
  ⟨hilaryBagels, ate_mem_alt_polar .hilary .bagels, Or.inr subset_rfl⟩

/-- "Hilary didn't eat bagels" partially answers "What did Hilary eat?" —
    it rules out the bagels alternative. -/
theorem neg_hilaryBagels_partiallyAnswers_qa :
    PartiallyAnswers (hilaryBagelsᶜ : Set D0World) q_a :=
  ⟨hilaryBagels, ate_mem_alt_whAte .hilary .bagels, Or.inr subset_rfl⟩

/-- "Hilary ate bagels" positively answers "Did Hilary eat the bagels?". -/
theorem hilaryBagels_partiallyAnswers_qai :
    PartiallyAnswers (hilaryBagels : Set D0World) q_ai :=
  ⟨hilaryBagels, ate_mem_alt_polar .hilary .bagels, Or.inl subset_rfl⟩

/-- "Hilary ate bagels" partially answers "Who ate what?" — it confirms
    one of its four alternatives. -/
theorem hilaryBagels_partiallyAnswers_q1 :
    PartiallyAnswers (hilaryBagels : Set D0World) q_1 :=
  ⟨hilaryBagels, ate_mem_alt_q1 .hilary .bagels, Or.inl subset_rfl⟩

/-! ### Relevance ((15)) -/

/-- "Hilary ate bagels" as a single-alternative declarative issue. -/
def hilaryBagels_assertion : Question D0World :=
  Question.declarative hilaryBagels

/-- "Hilary ate bagels" is relevant to move 1, "Who ate what?". -/
theorem hilaryBagels_relevant_to_q1 :
    Relevant hilaryBagels_assertion {q_1} := by
  refine ⟨hilaryBagels, ?_, q_1, rfl, hilaryBagels_partiallyAnswers_q1⟩
  show hilaryBagels ∈ alt (Question.declarative hilaryBagels)
  rw [alt_declarative]
  rfl

/-- The question `q_a` is relevant to `q_1` under the assertion-clause
    proxy: its bagels alternative confirms an alternative of `q_1`.
    (Roberts' own clause for interrogative moves is strategy membership,
    not partial answerhood.) -/
theorem qa_relevant_to_q1 : Relevant q_a {q_1} :=
  ⟨hilaryBagels, ate_mem_alt_whAte .hilary .bagels, q_1, rfl,
    hilaryBagels_partiallyAnswers_q1⟩

/-- "Hilary ate bagels" is relevant to the entire D₀ strategy: it
    partially answers `q_1` (the strategy's root). -/
theorem hilaryBagels_relevant_to_strategy :
    Relevant hilaryBagels_assertion {q | q ∈ strat_1.values} := by
  refine ⟨hilaryBagels, ?_, q_1, ?_, hilaryBagels_partiallyAnswers_q1⟩
  · show hilaryBagels ∈ alt (Question.declarative hilaryBagels)
    rw [alt_declarative]; rfl
  · simp [strat_1, strat_a, strat_b]

end Roberts2012
