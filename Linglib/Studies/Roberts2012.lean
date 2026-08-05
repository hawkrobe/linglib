import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Entailment
import Linglib.Semantics.Questions.Resolution
import Linglib.Core.Data.Fintype.Sets
import Linglib.Discourse.QUD.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
# [roberts-2012] — Information Structure in Discourse

[roberts-2012] "Information structure in discourse: Towards an integrated
formal theory of pragmatics" (Semantics & Pragmatics 5(6): 1–69), her
worked discourse D₀: two individuals (Hilary, Robin), two foods (bagels,
tofu), 4 Boolean dimensions, 16 worlds, 7 questions forming a strategy
tree. The file traces the QUD stack through the discourse, verifies her
(10g.iii) well-formedness invariant, and proves her entailment table and
strategy-completeness observations.

```
         q₁ (Who ate what?)
        /                            \
    q_a (What did Hilary eat?)    q_b (What did Robin eat?)
    /        \                    /        \
q_ai (H bagels?) q_aii (H tofu?) q_bi (R bagels?) q_bii (R tofu?)
```

## Representation

Questions are her (1)/(2) **q-alternative sets**, built with
`Question.ofList`: `q_a` has the two overlapping alternatives *Hilary
ate bagels* and *Hilary ate tofu* (her (7)), `q_1` the four of her
(45), and the yes/no questions the singleton `{|α|}` she specifies —
the substrate's inquisitive `Question.polar` (alternatives `{p, pᶜ}`)
is the rival convention, not hers. Her derived complete-answer
partition (4) is the theorem `mentionAll_q_a_iff`. Question entailment
(8) is rendered as complete-answer transmission — `MentionAll σ q₁ →
MentionAll σ q₂` — because the alt-witnessed `Question.Entails`
coincides with (8) only for partition-shaped alternatives (see the
fidelity note in `Semantics/Questions/Entailment.lean`); answerhood
(3) is `Question.PartiallyAnswers`/`Question.MentionAll` verbatim.
-/

namespace Roberts2012

open Question
open Discourse (QUDStack Strategy Relevant)

-- `decide` on `Set`-subset goals over the finite world space.
attribute [local instance] Set.decidableSubsetOfFintype

/-! ### D₀ world space -/

/-- A world in the D₀ scenario: 4 independent Boolean facts. -/
structure D0World where
  hb : Bool   -- Hilary ate bagels
  ht : Bool   -- Hilary ate tofu
  rb : Bool   -- Robin ate bagels
  rt : Bool   -- Robin ate tofu
  deriving DecidableEq, BEq, Repr

/-- Finite enumeration of D0World via the canonical equivalence with
    `Bool × Bool × Bool × Bool`. -/
instance : Fintype D0World :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool)
    { toFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      invFun := fun w => (w.hb, w.ht, w.rb, w.rt)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-! ### Atomic propositions -/

/-- Hilary ate the bagels. -/
abbrev hilaryBagels : Set D0World := {w | w.hb = true}
/-- Hilary ate the tofu. -/
abbrev hilaryTofu : Set D0World := {w | w.ht = true}
/-- Robin ate the bagels. -/
abbrev robinBagels : Set D0World := {w | w.rb = true}
/-- Robin ate the tofu. -/
abbrev robinTofu : Set D0World := {w | w.rt = true}

/-! ### Questions as q-alternative sets ((1), (2), (7)) -/

/-- "Did Hilary eat the bagels?" — singleton q-alternative `{|α|}` per
    Roberts' yes/no convention. -/
def q_ai : Question D0World := Question.ofList [hilaryBagels]

/-- "Did Hilary eat the tofu?" -/
def q_aii : Question D0World := Question.ofList [hilaryTofu]

/-- "Did Robin eat the bagels?" -/
def q_bi : Question D0World := Question.ofList [robinBagels]

/-- "Did Robin eat the tofu?" -/
def q_bii : Question D0World := Question.ofList [robinTofu]

/-- "What did Hilary eat?" — the two q-alternatives of her (7),
    overlapping on the Hilary-ate-both worlds. -/
def q_a : Question D0World := Question.ofList [hilaryBagels, hilaryTofu]

/-- "What did Robin eat?" -/
def q_b : Question D0World := Question.ofList [robinBagels, robinTofu]

/-- "Who ate what?" — D₀'s move 1, with the four q-alternatives
    `{u ate u′}` of her (45). -/
def q_1 : Question D0World :=
  Question.ofList [hilaryBagels, hilaryTofu, robinBagels, robinTofu]

/-! ### Alternative enumerations

Every D₀ question draws its alternatives from the same four atoms —
the `{u ate u′}` of her (45) — which are pairwise ⊆-incomparable and
nonempty, so each enumeration is the antichain characterization
specialized to a sublist. -/

/-- The four atomic q-alternatives of her (45). -/
private def atoms : List (Set D0World) :=
  [hilaryBagels, hilaryTofu, robinBagels, robinTofu]

private theorem atoms_antichain :
    ∀ p₁ ∈ atoms, ∀ p₂ ∈ atoms, p₁ ≠ p₂ → ¬ p₁ ⊆ p₂ := by
  rintro p₁ h₁ p₂ h₂ hne
  simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl <;>
    rcases h₂ with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hne | decide

private theorem atoms_ne_empty : ∀ p ∈ atoms, p ≠ ∅ := by
  rintro p hp
  simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [Set.Nonempty.ne_empty ⟨⟨true, false, false, false⟩, rfl⟩,
    Set.Nonempty.ne_empty ⟨⟨false, true, false, false⟩, rfl⟩,
    Set.Nonempty.ne_empty ⟨⟨false, false, true, false⟩, rfl⟩,
    Set.Nonempty.ne_empty ⟨⟨false, false, false, true⟩, rfl⟩]

private theorem alt_ofList_atoms {L : List (Set D0World)} (hL : L ≠ [])
    (hsub : ∀ p ∈ L, p ∈ atoms) :
    alt (Question.ofList L) = {p | p ∈ L} :=
  alt_ofList_of_antichain_nonempty L hL
    (fun p₁ h₁ p₂ h₂ => atoms_antichain p₁ (hsub p₁ h₁) p₂ (hsub p₂ h₂))
    (fun p hp => atoms_ne_empty p (hsub p hp))

private theorem alt_q_ai : alt q_ai = {hilaryBagels} := by
  rw [show q_ai = Question.ofList [hilaryBagels] from rfl,
    alt_ofList_atoms (by simp) (by simp [atoms])]
  ext p; simp

private theorem alt_q_aii : alt q_aii = {hilaryTofu} := by
  rw [show q_aii = Question.ofList [hilaryTofu] from rfl,
    alt_ofList_atoms (by simp) (by simp [atoms])]
  ext p; simp

private theorem alt_q_bi : alt q_bi = {robinBagels} := by
  rw [show q_bi = Question.ofList [robinBagels] from rfl,
    alt_ofList_atoms (by simp) (by simp [atoms])]
  ext p; simp

private theorem alt_q_bii : alt q_bii = {robinTofu} := by
  rw [show q_bii = Question.ofList [robinTofu] from rfl,
    alt_ofList_atoms (by simp) (by simp [atoms])]
  ext p; simp

private theorem alt_q_a : alt q_a = {hilaryBagels, hilaryTofu} := by
  rw [show q_a = Question.ofList [hilaryBagels, hilaryTofu] from rfl,
    alt_ofList_atoms (by simp) (by simp [atoms])]
  ext p; simp

private theorem alt_q_b : alt q_b = {robinBagels, robinTofu} := by
  rw [show q_b = Question.ofList [robinBagels, robinTofu] from rfl,
    alt_ofList_atoms (by simp) (by simp [atoms])]
  ext p; simp

private theorem alt_q_1 :
    alt q_1 = {hilaryBagels, hilaryTofu, robinBagels, robinTofu} := by
  rw [show q_1 = Question.ofList atoms from rfl,
    alt_ofList_atoms (by simp [atoms]) (fun _ h => h)]
  ext p; simp [atoms]

/-! ### The complete-answer partition ((4)), derived -/

/-- Hilary-bagels-only cell. -/
private abbrev qa_c1 : Set D0World := hilaryBagels ∩ hilaryTofuᶜ
/-- Hilary-tofu-only cell. -/
private abbrev qa_c2 : Set D0World := hilaryBagelsᶜ ∩ hilaryTofu
/-- Hilary-both cell. -/
private abbrev qa_c3 : Set D0World := hilaryBagels ∩ hilaryTofu
/-- Hilary-neither cell. -/
private abbrev qa_c4 : Set D0World := hilaryBagelsᶜ ∩ hilaryTofuᶜ

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

/-- Her (4): the complete answers to `q_a` are exactly the states lying
    within one cell of the partition the q-alternatives induce. -/
theorem mentionAll_q_a_iff {σ : Set D0World} :
    MentionAll σ q_a ↔ σ ⊆ qa_c3 ∨ σ ⊆ qa_c1 ∨ σ ⊆ qa_c2 ∨ σ ⊆ qa_c4 := by
  constructor
  · intro h
    exact subset_corners_iff.mp
      ⟨h hilaryBagels (by rw [alt_q_a]; simp),
        h hilaryTofu (by rw [alt_q_a]; simp)⟩
  · intro h p hp
    obtain ⟨h1, h2⟩ := subset_corners_iff.mpr h
    rw [alt_q_a] at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    exacts [h1, h2]

/-! ### Question entailment ((3), (8))

Her (8) — answering `q₁` yields a complete answer to `q₂` — rendered as
complete-answer transmission over the (3b) answerhood predicate. -/

private theorem mentionAll_mono {σ : Set D0World} {P Q : Question D0World}
    (h : alt Q ⊆ alt P) (hP : MentionAll σ P) : MentionAll σ Q :=
  fun p hp => hP p (h hp)

/-- "Who ate what?" entails "What did Hilary eat?". -/
theorem q1_entails_qa {σ : Set D0World} (h : MentionAll σ q_1) :
    MentionAll σ q_a :=
  mentionAll_mono (by rw [alt_q_a, alt_q_1]; simp [Set.insert_subset_iff]) h

/-- "Who ate what?" entails "What did Robin eat?". -/
theorem q1_entails_qb {σ : Set D0World} (h : MentionAll σ q_1) :
    MentionAll σ q_b :=
  mentionAll_mono (by rw [alt_q_b, alt_q_1]; simp [Set.insert_subset_iff]) h

/-- "What did Hilary eat?" entails "Did Hilary eat the bagels?". -/
theorem qa_entails_qai {σ : Set D0World} (h : MentionAll σ q_a) :
    MentionAll σ q_ai :=
  mentionAll_mono (by rw [alt_q_ai, alt_q_a]; simp) h

/-- "What did Hilary eat?" entails "Did Hilary eat the tofu?". -/
theorem qa_entails_qaii {σ : Set D0World} (h : MentionAll σ q_a) :
    MentionAll σ q_aii :=
  mentionAll_mono (by rw [alt_q_aii, alt_q_a]; simp) h

/-- "What did Robin eat?" entails "Did Robin eat the bagels?". -/
theorem qb_entails_qbi {σ : Set D0World} (h : MentionAll σ q_b) :
    MentionAll σ q_bi :=
  mentionAll_mono (by rw [alt_q_bi, alt_q_b]; simp) h

/-- "What did Robin eat?" entails "Did Robin eat the tofu?". -/
theorem qb_entails_qbii {σ : Set D0World} (h : MentionAll σ q_b) :
    MentionAll σ q_bii :=
  mentionAll_mono (by rw [alt_q_bii, alt_q_b]; simp) h

/-- Her î(1) table, completed: "Who ate what?" entails every polar
    subquestion directly. -/
theorem q1_entails_qai {σ : Set D0World} (h : MentionAll σ q_1) :
    MentionAll σ q_ai :=
  mentionAll_mono (by rw [alt_q_ai, alt_q_1]; simp) h

theorem q1_entails_qaii {σ : Set D0World} (h : MentionAll σ q_1) :
    MentionAll σ q_aii :=
  mentionAll_mono (by rw [alt_q_aii, alt_q_1]; simp) h

theorem q1_entails_qbi {σ : Set D0World} (h : MentionAll σ q_1) :
    MentionAll σ q_bi :=
  mentionAll_mono (by rw [alt_q_bi, alt_q_1]; simp) h

theorem q1_entails_qbii {σ : Set D0World} (h : MentionAll σ q_1) :
    MentionAll σ q_bii :=
  mentionAll_mono (by rw [alt_q_bii, alt_q_1]; simp) h

/-- Subquestions do not entail their superquestions: `qa_c3` (Hilary ate
    both) completely answers `q_a` but decides nothing about Robin. -/
theorem qa_not_entails_q1 :
    ¬ ∀ σ : Set D0World, MentionAll σ q_a → MentionAll σ q_1 := by
  intro h
  have hma : MentionAll (qa_c3 : Set D0World) q_a :=
    mentionAll_q_a_iff.mpr (Or.inl subset_rfl)
  have := h _ hma robinBagels (by rw [alt_q_1]; simp)
  rcases this with h' | h' <;> exact absurd h' (by decide)

/-- "Did Hilary eat the bagels?" does not entail "What did Hilary eat?":
    the positive answer leaves the tofu alternative open. -/
theorem qai_not_entails_qa :
    ¬ ∀ σ : Set D0World, MentionAll σ q_ai → MentionAll σ q_a := by
  intro h
  have hma : MentionAll (hilaryBagels : Set D0World) q_ai := fun p hp => by
    rw [alt_q_ai, Set.mem_singleton_iff] at hp
    subst hp
    exact Or.inl subset_rfl
  have := h _ hma hilaryTofu (by rw [alt_q_a]; simp)
  rcases this with h' | h' <;> exact absurd h' (by decide)

/-! ### Her (11): joint answers compose

The complete answers to the subquestions jointly are exactly the
complete answers to the parent. Partial answerhood is *not* transitive
in general (chaining loses completeness at the middle link), which is
why the stack invariant proofs below go direct rather than composing. -/

/-- Her (11a): jointly answering the polar subquestions answers "What
    did Hilary eat?". -/
theorem mentionAll_qai_and_qaii_iff {σ : Set D0World} :
    MentionAll σ q_ai ∧ MentionAll σ q_aii ↔ MentionAll σ q_a := by
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [alt_q_a] at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact h1 _ (by rw [alt_q_ai]; rfl)
    · exact h2 _ (by rw [alt_q_aii]; rfl)
  · exact fun h => ⟨qa_entails_qai h, qa_entails_qaii h⟩

/-- Her (11b): the Robin mirror. -/
theorem mentionAll_qbi_and_qbii_iff {σ : Set D0World} :
    MentionAll σ q_bi ∧ MentionAll σ q_bii ↔ MentionAll σ q_b := by
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [alt_q_b] at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact h1 _ (by rw [alt_q_bi]; rfl)
    · exact h2 _ (by rw [alt_q_bii]; rfl)
  · exact fun h => ⟨qb_entails_qbi h, qb_entails_qbii h⟩

/-- Her (11c): jointly answering "What did Hilary eat?" and "What did
    Robin eat?" answers "Who ate what?". -/
theorem mentionAll_qa_and_qb_iff {σ : Set D0World} :
    MentionAll σ q_a ∧ MentionAll σ q_b ↔ MentionAll σ q_1 := by
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [alt_q_1] at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1 _ (by rw [alt_q_a]; simp)
    · exact h1 _ (by rw [alt_q_a]; simp)
    · exact h2 _ (by rw [alt_q_b]; simp)
    · exact h2 _ (by rw [alt_q_b]; simp)
  · exact fun h => ⟨q1_entails_qa h, q1_entails_qb h⟩

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

private theorem meet_singles_entails {p p' : Set D0World}
    {Q : Question D0World} (hpQ : p ∈ alt Q) :
    (Question.ofList [p] ⊓ Question.ofList [p']).Entails Q := by
  intro r hr
  have hr' : r ∈ Question.ofList [p] :=
    (Question.mem_inf.mp (Question.mem_props.mp (alt_subset_props _ hr))).1
  rcases Question.mem_ofList.mp hr' with rfl | ⟨c, hc, hrc⟩
  · exact ⟨p, hpQ, Set.empty_subset _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    exact ⟨p, hpQ, hc ▸ hrc⟩

/-- The Hilary substrategy is complete: jointly resolving `q_ai` and
    `q_aii` resolves `q_a`. -/
theorem strat_a_complete : strat_a.IsComplete :=
  .node_pair (meet_singles_entails (by rw [alt_q_a]; simp))
    (.leaf _) (.leaf _)

/-- The Robin substrategy is complete. -/
theorem strat_b_complete : strat_b.IsComplete :=
  .node_pair (meet_singles_entails (by rw [alt_q_b]; simp))
    (.leaf _) (.leaf _)

/-- The whole D₀ strategy is complete: any joint resolution of `q_a` and
    `q_b` yields an alternative of `q_1` — the strategy-level face of her
    (11c), now a substantive claim about independently defined
    questions. -/
theorem strat_1_complete : strat_1.IsComplete := by
  refine .node_pair ?_ strat_a_complete strat_b_complete
  intro r hr
  have hr' : r ∈ q_a :=
    (Question.mem_inf.mp (Question.mem_props.mp (alt_subset_props _ hr))).1
  rcases Question.mem_ofList.mp hr' with rfl | ⟨c, hc, hrc⟩
  · exact ⟨hilaryBagels, by rw [alt_q_1]; simp, Set.empty_subset _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨hilaryBagels, by rw [alt_q_1]; simp, hrc⟩
    · exact ⟨hilaryTofu, by rw [alt_q_1]; simp, hrc⟩

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

private theorem qa_alts_partially_answer_q1 :
    ∀ a ∈ alt q_a, PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_q_a] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact ⟨hilaryBagels, by rw [alt_q_1]; simp, Or.inl subset_rfl⟩
  · exact ⟨hilaryTofu, by rw [alt_q_1]; simp, Or.inl subset_rfl⟩

private theorem qai_alts_partially_answer_qa :
    ∀ a ∈ alt q_ai, PartiallyAnswers a q_a := by
  intro a ha
  rw [alt_q_ai, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨hilaryBagels, by rw [alt_q_a]; simp, Or.inl subset_rfl⟩

private theorem qai_alts_partially_answer_q1 :
    ∀ a ∈ alt q_ai, PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_q_ai, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨hilaryBagels, by rw [alt_q_1]; simp, Or.inl subset_rfl⟩

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
  exact qa_alts_partially_answer_q1 a ha

/-- The full three-question stack `[q_ai, q_a, q_1]` is well-formed. -/
theorem stack_2_wellFormed : QUDStack.WellFormed Set.univ stack_2 := by
  show QUDStack.WellFormed Set.univ (q_ai :: stack_1)
  rw [QUDStack.wellFormed_cons]
  refine ⟨?_, stack_1_wellFormed⟩
  intro lower hlow a ha
  rw [Set.univ_inter]
  rcases List.mem_cons.mp hlow with rfl | hlow
  · exact qai_alts_partially_answer_qa a ha
  · simp only [stack_0, List.mem_singleton] at hlow
    subst hlow
    exact qai_alts_partially_answer_q1 a ha

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
  ⟨hilaryBagels, by rw [alt_q_ai]; rfl, Or.inr subset_rfl⟩

/-- "Hilary didn't eat bagels" partially answers "What did Hilary eat?" —
    it rules out the bagels alternative. -/
theorem neg_hilaryBagels_partiallyAnswers_qa :
    PartiallyAnswers (hilaryBagelsᶜ : Set D0World) q_a :=
  ⟨hilaryBagels, by rw [alt_q_a]; simp, Or.inr subset_rfl⟩

/-- "Hilary ate bagels" positively answers "Did Hilary eat the bagels?". -/
theorem hilaryBagels_partiallyAnswers_qai :
    PartiallyAnswers (hilaryBagels : Set D0World) q_ai :=
  ⟨hilaryBagels, by rw [alt_q_ai]; rfl, Or.inl subset_rfl⟩

/-- "Hilary ate bagels" partially answers "Who ate what?" — it confirms
    one of its four alternatives. -/
theorem hilaryBagels_partiallyAnswers_q1 :
    PartiallyAnswers (hilaryBagels : Set D0World) q_1 :=
  ⟨hilaryBagels, by rw [alt_q_1]; simp, Or.inl subset_rfl⟩

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
  ⟨hilaryBagels, by rw [alt_q_a]; simp, q_1, rfl,
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
