import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Entailment
import Linglib.Semantics.Questions.Resolution
import Linglib.Core.Data.Fintype.Sets
import Linglib.Discourse.QUD.Basic
import Linglib.Semantics.Focus.Interpretation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
# [roberts-2012] — Information Structure in Discourse

[roberts-2012] "Information structure in discourse: Towards an integrated
formal theory of pragmatics" (Semantics & Pragmatics 5(6): 1–69).

## Core Contributions Formalized

1. **QUD stack** — discourse state is an ordered stack of accepted, unanswered
   questions (`QUDStack`), not a single QUD.
2. **Strategy of inquiry** — questions decomposed into subquestions
   (`Strategy`), with completeness (`Strategy.IsComplete`) capturing her
   observation that jointly answering D₀'s subquestions answers the parent.
3. **Negative partial answerhood** — a proposition partially answers a question
   by ruling out an alternative, not just confirming one (`PartiallyAnswers`).
4. **Q-A congruence** — the focus alternatives of an answer equal the QUD
   alternatives (grounded by the Rooth–Hamblin type identity).

## D₀ Worked Example

Roberts' worked discourse D₀, on a model with two individuals (Hilary,
Robin) and two foods (bagels, tofu): 4 Boolean dimensions, 16 possible
worlds, 7 questions forming a strategy tree.

```
         q₁ (Who ate what?)
        /                            \
    q_a (What did Hilary eat?)    q_b (What did Robin eat?)
    /        \                    /        \
q_ai (H bagels?) q_aii (H tofu?) q_bi (R bagels?) q_bii (R tofu?)
```

## Representation

This file uses `Question` (Set-based, with `Question.Entails` from
`Entailment.lean`, `Question.PartiallyAnswers` from `Resolution.lean`, and
`Discourse.Relevant`, all reduced to decidable `Set` inclusions via
the `_polar_iff` lemmas). Non-polar issues are built via
`Question.ofList` and `⊓`; entailment for these goes through the lattice
route (`entails_of_le'`). Set-based partitions live in
`Semantics/Questions/Partition/` (`Question.IsPartition`, backed by
`Setoid.IsPartition`).
-/

namespace Roberts2012

open Question
open Discourse (QUDStack Strategy Relevant)

-- `decide` on `Set`-subset goals from the `_polar_iff` reductions.
attribute [local instance] Set.decidableSubsetOfFintype

-- ════════════════════════════════════════════════════
-- § D₀ World Space
-- ════════════════════════════════════════════════════

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

theorem card_D0World : Fintype.card D0World = 16 := by decide

-- ════════════════════════════════════════════════════
-- § Atomic Propositions (as Sets)
-- ════════════════════════════════════════════════════

/-- Hilary ate the bagels. -/
def hilaryBagels : Set D0World := {w | w.hb = true}
/-- Hilary ate the tofu. -/
def hilaryTofu : Set D0World := {w | w.ht = true}
/-- Robin ate the bagels. -/
def robinBagels : Set D0World := {w | w.rb = true}
/-- Robin ate the tofu. -/
def robinTofu : Set D0World := {w | w.rt = true}

instance : DecidablePred (· ∈ hilaryBagels) :=
  fun w => show Decidable (w.hb = true) from inferInstance
instance : DecidablePred (· ∈ (hilaryBagelsᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ hilaryBagels) from inferInstance
instance : DecidablePred (· ∈ hilaryTofu) :=
  fun w => show Decidable (w.ht = true) from inferInstance
instance : DecidablePred (· ∈ (hilaryTofuᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ hilaryTofu) from inferInstance
instance : DecidablePred (· ∈ robinBagels) :=
  fun w => show Decidable (w.rb = true) from inferInstance
instance : DecidablePred (· ∈ (robinBagelsᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ robinBagels) from inferInstance
instance : DecidablePred (· ∈ robinTofu) :=
  fun w => show Decidable (w.rt = true) from inferInstance
instance : DecidablePred (· ∈ (robinTofuᶜ : Set D0World)) :=
  fun w => show Decidable (¬ w ∈ robinTofu) from inferInstance

/-! ### Nontriviality lemmas (manual, one per atomic proposition) -/

theorem hb_ne_empty : hilaryBagels ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨true, false, false, false⟩ : D0World) ∈ hilaryBagels := rfl
  rw [h] at hmem; exact hmem.elim

theorem hb_ne_univ : hilaryBagels ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ hilaryBagels :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

theorem ht_ne_empty : hilaryTofu ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨false, true, false, false⟩ : D0World) ∈ hilaryTofu := rfl
  rw [h] at hmem; exact hmem.elim

theorem ht_ne_univ : hilaryTofu ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ hilaryTofu :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

theorem rb_ne_empty : robinBagels ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨false, false, true, false⟩ : D0World) ∈ robinBagels := rfl
  rw [h] at hmem; exact hmem.elim

theorem rb_ne_univ : robinBagels ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ robinBagels :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

theorem rt_ne_empty : robinTofu ≠ (∅ : Set D0World) := by
  intro h
  have hmem : (⟨false, false, false, true⟩ : D0World) ∈ robinTofu := rfl
  rw [h] at hmem; exact hmem.elim

theorem rt_ne_univ : robinTofu ≠ Set.univ := by
  intro h
  have hmem : (⟨false, false, false, false⟩ : D0World) ∈ robinTofu :=
    h.symm ▸ Set.mem_univ _
  exact Bool.false_ne_true hmem

-- ════════════════════════════════════════════════════
-- § Polar Questions (via `Question.polar`)
-- ════════════════════════════════════════════════════

/-- "Did Hilary eat the bagels?" -/
abbrev q_ai : Question D0World := Question.polar hilaryBagels

/-- "Did Hilary eat the tofu?" -/
abbrev q_aii : Question D0World := Question.polar hilaryTofu

/-- "Did Robin eat the bagels?" -/
abbrev q_bi : Question D0World := Question.polar robinBagels

/-- "Did Robin eat the tofu?" -/
abbrev q_bii : Question D0World := Question.polar robinTofu

-- ════════════════════════════════════════════════════
-- § Wh-Questions (via `Question.ofList`)
-- ════════════════════════════════════════════════════

/-- "What did Hilary eat?" — partition into 4 cells by ⟨hb, ht⟩.
    Bagels-only, tofu-only, both, neither. -/
def q_a : Question D0World := Question.ofList [
  {w | w.hb = true ∧ w.ht = false},
  {w | w.hb = false ∧ w.ht = true},
  {w | w.hb = true ∧ w.ht = true},
  {w | w.hb = false ∧ w.ht = false}
]

/-- "What did Robin eat?" — partition by ⟨rb, rt⟩. -/
def q_b : Question D0World := Question.ofList [
  {w | w.rb = true ∧ w.rt = false},
  {w | w.rb = false ∧ w.rt = true},
  {w | w.rb = true ∧ w.rt = true},
  {w | w.rb = false ∧ w.rt = false}
]

/-- "Who ate what?" — D₀'s move 1, rendered as the lattice meet of `q_a`
    and `q_b`. Roberts observes `Ans(a) ∩ Ans(b) = Ans(1)` for the
    independently given question (her (11c)); here the identification is
    definitional, so the root obligation of `strat_1_complete` is
    reflexivity rather than a substantive fact about D₀. -/
def q_1 : Question D0World := q_a ⊓ q_b

-- ════════════════════════════════════════════════════
-- § Internal: per-cell alternatives of q_a, q_b, q_1
-- (Shared infrastructure for negative-entailment, partial-answer,
--  and relevance theorems below.)
-- ════════════════════════════════════════════════════

/-- Hilary-bagels-only cell, the canonical witness in `alt q_a`. -/
private abbrev qa_c1 : Set D0World := {w | w.hb = true ∧ w.ht = false}

/-- Hilary-tofu-only cell. -/
private abbrev qa_c2 : Set D0World := {w | w.hb = false ∧ w.ht = true}

/-- Hilary-both cell. -/
private abbrev qa_c3 : Set D0World := {w | w.hb = true ∧ w.ht = true}

/-- Hilary-neither cell — used to construct atomic singletons of `alt q_1`. -/
private abbrev qa_c4 : Set D0World := {w | w.hb = false ∧ w.ht = false}

/-- Robin-bagels-only cell. -/
private abbrev qb_c1 : Set D0World := {w | w.rb = true ∧ w.rt = false}

/-- Robin-tofu-only cell. -/
private abbrev qb_c2 : Set D0World := {w | w.rb = false ∧ w.rt = true}

/-- Robin-both cell. -/
private abbrev qb_c3 : Set D0World := {w | w.rb = true ∧ w.rt = true}

/-- Robin-neither cell — paired with `qa_c4` to give the singleton
    `{⟨false, false, false, false⟩}`. -/
private abbrev qb_c4 : Set D0World := {w | w.rb = false ∧ w.rt = false}

/-- The "all-false" world — atomic alternative of `q_1`. -/
private abbrev w_zero : D0World := ⟨false, false, false, false⟩

/-- The Hilary-bagels-only, Robin-neither world — a second atomic
    alternative of `q_1`, outside `qa_c4`. -/
private abbrev w_hbOnly : D0World := ⟨true, false, false, false⟩

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

/-- `{v}` is an alternative of `q_1` when `ca` and `cb` are the unique
    `q_a`- and `q_b`-cells containing `v` and they intersect exactly in
    `v`. Maximality: any `q ⊇ {v}` in both prop-sets lies in `ca ∩ cb`. -/
private theorem singleton_mem_alt_q1_of {ca cb : Set D0World} {v : D0World}
    (hcaL : ca = qa_c1 ∨ ca = qa_c2 ∨ ca = qa_c3 ∨ ca = qa_c4)
    (hcbL : cb = qb_c1 ∨ cb = qb_c2 ∨ cb = qb_c3 ∨ cb = qb_c4)
    (hva : v ∈ ca) (hvb : v ∈ cb)
    (huniq_a : ∀ c, (c = qa_c1 ∨ c = qa_c2 ∨ c = qa_c3 ∨ c = qa_c4) →
      v ∈ c → c = ca)
    (huniq_b : ∀ c, (c = qb_c1 ∨ c = qb_c2 ∨ c = qb_c3 ∨ c = qb_c4) →
      v ∈ c → c = cb)
    (hcap : ∀ u ∈ ca, u ∈ cb → u = v) :
    ({v} : Set D0World) ∈ alt q_1 := by
  show ({v} : Set D0World) ∈ alt (q_a ⊓ q_b)
  rw [Question.mem_alt_inf_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ({v} : Set D0World) ∈ Question.ofList _
    rw [Question.mem_ofList]
    refine Or.inr ⟨ca, ?_, Set.singleton_subset_iff.mpr hva⟩
    rcases hcaL with rfl | rfl | rfl | rfl <;> simp
  · show ({v} : Set D0World) ∈ Question.ofList _
    rw [Question.mem_ofList]
    refine Or.inr ⟨cb, ?_, Set.singleton_subset_iff.mpr hvb⟩
    rcases hcbL with rfl | rfl | rfl | rfl <;> simp
  · rintro q ⟨hqa, hqb⟩ hsub
    have hqa' : q ∈ Question.ofList (W := D0World)
        [qa_c1, qa_c2, qa_c3, qa_c4] := hqa
    have hqb' : q ∈ Question.ofList (W := D0World)
        [qb_c1, qb_c2, qb_c3, qb_c4] := hqb
    rw [Question.mem_ofList] at hqa' hqb'
    have hvq : v ∈ q := hsub rfl
    rcases hqa' with rfl | ⟨ca', hca'L, hqca'⟩
    · exact hvq.elim
    rcases hqb' with rfl | ⟨cb', hcb'L, hqcb'⟩
    · exact hvq.elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hca'L hcb'L
    have hca'_eq : ca' = ca := huniq_a ca' hca'L (hqca' hvq)
    have hcb'_eq : cb' = cb := huniq_b cb' hcb'L (hqcb' hvq)
    intro u hu
    exact Set.mem_singleton_iff.mpr
      (hcap u (hca'_eq ▸ hqca' hu) (hcb'_eq ▸ hqcb' hu))

/-- The all-false singleton is an alternative of `q_1`: it is exactly
    `qa_c4 ∩ qb_c4`. -/
private theorem singleton_w_zero_in_alt_q1 :
    ({w_zero} : Set D0World) ∈ alt q_1 := by
  refine singleton_mem_alt_q1_of (Or.inr (Or.inr (Or.inr rfl)))
    (Or.inr (Or.inr (Or.inr rfl))) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ?_ ?_ (by decide)
  all_goals rintro c (rfl | rfl | rfl | rfl) hw <;>
    first | rfl | exact absurd hw (by decide)

/-- The Hilary-bagels-only, Robin-neither singleton is an alternative of
    `q_1`: it is exactly `qa_c1 ∩ qb_c4`. Witnesses partial answerhood
    for states containing `w_zero` (which `{w_zero}` cannot). -/
private theorem singleton_w_hbOnly_in_alt_q1 :
    ({w_hbOnly} : Set D0World) ∈ alt q_1 := by
  refine singleton_mem_alt_q1_of (Or.inl rfl)
    (Or.inr (Or.inr (Or.inr rfl))) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ?_ ?_ (by decide)
  all_goals rintro c (rfl | rfl | rfl | rfl) hw <;>
    first | rfl | exact absurd hw (by decide)

/-- The alternatives of `q_a` are exactly its four cells. -/
private theorem alt_qa_eq :
    alt q_a = {p | p ∈ [qa_c1, qa_c2, qa_c3, qa_c4]} := by
  apply Question.alt_ofList_of_pairwise_disjoint_nonempty
  · simp
  · rintro p₁ h₁ p₂ h₂ hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl | rfl | rfl <;>
      rcases h₂ with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hne
          | exact Set.disjoint_left.mpr (by decide)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact Set.Nonempty.ne_empty ⟨⟨true, false, false, false⟩, rfl, rfl⟩
    · exact Set.Nonempty.ne_empty ⟨⟨false, true, false, false⟩, rfl, rfl⟩
    · exact Set.Nonempty.ne_empty ⟨⟨true, true, false, false⟩, rfl, rfl⟩
    · exact Set.Nonempty.ne_empty ⟨⟨false, false, false, false⟩, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Question Entailment ([roberts-2012] Def. 8)
-- ════════════════════════════════════════════════════

-- Polar→polar entailment decides via `entails_polar_polar_iff`.

/-- `q_ai` entails itself (sanity check). -/
theorem qai_entails_qai : q_ai.Entails q_ai :=
  Entails.refl _

/-- `q_ai` does NOT entail `q_bi`: knowing whether Hilary ate bagels tells
    you nothing about whether Robin ate bagels (orthogonal polar questions). -/
theorem qai_not_entails_qbi : ¬ q_ai.Entails q_bi := by
  rw [entails_polar_polar_iff hb_ne_empty hb_ne_univ
        rb_ne_empty rb_ne_univ]
  decide

-- Wh→polar entailments now decide via `ofList_le_polar_of_classified`
-- (each cell of the wh-partition lies in `p` or `pᶜ` of the polar
-- question) composed with `entails_of_le'` (lattice → Roberts).
-- The move-1 entailments use `inf_le_left`/`inf_le_right`.

/-- "Who ate what?" entails "What did Hilary eat?" -/
theorem q1_entails_qa : q_1.Entails q_a :=
  entails_of_le' inf_le_left

/-- "Who ate what?" entails "What did Robin eat?" -/
theorem q1_entails_qb : q_1.Entails q_b :=
  entails_of_le' inf_le_right

/-- "What did Hilary eat?" entails "Did Hilary eat the bagels?" -/
theorem qa_entails_qai : q_a.Entails q_ai := by
  apply entails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwhb => Bool.false_ne_true (hw.1.symm.trans hwhb))
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwhb => Bool.false_ne_true (hw.1.symm.trans hwhb))

/-- "What did Hilary eat?" entails "Did Hilary eat the tofu?" -/
theorem qa_entails_qaii : q_a.Entails q_aii := by
  apply entails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (fun w hw hwht => Bool.false_ne_true (hw.2.symm.trans hwht))
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inr (fun w hw hwht => Bool.false_ne_true (hw.2.symm.trans hwht))

/-- "What did Robin eat?" entails "Did Robin eat the bagels?" -/
theorem qb_entails_qbi : q_b.Entails q_bi := by
  apply entails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwrb => Bool.false_ne_true (hw.1.symm.trans hwrb))
  · exact Or.inl (fun w hw => hw.1)
  · exact Or.inr (fun w hw hwrb => Bool.false_ne_true (hw.1.symm.trans hwrb))

/-- "What did Robin eat?" entails "Did Robin eat the tofu?" -/
theorem qb_entails_qbii : q_b.Entails q_bii := by
  apply entails_of_le'
  apply ofList_le_polar_of_classified
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (fun w hw hwrt => Bool.false_ne_true (hw.2.symm.trans hwrt))
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inl (fun w hw => hw.2)
  · exact Or.inr (fun w hw hwrt => Bool.false_ne_true (hw.2.symm.trans hwrt))

-- Entailment is asymmetric: subquestions do NOT entail their parents.

/-- q_a does NOT entail q_1. The witness `qa_c1 ∈ alt q_a` (Hilary-bagels-only)
    contains worlds with all four (rb, rt) combinations; no single q_b cell
    contains them all, so no `alt q_1` (which lies in some q_b cell) can
    extend `qa_c1`. -/
theorem qa_not_entails_q1 : ¬ q_a.Entails q_1 := by
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

/-- q_ai does NOT entail q_a. The witness `hilaryBagels ∈ alt q_ai` contains
    worlds with both `ht = true` and `ht = false`; no q_a cell (each fixing
    `ht`) can extend `hilaryBagels`. -/
theorem qai_not_entails_qa : ¬ q_ai.Entails q_a := by
  intro h
  have halt : hilaryBagels ∈ alt q_ai := by
    rw [show q_ai = Question.polar hilaryBagels from rfl,
        alt_polar_of_nontrivial hb_ne_empty hb_ne_univ]
    left; rfl
  obtain ⟨q, hq, hsub⟩ := h hilaryBagels halt
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
-- § Subquestions ([roberts-2012] Def. 8–9)
-- ════════════════════════════════════════════════════

/-- q_a is a subquestion of q_1. -/
theorem qa_sub_q1 : q_a.IsSubquestion q_1 := q1_entails_qa

/-- q_b is a subquestion of q_1. -/
theorem qb_sub_q1 : q_b.IsSubquestion q_1 := q1_entails_qb

-- ════════════════════════════════════════════════════
-- § Strategy of Inquiry ([roberts-2012] Def. 12)
-- ════════════════════════════════════════════════════

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
theorem strat_1_count : strat_1.numNodes = 7 := by
  simp [strat_1, strat_a, strat_b]

/-- The Hilary substrategy is complete: jointly resolving the polar
    subquestions `q_ai` and `q_aii` resolves the wh-question `q_a` they
    partition. Closes via `polar_inf_polar_le_ofList_of_corners`: the
    four corners (Hilary's bagels × tofu) are exactly the cells of `q_a`. -/
theorem strat_a_complete : strat_a.IsComplete := by
  refine .node_pair ?_ (.leaf _) (.leaf _)
  apply entails_of_le'
  show Question.polar hilaryBagels ⊓ Question.polar hilaryTofu ≤ q_a
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

/-- The Robin substrategy is complete (mirror of `strat_a_complete`). -/
theorem strat_b_complete : strat_b.IsComplete := by
  refine .node_pair ?_ (.leaf _) (.leaf _)
  apply entails_of_le'
  show Question.polar robinBagels ⊓ Question.polar robinTofu ≤ q_b
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

/-- The whole D₀ strategy is complete: both substrategies are, and the
    meet of their root questions is `q_1` by definition (see `q_1`). -/
theorem strat_1_complete : strat_1.IsComplete :=
  .node_pair (Entails.refl _) strat_a_complete strat_b_complete

-- ════════════════════════════════════════════════════
-- § QUD Stack Traces
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § Stack Well-Formedness ([roberts-2012] (10g.iii))
-- ════════════════════════════════════════════════════

/-- Each `q_a`-cell partially answers "Who ate what?": the cells missing
    `w_zero` refute the `{w_zero}` alternative; `qa_c4` refutes
    `{w_hbOnly}`. -/
private theorem qa_alts_partially_answer_q1 :
    ∀ a ∈ alt q_a, PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_qa_eq] at ha
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨{w_zero}, singleton_w_zero_in_alt_q1,
          Or.inr (Set.subset_compl_singleton_iff.mpr (by decide))⟩
      | exact ⟨{w_hbOnly}, singleton_w_hbOnly_in_alt_q1,
          Or.inr (Set.subset_compl_singleton_iff.mpr (by decide))⟩

/-- Each alternative of "Did Hilary eat the bagels?" partially answers
    "What did Hilary eat?". -/
private theorem qai_alts_partially_answer_qa :
    ∀ a ∈ alt q_ai, PartiallyAnswers a q_a := by
  intro a ha
  rw [alt_polar_of_nontrivial hb_ne_empty hb_ne_univ] at ha
  rcases ha with rfl | ha
  · exact ⟨qa_c2, by rw [alt_qa_eq]; simp, Or.inr (by decide)⟩
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨qa_c1, qa_c1_in_alt, Or.inr (by decide)⟩

/-- Each alternative of "Did Hilary eat the bagels?" partially answers
    "Who ate what?". -/
private theorem qai_alts_partially_answer_q1 :
    ∀ a ∈ alt q_ai, PartiallyAnswers a q_1 := by
  intro a ha
  rw [alt_polar_of_nontrivial hb_ne_empty hb_ne_univ] at ha
  rcases ha with rfl | ha
  · exact ⟨{w_zero}, singleton_w_zero_in_alt_q1,
      Or.inr (Set.subset_compl_singleton_iff.mpr (by decide))⟩
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨{w_hbOnly}, singleton_w_hbOnly_in_alt_q1,
      Or.inr (Set.subset_compl_singleton_iff.mpr (by decide))⟩

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

/-- [roberts-2012] warns against strengthening (10g.iii) to question
    entailment (her (8)): the D₀ stack `[q_a, q_1]` is well-formed
    (`stack_1_wellFormed`) yet fails the strengthened ordering, since
    `q_a` does not entail `q_1` (`qa_not_entails_q1`). -/
theorem stack_1_not_pairwise_entails :
    ¬ stack_1.Pairwise Question.Entails := by
  intro h
  exact qa_not_entails_q1
    ((List.pairwise_cons.mp h).1 q_1 (List.mem_singleton_self _))

-- ════════════════════════════════════════════════════
-- § Negative Partial Answerhood
-- ════════════════════════════════════════════════════

/-- "Hilary didn't eat bagels" (`hilaryBagelsᶜ`) negatively partially answers
    "Did Hilary eat bagels?" — it rules out the `hilaryBagels` alternative. -/
theorem neg_hb_partially_answers_qai :
    PartiallyAnswers (hilaryBagelsᶜ : Set D0World) q_ai := by
  rw [partiallyAnswers_polar_iff hb_ne_empty hb_ne_univ]
  decide

/-- "Hilary didn't eat bagels" also partially answers "What did Hilary eat?" —
    it rules out the `qa_c1` (Hilary-bagels-only) alternative. -/
theorem neg_hb_partially_answers_qa :
    PartiallyAnswers (hilaryBagelsᶜ : Set D0World) q_a := by
  refine ⟨qa_c1, qa_c1_in_alt, Or.inr ?_⟩
  intro w hw hw'
  exact hw hw'.1

-- ════════════════════════════════════════════════════
-- § Positive Partial Answerhood
-- ════════════════════════════════════════════════════

/-- "Hilary ate bagels" positively partially answers q_ai. -/
theorem hb_partially_answers_qai :
    PartiallyAnswers hilaryBagels q_ai := by
  rw [partiallyAnswers_polar_iff hb_ne_empty hb_ne_univ]
  decide

/-- "Hilary ate bagels" partially answers "Who ate what?" — it rules out
    the `{w_zero}` (all-false) alternative. -/
theorem hb_partially_answers_q1 :
    PartiallyAnswers hilaryBagels q_1 := by
  refine ⟨{w_zero}, singleton_w_zero_in_alt_q1, Or.inr ?_⟩
  intro w hw hw'
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  exact Bool.false_ne_true hw

-- ════════════════════════════════════════════════════
-- § Relevance ([roberts-2012] Def. 15)
-- ════════════════════════════════════════════════════

/-- "Hilary ate bagels" as a single-alternative declarative issue. -/
def hilaryBagels_assertion : Question D0World := Question.declarative hilaryBagels

/-- "Hilary ate bagels" is relevant to move 1, "Who ate what?". -/
theorem hilaryBagels_relevant_to_q1 :
    Relevant hilaryBagels_assertion {q_1} := by
  refine ⟨hilaryBagels, ?_, q_1, rfl, hb_partially_answers_q1⟩
  show hilaryBagels ∈ alt (Question.declarative hilaryBagels)
  rw [alt_declarative]
  rfl

/-- The question `q_a` is relevant to `q_1` under the assertion-clause
    proxy: its Hilary-bagels-only alternative `qa_c1` rules out the
    `{w_zero}` alternative of `q_1`. (Roberts' own clause for
    interrogative moves is strategy membership, not partial answerhood.) -/
theorem qa_relevant_to_q1 :
    Relevant q_a {q_1} := by
  refine ⟨qa_c1, qa_c1_in_alt, q_1, rfl, ?_⟩
  refine ⟨{w_zero}, singleton_w_zero_in_alt_q1, Or.inr ?_⟩
  intro w hw hw'
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  exact Bool.false_ne_true hw.1

/-- "Hilary ate bagels" is relevant to the entire D₀ strategy: it partially
    answers `q_1` (the strategy's root). -/
theorem hilaryBagels_relevant_to_strategy :
    Relevant hilaryBagels_assertion {q | q ∈ strat_1.values} := by
  refine ⟨hilaryBagels, ?_, q_1, ?_, hb_partially_answers_q1⟩
  · show hilaryBagels ∈ alt (Question.declarative hilaryBagels)
    rw [alt_declarative]; rfl
  · simp [strat_1, strat_a, strat_b]

-- ════════════════════════════════════════════════════
-- § Q-A Congruence / Focus Type Identity
-- ════════════════════════════════════════════════════

/-- Q-A congruence in Rooth's framework rests on the type identity
    `PropFocusValue W = Set (Set W)`: focus values and question
    denotations are both flat sets of propositions over `W`. The
    substrate-level bridge to `Question W` (inquisitive,
    downward-closed) lives in the focus-as-issue lift; see
    Focus/Interpretation.lean. -/
theorem focus_value_is_propositional_set :
    Focus.Interpretation.PropFocusValue D0World =
    Set (Set D0World) := rfl

end Roberts2012
