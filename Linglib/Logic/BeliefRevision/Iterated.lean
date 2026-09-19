import Linglib.Core.Order.TotalPreorder
import Linglib.Logic.RankingFunction
import Mathlib.Order.Lattice.Nat

/-!
# Iterated belief revision

This file defines revision operators on epistemic states and the postulates of Darwiche and Pearl
for iterated belief revision, and proves their representation by total preorders on worlds.

Darwiche and Pearl revise *epistemic states* rather than belief sets. A state carries the worlds
its belief set admits together with a disposition to revise, and a revision operator sends a state
and a proposition, a set of worlds, to a new state. The postulates of Alchourrón, Gärdenfors and
Makinson, in the form Katsuno and Mendelzon gave them, transfer to states with syntax-irrelevance
weakened. An operator satisfies them iff a faithful assignment of total preorders to states
represents it, which means that the belief worlds of a state are its least worlds and that
revision by `μ` selects the least `μ`-worlds (Theorem 2). A state accepts `β` given `α` when
revising it by `α` yields a state that believes `β`. These conditional beliefs form a rational
consequence relation in the sense of Lehmann and Magidor, and the preorder of the state encodes
them. The iterated-revision postulates C1–C4 say which conditional beliefs a revision preserves.
Each of them, and Boutilier's postulate CB, is equivalent to a condition on how the preorder of a
state relates to the preorder of its revision (Theorems 3 and 4). The conditions are agreement on
the `μ`-worlds, agreement on the non-`μ`-worlds, preservation of strict and of weak rankings of a
`μ`-world over a non-`μ`-world, and agreement outside the revised belief set. Spohn's
conditionalisation of rankings, which makes the evidence one degree more plausible than it was
implausible, is represented by the rankings' own orderings and meets every postulate (Theorem 5).
On normalised rankings it is the revision of `RankingFunction`.

## Implementation notes

* Rankings are bare functions `W → ℕ`, as the paper relaxes normalisation so that revision by
  an unsatisfiable proposition yields an unsatisfiable belief set; `rank` of a proposition is
  the infimum of its worlds' ranks.
* The postulate of syntax-irrelevance holds by construction: propositions are sets of worlds
  and revision is a function of the state.
* The consistency postulate and the representation of C3 and C4 need least elements to exist,
  which a finite set of worlds, the paper's propositional setting, guarantees.

## References

* [A. Darwiche and J. Pearl, *On the Logic of Iterated Belief Revision*
  (1997)][darwiche-pearl-1997]
* [C. E. Alchourrón, P. Gärdenfors and D. Makinson, *On the Logic of Theory Change: Partial
  Meet Contraction and Revision Functions* (1985)][alchouron-gardenfors-makinson-1985]
* [H. Katsuno and A. O. Mendelzon, *Propositional Knowledge Base Revision and Minimal Change*
  (1991)][katsuno-mendelzon-1991]
* [D. Lehmann and M. Magidor, *What Does a Conditional Knowledge Base Entail?*
  (1992)][lehmann-magidor-1992]
* [W. Spohn, *Ordinal Conditional Functions: A Dynamic Theory of Epistemic States*
  (1988)][spohn-1988]
-/

namespace BeliefRevision

open Core.Order

variable {S W : Type*}

/-- A revision operator on epistemic states over the worlds `W` assigns each state the worlds
its belief set admits and revises a state by a proposition. -/
structure Revision (S W : Type*) where
  /-- The worlds admitted by the state's belief set. -/
  bel : S → Set W
  /-- Revision of a state by a proposition. -/
  revise : S → Set W → S

/-- Two total preorders agree on `d`. -/
def AgreesOn (p q : TotalPreorder W) (d : Set W) : Prop :=
  ∀ w ∈ d, ∀ v ∈ d, (p.le w v ↔ q.le w v)

/-- A `μ`-world strictly below a non-`μ`-world in `p` stays strictly below in `q`. -/
def PreservesLt (p q : TotalPreorder W) (μ : Set W) : Prop :=
  ∀ w ∈ μ, ∀ v ∉ μ, p.lt w v → q.lt w v

/-- A `μ`-world weakly below a non-`μ`-world in `p` stays weakly below in `q`. -/
def PreservesLe (p q : TotalPreorder W) (μ : Set W) : Prop :=
  ∀ w ∈ μ, ∀ v ∉ μ, p.le w v → q.le w v

section Decidable

variable [Fintype W] {p q : TotalPreorder W} [DecidableRel p.le] [DecidableRel q.le] {d : Set W}
  [DecidablePred (· ∈ d)]

instance : Decidable (AgreesOn p q d) := by unfold AgreesOn; infer_instance

instance : Decidable (PreservesLt p q d) := by unfold PreservesLt; infer_instance

instance : Decidable (PreservesLe p q d) := by unfold PreservesLe; infer_instance

end Decidable

theorem AgreesOn.least_eq {p q : TotalPreorder W} {d α : Set W} (h : AgreesOn p q d)
    (hα : α ⊆ d) : p.least α = q.least α := by
  ext w
  simp only [TotalPreorder.mem_least]
  exact ⟨fun ⟨hw, hle⟩ ↦ ⟨hw, fun y hy ↦ (h w (hα hw) y (hα hy)).1 (hle y hy)⟩,
    fun ⟨hw, hle⟩ ↦ ⟨hw, fun y hy ↦ (h w (hα hw) y (hα hy)).2 (hle y hy)⟩⟩

namespace Revision

variable (r : Revision S W)

/-- A revision operator satisfies the AGM postulates on epistemic states when it has success,
expansion when the evidence is consistent with the beliefs, consistency, superexpansion and
subexpansion. -/
structure IsAGM : Prop where
  success : ∀ Ψ μ, r.bel (r.revise Ψ μ) ⊆ μ
  expansion : ∀ Ψ μ, (r.bel Ψ ∩ μ).Nonempty → r.bel (r.revise Ψ μ) = r.bel Ψ ∩ μ
  consistency : ∀ Ψ μ, μ.Nonempty → (r.bel (r.revise Ψ μ)).Nonempty
  superexpansion : ∀ Ψ μ φ, r.bel (r.revise Ψ μ) ∩ φ ⊆ r.bel (r.revise Ψ (μ ∩ φ))
  subexpansion : ∀ Ψ μ φ, (r.bel (r.revise Ψ μ) ∩ φ).Nonempty →
    r.bel (r.revise Ψ (μ ∩ φ)) ⊆ r.bel (r.revise Ψ μ) ∩ φ

/-- An assignment of total preorders to states is faithful and represents `r` when the belief
worlds of a state are equally plausible and strictly more plausible than the others, and
revision selects the least worlds of the evidence. -/
structure Faithful (ord : S → TotalPreorder W) : Prop where
  equiv_of_mem : ∀ Ψ w v, w ∈ r.bel Ψ → v ∈ r.bel Ψ → (ord Ψ).equiv w v
  lt_of_mem : ∀ Ψ w v, w ∈ r.bel Ψ → v ∉ r.bel Ψ → (ord Ψ).lt w v
  bel_revise : ∀ Ψ μ, r.bel (r.revise Ψ μ) = (ord Ψ).least μ

/-- Postulate (C1) says that evidence entailed by later evidence is redundant. -/
def C1 : Prop :=
  ∀ Ψ μ α, α ⊆ μ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)

/-- Postulate (C2) says that evidence contradicted by later evidence is overridden. -/
def C2 : Prop :=
  ∀ Ψ μ α, α ⊆ μᶜ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)

/-- Postulate (C3) says that evidence implied by later evidence given the state is retained. -/
def C3 : Prop :=
  ∀ Ψ μ α, r.bel (r.revise Ψ α) ⊆ μ → r.bel (r.revise (r.revise Ψ μ) α) ⊆ μ

/-- Postulate (C4) says that evidence not contradicted by later evidence stays
uncontradicted. -/
def C4 : Prop :=
  ∀ Ψ μ α, ¬ r.bel (r.revise Ψ α) ⊆ μᶜ → ¬ r.bel (r.revise (r.revise Ψ μ) α) ⊆ μᶜ

/-- Boutilier's postulate (CB) says that evidence contradicted by later evidence is forgotten. -/
def CB : Prop :=
  ∀ Ψ μ α, r.bel (r.revise Ψ μ) ⊆ αᶜ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)

/-- Revising by a conjunction is conditioning the revision by the first conjunct on the
second, when that leaves something. -/
theorem IsAGM.revise_inter {r : Revision S W} (h : r.IsAGM) {Ψ : S} {μ φ : Set W}
    (hne : (r.bel (r.revise Ψ μ) ∩ φ).Nonempty) :
    r.bel (r.revise Ψ (μ ∩ φ)) = r.bel (r.revise Ψ μ) ∩ φ :=
  (h.subexpansion Ψ μ φ hne).antisymm (h.superexpansion Ψ μ φ)

/-- The state `Ψ` accepts `β` given `α`, and `β ∣ α` is a conditional belief of `Ψ`, when the
belief set of the revision of `Ψ` by `α` entails `β`. -/
def Accepts (Ψ : S) (α β : Set W) : Prop := r.bel (r.revise Ψ α) ⊆ β

/-- Postulate (C1) holds iff accommodating `μ` perturbs no conditional belief whose premise
entails `μ`. -/
theorem c1_iff_accepts : r.C1 ↔
    ∀ Ψ μ α β, α ⊆ μ → (r.Accepts (r.revise Ψ μ) α β ↔ r.Accepts Ψ α β) :=
  ⟨fun h Ψ μ α β hα ↦ by rw [Accepts, Accepts, h Ψ μ α hα], fun h Ψ μ α hα ↦
    ((h Ψ μ α _ hα).2 subset_rfl).antisymm ((h Ψ μ α _ hα).1 subset_rfl)⟩

/-- Postulate (C2) holds iff accommodating `μ` perturbs no conditional belief whose premise
contradicts `μ`. -/
theorem c2_iff_accepts : r.C2 ↔
    ∀ Ψ μ α β, α ⊆ μᶜ → (r.Accepts (r.revise Ψ μ) α β ↔ r.Accepts Ψ α β) :=
  ⟨fun h Ψ μ α β hα ↦ by rw [Accepts, Accepts, h Ψ μ α hα], fun h Ψ μ α hα ↦
    ((h Ψ μ α _ hα).2 subset_rfl).antisymm ((h Ψ μ α _ hα).1 subset_rfl)⟩

/-- Postulate (C3) holds iff the conditional belief `μ ∣ α` is never given up on accommodating
`μ`. -/
theorem c3_iff_accepts : r.C3 ↔ ∀ Ψ μ α, r.Accepts Ψ α μ → r.Accepts (r.revise Ψ μ) α μ :=
  Iff.rfl

/-- Postulate (C4) holds iff the conditional belief `μᶜ ∣ α` is never acquired on accommodating
`μ`. -/
theorem c4_iff_accepts : r.C4 ↔
    ∀ Ψ μ α, ¬ r.Accepts Ψ α μᶜ → ¬ r.Accepts (r.revise Ψ μ) α μᶜ :=
  Iff.rfl

variable {r}

/-- The conditional beliefs of a state of an AGM operator form a rational consequence relation.
Superexpansion gives Or, and subexpansion gives cautious and rational monotonicity. -/
theorem IsAGM.isRational_accepts (h : r.IsAGM) (Ψ : S) : Nonmonotonic.IsRational (r.Accepts Ψ) where
  refl α := h.success Ψ α
  rightWeakening hβ hβγ := hβ.trans hβγ
  and hβ hγ := Set.subset_inter hβ hγ
  or := by
    rintro α β γ hα hβ w hw
    rcases h.success Ψ _ hw with hwα | hwβ
    · exact hα (by
        simpa only [Set.union_inter_cancel_left] using h.superexpansion Ψ (α ∪ β) α ⟨hw, hwα⟩)
    · exact hβ (by
        simpa only [Set.union_inter_cancel_right] using h.superexpansion Ψ (α ∪ β) β ⟨hw, hwβ⟩)
  cautiousMonotonicity := by
    intro α β γ hβ hγ
    rcases (r.bel (r.revise Ψ α)).eq_empty_or_nonempty with he | ⟨w, hw⟩
    · have hα : α = ∅ := Set.not_nonempty_iff_eq_empty.1 fun hne ↦
        (h.consistency Ψ α hne).ne_empty he
      exact fun w hw ↦ absurd (h.success Ψ _ hw).1 (by simp [hα])
    · exact ((h.subexpansion Ψ α β ⟨w, hw, hβ hw⟩).trans Set.inter_subset_left).trans hγ
  rationalMonotonicity := by
    intro α β γ hγ hβ
    obtain ⟨w, hw, hwβ⟩ := Set.not_subset.1 hβ
    exact ((h.subexpansion Ψ α β ⟨w, hw, not_not.1 hwβ⟩).trans Set.inter_subset_left).trans hγ

/-! ### The representation theorem -/

/-- A faithfully represented operator satisfies the postulates. -/
theorem Faithful.isAGM [Finite W] {ord : S → TotalPreorder W} (h : r.Faithful ord) :
    r.IsAGM where
  success Ψ μ := by rw [h.bel_revise]; exact (ord Ψ).least_subset μ
  expansion Ψ μ hne := by
    rw [h.bel_revise]
    obtain ⟨u, hu, huμ⟩ := hne
    ext w
    constructor
    · rintro ⟨hwμ, hw⟩
      refine ⟨?_, hwμ⟩
      by_contra hwΨ
      exact (h.lt_of_mem Ψ u w hu hwΨ).2 (hw u huμ)
    · rintro ⟨hwΨ, hwμ⟩
      refine ⟨hwμ, fun y hy ↦ ?_⟩
      by_cases hyΨ : y ∈ r.bel Ψ
      · exact (h.equiv_of_mem Ψ w y hwΨ hyΨ).1
      · exact (h.lt_of_mem Ψ w y hwΨ hyΨ).1
  consistency Ψ μ hμ := by rw [h.bel_revise]; exact (ord Ψ).exists_isLeast hμ
  superexpansion Ψ μ φ := by
    rw [h.bel_revise, h.bel_revise]
    rintro w ⟨⟨hwμ, hw⟩, hwφ⟩
    exact ⟨⟨hwμ, hwφ⟩, fun y hy ↦ hw y hy.1⟩
  subexpansion Ψ μ φ hne := by
    rw [h.bel_revise] at hne
    rw [h.bel_revise, h.bel_revise]
    obtain ⟨u, ⟨huμ, hu⟩, huφ⟩ := hne
    rintro w ⟨⟨hwμ, hwφ⟩, hw⟩
    exact ⟨⟨hwμ, fun y hy ↦ (ord Ψ).le_trans _ _ _ (hw u ⟨huμ, huφ⟩) (hu y hy)⟩, hwφ⟩

/-- In the ordering an AGM operator induces on a state, `w` is at least as plausible as `v` when
`w` is believed or survives revision by the pair. -/
def IsAGM.ord (h : r.IsAGM) (Ψ : S) : TotalPreorder W where
  le w v := w ∈ r.bel Ψ ∨ w ∈ r.bel (r.revise Ψ {w, v})
  total := ⟨fun w v ↦ by
    obtain ⟨u, hu⟩ := h.consistency Ψ {w, v} ⟨w, by simp⟩
    rcases Set.mem_insert_iff.1 (h.success Ψ _ hu) with rfl | huv
    · exact Or.inl (Or.inr hu)
    · rw [Set.mem_singleton_iff] at huv
      subst huv
      exact Or.inr (Or.inr (by rwa [Set.pair_comm]))⟩
  isPreorder :=
    { refl := fun w ↦ by
        obtain ⟨u, hu⟩ := h.consistency Ψ {w, w} ⟨w, by simp⟩
        have := h.success Ψ _ hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at this
        subst this
        exact Or.inr hu
      trans := fun w₁ w₂ w₃ h₁₂ h₂₃ ↦ by
        by_cases hw₁ : w₁ ∈ r.bel Ψ
        · exact Or.inl hw₁
        right
        have h₁ : w₁ ∈ r.bel (r.revise Ψ {w₁, w₂}) := h₁₂.resolve_left hw₁
        have hw₂ : w₂ ∉ r.bel Ψ := fun hw₂ ↦ hw₁ (by
          rw [h.expansion Ψ {w₁, w₂} ⟨w₂, hw₂, by simp⟩] at h₁
          exact h₁.1)
        have h₂ : w₂ ∈ r.bel (r.revise Ψ {w₂, w₃}) := h₂₃.resolve_left hw₂
        set T : Set W := {w₁, w₂, w₃} with hT
        have key : ∀ φ ⊆ T, (r.bel (r.revise Ψ T) ∩ φ).Nonempty →
            r.bel (r.revise Ψ φ) = r.bel (r.revise Ψ T) ∩ φ := fun φ hφ hne ↦ by
          have := h.revise_inter hne
          rwa [Set.inter_eq_right.2 hφ] at this
        by_cases hne : (r.bel (r.revise Ψ T) ∩ {w₁, w₂}).Nonempty
        · have e := key {w₁, w₂} (by simp [hT, Set.pair_subset_iff]) hne
          have hw₁T : w₁ ∈ r.bel (r.revise Ψ T) := (e ▸ h₁).1
          have e' := key {w₁, w₃} (by simp [hT, Set.pair_subset_iff]) ⟨w₁, hw₁T, by simp⟩
          rw [e']
          exact ⟨hw₁T, by simp⟩
        · exfalso
          rw [Set.not_nonempty_iff_eq_empty] at hne
          have hnot : ∀ x ∈ r.bel (r.revise Ψ T), x ≠ w₁ ∧ x ≠ w₂ := fun x hx ↦
            ⟨fun e ↦ Set.eq_empty_iff_forall_notMem.1 hne x ⟨hx, by simp [e]⟩,
              fun e ↦ Set.eq_empty_iff_forall_notMem.1 hne x ⟨hx, by simp [e]⟩⟩
          obtain ⟨u, hu⟩ := h.consistency Ψ T ⟨w₁, by simp [hT]⟩
          have huT := h.success Ψ T hu
          simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at huT
          rcases huT with rfl | rfl | rfl
          · exact (hnot u hu).1 rfl
          · exact (hnot u hu).2 rfl
          · have e := key {w₂, u} (by simp [hT]) ⟨u, hu, by simp⟩
            exact (hnot w₂ (e ▸ h₂).1).2 rfl }

/-- The induced ordering is a faithful assignment representing the operator. -/
theorem IsAGM.faithful (h : r.IsAGM) : r.Faithful h.ord where
  equiv_of_mem _ _ _ hw hv := ⟨Or.inl hw, Or.inl hv⟩
  lt_of_mem Ψ w v hw hv := ⟨Or.inl hw, fun hvw ↦ hvw.elim hv fun hvw ↦ hv (by
    rw [h.expansion Ψ {v, w} ⟨w, hw, by simp⟩] at hvw
    exact hvw.1)⟩
  bel_revise Ψ μ := by
    ext w
    constructor
    · intro hw
      refine ⟨h.success Ψ μ hw, fun v hv ↦ Or.inr ?_⟩
      have := h.superexpansion Ψ μ {w, v} ⟨hw, by simp⟩
      rwa [Set.inter_eq_right.2 (Set.pair_subset (h.success Ψ μ hw) hv)] at this
    · rintro ⟨hwμ, hw⟩
      obtain ⟨u, hu⟩ := h.consistency Ψ μ ⟨w, hwμ⟩
      rcases hw u (h.success Ψ μ hu) with hwΨ | hwu
      · rw [h.expansion Ψ μ ⟨w, hwΨ, hwμ⟩]
        exact ⟨hwΨ, hwμ⟩
      · have := h.subexpansion Ψ μ {w, u} ⟨u, hu, by simp⟩
        rw [Set.inter_eq_right.2 (Set.pair_subset hwμ (h.success Ψ μ hu))] at this
        exact (this hwu).1

/-- The preorder of a state encodes its conditional beliefs, since `β` is accepted given `α`
exactly when the least `α`-worlds are `β`-worlds. -/
theorem Faithful.accepts_iff {ord : S → TotalPreorder W} (h : r.Faithful ord) {Ψ : S}
    {α β : Set W} : r.Accepts Ψ α β ↔ (ord Ψ).least α ⊆ β := by
  rw [Accepts, h.bel_revise]

/-- An operator satisfies the postulates iff a faithful assignment represents it
(Theorem 2). -/
theorem isAGM_iff [Finite W] : r.IsAGM ↔ ∃ ord, r.Faithful ord :=
  ⟨fun h ↦ ⟨_, h.faithful⟩, fun ⟨_, h⟩ ↦ h.isAGM⟩

/-! ### The iterated-revision postulates -/

/-- Revising by `μ` before `α ⊆ D Ψ μ` leaves the beliefs of revising by `α` alone iff the
preorders of a state and of its revision agree on `D Ψ μ`. -/
theorem Faithful.agreesAfter_iff {ord : S → TotalPreorder W} (h : r.Faithful ord)
    (D : S → Set W → Set W) :
    (∀ Ψ μ α, α ⊆ D Ψ μ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)) ↔
      ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) (D Ψ μ) := by
  constructor
  · intro hC Ψ μ w hw v hv
    have := hC Ψ μ {w, v} (Set.pair_subset hw hv)
    rw [h.bel_revise, h.bel_revise] at this
    rw [← (ord Ψ).mem_least_pair, ← (ord (r.revise Ψ μ)).mem_least_pair, this]
  · intro hCR Ψ μ α hα
    rw [h.bel_revise, h.bel_revise, (hCR Ψ μ).least_eq hα]

/-- Postulate (C1) holds iff the preorders of a state and of its revision by `μ` agree on the
`μ`-worlds, which is condition (CR1) of Theorem 4. -/
theorem Faithful.c1_iff {ord : S → TotalPreorder W} (h : r.Faithful ord) :
    r.C1 ↔ ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) μ :=
  h.agreesAfter_iff fun _ μ ↦ μ

/-- Postulate (C2) holds iff the preorders of a state and of its revision by `μ` agree on the
non-`μ`-worlds, which is condition (CR2) of Theorem 4. -/
theorem Faithful.c2_iff {ord : S → TotalPreorder W} (h : r.Faithful ord) :
    r.C2 ↔ ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) μᶜ :=
  h.agreesAfter_iff fun _ μ ↦ μᶜ

/-- Postulate (CB) holds iff the preorders of a state and of its revision agree outside the
revised belief set, which is condition (CBR) of Theorem 3. -/
theorem Faithful.cb_iff {ord : S → TotalPreorder W} (h : r.Faithful ord) :
    r.CB ↔ ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) (r.bel (r.revise Ψ μ))ᶜ := by
  rw [← h.agreesAfter_iff fun Ψ μ ↦ (r.bel (r.revise Ψ μ))ᶜ]
  exact forall₃_congr fun _ _ _ ↦ imp_congr_left Set.subset_compl_comm

/-- Postulate (C3) holds iff revision by `μ` preserves each strict ranking of a `μ`-world below a
non-`μ`-world, which is condition (CR3) of Theorem 4. -/
theorem Faithful.c3_iff [Finite W] {ord : S → TotalPreorder W} (h : r.Faithful ord) :
    r.C3 ↔ ∀ Ψ μ, PreservesLt (ord Ψ) (ord (r.revise Ψ μ)) μ := by
  constructor
  · intro hC Ψ μ w hw v hv hlt
    have h₁ : r.bel (r.revise Ψ {w, v}) ⊆ μ := by
      rw [h.bel_revise]
      rintro x ⟨hx, hxle⟩
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact hw
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact absurd (hxle w (by simp)) hlt.2
    have h₂ := hC Ψ μ {w, v} h₁
    rw [h.bel_revise, Set.pair_comm] at h₂
    have hnvw : ¬ (ord (r.revise Ψ μ)).le v w := fun hvw ↦
      hv (h₂ ((ord (r.revise Ψ μ)).mem_least_pair.2 hvw))
    exact ⟨((ord (r.revise Ψ μ)).le_total w v).resolve_right hnvw, hnvw⟩
  · intro hCR Ψ μ α hα
    rw [h.bel_revise] at hα ⊢
    intro w hw
    by_contra hwμ
    obtain ⟨u, hu⟩ := (ord Ψ).exists_isLeast ⟨w, hw.1⟩
    have hlt : (ord Ψ).lt u w :=
      ⟨hu.2 w hw.1, fun hwu ↦
        hwμ (hα ⟨hw.1, fun y hy ↦ (ord Ψ).le_trans _ _ _ hwu (hu.2 y hy)⟩)⟩
    exact (hCR Ψ μ u (hα hu) w hwμ hlt).2 (hw.2 u hu.1)

/-- Postulate (C4) holds iff revision by `μ` preserves each weak ranking of a `μ`-world below a
non-`μ`-world, which is condition (CR4) of Theorem 4. -/
theorem Faithful.c4_iff [Finite W] {ord : S → TotalPreorder W} (h : r.Faithful ord) :
    r.C4 ↔ ∀ Ψ μ, PreservesLe (ord Ψ) (ord (r.revise Ψ μ)) μ := by
  constructor
  · intro hC Ψ μ w hw v hv hle
    have h₁ : ¬ r.bel (r.revise Ψ {w, v}) ⊆ μᶜ := by
      rw [h.bel_revise, Set.not_subset]
      exact ⟨w, (ord Ψ).mem_least_pair.2 hle, fun hwc ↦ hwc hw⟩
    have h₂ := hC Ψ μ {w, v} h₁
    rw [h.bel_revise, Set.not_subset] at h₂
    obtain ⟨x, hx, hxμ⟩ := h₂
    rw [Set.mem_compl_iff, not_not] at hxμ
    rcases Set.mem_insert_iff.1 hx.1 with rfl | hx'
    · exact (ord _).mem_least_pair.1 hx
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact absurd hxμ hv
  · intro hCR Ψ μ α hα
    rw [h.bel_revise, Set.not_subset] at hα ⊢
    obtain ⟨u, hu, huμ⟩ := hα
    rw [Set.mem_compl_iff, not_not] at huμ
    obtain ⟨w, hw⟩ := (ord (r.revise Ψ μ)).exists_isLeast ⟨u, hu.1⟩
    by_cases hwμ : w ∈ μ
    · exact ⟨w, hw, fun hwc ↦ hwc hwμ⟩
    · refine ⟨u, ⟨hu.1, fun y hy ↦ (ord _).le_trans _ _ _ ?_ (hw.2 y hy)⟩, fun huc ↦ huc huμ⟩
      exact hCR Ψ μ u huμ w hwμ (hu.2 w hw.1)

end Revision

/-! ### Spohn's revision of rankings -/

section Spohn

variable (κ : W → ℕ) (μ : Set W)

/-- The rank of a proposition is the least rank of its worlds, and `0` for the empty
proposition. -/
noncomputable def rank : ℕ := sInf (κ '' μ)

theorem rank_le {w : W} (hw : w ∈ μ) : rank κ μ ≤ κ w :=
  Nat.sInf_le (Set.mem_image_of_mem κ hw)

theorem exists_rank_eq (hμ : μ.Nonempty) : ∃ w ∈ μ, κ w = rank κ μ :=
  Nat.sInf_mem (hμ.image κ)

theorem rank_eq_of {n : ℕ} (h₁ : ∃ w ∈ μ, κ w = n) (h₂ : ∀ w ∈ μ, n ≤ κ w) :
    rank κ μ = n := by
  obtain ⟨w, hw, e⟩ := h₁
  exact le_antisymm (e ▸ rank_le κ μ hw)
    (le_csInf ⟨n, w, hw, e⟩ (by rintro _ ⟨v, hv, rfl⟩; exact h₂ v hv))

open Classical in
/-- Spohn's revision shifts the `μ`-worlds down so that the best reach rank `0` and the others
up by one, which makes the evidence one degree more plausible than it was implausible. -/
noncomputable def spohn : W → ℕ := fun w ↦ if w ∈ μ then κ w - rank κ μ else κ w + 1

/-- Spohn's revision is an operator on rankings whose belief sets are the rank-`0` worlds. -/
noncomputable def spohnRevision (W : Type*) : Revision (W → ℕ) W where
  bel κ := {w | κ w = 0}
  revise := spohn

/-- A revision of rankings that conditions the `μ`-worlds on `μ` and leaves the rest
disbelieved is represented by the rankings' own orderings. -/
theorem faithful_lift {f : (W → ℕ) → Set W → W → ℕ}
    (hμ : ∀ κ μ, ∀ w ∈ μ, f κ μ w = κ w - rank κ μ) (hν : ∀ κ μ, ∀ w ∉ μ, 0 < f κ μ w) :
    Revision.Faithful ⟨fun κ ↦ {w | κ w = 0}, f⟩ (fun κ ↦ TotalPreorder.lift κ) where
  equiv_of_mem κ w v hw hv := by
    simp only [Set.mem_ofPred_eq] at hw hv
    exact ⟨by simp [hw, hv], by simp [hw, hv]⟩
  lt_of_mem κ w v hw hv := by
    simp only [Set.mem_ofPred_eq] at hw hv
    exact (TotalPreorder.lift_lt κ w v).2 (by omega)
  bel_revise κ μ := by
    ext w
    simp only [Set.mem_ofPred_eq, TotalPreorder.mem_least, TotalPreorder.lift_le]
    by_cases hw : w ∈ μ
    · rw [hμ κ μ w hw]
      constructor
      · intro h
        exact ⟨hw, fun y hy ↦ (Nat.sub_eq_zero_iff_le.1 h).trans (rank_le κ μ hy)⟩
      · rintro ⟨-, h⟩
        obtain ⟨u, hu, e⟩ := exists_rank_eq κ μ ⟨w, hw⟩
        exact Nat.sub_eq_zero_iff_le.2 (e ▸ h u hu)
    · exact ⟨fun h ↦ absurd h (hν κ μ w hw).ne', fun h ↦ absurd h.1 hw⟩

/-- Conditioning the `μ`-worlds on `μ` preserves their ordering. -/
theorem agreesOn_lift {f : (W → ℕ) → Set W → W → ℕ}
    (hμ : ∀ κ μ, ∀ w ∈ μ, f κ μ w = κ w - rank κ μ) :
    AgreesOn (TotalPreorder.lift κ) (TotalPreorder.lift (f κ μ)) μ := fun w hw v hv ↦ by
  simp only [TotalPreorder.lift_le, hμ κ μ w hw, hμ κ μ v hv]
  have h₁ := rank_le κ μ hw
  have h₂ := rank_le κ μ hv
  constructor <;> intro <;> omega

theorem spohn_of_mem {w : W} (hw : w ∈ μ) : spohn κ μ w = κ w - rank κ μ := by
  simp [spohn, hw]

theorem spohn_of_notMem {w : W} (hw : w ∉ μ) : spohn κ μ w = κ w + 1 := by
  simp [spohn, hw]

/-- The rankings' orderings faithfully represent Spohn's revision (Lemma 2). -/
theorem spohnRevision_faithful :
    (spohnRevision W).Faithful (fun κ ↦ TotalPreorder.lift κ) :=
  faithful_lift (fun κ μ _ hw ↦ spohn_of_mem κ μ hw)
    (fun κ μ _ hw ↦ by rw [spohn_of_notMem κ μ hw]; exact Nat.succ_pos _)

/-- Spohn's revision satisfies condition (CR1), the first part of Lemma 3. -/
theorem spohn_agreesOn : AgreesOn (TotalPreorder.lift κ) (TotalPreorder.lift (spohn κ μ)) μ :=
  agreesOn_lift κ μ fun κ μ _ hw ↦ spohn_of_mem κ μ hw

/-- Spohn's revision satisfies condition (CR2), the second part of Lemma 3. -/
theorem spohn_agreesOn_compl :
    AgreesOn (TotalPreorder.lift κ) (TotalPreorder.lift (spohn κ μ)) μᶜ := fun w hw v hv ↦ by
  simp only [TotalPreorder.lift_le, spohn_of_notMem κ μ hw, spohn_of_notMem κ μ hv]
  omega

/-- Spohn's revision satisfies condition (CR3), the third part of Lemma 3. -/
theorem spohn_preservesLt :
    PreservesLt (TotalPreorder.lift κ) (TotalPreorder.lift (spohn κ μ)) μ := fun w hw v hv h ↦ by
  rw [TotalPreorder.lift_lt] at h ⊢
  rw [spohn_of_mem κ μ hw, spohn_of_notMem κ μ hv]
  omega

/-- Spohn's revision satisfies condition (CR4), the fourth part of Lemma 3. -/
theorem spohn_preservesLe :
    PreservesLe (TotalPreorder.lift κ) (TotalPreorder.lift (spohn κ μ)) μ := fun w hw v hv h ↦ by
  rw [TotalPreorder.lift_le] at h ⊢
  rw [spohn_of_mem κ μ hw, spohn_of_notMem κ μ hv]
  omega

/-- Spohn's revision satisfies the AGM postulates (Theorem 5). -/
theorem spohnRevision_isAGM [Finite W] : (spohnRevision W).IsAGM :=
  spohnRevision_faithful.isAGM

/-- Spohn's revision satisfies (C1) (Theorem 5). -/
theorem spohnRevision_c1 : (spohnRevision W).C1 :=
  spohnRevision_faithful.c1_iff.2 spohn_agreesOn

/-- Spohn's revision satisfies (C2) (Theorem 5). -/
theorem spohnRevision_c2 : (spohnRevision W).C2 :=
  spohnRevision_faithful.c2_iff.2 spohn_agreesOn_compl

/-- Spohn's revision satisfies (C3) (Theorem 5). -/
theorem spohnRevision_c3 [Finite W] : (spohnRevision W).C3 :=
  spohnRevision_faithful.c3_iff.2 spohn_preservesLt

/-- Spohn's revision satisfies (C4) (Theorem 5). -/
theorem spohnRevision_c4 [Finite W] : (spohnRevision W).C4 :=
  spohnRevision_faithful.c4_iff.2 spohn_preservesLe

/-- On a normalised ranking, Spohn's revision is `RankingFunction.revise`. -/
theorem _root_.RankingFunction.revise_rank (κ : RankingFunction W) (A : Set W)
    (hA : A.Nonempty) : (κ.revise A hA).rank = spohn κ.rank A := by
  have hrank : ∀ B : Set W, B.Nonempty → (κ.rankSet B).toNat = rank κ.rank B := fun B hB ↦ by
    obtain ⟨u, hu, e⟩ := exists_rank_eq κ.rank B hB
    obtain ⟨v, hv, e'⟩ := κ.exists_rank_eq_rankSet hB
    rw [← e', ENat.toNat_natCast, ← e]
    exact le_antisymm (by exact_mod_cast e' ▸ κ.rankSet_le hu) (e ▸ rank_le κ.rank B hv)
  funext w
  by_cases hw : w ∈ A
  · rw [RankingFunction.revise, κ.conditionα_of_mem _ _ hw, spohn_of_mem κ.rank A hw,
      RankingFunction.aPart, hrank A hA]
  · rw [RankingFunction.revise, κ.conditionα_of_notMem _ _ hw, spohn_of_notMem κ.rank A hw,
      RankingFunction.aPart]
    have := κ.toNat_rankSet_le (A := Aᶜ) hw
    omega

/-- The conditional beliefs of a ranking function under Spohn's revision are the consequences
of its ranked model. -/
theorem _root_.RankingFunction.accepts_spohnRevision_iff (κ : RankingFunction W) {A B : Set W} :
    (spohnRevision W).Accepts κ.rank A B ↔ κ.Entails A B := by
  rw [spohnRevision_faithful.accepts_iff, κ.entails_iff_forall_least]
  exact ⟨fun h w hw hmin ↦ h ⟨hw, hmin⟩, fun h w hw ↦ h w hw.1 hw.2⟩

end Spohn

end BeliefRevision
