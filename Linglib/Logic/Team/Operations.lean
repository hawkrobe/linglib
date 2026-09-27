module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Logic.Team.Algebra
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# Team operations: the connectives of team semantics as operations on team properties

A team-semantic connective takes the team properties defined by its arguments to the team
property defined by the compound. This file defines those operations on `TeamProperty α`
once, so that each team logic's evaluation is a fold over them and each closure fact about
a connective is proved once rather than per logic: the pointwise lift `flat` of a property
of points, the tensor (split) disjunction `tensor`, the non-emptiness atom `ne`, and the
modalities — the flat `poss`/`nec` over successor sets ([aloni-2022]), the single-witness
`possWitness`/`necImage` of modal dependence logic ([vaananen-2008]), and the lax
`possLax` of modal inclusion logic ([anttila-haggblom-yang-2024]).

Two families of results follow [anttila-2021]. The closure lemmas are his Propositions
2.2.8 and 2.2.10 stated per connective: `tensor` preserves downward closure, union closure,
the empty-team property and, given union closure, convexity ([anttila-2025] Proposition
3.3.1); the flat modalities and every `flat` property are flat outright. The homomorphism
lemmas are the content of his Proposition 2.2.16: `flat` commutes with conjunction, tensor
disjunction and the flat modalities, so a formula built from flat atoms by these connectives
defines a flat property, pointwise its classical truth.

## Main definitions

* `Team.flat`, `Team.tensor`, `Team.ne`, `Team.poss`, `Team.nec` — the BSML connectives.
* `Team.possWitness`, `Team.necImage`, `Team.possLax` — the modal clauses of modal
  dependence and inclusion logic.

## Main results

* `Team.isFlat_flat`, `Team.IsLowerSet.tensor`, `Team.SupClosed.tensor`,
  `Team.empty_mem_tensor`, `Team.OrdConnected.tensor` — closure per connective.
* `Team.flat_inter`, `Team.tensor_flat`, `Team.poss_flat`, `Team.nec_flat` — `flat` is a
  homomorphism.

## Implementation notes

Conjunction is set intersection, so it needs no operation of its own: mathlib's
`IsLowerSet.inter`, `SupClosed.inter` and `Set.OrdConnected.inter` are its closure lemmas.
The bilateral anti-support of `ne` is the singleton property `{∅}`. Membership in each
operation unfolds definitionally (`mem_flat`, `mem_tensor`, …), so a logic's evaluation
clauses written through these operations are the same propositions as before.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal
  Logics
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
* [anttila-haggblom-yang-2024] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [vaananen-2008] Väänänen, Modal Dependence Logic
-/

@[expose] public section

namespace Team

variable {α : Type*} [DecidableEq α]

/-! ### The connectives -/

/-- The pointwise lift of a property of points: the teams all of whose points satisfy `p`.
    Atoms, and every flat connective, define such properties. -/
def flat (p : α → Prop) : TeamProperty α := {t | ∀ x ∈ t, p x}

/-- Tensor (split) disjunction: the teams that split into a part in `P` and a part in `Q`. -/
def tensor (P Q : TeamProperty α) : TeamProperty α :=
  {t | ∃ t₁ t₂, splitsAs t t₁ t₂ ∧ t₁ ∈ P ∧ t₂ ∈ Q}

/-- The non-emptiness atom `NE`: the non-empty teams. -/
def ne : TeamProperty α := {t | t.Nonempty}

/-- The flat possibility modality over successor sets `R`: every point of the team has a
    non-empty subteam of its successors in `P`. -/
def poss (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  flat fun x ↦ ∃ s ⊆ R x, s.Nonempty ∧ s ∈ P

/-- The flat necessity modality: the successor set of every point of the team is in `P`. -/
def nec (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  flat fun x ↦ R x ∈ P

/-- The single-witness possibility modality of modal dependence logic ([vaananen-2008]
    clause (T8)): one team `Y` in `P` supplies a successor to every point. -/
def possWitness (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  {t | ∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P}

/-- The image necessity modality ([vaananen-2008] clause (T9)): the union of the successor
    sets is in `P`. -/
def necImage (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  {t | t.biUnion R ∈ P}

/-- The lax possibility modality of modal inclusion logic ([anttila-haggblom-yang-2024]
    Definition 2.2): a team of successors in `P` that reaches every point. -/
def possLax (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  {t | ∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P}

variable {p q : α → Prop} {P Q : TeamProperty α} {R : α → Finset α} {t : Finset α}

omit [DecidableEq α] in
@[simp] theorem mem_flat : t ∈ flat p ↔ ∀ x ∈ t, p x := Iff.rfl

@[simp] theorem mem_tensor :
    t ∈ tensor P Q ↔ ∃ t₁ t₂, splitsAs t t₁ t₂ ∧ t₁ ∈ P ∧ t₂ ∈ Q := Iff.rfl

omit [DecidableEq α] in
@[simp] theorem mem_ne : t ∈ (ne : TeamProperty α) ↔ t.Nonempty := Iff.rfl

omit [DecidableEq α] in
@[simp] theorem mem_poss : t ∈ poss R P ↔ ∀ x ∈ t, ∃ s ⊆ R x, s.Nonempty ∧ s ∈ P := Iff.rfl

omit [DecidableEq α] in
@[simp] theorem mem_nec : t ∈ nec R P ↔ ∀ x ∈ t, R x ∈ P := Iff.rfl

omit [DecidableEq α] in
@[simp] theorem mem_possWitness :
    t ∈ possWitness R P ↔ ∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P := Iff.rfl

@[simp] theorem mem_necImage : t ∈ necImage R P ↔ t.biUnion R ∈ P := Iff.rfl

@[simp] theorem mem_possLax :
    t ∈ possLax R P ↔ ∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P := Iff.rfl

/-! ### Decidability -/

instance flat.instDecidableMem [DecidablePred p] (t : Finset α) : Decidable (t ∈ flat p) :=
  Finset.decidableDforallFinset

instance tensor.instDecidableMem [Fintype α] (P Q : TeamProperty α) [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ Q)] (t : Finset α) : Decidable (t ∈ tensor P Q) :=
  inferInstanceAs (Decidable (∃ t₁ t₂, splitsAs t t₁ t₂ ∧ t₁ ∈ P ∧ t₂ ∈ Q))

instance ne.instDecidableMem (t : Finset α) : Decidable (t ∈ (ne : TeamProperty α)) :=
  inferInstanceAs (Decidable t.Nonempty)

instance poss.instDecidableMem [Fintype α] (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ poss R P) :=
  inferInstanceAs (Decidable (∀ x ∈ t, ∃ s ⊆ R x, s.Nonempty ∧ s ∈ P))

instance nec.instDecidableMem (R : α → Finset α) (P : TeamProperty α) [DecidablePred (· ∈ P)]
    (t : Finset α) : Decidable (t ∈ nec R P) :=
  inferInstanceAs (Decidable (∀ x ∈ t, R x ∈ P))

instance possWitness.instDecidableMem [Fintype α] (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ possWitness R P) :=
  inferInstanceAs (Decidable (∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P))

instance necImage.instDecidableMem (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ necImage R P) :=
  inferInstanceAs (Decidable (t.biUnion R ∈ P))

instance possLax.instDecidableMem [Fintype α] (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ possLax R P) :=
  inferInstanceAs (Decidable (∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P))

/-! ### Flat properties -/

omit [DecidableEq α] in
theorem isFlat_flat (p : α → Prop) : IsFlat (flat p) := fun t ↦ by simp

theorem isLowerSet_flat (p : α → Prop) : IsLowerSet (flat p) := (isFlat_flat p).isLowerSet

theorem supClosed_flat (p : α → Prop) : SupClosed (flat p) := (isFlat_flat p).supClosed

theorem empty_mem_flat (p : α → Prop) : ∅ ∈ flat p := (isFlat_flat p).empty_mem

theorem ordConnected_flat (p : α → Prop) : (flat p).OrdConnected := (isFlat_flat p).ordConnected

/-! ### The non-emptiness atom -/

theorem supClosed_ne : SupClosed (ne : TeamProperty α) := by
  intro s hs t _
  exact hs.mono Finset.subset_union_left

omit [DecidableEq α] in
theorem ordConnected_ne : (ne : TeamProperty α).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro s hs u _ _ t ht
  exact hs.mono ht.1

omit [DecidableEq α] in
theorem isLowerSet_singleton_empty : IsLowerSet ({∅} : TeamProperty α) := by
  intro s t hts hs
  rw [Set.mem_singleton_iff] at hs ⊢
  exact Finset.subset_empty.mp (hs ▸ hts)

theorem supClosed_singleton_empty : SupClosed ({∅} : TeamProperty α) := by
  intro s hs t ht
  rw [Set.mem_singleton_iff] at hs ht ⊢
  rw [hs, ht]
  exact sup_idem _

omit [DecidableEq α] in
theorem ordConnected_singleton_empty : ({∅} : TeamProperty α).OrdConnected :=
  isLowerSet_singleton_empty.ordConnected

/-! ### Tensor disjunction (Anttila Proposition 2.2.8) -/

theorem _root_.IsLowerSet.tensor (hP : IsLowerSet P) (hQ : IsLowerSet Q) :
    IsLowerSet (tensor P Q) := by
  rintro s t hts ⟨t₁, t₂, hu, h₁, h₂⟩
  refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, hP Finset.inter_subset_left h₁, hQ Finset.inter_subset_left h₂⟩
  show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
  rw [← Finset.union_inter_distrib_right, hu, Finset.inter_eq_right.mpr hts]

theorem _root_.SupClosed.tensor (hP : SupClosed P) (hQ : SupClosed Q) : SupClosed (tensor P Q) := by
  rintro s ⟨s₁, s₂, hs, hs₁, hs₂⟩ t ⟨t₁, t₂, ht, ht₁, ht₂⟩
  refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, hP hs₁ ht₁, hQ hs₂ ht₂⟩
  show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
  rw [Finset.union_union_union_comm, hs, ht]

theorem empty_mem_tensor (hP : ∅ ∈ P) (hQ : ∅ ∈ Q) : ∅ ∈ tensor P Q :=
  ⟨∅, ∅, Finset.union_empty ∅, hP, hQ⟩

/-- Tensor disjunction preserves convexity when both disjuncts are union-closed
    ([anttila-2025] Proposition 3.3.1): the middle team `t` of `s ⊆ t ⊆ u` splits as
    `(sᵢ ∪ uᵢ) ∩ t`, each part lying between `sᵢ` and `sᵢ ∪ uᵢ`. -/
theorem _root_.Set.OrdConnected.tensor (hP : P.OrdConnected) (hQ : Q.OrdConnected) (hP' : SupClosed P)
    (hQ' : SupClosed Q) : (tensor P Q).OrdConnected := by
  rw [Set.ordConnected_iff]
  rintro s ⟨s₁, s₂, hs, hs₁, hs₂⟩ u ⟨u₁, u₂, hu, hu₁, hu₂⟩ - t ⟨hst, htu⟩
  have hs₁t : s₁ ⊆ t := (splitsAs_left_subset hs).trans hst
  have hs₂t : s₂ ⊆ t := (splitsAs_right_subset hs).trans hst
  refine ⟨(s₁ ∪ u₁) ∩ t, (s₂ ∪ u₂) ∩ t, ?_,
    hP.out hs₁ (hP' hs₁ hu₁)
      ⟨Finset.subset_inter Finset.subset_union_left hs₁t, Finset.inter_subset_left⟩,
    hQ.out hs₂ (hQ' hs₂ hu₂)
      ⟨Finset.subset_inter Finset.subset_union_left hs₂t, Finset.inter_subset_left⟩⟩
  show ((s₁ ∪ u₁) ∩ t) ∪ ((s₂ ∪ u₂) ∩ t) = t
  rw [← Finset.union_inter_distrib_right, Finset.union_union_union_comm, hs, hu,
    Finset.union_eq_right.mpr (hst.trans htu), Finset.inter_eq_right.mpr htu]

/-! ### Preimages along union-preserving maps

A clause of the form "`f s` is in `P`" for a map `f` of teams — the image modalities, and the
universal-extension clauses of quantified logics — is the preimage `f ⁻¹' P`. Its closure
follows from that of `P` when `f` is monotone (mathlib's `IsLowerSet.preimage`), preserves
unions, or preserves `∅`. -/

theorem _root_.SupClosed.preimage_of_map_union {β : Type*} [DecidableEq β]
    {P : TeamProperty β} {f : Finset α → Finset β} (hP : SupClosed P)
    (hf : ∀ s t, f (s ∪ t) = f s ∪ f t) : SupClosed (f ⁻¹' P) := by
  intro s hs t ht
  show f (s ∪ t) ∈ P
  rw [hf]
  exact hP hs ht

omit [DecidableEq α] in
theorem empty_mem_preimage {β : Type*} {P : TeamProperty β} {f : Finset α → Finset β}
    (hP : ∅ ∈ P) (hf : f ∅ = ∅) : ∅ ∈ f ⁻¹' P := by
  show f ∅ ∈ P
  rw [hf]
  exact hP

/-! ### The modalities of dependence and inclusion logic -/

omit [DecidableEq α] in
theorem isLowerSet_possWitness (R : α → Finset α) (P : TeamProperty α) :
    IsLowerSet (possWitness R P) := by
  rintro s t hts ⟨Y, hY, hYP⟩
  exact ⟨Y, fun x hx ↦ hY x (hts hx), hYP⟩

theorem _root_.SupClosed.possWitness (hP : SupClosed P) : SupClosed (possWitness R P) := by
  rintro s ⟨Y, hY, hYP⟩ t ⟨Z, hZ, hZP⟩
  refine ⟨Y ∪ Z, fun x hx ↦ ?_, hP hYP hZP⟩
  rcases Finset.mem_union.mp hx with h | h
  · exact (hY x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_left _ hy, hr⟩
  · exact (hZ x h).imp fun _ ⟨hz, hr⟩ ↦ ⟨Finset.mem_union_right _ hz, hr⟩

omit [DecidableEq α] in
theorem empty_mem_possWitness (hP : ∅ ∈ P) : ∅ ∈ possWitness R P :=
  ⟨∅, fun _ hx ↦ absurd hx (Finset.notMem_empty _), hP⟩

theorem _root_.IsLowerSet.necImage (hP : IsLowerSet P) : IsLowerSet (necImage R P) := by
  intro s t hts h
  exact hP (Finset.biUnion_subset_biUnion_of_subset_left R hts) h

theorem _root_.SupClosed.necImage (hP : SupClosed P) : SupClosed (necImage R P) := by
  intro s hs t ht
  show (s ∪ t).biUnion R ∈ P
  rw [Finset.union_biUnion]
  exact hP hs ht

theorem empty_mem_necImage (hP : ∅ ∈ P) : ∅ ∈ necImage R P := by
  show (∅ : Finset α).biUnion R ∈ P
  rw [Finset.biUnion_empty]
  exact hP

theorem _root_.IsLowerSet.possLax (hP : IsLowerSet P) : IsLowerSet (possLax R P) := by
  rintro s t hts ⟨S, -, hS, hSP⟩
  refine ⟨S.filter (· ∈ t.biUnion R), fun _ hy ↦ (Finset.mem_filter.mp hy).2,
    fun x hx ↦ ?_, hP (Finset.filter_subset _ _) hSP⟩
  exact (hS x (hts hx)).imp fun y ⟨hy, hr⟩ ↦
    ⟨Finset.mem_filter.mpr ⟨hy, Finset.mem_biUnion.mpr ⟨x, hx, hr⟩⟩, hr⟩

theorem _root_.SupClosed.possLax (hP : SupClosed P) : SupClosed (possLax R P) := by
  rintro s ⟨S, hSs, hS, hSP⟩ t ⟨T, hTt, hT, hTP⟩
  refine ⟨S ∪ T, ?_, fun x hx ↦ ?_, hP hSP hTP⟩
  · show S ∪ T ⊆ (s ∪ t).biUnion R
    rw [Finset.union_biUnion]
    exact Finset.union_subset_union hSs hTt
  · rcases Finset.mem_union.mp hx with h | h
    · exact (hS x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_left _ hy, hr⟩
    · exact (hT x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_right _ hy, hr⟩

theorem empty_mem_possLax (hP : ∅ ∈ P) : ∅ ∈ possLax R P :=
  ⟨∅, Finset.empty_subset _, fun _ hx ↦ absurd hx (Finset.notMem_empty _), hP⟩

/-! ### `flat` is a homomorphism (Anttila Proposition 2.2.16) -/

omit [DecidableEq α] in
theorem flat_inter (p q : α → Prop) : flat p ∩ flat q = flat fun x ↦ p x ∧ q x :=
  Set.ext fun _ ↦ by simp [flat, forall_and]

theorem tensor_flat (p q : α → Prop) : tensor (flat p) (flat q) = flat fun x ↦ p x ∨ q x :=
  Set.ext fun t ↦ exists_splitsAs_forall_iff t p q

omit [DecidableEq α] in
theorem poss_flat (R : α → Finset α) (p : α → Prop) :
    poss R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ forall₂_congr fun x _ ↦ exists_nonempty_subset_forall_iff (R x) p

omit [DecidableEq α] in
theorem nec_flat (R : α → Finset α) (p : α → Prop) :
    nec R (flat p) = flat fun x ↦ ∀ y ∈ R x, p y := rfl

end Team
