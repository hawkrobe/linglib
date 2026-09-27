module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Hom.BoundedLattice
public import Linglib.Core.Order.Sups
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

The operations are mathlib's where mathlib has them. Tensor disjunction is the pointwise
sup `P ⊻ Q` (`Set.sups`) of the lattice `Finset α`, so its closure lemmas are the
lattice-general ones of `Core/Order/Sups.lean`; conjunction is intersection; the image
modality is the preimage of a property along the bundled `SupBotHom` `biUnionHom R`, so
its closure lemmas are `IsLowerSet.preimage` and `SupClosed.preimage`. The remaining
results follow [anttila-2021]: `flat` properties and the flat modalities are flat outright,
and `flat` commutes with conjunction, tensor disjunction and the flat modalities — the
content of his Proposition 2.2.16, by which a formula built from flat atoms by these
connectives defines a flat property, pointwise its classical truth.

## Main definitions

* `Team.flat`, `Team.tensor`, `Team.ne`, `Team.poss`, `Team.nec` — the BSML connectives.
* `Team.biUnionHom`, `Team.possWitness`, `Team.necImage`, `Team.possLax` — the modal
  clauses of modal dependence and inclusion logic.

## Main results

* `Team.isFlat_flat`, `IsLowerSet.tensor`, `SupClosed.tensor`, `Team.empty_mem_tensor`,
  `Set.OrdConnected.tensor` — closure per connective.
* `Team.flat_inter`, `Team.tensor_flat`, `Team.poss_flat`, `Team.nec_flat`,
  `Team.possWitness_flat`, `Team.possLax_flat`, `Team.necImage_flat` — `flat` is a
  homomorphism.

## Implementation notes

The pointwise connectives need no decidable equality on points and come first; the split
and image connectives, which form unions of teams, follow under `[DecidableEq α]`. The
bilateral anti-support of `ne` is the singleton property `{∅}`. Membership in each
operation unfolds definitionally (`mem_flat`, `mem_tensor`, …), so a logic's evaluation
clauses written through these operations are the same propositions as the paper's; a
split of a team appears as a witness `t₁ ∪ t₂ = t`.

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

open scoped SetFamily

namespace Team

variable {α : Type*}

/-! ### Pointwise connectives -/

/-- The pointwise lift of a property of points: the teams all of whose points satisfy `p`.
    Atoms, and every flat connective, define such properties. -/
def flat (p : α → Prop) : TeamProperty α := {t | ∀ x ∈ t, p x}

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

variable {p q : α → Prop} {P : TeamProperty α} {R : α → Finset α} {t : Finset α}

@[simp] theorem mem_flat : t ∈ flat p ↔ ∀ x ∈ t, p x := Iff.rfl

@[simp] theorem mem_ne : t ∈ (ne : TeamProperty α) ↔ t.Nonempty := Iff.rfl

@[simp] theorem mem_poss : t ∈ poss R P ↔ ∀ x ∈ t, ∃ s ⊆ R x, s.Nonempty ∧ s ∈ P := Iff.rfl

@[simp] theorem mem_nec : t ∈ nec R P ↔ ∀ x ∈ t, R x ∈ P := Iff.rfl

@[simp] theorem mem_possWitness :
    t ∈ possWitness R P ↔ ∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P := Iff.rfl

instance flat.instDecidableMem [DecidablePred p] (t : Finset α) : Decidable (t ∈ flat p) :=
  Finset.decidableDforallFinset

instance ne.instDecidableMem (t : Finset α) : Decidable (t ∈ (ne : TeamProperty α)) :=
  inferInstanceAs (Decidable t.Nonempty)

instance nec.instDecidableMem (R : α → Finset α) (P : TeamProperty α) [DecidablePred (· ∈ P)]
    (t : Finset α) : Decidable (t ∈ nec R P) :=
  inferInstanceAs (Decidable (∀ x ∈ t, R x ∈ P))

theorem isFlat_flat (p : α → Prop) : IsFlat (flat p) := fun t ↦ by simp

theorem ordConnected_ne : (ne : TeamProperty α).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro s hs u _ _ t ht
  exact hs.mono ht.1

theorem isLowerSet_singleton_empty : IsLowerSet ({∅} : TeamProperty α) := by
  intro s t hts hs
  rw [Set.mem_singleton_iff] at hs ⊢
  exact Finset.subset_empty.mp (hs ▸ hts)

theorem ordConnected_singleton_empty : ({∅} : TeamProperty α).OrdConnected :=
  isLowerSet_singleton_empty.ordConnected

theorem isLowerSet_possWitness (R : α → Finset α) (P : TeamProperty α) :
    IsLowerSet (possWitness R P) := by
  rintro s t hts ⟨Y, hY, hYP⟩
  exact ⟨Y, fun x hx ↦ hY x (hts hx), hYP⟩

theorem empty_mem_possWitness (hP : ∅ ∈ P) : ∅ ∈ possWitness R P :=
  ⟨∅, fun _ hx ↦ absurd hx (Finset.notMem_empty _), hP⟩

/-- `flat` commutes with conjunction. -/
theorem flat_inter (p q : α → Prop) : flat p ∩ flat q = flat fun x ↦ p x ∧ q x :=
  Set.ext fun _ ↦ by simp [flat, forall_and]

/-- `flat` commutes with the flat possibility modality. -/
theorem poss_flat (R : α → Finset α) (p : α → Prop) :
    poss R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ forall₂_congr fun x _ ↦ exists_nonempty_subset_forall_iff (R x) p

/-- `flat` commutes with the flat necessity modality. -/
theorem nec_flat (R : α → Finset α) (p : α → Prop) :
    nec R (flat p) = flat fun x ↦ ∀ y ∈ R x, p y := rfl

/-! ### Split and image connectives -/

variable [DecidableEq α] {Q : TeamProperty α}

/-- Tensor (split) disjunction: the teams that split into a part in `P` and a part in `Q`.
    This is the pointwise sup `P ⊻ Q` of `Finset α` (`tensor_eq_sups`), spelled out so that
    a split appears as `t₁ ∪ t₂ = t`. -/
def tensor (P Q : TeamProperty α) : TeamProperty α := {t | ∃ t₁ ∈ P, ∃ t₂ ∈ Q, t₁ ∪ t₂ = t}

theorem tensor_eq_sups (P Q : TeamProperty α) : tensor P Q = P ⊻ Q := rfl

/-- The image of a team under successor sets, `t ↦ t.biUnion R`, as a map of the bounded
    join-semilattices of teams. -/
def biUnionHom {β : Type*} [DecidableEq β] (R : α → Finset β) :
    SupBotHom (Finset α) (Finset β) where
  toFun t := t.biUnion R
  map_sup' _ _ := Finset.union_biUnion
  map_bot' := Finset.biUnion_empty

@[simp] theorem biUnionHom_apply {β : Type*} [DecidableEq β] (R : α → Finset β) (t : Finset α) :
    biUnionHom R t = t.biUnion R := rfl

/-- The image necessity modality ([vaananen-2008] clause (T9)): the union of the successor
    sets is in `P`. -/
def necImage (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  biUnionHom R ⁻¹' P

/-- The lax possibility modality of modal inclusion logic ([anttila-haggblom-yang-2024]
    Definition 2.2): a team of successors in `P` that reaches every point. -/
def possLax (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  {t | ∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P}

@[simp] theorem mem_tensor : t ∈ tensor P Q ↔ ∃ t₁ ∈ P, ∃ t₂ ∈ Q, t₁ ∪ t₂ = t := Iff.rfl

@[simp] theorem mem_necImage : t ∈ necImage R P ↔ t.biUnion R ∈ P := Iff.rfl

@[simp] theorem mem_possLax :
    t ∈ possLax R P ↔ ∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P := Iff.rfl

instance tensor.instDecidableMem [Fintype α] (P Q : TeamProperty α) [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ Q)] (t : Finset α) : Decidable (t ∈ tensor P Q) :=
  inferInstanceAs (Decidable (∃ t₁ ∈ P, ∃ t₂ ∈ Q, t₁ ∪ t₂ = t))

instance poss.instDecidableMem [Fintype α] (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ poss R P) :=
  inferInstanceAs (Decidable (∀ x ∈ t, ∃ s ⊆ R x, s.Nonempty ∧ s ∈ P))

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

theorem isLowerSet_flat (p : α → Prop) : IsLowerSet (flat p) := (isFlat_flat p).isLowerSet

theorem supClosed_flat (p : α → Prop) : SupClosed (flat p) := (isFlat_flat p).supClosed

theorem empty_mem_flat (p : α → Prop) : ∅ ∈ flat p := (isFlat_flat p).empty_mem

theorem ordConnected_flat (p : α → Prop) : (flat p).OrdConnected := (isFlat_flat p).ordConnected

/-! ### The non-emptiness atom -/

theorem supClosed_ne : SupClosed (ne : TeamProperty α) := by
  intro s hs t _
  exact hs.mono Finset.subset_union_left

theorem supClosed_singleton_empty : SupClosed ({∅} : TeamProperty α) := by
  intro s hs t ht
  rw [Set.mem_singleton_iff] at hs ht ⊢
  rw [hs, ht]
  exact sup_idem _

/-! ### Tensor disjunction (Anttila Proposition 2.2.8)

The closure lemmas are those of `⊻` in the distributive lattice `Finset α`. -/

theorem _root_.IsLowerSet.tensor (hP : IsLowerSet P) (hQ : IsLowerSet Q) :
    IsLowerSet (tensor P Q) :=
  hP.sups hQ

theorem _root_.SupClosed.tensor (hP : SupClosed P) (hQ : SupClosed Q) : SupClosed (tensor P Q) :=
  hP.sups hQ

theorem empty_mem_tensor (hP : ∅ ∈ P) (hQ : ∅ ∈ Q) : ∅ ∈ tensor P Q :=
  Set.bot_mem_sups hP hQ

/-- Tensor disjunction preserves convexity when both disjuncts are union-closed
    ([anttila-2025] Proposition 3.3.1). -/
theorem _root_.Set.OrdConnected.tensor (hP : P.OrdConnected) (hQ : Q.OrdConnected)
    (hP' : SupClosed P) (hQ' : SupClosed Q) : (tensor P Q).OrdConnected :=
  hP.sups hQ hP' hQ'

/-! ### The modalities of dependence and inclusion logic -/

theorem _root_.SupClosed.possWitness (hP : SupClosed P) : SupClosed (possWitness R P) := by
  rintro s ⟨Y, hY, hYP⟩ t ⟨Z, hZ, hZP⟩
  refine ⟨Y ∪ Z, fun x hx ↦ ?_, hP hYP hZP⟩
  rcases Finset.mem_union.mp hx with h | h
  · exact (hY x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_left _ hy, hr⟩
  · exact (hZ x h).imp fun _ ⟨hz, hr⟩ ↦ ⟨Finset.mem_union_right _ hz, hr⟩

theorem _root_.IsLowerSet.necImage (hP : IsLowerSet P) : IsLowerSet (necImage R P) :=
  hP.preimage (OrderHomClass.mono (biUnionHom R))

theorem _root_.SupClosed.necImage (hP : SupClosed P) : SupClosed (necImage R P) :=
  hP.preimage (biUnionHom R)

theorem empty_mem_necImage (hP : ∅ ∈ P) : ∅ ∈ necImage R P :=
  bot_mem_preimage (biUnionHom R) hP

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

/-! ### `flat` commutes with tensor disjunction (Anttila Proposition 2.2.16) -/

/-- A team of points satisfying `p ∨ q` splits into its `p`-points and its `¬p`-points. -/
theorem mem_tensor_flat : t ∈ tensor (flat p) (flat q) ↔ ∀ x ∈ t, p x ∨ q x where
  mp := fun ⟨_, h₁, _, h₂, hu⟩ x hx ↦ by
    subst hu
    exact (Finset.mem_union.mp hx).imp (h₁ x) (h₂ x)
  mpr h := by
    classical
    exact ⟨t.filter p, fun x hx ↦ (Finset.mem_filter.mp hx).2, t.filter (¬ p ·),
      fun x hx ↦ (h x (Finset.mem_filter.mp hx).1).resolve_left (Finset.mem_filter.mp hx).2,
      Finset.filter_union_filter_not_eq _ _⟩

theorem tensor_flat (p q : α → Prop) : tensor (flat p) (flat q) = flat fun x ↦ p x ∨ q x :=
  Set.ext fun _ ↦ mem_tensor_flat

/-! ### `flat` commutes with the image modalities

On flat properties the single-witness, lax and image modalities agree with the flat ones:
the witness team may be taken to be the `p`-successors of the team. -/

theorem mem_possWitness_flat : t ∈ possWitness R (flat p) ↔ ∀ x ∈ t, ∃ y ∈ R x, p y where
  mp := fun ⟨_, hY, hYp⟩ x hx ↦ (hY x hx).imp fun _ ⟨hyY, hyR⟩ ↦ ⟨hyR, hYp _ hyY⟩
  mpr h := by
    classical
    exact ⟨(t.biUnion R).filter p, fun x hx ↦ (h x hx).imp fun _ ⟨hyR, hy⟩ ↦
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hx, hyR⟩, hy⟩, hyR⟩,
      fun _ hy ↦ (Finset.mem_filter.mp hy).2⟩

theorem possWitness_flat (R : α → Finset α) (p : α → Prop) :
    possWitness R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_possWitness_flat

theorem mem_possLax_flat : t ∈ possLax R (flat p) ↔ ∀ x ∈ t, ∃ y ∈ R x, p y where
  mp := fun ⟨_, _, hS, hSp⟩ x hx ↦ (hS x hx).imp fun _ ⟨hyS, hyR⟩ ↦ ⟨hyR, hSp _ hyS⟩
  mpr h := by
    classical
    exact ⟨(t.biUnion R).filter p, Finset.filter_subset _ _, fun x hx ↦ (h x hx).imp
      fun _ ⟨hyR, hy⟩ ↦ ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hx, hyR⟩, hy⟩, hyR⟩,
      fun _ hy ↦ (Finset.mem_filter.mp hy).2⟩

theorem possLax_flat (R : α → Finset α) (p : α → Prop) :
    possLax R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_possLax_flat

theorem mem_necImage_flat : t ∈ necImage R (flat p) ↔ ∀ x ∈ t, ∀ y ∈ R x, p y := by
  simp only [mem_necImage, mem_flat, Finset.mem_biUnion, forall_exists_index, and_imp]
  exact ⟨fun h x hx y hy ↦ h y x hx hy, fun h y x hx hy ↦ h x hx y hy⟩

theorem necImage_flat (R : α → Finset α) (p : α → Prop) :
    necImage R (flat p) = flat fun x ↦ ∀ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_necImage_flat

end Team
