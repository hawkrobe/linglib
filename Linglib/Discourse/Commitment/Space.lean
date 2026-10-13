module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Questions.Basic
public import Linglib.Discourse.QUD.Issue
public import Linglib.Discourse.Role

/-!
# Commitment spaces

A commitment space is a set of discourse states with a least member, its root: the current state
together with the continuations it projects. Speech acts transform spaces in two ways. A basic
act adds commitments to the root and keeps the projected states that carry them. A meta-speech
act keeps the root and prunes the continuations: a question restricts them to the answers it
proposes, a denegation removes the states an act would reach. Conjunction and disjunction of
acts are intersection and union of the sets of states they reach, which need not be rooted, so
the laws relating the acts are stated on those sets.

Commitment Space Semantics is the instance over commitment states, sets of `Commitment`s ordered
by inclusion, where a basic act adds a set of commitments and an assertion adds the speaker's
commitment to a proposition. The issue a space raises is settled by the information states
inside some continuation's context set.

## Main definitions

* `Commitment.Space S`: rooted sets of states, ordered by inclusion, with the free space
  `Space.Ici`.
* `Space.update`: the basic act adding `k` to the root.
* `Space.restrict`, `Space.denegate`: the meta-speech acts.
* `Space.assert`: assertion in Commitment Space Semantics.
* `Space.toIssue`: the issue projection.

## Main results

* `Space.coe_update_of_mem`: a projected update is the restriction `{c ∈ C | √C + A ⊆ c}`.
* `Space.coe_update_sSup`: the update by a join is the conjunction of the updates.
* `Space.sdiff_coe_denegate`, `Space.coe_denegate_inter`: two denegations cancel, and de
  Morgan's laws hold for them.

## Implementation notes

* The operations are total. `update` adjoins the new root whether or not the space projects
  it, and `restrict` and `denegate` always keep the root. The papers' set equations hold when
  the act is projected, `k ⊔ C.root ∈ C`, and not redundant, `¬ k ≤ C.root`; these are
  hypotheses of the theorems, not arguments of the operations.
* The root is a field, so that roots of updates compute; it is determined by the states, which
  makes `Space S` a `SetLike`.

## References

* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
-/

@[expose] public section

namespace Commitment

/-- A commitment space is a set of states with a least member, its root. -/
structure Space (S : Type*) [LE S] where
  /-- The states the space projects. -/
  carrier : Set S
  /-- The current state. -/
  root : S
  /-- The root is the least state. -/
  isLeast' : IsLeast carrier root

namespace Space

section PartialOrder

variable {S : Type*} [PartialOrder S] (C : Space S) {D E : Set S} {c d : S}

instance : SetLike (Space S) S where
  coe := carrier
  coe_injective := by
    rintro ⟨s, r, h⟩ ⟨_, r', h'⟩ (rfl : s = _)
    obtain rfl := h.unique h'
    rfl

/-- Spaces are ordered by inclusion, and the smaller space is the stronger act. -/
instance : PartialOrder (Space S) := .ofSetLike (Space S) S

@[ext] theorem ext {C D : Space S} (h : ∀ c, c ∈ C ↔ c ∈ D) : C = D := SetLike.ext h

@[simp] theorem mem_carrier : c ∈ C.carrier ↔ c ∈ C := Iff.rfl

@[simp] theorem mem_mk {s : Set S} {r : S} (h : IsLeast s r) : c ∈ mk s r h ↔ c ∈ s := Iff.rfl

@[simp, norm_cast] theorem coe_mk {s : Set S} {r : S} (h : IsLeast s r) :
    (mk s r h : Set S) = s := rfl

protected theorem isLeast : IsLeast (C : Set S) C.root := C.isLeast'

theorem root_mem : C.root ∈ C := C.isLeast.1

theorem root_le (hc : c ∈ C) : C.root ≤ c := C.isLeast.2 hc

/-- The continuations of a space are its members other than the root. -/
def continuations : Set S := ↑C \ {C.root}

/-- The space with only its root. -/
instance : Singleton S (Space S) := ⟨fun c ↦ ⟨{c}, c, isLeast_singleton⟩⟩

@[simp, norm_cast] theorem coe_singleton (c : S) : (({c} : Space S) : Set S) = {c} := rfl

@[simp] theorem mem_singleton : d ∈ ({c} : Space S) ↔ d = c := Iff.rfl

@[simp] theorem root_singleton (c : S) : ({c} : Space S).root = c := rfl

/-- The free space on `c` has every state above `c`. -/
protected def Ici (c : S) : Space S := ⟨Set.Ici c, c, isLeast_Ici⟩

@[simp, norm_cast] theorem coe_Ici (c : S) : (Space.Ici c : Set S) = Set.Ici c := rfl

@[simp] theorem mem_Ici : d ∈ Space.Ici c ↔ c ≤ d := Iff.rfl

@[simp] theorem root_Ici (c : S) : (Space.Ici c).root = c := rfl

/-! ### Meta-speech acts -/

/-- `C.restrict D` has the root and the members of `C` in `D`. A meta-speech act is such a
restriction, which keeps the root and prunes the continuations. -/
def restrict (D : Set S) : Space S :=
  ⟨insert C.root (↑C ∩ D), C.root, Set.mem_insert _ _,
    Set.forall_mem_insert.2 ⟨le_rfl, fun _ hd ↦ C.root_le hd.1⟩⟩

@[simp] theorem root_restrict (D : Set S) : (C.restrict D).root = C.root := rfl

@[simp, norm_cast] theorem coe_restrict (D : Set S) :
    (C.restrict D : Set S) = insert C.root (↑C ∩ D) := rfl

@[simp] theorem mem_restrict : d ∈ C.restrict D ↔ d = C.root ∨ d ∈ C ∧ d ∈ D := Iff.rfl

theorem coe_restrict_of_root_mem (h : C.root ∈ D) : (C.restrict D : Set S) = ↑C ∩ D :=
  Set.insert_eq_of_mem ⟨C.root_mem, h⟩

/-- Restricting to a union is the disjunction of the restrictions. -/
theorem coe_restrict_union (D E : Set S) :
    (C.restrict (D ∪ E) : Set S) = ↑(C.restrict D) ∪ ↑(C.restrict E) := by
  rw [coe_restrict, coe_restrict, coe_restrict, Set.inter_union_distrib_left,
    Set.insert_union_distrib]

/-- Restricting to an intersection is the conjunction of the restrictions. -/
theorem coe_restrict_inter (D E : Set S) :
    (C.restrict (D ∩ E) : Set S) = ↑(C.restrict D) ∩ ↑(C.restrict E) := by
  rw [coe_restrict, coe_restrict, coe_restrict, Set.inter_inter_distrib_left,
    Set.insert_inter_distrib]

/-- The denegation `C − D` has the root and the members of `C` outside `D`
([cohen-krifka-2014] (26), [krifka-2015] (5), [van-der-leer-2026] Definition 22). -/
def denegate (D : Set S) : Space S := C.restrict Dᶜ

@[simp] theorem root_denegate (D : Set S) : (C.denegate D).root = C.root := rfl

@[simp] theorem mem_denegate : d ∈ C.denegate D ↔ d = C.root ∨ d ∈ C ∧ d ∉ D := Iff.rfl

/-- Denegating an act that moves the root leaves the relative complement. -/
theorem coe_denegate_of_root_notMem (h : C.root ∉ D) : (C.denegate D : Set S) = ↑C \ D :=
  C.coe_restrict_of_root_mem h

/-- Two denegations cancel ([cohen-krifka-2014] (28)). -/
theorem sdiff_coe_denegate (hD : D ⊆ C) (h : C.root ∉ D) :
    (C : Set S) \ ↑(C.denegate D) = D := by
  rw [C.coe_denegate_of_root_notMem h, Set.sdiff_sdiff_cancel_left hD]

/-- De Morgan's law `∼[A & B] = ∼A ∨ ∼B` for denegations ([cohen-krifka-2014] (34)). -/
theorem coe_denegate_inter (D E : Set S) :
    (C.denegate (D ∩ E) : Set S) = ↑(C.denegate D) ∪ ↑(C.denegate E) := by
  rw [denegate, Set.compl_inter, coe_restrict_union]; rfl

/-- De Morgan's law `∼[A ∨ B] = ∼A & ∼B` for denegations ([cohen-krifka-2014] (35)), whose two
sides are rooted though the disjunction is not. -/
theorem coe_denegate_union (D E : Set S) :
    (C.denegate (D ∪ E) : Set S) = ↑(C.denegate D) ∩ ↑(C.denegate E) := by
  rw [denegate, Set.compl_union, coe_restrict_inter]; rfl

end PartialOrder

/-! ### Basic speech acts -/

section SemilatticeSup

variable {S : Type*} [SemilatticeSup S] (C : Space S) {k l d : S}

/-- The update `C + k` is rooted at `k` joined with the root and keeps the members of `C` above
`k` ([cohen-krifka-2014] (23), [krifka-2015] (3)). -/
def update (k : S) : Space S :=
  ⟨insert (k ⊔ C.root) (↑C ∩ Set.Ici k), k ⊔ C.root, Set.mem_insert _ _,
    Set.forall_mem_insert.2 ⟨le_rfl, fun _ hd ↦ sup_le hd.2 (C.root_le hd.1)⟩⟩

@[simp] theorem root_update (k : S) : (C.update k).root = k ⊔ C.root := rfl

@[simp] theorem mem_update : d ∈ C.update k ↔ d = k ⊔ C.root ∨ d ∈ C ∧ k ≤ d := Iff.rfl

/-- A projected update is the restriction to the states above `k`. -/
theorem coe_update_of_mem (h : k ⊔ C.root ∈ C) : (C.update k : Set S) = ↑C ∩ Set.Ici k :=
  Set.insert_eq_of_mem ⟨h, le_sup_left⟩

theorem update_le (h : k ⊔ C.root ∈ C) : C.update k ≤ C := by
  rintro d (rfl | hd)
  exacts [h, hd.1]

/-- The root survives an update iff the update is redundant. -/
theorem root_mem_update_iff : C.root ∈ C.update k ↔ k ≤ C.root :=
  ⟨fun h ↦ h.elim right_eq_sup.1 And.right, fun h ↦ Or.inr ⟨C.root_mem, h⟩⟩

/-- Adding more is the stronger act ([cohen-krifka-2014] (86)). -/
theorem update_le_update (hkl : k ≤ l) (h : l ⊔ C.root ∈ C) : C.update l ≤ C.update k := by
  rintro d (rfl | hd)
  exacts [Or.inr ⟨h, hkl.trans le_sup_left⟩, Or.inr ⟨hd.1, hkl.trans hd.2⟩]

/-- Consecutive updates are the update by the join. -/
theorem update_update (k l : S) : (C.update k).update l = C.update (l ⊔ k) := by
  ext d
  simp only [mem_update, root_update, sup_assoc, sup_le_iff]
  constructor
  · rintro (rfl | ⟨rfl | hd, hl⟩)
    · exact Or.inl rfl
    · exact Or.inl (sup_eq_right.2 hl).symm
    · exact Or.inr ⟨hd.1, hl, hd.2⟩
  · rintro (rfl | ⟨hd, hl, hk⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Or.inr ⟨hd, hk⟩, hl⟩

/-- Consecutive updates commute ([cohen-krifka-2014] (31), [krifka-2015] (6)). -/
theorem update_comm (k l : S) : (C.update k).update l = (C.update l).update k := by
  rw [update_update, update_update, sup_comm]

/-- Restricting to an update keeps the members above `k`, projected or not. -/
theorem restrict_coe_update (k : S) : C.restrict (C.update k) = C.restrict (Set.Ici k) := by
  ext d
  simp only [mem_restrict, SetLike.mem_coe, mem_update, Set.mem_Ici]
  refine or_congr_right (and_congr_right fun hd ↦ ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨hd, h⟩⟩)
  exact h.elim (fun e ↦ e ▸ le_sup_left) And.right

end SemilatticeSup

/-- The update by a join is the conjunction of the updates ([cohen-krifka-2014] (31)), when the
space projects it. -/
theorem coe_update_sSup {S : Type*} [CompleteLattice S] (C : Space S) {K : Set S}
    (hK : K.Nonempty) (h : sSup K ⊔ C.root ∈ C) :
    (C.update (sSup K) : Set S) = ⋂ k ∈ K, (C.update k : Set S) := by
  ext d
  simp only [SetLike.mem_coe, mem_update, Set.mem_iInter]
  refine ⟨fun hd k hk ↦ Or.inr ?_, fun hd ↦ ?_⟩
  · rcases hd with rfl | hd
    exacts [⟨h, (le_sSup hk).trans le_sup_left⟩, ⟨hd.1, (le_sSup hk).trans hd.2⟩]
  · have hle : sSup K ≤ d :=
      sSup_le fun k hk ↦ (hd k hk).elim (fun e ↦ e ▸ le_sup_left) And.right
    by_cases hC : d ∈ C
    · exact Or.inr ⟨hC, hle⟩
    · obtain ⟨k, hk⟩ := hK
      obtain rfl := (hd k hk).resolve_right fun h' ↦ hC h'.1
      exact Or.inl (le_antisymm (sup_le_sup_right (le_sSup hk) _) (sup_le hle le_sup_right))

/-! ### Commitment space semantics -/

variable {A W : Type*} (C : Space (State A W)) (a : A) (φ : Set W) (force : Force)
  {d : State A W}

/-- In the assertion `C + S⊢φ`, `a` commits to `φ` ([cohen-krifka-2014] (37), [krifka-2015]
(14)). -/
def assert (force : Force := .doxastic) : Space (State A W) :=
  C.update {commit a φ force}

@[simp] theorem root_assert : (C.assert a φ force).root = insert (commit a φ force) C.root :=
  rfl

theorem mem_assert :
    d ∈ C.assert a φ force ↔
      d = insert (commit a φ force) C.root ∨ d ∈ C ∧ commit a φ force ∈ d :=
  or_congr_right (and_congr_right fun _ ↦ Set.singleton_subset_iff)

/-- The root survives an assertion iff the assertion is redundant. -/
theorem root_mem_assert_iff : C.root ∈ C.assert a φ force ↔ commit a φ force ∈ C.root :=
  C.root_mem_update_iff.trans Set.singleton_subset_iff

open scoped Classical in
/-- The issue a space raises is settled by the information states inside some continuation's
context set, or inside the root's when the space has no continuations. -/
noncomputable def toIssue : Question W :=
  if C.continuations = ∅ then Question.ofSet (contextSet C.root)
  else ⨆ c ∈ C.continuations, Question.ofSet (contextSet c)

noncomputable instance : Discourse.HasIssue (Space (State A W)) W := ⟨toIssue⟩

theorem mem_toIssue_iff {i : Set W} :
    i ∈ C.toIssue ↔
      (C.continuations = ∅ ∧ i ⊆ contextSet C.root) ∨ ∃ c ∈ C.continuations, i ⊆ contextSet c := by
  unfold toIssue
  split_ifs with h
  · simp [h, Question.mem_ofSet]
  · simp only [h, false_and, false_or, Question.mem_biSup_iff, Question.mem_ofSet]
    refine ⟨fun h' ↦ h'.elim (fun e ↦ ?_) id, Or.inr⟩
    obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨c, hc, e ▸ Set.empty_subset _⟩

/-- The common ground of a space is what its root entails; the speaker's assertion is
Stalnakerian on it. -/
instance : HasAssertion (Space (State Discourse.Role W)) W where
  commonGround C := slate C.root
  initial := Space.Ici ∅
  assert C φ := C.assert .speaker φ
  commonGround_initial := slate_empty
  commonGround_assert _ _ := slate_insert_of_commit rfl

end Space

end Commitment
