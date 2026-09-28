module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.RelClasses
public import Mathlib.Data.Fintype.Card
public import Linglib.Core.Order.PiLex

/-!
# Constraint rankings

A ranking of a constraint set indexed by `ι` ([prince-2002]'s total domination order `≫`) is an
enumeration `r : Fin n ≃ ι` of the constraints in rank order: `r p` is the constraint at rank
position `p`, position `0` most dominant, and `r.symm i` is the rank position of `i`. For
`ι = Fin n` a ranking is a permutation, `Equiv.Perm (Fin n)`. `Ranking.Dominates` is the induced
strict dominance relation, a strict total order on the constraints, and `Ranking.toRel` its
reflexive closure, from which the ranking is recoverable (`toRel_le_toRel_iff`). Reading two
violation vectors in rank order and comparing them lexicographically is `Pi.Lex` under dominance
(`toLex_comp_lt_iff`). The `Tableau` machinery evaluates under a ranking, and the
elementary-ranking-condition layer (`ElementaryRankingCondition.lean`) infers rankings from
winner–loser pairs.

## Implementation notes

A ranking is stored as the enumeration rather than as the order relation, so that rankings can be
enumerated and compared decidably; the relation is derived (`Dominates`). The length `n` is a
parameter rather than `Fintype.card ι`, so that a ranking of `Fin n` is literally a permutation;
`card_eq` recovers `Fintype.card ι = n` from any ranking, and a statement quantifying over all
rankings is vacuous when `n` does not match.

## References

* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
-/

@[expose] public section

namespace OptimalityTheory

/-- A ranking of the constraints `ι` into `n` rank positions, Prince's total domination order
`≫`, is an enumeration of the constraints in rank order: `r p` is the constraint at rank position
`p`, position `0` being the most dominant, and `r.symm i` is the rank position of `i`. -/
abbrev Ranking (ι : Type*) (n : ℕ) := Fin n ≃ ι

variable {ι : Type*} {n : ℕ}

/-- A total relation is maximal among antisymmetric relations, so an antisymmetric relation
above it in the pointwise lattice equals it. -/
theorem total_eq_of_le {α : Type*} {r s : α → α → Prop}
    [ht : Std.Total r] [ha : Std.Antisymm s] (h : r ≤ s) : r = s := by
  refine le_antisymm h fun a b hs => ?_
  rcases ht.total a b with hr | hr
  · exact hr
  · obtain rfl := ha.antisymm _ _ hs (h b a hr)
    exact (ht.total a a).elim id id

namespace Ranking

variable (r : Ranking ι n)

/-- Constraint `i` dominates constraint `j` under `r` when it sits at a lower, more dominant,
rank position. -/
def Dominates (i j : ι) : Prop := r.symm i < r.symm j

instance (i j : ι) : Decidable (r.Dominates i j) :=
  inferInstanceAs (Decidable (r.symm i < r.symm j))

instance : IsStrictTotalOrder ι r.Dominates := InvImage.isStrictTotalOrder r.symm.injective

/-- Dominance between ranked positions is position order. -/
@[simp] theorem dominates_apply_iff {p q : Fin n} : r.Dominates (r p) (r q) ↔ p < q := by
  simp [Dominates]

omit r in
/-- A ranking enumerates all the constraints, so their number is the number of rank positions. -/
theorem card_eq [Fintype ι] (r : Ranking ι n) : Fintype.card ι = n := by
  simpa using Fintype.card_congr r.symm

/-- Reading two vectors in rank order and comparing them lexicographically is `Pi.Lex` under
dominance. -/
theorem toLex_comp_lt_iff {β : Type*} [LT β] (v w : ι → β) :
    toLex (v ∘ r) < toLex (w ∘ r) ↔ Pi.Lex r.Dominates (· < ·) v w :=
  Pi.lex_comp_equiv r (· < ·) (· < ·) v w

/-- Under the identity ranking `1`, dominance is index order. -/
@[simp] theorem one_dominates_iff {i j : Fin n} : (1 : Ranking (Fin n) n).Dominates i j ↔ i < j :=
  Iff.rfl

/-- The ranking's *reading* of a lex-ordered vector: coordinate `p` of `r • v` is the
value of `v` at the constraint ranked `p`-th. Reordering is the one operation that
breaks and reconstitutes the lex order — the `Sₙ` action whose orbit structure is
constraint ranking. (With this convention the action is a right action:
`(r * s) • v = s • r • v`.) -/
instance {α : Type*} : SMul (Ranking (Fin n) n) (Lex (Fin n → α)) :=
  ⟨fun r v => toLex fun p => ofLex v (r p)⟩

@[simp] theorem smul_apply {α : Type*} (r : Ranking (Fin n) n) (v : Lex (Fin n → α)) (p : Fin n) :
    ofLex (r • v) p = ofLex v (r p) := rfl

@[simp] theorem one_smul {α : Type*} (v : Lex (Fin n → α)) : (1 : Ranking (Fin n) n) • v = v :=
  rfl

/-- Any two distinct constraints can be ranked either way, so some ranking makes `i` dominate
`j`. -/
theorem exists_dominates {i j : Fin n} (hij : i ≠ j) :
    ∃ r : Ranking (Fin n) n, r.Dominates i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨1, one_dominates_iff.mpr h⟩
  · exact ⟨Equiv.swap i j, by simpa [Dominates] using h⟩

/-- Any constraint can be ranked above all the others. -/
theorem exists_forall_dominates (i : Fin n) :
    ∃ r : Ranking (Fin n) n, ∀ j, j ≠ i → r.Dominates i j := by
  refine ⟨Equiv.swap ⟨0, i.pos⟩ i, fun j hj ↦ ?_⟩
  have hi : (Equiv.swap ⟨0, i.pos⟩ i).symm i = ⟨0, i.pos⟩ := by simp
  rw [Dominates, hi, Fin.lt_def]
  exact Nat.pos_of_ne_zero fun h0 ↦ hj <| (Equiv.swap ⟨0, i.pos⟩ i).symm.injective <|
    Fin.ext (h0.trans (congrArg Fin.val hi).symm)

/-! ### The ranking as a total order -/

/-- The ranking as its dominance-or-equal relation: `r.toRel i j` iff `i` is
ranked at least as high as `j` — the reflexive closure of `Dominates`
(`toRel_iff`), and a total order on constraints. -/
def toRel : ι → ι → Prop := fun i j => r.symm i ≤ r.symm j

instance (i j : ι) : Decidable (r.toRel i j) :=
  inferInstanceAs (Decidable (r.symm i ≤ r.symm j))

instance : IsPartialOrder ι r.toRel where
  refl _ := le_refl _
  trans _ _ _ := le_trans
  antisymm _ _ h₁ h₂ := r.symm.injective (le_antisymm h₁ h₂)

instance : Std.Total r.toRel := ⟨fun _ _ => le_total _ _⟩

/-- `toRel` is the reflexive closure of `Dominates`. -/
theorem toRel_iff {i j : ι} : r.toRel i j ↔ i = j ∨ r.Dominates i j := by
  unfold toRel Dominates
  rw [le_iff_lt_or_eq, or_comm, r.symm.injective.eq_iff]

/-- On distinct constraints, `toRel` is `Dominates`. -/
theorem toRel_iff_dominates {i j : ι} (hij : i ≠ j) :
    r.toRel i j ↔ r.Dominates i j := by
  rw [toRel_iff]
  simp [hij]

/-- Relabeling constraints by `g` pulls the induced order back along `g⁻¹`. -/
@[simp] theorem toRel_mul (g σ : Ranking (Fin n) n) (i j : Fin n) :
    (g * σ).toRel i j ↔ σ.toRel (g⁻¹ i) (g⁻¹ j) := Iff.rfl

variable {r} {σ τ : Ranking ι n}

/-- A ranking is recoverable from its induced total order. -/
theorem toRel_injective : Function.Injective (toRel (ι := ι) (n := n)) := by
  intro σ τ h
  have hmono : Monotone (⇑τ.symm ∘ ⇑σ) := by
    intro a b hab
    have hrel : σ.toRel (σ a) (σ b) := by
      show σ.symm (σ a) ≤ σ.symm (σ b)
      simpa using hab
    rw [h] at hrel
    exact hrel
  have hcomp := (hmono.strictMono_of_injective (τ.symm.injective.comp σ.injective)).eq_id
  exact Equiv.ext fun k => (Equiv.symm_apply_eq τ).mp (congr_fun hcomp k)

/-- Total orders comparable in the relation lattice coincide, so `toRel` is
rigid: nothing sits strictly between two ranking-induced orders. -/
theorem toRel_le_toRel_iff : σ.toRel ≤ τ.toRel ↔ σ = τ :=
  ⟨fun h => toRel_injective (total_eq_of_le h), fun h => h ▸ le_refl _⟩

/-- Every linear order on the constraints is the induced order of a ranking, the surjectivity
companion to `toRel_injective`: enumerate the constraints in `s`-order (`Finset.sort`) and read
off the ranking. -/
theorem exists_toRel_eq [Fintype ι] (s : ι → ι → Prop) [IsLinearOrder ι s]
    (h : Fintype.card ι = n := by simp) : ∃ σ : Ranking ι n, σ.toRel = s := by
  classical
  have hlen : (Finset.univ.sort s).length = n := by simp [h]
  let e : Fin (Finset.univ.sort s).length ≃ ι :=
    List.Nodup.getEquivOfForallMemList _ (Finset.sort_nodup _ _)
      fun x => by simp
  refine ⟨(finCongr hlen).symm.trans e, total_eq_of_le fun a b hab => ?_⟩
  have h := (Finset.pairwise_sort _ _).rel_get_of_le
    (show e.symm a ≤ e.symm b from hab)
  rwa [show (Finset.univ.sort s).get (e.symm a) = a from e.apply_symm_apply a,
    show (Finset.univ.sort s).get (e.symm b) = b from e.apply_symm_apply b] at h

end Ranking
end OptimalityTheory
