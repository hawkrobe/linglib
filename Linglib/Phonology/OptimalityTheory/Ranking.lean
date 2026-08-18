import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.PiLex
import Mathlib.Order.Preorder.Finite

/-!
# Constraint rankings

A constraint ranking is a permutation of `Fin n` ([prince-2002]'s total domination
order `≫`): `r i` is the constraint at rank position `i`, position `0` most dominant.
`Ranking.Dominates` is the induced strict dominance relation between constraints and
`Ranking.toRel` its reflexive closure — the ranking as a total order, from which the
ranking is recoverable (`toRel_le_toRel_iff`). The `Tableau` machinery evaluates
under a ranking, and the elementary-ranking-condition layer
(`ElementaryRankingCondition.lean`) infers rankings from winner–loser pairs.
-/

namespace OptimalityTheory

variable {n : ℕ}

/-- A constraint ranking: a permutation of `Fin n` ([prince-2002]'s total domination
order `≫`). `r i` is the constraint at rank position `i` (position `0` is most
dominant); `r.symm k` is the rank position of `k`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

variable {n : ℕ}

/-- A total relation is maximal among antisymmetric relations: anything above
it in the pointwise lattice collapses back onto it. -/
theorem total_eq_of_le {α : Type*} {r s : α → α → Prop}
    [ht : Std.Total r] [ha : Std.Antisymm s] (h : r ≤ s) : r = s := by
  refine le_antisymm h fun a b hs => ?_
  rcases ht.total a b with hr | hr
  · exact hr
  · obtain rfl := ha.antisymm _ _ hs (h b a hr)
    exact (ht.total a a).elim id id

namespace Ranking

variable (r : Ranking n)

/-- Constraint `i` *dominates* constraint `j` under `r`: it sits at a lower
(more dominant) rank position. -/
def Dominates (i j : Fin n) : Prop := r.symm i < r.symm j

instance (i j : Fin n) : Decidable (r.Dominates i j) := inferInstanceAs (Decidable (r.symm i < r.symm j))

/-- Dominance between ranked positions is position order. -/
@[simp] theorem dominates_apply_iff {p q : Fin n} : r.Dominates (r p) (r q) ↔ p < q := by
  simp [Dominates]

/-- The identity ranking: rank position equals constraint index. -/
def id (n : ℕ) : Ranking n := Equiv.refl _

/-- Under the identity ranking, dominance is index order. -/
@[simp] theorem id_dominates_iff {i j : Fin n} : (Ranking.id n).Dominates i j ↔ i < j := Iff.rfl

/-- The ranking's *reading* of a lex-ordered vector: coordinate `p` of `r • v` is the
value of `v` at the constraint ranked `p`-th. Reordering is the one operation that
breaks and reconstitutes the lex order — the `Sₙ` action whose orbit structure is
constraint ranking. (With this convention the action is a right action:
`(r * s) • v = s • r • v`.) -/
instance {α : Type*} : SMul (Ranking n) (Lex (Fin n → α)) :=
  ⟨fun r v => toLex fun p => ofLex v (r p)⟩

@[simp] theorem smul_apply {α : Type*} (r : Ranking n) (v : Lex (Fin n → α)) (p : Fin n) :
    ofLex (r • v) p = ofLex v (r p) := rfl

@[simp] theorem id_smul {α : Type*} (v : Lex (Fin n → α)) : Ranking.id n • v = v := rfl

/-- Any two distinct constraints can be ranked either way: some ranking makes `i`
dominate `j`. -/
theorem exists_dominates {i j : Fin n} (hij : i ≠ j) : ∃ r : Ranking n, r.Dominates i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨Ranking.id n, id_dominates_iff.mpr h⟩
  · exact ⟨Equiv.swap i j, by simpa [Dominates] using h⟩

/-! ### The ranking as a total order -/

/-- The ranking as its dominance-or-equal relation: `r.toRel i j` iff `i` is
ranked at least as high as `j` — the reflexive closure of `Dominates`
(`toRel_iff`), and a total order on constraints. -/
def toRel : Fin n → Fin n → Prop := fun i j => r.symm i ≤ r.symm j

instance (i j : Fin n) : Decidable (r.toRel i j) :=
  inferInstanceAs (Decidable (r.symm i ≤ r.symm j))

instance : IsPartialOrder (Fin n) r.toRel where
  refl _ := le_refl _
  trans _ _ _ := le_trans
  antisymm _ _ h₁ h₂ := r.symm.injective (le_antisymm h₁ h₂)

instance : Std.Total r.toRel := ⟨fun _ _ => le_total _ _⟩

/-- `toRel` is the reflexive closure of `Dominates`. -/
theorem toRel_iff {i j : Fin n} : r.toRel i j ↔ i = j ∨ r.Dominates i j := by
  unfold toRel Dominates
  rw [le_iff_lt_or_eq, or_comm, r.symm.injective.eq_iff]

/-- On distinct constraints, `toRel` is `Dominates`. -/
theorem toRel_iff_dominates {i j : Fin n} (hij : i ≠ j) :
    r.toRel i j ↔ r.Dominates i j := by
  rw [toRel_iff]
  simp [hij]

/-- Relabeling constraints by `g` pulls the induced order back along `g⁻¹`. -/
@[simp] theorem toRel_mul (g σ : Ranking n) (i j : Fin n) :
    (g * σ).toRel i j ↔ σ.toRel (g⁻¹ i) (g⁻¹ j) := Iff.rfl

variable {r} {σ τ : Ranking n}

/-- A ranking is recoverable from its induced total order. -/
theorem toRel_injective : Function.Injective (toRel (n := n)) := by
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

/-- Every linear order on `Fin n` is the induced order of a ranking — the
surjectivity companion to `toRel_injective`: enumerate the constraints in
`s`-order (`Finset.sort`) and read off the ranking. -/
theorem exists_toRel_eq (s : Fin n → Fin n → Prop) [IsLinearOrder (Fin n) s] :
    ∃ σ : Ranking n, σ.toRel = s := by
  classical
  have hlen : (Finset.univ.sort s).length = n := by simp
  let e : Fin (Finset.univ.sort s).length ≃ Fin n :=
    List.Nodup.getEquivOfForallMemList _ (Finset.sort_nodup _ _)
      fun x => by simp
  refine ⟨(finCongr hlen).symm.trans e, total_eq_of_le fun a b hab => ?_⟩
  have h := (Finset.pairwise_sort _ _).rel_get_of_le
    (show e.symm a ≤ e.symm b from hab)
  rwa [show (Finset.univ.sort s).get (e.symm a) = a from e.apply_symm_apply a,
    show (Finset.univ.sort s).get (e.symm b) = b from e.apply_symm_apply b] at h

end Ranking
end OptimalityTheory
