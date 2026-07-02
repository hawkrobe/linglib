import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.PiLex

/-!
# Constraint rankings

A constraint ranking is a permutation of `Fin n` ([prince-2002]'s total domination
order `≫`): `r i` is the constraint at rank position `i`, position `0` most dominant.
`Ranking.Dominates` is the induced dominance relation between constraints; the
`Tableau` machinery evaluates under a ranking, and the elementary-ranking-condition
layer (`ElementaryRankingCondition.lean`) infers rankings from winner–loser pairs.
-/

namespace OptimalityTheory

variable {n : ℕ}

/-- A constraint ranking: a permutation of `Fin n` ([prince-2002]'s total domination
order `≫`). `r i` is the constraint at rank position `i` (position `0` is most
dominant); `r.symm k` is the rank position of `k`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

variable {n : ℕ}

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

end Ranking
end OptimalityTheory
