/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Logic.Natural.Soundness
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Bounds.Basic

/-!
# Completeness of the relation algebra

This file proves the converses to `Logic/Natural/Soundness.lean` for
the relation algebra: the join table is tight, and the seven relations
are exactly the nondegenerately realizable conjunctions of constraint
atoms.

Tightness ([icard-2012]'s Lemma 1.5, as an equality) has countermodels
already on the three-atom Boolean algebra `Finset (Fin 3)`. The
classification is [maccartney-manning-2009] §2's sixteen-class
partition, following Sánchez Valencia: the nine subsets outside the
range of `Relation.constraints` force an argument to `⊥` or `⊤` in
every bounded lattice.

## Main declarations

* `Relation.isLeast_join`, `Relation.join_le_iff`: each join cell is
  the least sound chaining ([icard-2012] Definition 1.4).
* `Relation.mem_range_constraints_of_holds`: a constraint set realized
  by a nondegenerate pair is one of the seven.
* `Relation.mem_range_constraints_iff`: the classification, as an iff
  against realizability on `Finset (Fin 3)`.
* `Relation.exists_isLeast_holds`: [icard-2012]'s Lemma 1.3 — any
  nondegenerate pair stands in a strongest relation — on any bounded
  lattice.

## References

* [icard-2012] — Definition 1.4, Lemmas 1.3 and 1.5.
* [maccartney-manning-2009] — §2's sixteen-class partition, following
  Sánchez Valencia.
-/

namespace NaturalLogic

/-! ### Tightness of the join table -/

/-- **Tightness of the join table** ([icard-2012] Lemma 1.5 is an
equality): `R.join S` is the least — strongest — relation sound for
chaining `R` then `S`, already over the three-atom Boolean algebra.
Soundness over any bounded distributive lattice is
`Relation.Holds.join`; conversely any `T` sound on `Finset (Fin 3)`
alone weakens the table entry. -/
theorem Relation.isLeast_join (R S : Relation) :
    IsLeast {T : Relation | ∀ x y z : Finset (Fin 3),
      R.Holds x y → S.Holds y z → T.Holds x z} (R.join S) := by
  refine ⟨λ x y z hR hS => hR.join hS, λ T hT => ?_⟩
  by_contra hle
  have h : ∀ R S T : Relation, ¬ R.join S ≤ T →
      ∃ x y z : Finset (Fin 3), R.Holds x y ∧ S.Holds y z ∧ ¬ T.Holds x z := by
    decide
  obtain ⟨x, y, z, hR, hS, hT'⟩ := h R S T hle
  exact hT' (hT x y z hR hS)

/-! ### Why seven relations -/

/-- Completeness half of the classification: a conjunction of atomic
constraints satisfied by a nondegenerate pair, in any bounded lattice,
is the constraint set of one of the seven relations. -/
theorem Relation.mem_range_constraints_of_holds {α : Type*} [Lattice α]
    [BoundedOrder α] {s : Finset Relation.Atom} {x y : α}
    (h : ∀ a ∈ s, a.Holds x y) (hx : x ≠ ⊥) (hx' : x ≠ ⊤)
    (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    s ∈ Set.range Relation.constraints := by
  by_contra hs
  have key : ∀ s : Finset Relation.Atom, (¬ ∃ R : Relation, R.constraints = s) →
      ({.le, .disjoint} ⊆ s ∨ {.le, .codisjoint} ⊆ s ∨
       {.ge, .disjoint} ⊆ s ∨ {.ge, .codisjoint} ⊆ s) := by decide
  rcases key s (λ ⟨R, hR⟩ => hs ⟨R, hR⟩) with hp | hp | hp | hp
  · exact hx ((h .disjoint (hp (by decide))).eq_bot_of_le (h .le (hp (by decide))))
  · exact hy' ((h .codisjoint (hp (by decide))).eq_top_of_ge (h .le (hp (by decide))))
  · exact hy ((h .disjoint (hp (by decide))).eq_bot_of_ge (h .ge (hp (by decide))))
  · exact hx' ((h .codisjoint (hp (by decide))).eq_top_of_le (h .ge (hp (by decide))))

/-- **Why seven**: of the sixteen conjunctions of atomic constraints,
exactly the seven in the range of `constraints` are nondegenerately
realizable — here already on the three-atom Boolean algebra; the other
nine force an argument to `⊥` or `⊤` on every bounded lattice
([maccartney-manning-2009]'s nontrivial-denotation proviso,
[icard-2012] §1). -/
theorem Relation.mem_range_constraints_iff {s : Finset Relation.Atom} :
    s ∈ Set.range Relation.constraints ↔
      ∃ x y : Finset (Fin 3), x ≠ ⊥ ∧ x ≠ ⊤ ∧ y ≠ ⊥ ∧ y ≠ ⊤ ∧
        ∀ a ∈ s, a.Holds x y := by
  constructor
  · rintro ⟨R, rfl⟩
    revert R; decide
  · rintro ⟨x, y, hx, hx', hy, hy', h⟩
    exact Relation.mem_range_constraints_of_holds h hx hx' hy hy'

/-! ### The join characterization and the strongest relation -/

/-- [icard-2012]'s Definition 1.4 as a characterization: `R.join S ≤ T`
exactly when chaining `R`'s content with `S`'s lands inside `T`'s —
soundness and tightness in one iff, the `sup_le_iff` idiom. -/
theorem Relation.join_le_iff {R S T : Relation} :
    R.join S ≤ T ↔
      ∀ x y z : Finset (Fin 3), R.Holds x y → S.Holds y z → T.Holds x z :=
  ⟨λ h _ _ _ hR hS => (hR.join hS).of_le h, λ h => (Relation.isLeast_join R S).2 h⟩

/-- [icard-2012]'s Lemma 1.3: any two elements distinct from `⊥` and `⊤`
stand in a strongest natural-logic relation — stated there for Boolean
lattices, proved here for any bounded lattice. It fails at `⊥`/`⊤`:
`x ⌣ ⊤` and `x ⊑ ⊤` hold with no common strengthening. -/
theorem Relation.exists_isLeast_holds {α : Type*} [Lattice α] [BoundedOrder α]
    {x y : α} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    ∃ R : Relation, IsLeast {S : Relation | S.Holds x y} R := by
  classical
  obtain ⟨R, hR⟩ := Relation.mem_range_constraints_of_holds
    (s := Finset.univ.filter (λ a => a.Holds x y))
    (λ a ha => (Finset.mem_filter.mp ha).2) hx hx' hy hy'
  refine ⟨R, Relation.holds_iff.mpr (λ a ha => ?_),
    λ S hS => Relation.le_iff.mpr (λ a ha => ?_)⟩
  · rw [hR] at ha
    exact (Finset.mem_filter.mp ha).2
  · rw [hR]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.holds_iff.mp hS a ha⟩

end NaturalLogic
