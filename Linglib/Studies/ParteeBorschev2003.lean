import Linglib.Semantics.Possession.Basic

/-!
# Partee and Borschev (2003): Genitives, Relational Nouns, and Argument-Modifier Ambiguity

This file formalizes the comparison in [partee-borschev-2003] between two analyses of the
genitive. On the split analysis the paper defends, a genitive is either the argument of a
relational noun, *teacher of John's*, or a modifier of a sortal noun carrying a free
contextual relation, *team of John's*; on the uniform analysis of [vikner-jensen-2002] every
genitive is an argument, a sortal noun being coerced to a relational one. For a
pragmatically coerced sortal noun the two assemble the same predicate and differ only in
where the free relation enters (`convergence`); they come apart under *former* (§4.3):
*Mary's former mansion* has a reading on which the building is a former mansion now
Mary's and one on which it was formerly Mary's mansion, the free relation outside or inside
the scope of *former* (`readingA`, `readingB`). The split analysis derives only the first,
since the relation enters with the genitive after *former* has combined with the noun, and
coercion derives both. The two readings coincide whenever the free relation is constant
over time (`readingA_eq_readingB_of_constant`) and come apart exactly when it changes:
the second reading holds and the first fails of what was the possessor's and is no longer,
whether or not it is still a mansion (`readingB_not_readingA_iff`), and the first holds and
the second fails of a former mansion that has become the possessor's since
(`readingA_not_readingB_iff`).

## Implementation notes

The possessive combinator `π` is that of `Semantics/Possession/Relationalizer`, where the
convergence of the two analyses is already recorded on its definition; *former* is modelled
against a fixed past time. The paper's compositional tree for the split analysis and its
discussion of the Russian genitive are not represented.

## References

* [partee-borschev-2003]
* [vikner-jensen-2002]
-/

namespace ParteeBorschev2003

open Possession

variable {E S : Type*}

/-! ### Convergence (15), (16) -/

/-- The uniform analysis: a sortal noun coerced to a relation by a free relation, then applied
to its possessor. -/
def coerced (N : E → S → Prop) (R : E → E → S → Prop) : E → E → S → Prop :=
  λ y x s => N x s ∧ R y x s

/-- The coerced noun taken as argument and the modifier genitive `π N R y` assemble the same
predicate: the accounts differ only in where the free relation enters. -/
theorem convergence (N : E → S → Prop) (R : E → E → S → Prop) (y : E) :
    coerced N R y = π N R y :=
  rfl

/-! ### Divergence under *former* (17), (18) -/

/-- *former* on a noun: held at the past time and no longer holds. -/
def former (past : S) (P : E → S → Prop) : E → S → Prop := λ x s => P x past ∧ ¬ P x s

/-- *former* on a relation, the shifted modifier of *former owner*. -/
def formerRel (past : S) (Rel : E → E → S → Prop) : E → E → S → Prop :=
  λ y x s => Rel y x past ∧ ¬ Rel y x s

variable (past : S) (N : E → S → Prop) (R : E → E → S → Prop) (y x : E) (s : S)

/-- Reading A: the free relation outside the scope of *former*, *a former mansion that is now
Mary's*. -/
def readingA : E → S → Prop := π (former past N) R y

/-- Reading B: the free relation inside the scope of *former*, *something that was formerly
Mary's mansion*. -/
def readingB : E → S → Prop := formerRel past (π N R) y

/-- When the free relation does not change over time the two readings coincide, so the
position of the relation is undetectable. -/
theorem readingA_eq_readingB_of_constant (hR : ∀ x s, R y x s ↔ R y x past) :
    readingA past N R y = readingB past N R y := by
  funext x s
  simp only [readingA, readingB, π, former, formerRel, hR x s]
  exact propext (by tauto)

/-- Reading B holds and reading A fails of exactly what was the possessor's `N` and is no
longer the possessor's, whether or not it is still an `N`: the building that is still a
mansion but no longer Mary's. -/
theorem readingB_not_readingA_iff :
    readingB past N R y x s ∧ ¬ readingA past N R y x s ↔
      N x past ∧ R y x past ∧ ¬ R y x s := by
  simp only [readingA, readingB, π, former, formerRel]; tauto

/-- Reading A holds and reading B fails of exactly a former `N` that is the possessor's now
and was not when it was an `N`: a ruin Mary has acquired since. -/
theorem readingA_not_readingB_iff :
    readingA past N R y x s ∧ ¬ readingB past N R y x s ↔
      N x past ∧ ¬ N x s ∧ R y x s ∧ ¬ R y x past := by
  simp only [readingA, readingB, π, former, formerRel]; tauto

end ParteeBorschev2003
