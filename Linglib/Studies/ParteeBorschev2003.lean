import Linglib.Semantics.Possession.Basic

/-!
# Partee and Borschev (2003): Genitives, Relational Nouns, and Argument-Modifier Ambiguity

This file formalizes the comparison in [partee-borschev-2003] between two analyses of the
genitive. On the split analysis the paper defends, a genitive is either the argument of a
relational noun, *teacher of John's*, or a modifier of a sortal noun carrying a free
contextual relation, *team of John's*; on the uniform analysis of [vikner-jensen-2002] every
genitive is an argument, a sortal noun being coerced to a relational one. For a
pragmatically coerced sortal noun the two assemble the same denotation and differ only in
where the free relation enters; they come apart under *former* (§4.3): *Mary's former
mansion* has a reading on which the building is a former mansion now Mary's and one on which
it was formerly Mary's mansion, the free relation outside or inside the scope of *former*
(`readingA`, `readingB`). The split analysis derives only the first and coercion both, and
the two are distinct predicates on a model where the building is still a mansion but no
longer Mary's (`FormerMansion.readingA_ne_readingB`).

## Implementation notes

The possessive combinator `π` is that of `Semantics/Possession/Basic`; the paper's
compositional tree for the split analysis and its discussion of the Russian genitive are not
represented.

## References

* [partee-borschev-2003]
* [vikner-jensen-2002]
-/

namespace ParteeBorschev2003

open Possession

variable {E S : Type*}

/-! ### The readings of *Mary's former mansion* (P&B §4.3)

`former` (CN/CN) modifies the noun predicate; `formerRel` (TCN/TCN) modifies a
relation. With the free relation `R` *outside* `former` (Reading A) vs. *inside*
`formerRel`'s scope (Reading B), the genitive denotes differently. P&B's split
introduces `R` only with the construction, after `former`, deriving Reading A
alone; J&V's coercion can introduce `R` at the noun-shift, deriving both. -/

/-- Reading A: the free relation is outside `former`'s scope — *a former mansion
that is now Mary's*. The only reading P&B's split derives. -/
def readingA (former : (E → S → Prop) → E → S → Prop) (possessor : E)
    (noun : E → S → Prop) (R : E → E → S → Prop) : E → S → Prop :=
  π (former noun) R possessor

/-- Reading B: the free relation is inside `formerRel`'s scope — *something that
was formerly Mary's mansion*. Available on J&V's coercion. -/
def readingB (formerRel : (E → E → S → Prop) → E → E → S → Prop) (possessor : E)
    (noun : E → S → Prop) (R : E → E → S → Prop) : E → S → Prop :=
  formerRel (π noun R) possessor

namespace FormerMansion

/-- Entities: building `0`, Mary `1`. -/
abbrev Ent := Fin 2
/-- Time: `true` now, `false` past. -/
abbrev Tm := Bool

/-- The building `0` is a mansion at every time. -/
def mansion : Ent → Tm → Prop := λ x _ => x = 0
/-- Mary (`1`) owned the building (`0`) only in the past. -/
def owns : Ent → Ent → Tm → Prop := λ o x t => o = 1 ∧ x = 0 ∧ t = false
/-- *former* P: was P in the past, no longer P now. -/
def former (P : Ent → Tm → Prop) : Ent → Tm → Prop := λ x t => P x false ∧ ¬ P x t
/-- *former* on a relation: held in the past, no longer. -/
def formerRel (Rel : Ent → Ent → Tm → Prop) : Ent → Ent → Tm → Prop :=
  λ o x t => Rel o x false ∧ ¬ Rel o x t

/-- **Divergence**: the locus of the free relation is detectable under *former*.
The building is still a mansion now but Mary no longer owns it, so Reading B
(*was Mary's mansion*) holds of it while Reading A (*a former mansion now
Mary's*) does not. P&B's split derives only Reading A; J&V's coercion derives
both — J&V's empirical advantage (P&B §4.3). -/
theorem readingA_ne_readingB :
    readingA former 1 mansion owns ≠ readingB formerRel 1 mansion owns := by
  intro h
  have hA : ¬ readingA former 1 mansion owns 0 true := by
    unfold readingA π former mansion owns; decide
  have hB : readingB formerRel 1 mansion owns 0 true := by
    unfold readingB formerRel π mansion owns; decide
  rw [h] at hA
  exact hA hB

end FormerMansion

end ParteeBorschev2003
