import Linglib.Semantics.Possession.Basic

/-!
# Partee & Borschev 2003: Genitives, relational nouns, and argument-modifier ambiguity

Paper-anchored consumer of the relational/possessive substrate for
[partee-borschev-2003]. P&B defend a **split** analysis of the genitive against
the **uniform "argument-only"** analysis of [vikner-jensen-2002] (J&V): some
genitives are *arguments* of a relational noun, others are *modifiers* carrying
a free contextual relation. The two construction types map exactly onto the
substrate:

* **argument genitive** (relational head noun supplies R): `of John's = λR[R(John)]`,
  `teacher of John's = λx[teacher(John)(x)]` — the relational noun applied to its
  possessor, `teacher John`.
* **modifier genitive** (sortal head noun + free relation `Rᵢ`):
  `of John's = λPλx[P(x) ∧ Rᵢ(John)(x)]`, `team of John's = λx[team(x) ∧ Rᵢ(John)(x)]`
  — Barker's `π team Rᵢ` applied to the possessor.

## Main statements

* **Convergence** (P&B §4.3): for a pragmatically coerced sortal noun, J&V's "coerce
  to a relation, then take as argument" and P&B's modifier genitive assemble the
  same term `π team Rᵢ Mary`; the accounts differ only in *where* the free relation
  enters, not in truth conditions.
* `FormerMansion.readingA_ne_readingB` — **divergence** (P&B §4.3, *Mary's former
  mansion*): under the modifier *former*, putting the free relation inside vs.
  outside its scope gives different predicates. J&V's coercion derives both;
  P&B's split derives only the R-outside reading — J&V's empirical advantage.

## References

* [partee-borschev-2003]: Genitives, relational nouns, and argument-modifier
  ambiguity.
* [vikner-jensen-2002]: the uniform "argument-only" analysis P&B argue against.
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
def mansion : Ent → Tm → Prop := fun x _ => x = 0
/-- Mary (`1`) owned the building (`0`) only in the past. -/
def owns : Ent → Ent → Tm → Prop := fun o x t => o = 1 ∧ x = 0 ∧ t = false
/-- *former* P: was P in the past, no longer P now. -/
def former (P : Ent → Tm → Prop) : Ent → Tm → Prop := fun x t => P x false ∧ ¬ P x t
/-- *former* on a relation: held in the past, no longer. -/
def formerRel (Rel : Ent → Ent → Tm → Prop) : Ent → Ent → Tm → Prop :=
  fun o x t => Rel o x false ∧ ¬ Rel o x t

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
