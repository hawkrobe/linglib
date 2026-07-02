import Linglib.Semantics.Possessive.Basic

/-!
# Partee & Borschev 2003: Genitives, relational nouns, and argument-modifier ambiguity

Paper-anchored consumer of the relational/possessive substrate for
[partee-borschev-2003]. P&B defend a **split** analysis of the genitive against
the **uniform "argument-only"** analysis of [vikner-jensen-2002] (J&V): some
genitives are *arguments* of a relational noun, others are *modifiers* carrying
a free contextual relation. The two construction types map exactly onto the
substrate:

* **argument genitive** (relational head noun supplies R): `of John's = λR[R(John)]`,
  `teacher of John's = λx[teacher(John)(x)]` — this is `viaArgument`.
* **modifier genitive** (sortal head noun + free relation `Rᵢ`):
  `of John's = λPλx[P(x) ∧ Rᵢ(John)(x)]`, `team of John's = λx[team(x) ∧ Rᵢ(John)(x)]`
  — this is `viaModifier` (Barker's `π`).

## Main statements

* `vj_coerce_eq_pb_modifier` — **convergence** (P&B §4.3): for a pragmatically
  coerced sortal noun, J&V's "coerce to a relation, then take as argument" and
  P&B's modifier genitive yield the *same* predicate. The accounts differ only
  in *where* the free relation enters, not in truth conditions — `rfl`.
* `FormerMansion.readingA_ne_readingB` — **divergence** (P&B §4.3, *Mary's former
  mansion*): under the modifier *former*, putting the free relation inside vs.
  outside its scope gives different predicates. J&V's coercion derives both;
  P&B's split derives only the R-outside reading — J&V's empirical advantage.
* `predicateGenitive_eq` — P&B §5.1: the predicate genitive *John's* (*that team
  is John's*) is a bare ⟨e,t⟩ predicate `λx[Rᵢ(John)(x)]` = `viaArgument`,
  which the uniform argument-only approach cannot produce standalone.

## References

* [partee-borschev-2003]: Genitives, relational nouns, and argument-modifier
  ambiguity.
* [vikner-jensen-2002]: the uniform "argument-only" analysis P&B argue against.
-/

namespace ParteeBorschev2003

open ArgumentStructure.Relational
open Possessive

variable {E S : Type*}

/-! ### The two approaches converge on coerced sortals (P&B §4.3)

For *team of Mary's* both accounts derive `λx[team(x) ∧ Rᵢ(Mary)(x)]`. J&V coerce
*team* to the relation `π team Rᵢ` and apply the argument genitive; P&B apply the
modifier genitive directly. The free relation enters inside the coerced noun for
J&V, with the construction for P&B — but the result is identical. -/

/-- **Convergence** (P&B §4.3): J&V's coerce-then-argument equals P&B's modifier
genitive. The "two theories of genitives" are, on the coerced-sortal case, a
single denotation reached two ways. -/
theorem vj_coerce_eq_pb_modifier (possessor : E) (P : Pred1 E S) (R : Pred2 E S) :
    viaArgument possessor (π P R) = viaModifier possessor P R :=
  rfl

/-! ### The predicate genitive (P&B §5.1)

*That team is John's*: the genitive surfaces as a bare one-place predicate with a
free relation, `λx[Rᵢ(John)(x)]`. P&B argue this is not always reducible to an
elliptical argument NP, so English needs the modifier genitive — a problem for
the uniform argument-only approach. -/

/-- The predicate genitive *John's* is the possessee predicate `λx[R possessor x]`
= `viaArgument possessor R`, a genuine ⟨e,t⟩ predicate (here `Pred1`). -/
theorem predicateGenitive_eq (possessor : E) (R : Pred2 E S) :
    (fun x s => R possessor x s) = viaArgument possessor R :=
  rfl

/-! ### The readings of *Mary's former mansion* (P&B §4.3)

`former` (CN/CN) modifies the noun predicate; `formerRel` (TCN/TCN) modifies a
relation. With the free relation `R` *outside* `former` (Reading A) vs. *inside*
`formerRel`'s scope (Reading B), the genitive denotes differently. P&B's split
introduces `R` only with the construction, after `former`, deriving Reading A
alone; J&V's coercion can introduce `R` at the noun-shift, deriving both. -/

/-- Reading A: the free relation is outside `former`'s scope — *a former mansion
that is now Mary's*. The only reading P&B's split derives. -/
def readingA (former : Pred1 E S → Pred1 E S) (possessor : E)
    (noun : Pred1 E S) (R : Pred2 E S) : Pred1 E S :=
  viaModifier possessor (former noun) R

/-- Reading B: the free relation is inside `formerRel`'s scope — *something that
was formerly Mary's mansion*. Available on J&V's coercion. -/
def readingB (formerRel : Pred2 E S → Pred2 E S) (possessor : E)
    (noun : Pred1 E S) (R : Pred2 E S) : Pred1 E S :=
  viaArgument possessor (formerRel (π noun R))

namespace FormerMansion

/-- Entities: building `0`, Mary `1`. -/
abbrev Ent := Fin 2
/-- Time: `true` now, `false` past. -/
abbrev Tm := Bool

/-- The building `0` is a mansion at every time. -/
def mansion : Pred1 Ent Tm := fun x _ => x = 0
/-- Mary (`1`) owned the building (`0`) only in the past. -/
def owns : Pred2 Ent Tm := fun o x t => o = 1 ∧ x = 0 ∧ t = false
/-- *former* P: was P in the past, no longer P now. -/
def former (P : Pred1 Ent Tm) : Pred1 Ent Tm := fun x t => P x false ∧ ¬ P x t
/-- *former* on a relation: held in the past, no longer. -/
def formerRel (Rel : Pred2 Ent Tm) : Pred2 Ent Tm :=
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
    unfold readingA viaModifier π former mansion owns; decide
  have hB : readingB formerRel 1 mansion owns 0 true := by
    unfold readingB viaArgument formerRel π mansion owns; decide
  rw [h] at hA
  exact hA hB

end FormerMansion

end ParteeBorschev2003
