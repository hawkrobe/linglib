import Linglib.Semantics.Presupposition.Basic

/-!
# Nominal denotations: a unified presuppositional referential core

A pronoun, definite description, demonstrative, and bound variable are one
kind of thing — a presuppositional, assignment/context-relative individual
denotation — differing only in their *selector* (which individual: `g i`,
`ι`, the demonstratum) and their intrinsic *presupposition* (φ-features,
uniqueness, deixis). `NominalDenot` makes that common shape explicit.

This is the static core: the selector returns an `Option E` against a context
`Ctx` (an assignment for pronouns/bound variables, a discourse context for
definites). The dynamic case — where a selector returns a *family* of
referents (`Set`/`PMF` anaphora) — is the functor-parameterised
generalisation of this signature, to be added when a dynamic study needs it.

## Main definitions

* `NominalDenot Ctx W E` — intrinsic presupposition plus a partial referent
  selector.
* `NominalDenot.resolve` — resolve a nominal against a scope, as
  `PrProp.presupOfReferent` applied to the selector at a context. Existing
  definite denotations *are* this, by `rfl` (see `Semantics.Reference.Donnellan`).
* `NominalDenot.toPrProp` — the full denotation: `resolve` conjoined with the
  intrinsic presupposition, so a pronoun's φ-features project.

## Implementation notes

`resolve` is deliberately *just* `presupOfReferent` applied to the selector at
a context, so that the existing `presupOfReferent`-built definite denotations
fold into a `NominalDenot` by `rfl` without migrating any consumer; the
intrinsic presupposition is layered on separately in `toPrProp`.

## Relation to the dynamic lookup interface

The unification this core was built toward is realized by the seam lemma
`PronounDenotation.interpPronoun_eq_iLookup`: the pronoun's static
`interpPronoun` selector *is* the `M = Id` extensional-baseline instance of
`Semantics.Dynamic.Context.HasFiberedLookup.iLookup`, modulo the `Option`
partiality layer this signature adds. Static reference and dynamic
(`Set`/`PMF`) anaphora therefore meet at one lookup interface on the static
fiber, and bound pronouns share that selector with binding supplied externally
(`Semantics.Reference.Binding`).

Carrying the effect functor `M` *in this structure* (so `selector` is
`Ctx → W → M (Option E)` and literally `iLookup`) is deliberately **not** done
here: with only `Id` exercised it would be the same un-exercised generality
PR1 removed, and a faithful `resolve`/`toPrProp` for `M ≠ Id` needs a
dynamic-semantic commitment (a nonempty-set / distribution presupposition) that
belongs with the first dynamic consumer that requires it. Until then the seam
lemma carries the connection.
-/

set_option autoImplicit false

namespace Semantics.Reference

open Semantics.Presupposition (PrProp)

/-- A presuppositional, context-relative individual denotation.

`presup` is the intrinsic presupposition beyond definedness — φ-features for
a pronoun, deixis for a demonstrative, vacuous for a definite (whose only
presupposition is that the selector is defined). `selector` is the partial
choice of referent (`g i`, `ι`, the demonstratum) at a context and world. -/
structure NominalDenot (Ctx : Type*) (W : Type*) (E : Type*) where
  /-- Intrinsic presupposition beyond definedness (φ-features, deixis). -/
  presup : Ctx → W → Prop
  /-- The partial referent selector. -/
  selector : Ctx → W → Option E

namespace NominalDenot

variable {Ctx : Type*} {W : Type*} {E : Type*}

/-- The simplest nominal: a context-free referent selector with no intrinsic
presupposition — a bare iota/definite. `(ofReferent r).resolve scope ⟨⟩`
unfolds to `presupOfReferent r scope`, so any `presupOfReferent`-built
denotation is an `ofReferent` resolved (`ofReferent_resolve`). -/
def ofReferent (referent : W → Option E) : NominalDenot Unit W E where
  presup := fun _ _ => True
  selector := fun _ => referent

/-- Resolve a nominal against a `scope` at context `c`: the presuppositional
proposition whose presupposition is definedness of the selected referent and
whose assertion applies `scope` to it. This is just `presupOfReferent` over
`nd.selector c`, so any `presupOfReferent`-built denotation is a `resolve`, by
`rfl`. -/
def resolve (nd : NominalDenot Ctx W E) (scope : E → W → Prop)
    (c : Ctx) : PrProp W :=
  PrProp.presupOfReferent (nd.selector c) scope

/-- An `ofReferent` resolved is exactly the canonical `presupOfReferent` — the
bridge every definite denotation folds across. -/
theorem ofReferent_resolve (referent : W → Option E) (scope : E → W → Prop) :
    (ofReferent referent).resolve scope ⟨⟩ = PrProp.presupOfReferent referent scope :=
  rfl

/-- The full denotation: `resolve` conjoined with the intrinsic
presupposition. For a definite the intrinsic presupposition is vacuous, so
`toPrProp` and `resolve` agree; for a pronoun the conjoined presupposition is
where the φ-features project. -/
def toPrProp (nd : NominalDenot Ctx W E) (scope : E → W → Prop)
    (c : Ctx) : PrProp W :=
  PrProp.and { presup := nd.presup c, assertion := fun _ => True }
    (nd.resolve scope c)

end NominalDenot

end Semantics.Reference
