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
  `PartialProp.presupOfReferent` applied to the selector at a context. Existing
  definite denotations *are* this, by `rfl` (see `Semantics.Reference.Donnellan`).
* `NominalDenot.toPartialProp` — the full denotation: `resolve` conjoined with the
  intrinsic presupposition, so a pronoun's φ-features project.

## Implementation notes

`resolve` is deliberately *just* `presupOfReferent` applied to the selector at
a context, so that the existing `presupOfReferent`-built definite denotations
fold into a `NominalDenot` by `rfl` without migrating any consumer; the
intrinsic presupposition is layered on separately in `toPartialProp`.

## Relation to the dynamic lookup interface

The unification this core was built toward is realized by the seam lemma
`PronounDenotation.interpPronoun_eq_iLookup`: the pronoun's static
`interpPronoun` selector *is* the `M = Id` extensional-baseline instance of
`DynamicSemantics.HasFiberedLookup.iLookup`, modulo the `Option`
partiality layer this signature adds. Static reference and dynamic
(`Set`/`PMF`) anaphora therefore meet at one lookup interface on the static
fiber, and bound pronouns share that selector with binding supplied externally
(`Semantics.Reference.Binding`).

Carrying the effect functor `M` *in this structure* (so `selector` is
`Ctx → W → M (Option E)` and literally `iLookup`) is deliberately **not** done
here: with only `Id` exercised it would be the same un-exercised generality
PR1 removed, and a faithful `resolve`/`toPartialProp` for `M ≠ Id` needs a
dynamic-semantic commitment (a nonempty-set / distribution presupposition) that
belongs with the first dynamic consumer that requires it. Until then the seam
lemma carries the connection.
-/

set_option autoImplicit false

namespace Semantics.Reference

open Semantics.Presupposition (PartialProp)

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
    (c : Ctx) : PartialProp W :=
  PartialProp.presupOfReferent (nd.selector c) scope

/-- An `ofReferent` resolved is exactly the canonical `presupOfReferent` — the
bridge every definite denotation folds across. -/
theorem ofReferent_resolve (referent : W → Option E) (scope : E → W → Prop) :
    (ofReferent referent).resolve scope ⟨⟩ = PartialProp.presupOfReferent referent scope :=
  rfl

/-- The full denotation: `resolve` conjoined with the intrinsic
presupposition. For a definite the intrinsic presupposition is vacuous, so
`toPartialProp` and `resolve` agree; for a pronoun the conjoined presupposition is
where the φ-features project. -/
def toPartialProp (nd : NominalDenot Ctx W E) (scope : E → W → Prop)
    (c : Ctx) : PartialProp W :=
  PartialProp.and { presup := nd.presup c, assertion := fun _ => True }
    (nd.resolve scope c)

/-! ### Monad structure

`NominalDenot Ctx W` is the presupposition-projecting partiality monad: `bind`
threads the partial referent (`Option.bind`) and accumulates presuppositions,
projecting the continuation's presupposition through definedness of the head
(`Option.elim`). This is what lets a re-selection (e.g. possessive-of) compose
as a Kleisli arrow while a head's intrinsic presupposition (φ-features, deixis)
rides along. -/

instance : Monad (NominalDenot Ctx W) where
  pure a := { presup := fun _ _ => True, selector := fun _ _ => some a }
  bind nd k :=
    { presup := fun c w =>
        nd.presup c w ∧ (nd.selector c w).elim True (fun e => (k e).presup c w)
      selector := fun c w => (nd.selector c w).bind (fun e => (k e).selector c w) }

/-- Extensionality: a `NominalDenot` is its presupposition and selector. -/
@[ext] theorem ext {nd₁ nd₂ : NominalDenot Ctx W E}
    (hp : nd₁.presup = nd₂.presup) (hs : nd₁.selector = nd₂.selector) : nd₁ = nd₂ := by
  cases nd₁; cases nd₂; cases hp; cases hs; rfl

universe u
variable {α β γ : Type u}

@[simp] theorem pure_selector (a : α) (c : Ctx) (w : W) :
    (pure a : NominalDenot Ctx W α).selector c w = some a := rfl

@[simp] theorem pure_presup (a : α) (c : Ctx) (w : W) :
    (pure a : NominalDenot Ctx W α).presup c w = True := rfl

@[simp] theorem bind_selector (nd : NominalDenot Ctx W α)
    (k : α → NominalDenot Ctx W β) (c : Ctx) (w : W) :
    (nd >>= k).selector c w = (nd.selector c w).bind (fun e => (k e).selector c w) := rfl

@[simp] theorem bind_presup (nd : NominalDenot Ctx W α)
    (k : α → NominalDenot Ctx W β) (c : Ctx) (w : W) :
    (nd >>= k).presup c w =
      (nd.presup c w ∧ (nd.selector c w).elim True (fun e => (k e).presup c w)) := rfl

/-- Left identity: feeding a pure referent to a continuation is the continuation
at that referent. -/
theorem pure_bind (a : α) (k : α → NominalDenot Ctx W β) :
    (pure a : NominalDenot Ctx W α) >>= k = k a := by
  ext c w <;> simp

/-- Right identity: re-selecting a denotation by `pure` is the identity. -/
theorem bind_pure (nd : NominalDenot Ctx W α) : nd >>= pure = nd := by
  ext c w <;>
    simp only [bind_presup, bind_selector, pure_presup, pure_selector] <;>
    cases nd.selector c w <;> simp

/-- Associativity: nested binds compose — the law that makes possessive nesting
(*John's mother's friend*) free. -/
theorem bind_assoc (nd : NominalDenot Ctx W α) (k : α → NominalDenot Ctx W β)
    (h : β → NominalDenot Ctx W γ) :
    nd >>= k >>= h = nd >>= fun a => k a >>= h := by
  ext c w <;>
    simp only [bind_presup, bind_selector] <;>
    cases nd.selector c w <;> simp [and_assoc]

end NominalDenot

end Semantics.Reference
