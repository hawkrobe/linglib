/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.Group.Aperiodic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Finite.Defs

/-!
# Pseudovarieties of finite monoids

A **pseudovariety** of finite monoids ([eilenberg-1976], [almeida-1995]) is a class of finite
monoids closed under taking submonoids, quotients (homomorphic images), and finite direct products
(the empty product being the trivial monoid). Pseudovarieties are the algebraic side of the
Eilenberg correspondence: the recognizable-language classes closed under the boolean / quotient /
inverse-homomorphism operations are exactly `{L | L.syntacticMonoid ∈ V}` for `V` a pseudovariety.

## Main definitions

* `Monoid.Pseudovariety` — a class of finite monoids closed under submonoid, quotient, product.
* `Monoid.aperiodicVariety` — the pseudovariety **A** of aperiodic monoids (the star-free side).

## Implementation notes

`mem` is a *total* predicate over `Type u` monoids (no `[Finite]` binder), mirroring
`Monoid.IsAperiodic`; the finiteness restriction characteristic of a *pseudo*variety lives on the
closure-field hypotheses, where it is used. This lets `V.mem M` be stated before a `Finite M`
instance is in scope (as in the language-side operator `Pseudovariety.langs`, where finiteness is
recovered from regularity).

Like mathlib's `MorphismProperty`, a `Pseudovariety` is relative to a *fixed* universe `u` (structure
fields cannot be universe-polymorphic); concrete pseudovarieties such as `aperiodicVariety` are
universe-polymorphic `def`s producing one `Pseudovariety.{u}` per `u`, so nothing is lost in use.
-/

universe u

namespace Monoid

/-- A **pseudovariety of finite monoids**: a class closed under submonoids, quotients, and finite
products. Submonoid/quotient closure is phrased via injective/surjective monoid homomorphisms (the
divisor form), which is what the closure proofs and the syntactic-monoid arguments consume. -/
structure Pseudovariety where
  /-- The monoids belonging to the pseudovariety. -/
  mem : ∀ (M : Type u) [Monoid M], Prop
  /-- Closed under submonoids: an injective homomorphism into a member has member domain. -/
  sub : ∀ {M N : Type u} [Monoid M] [Monoid N] [Finite M] [Finite N] {f : M →* N},
    Function.Injective f → mem N → mem M
  /-- Closed under quotients: a surjective homomorphism from a member has member codomain. -/
  quot : ∀ {M N : Type u} [Monoid M] [Monoid N] [Finite M] [Finite N] {f : M →* N},
    Function.Surjective f → mem M → mem N
  /-- Closed under binary products. -/
  prod : ∀ {M N : Type u} [Monoid M] [Monoid N] [Finite M] [Finite N],
    mem M → mem N → mem (M × N)
  /-- Contains the trivial monoid (the empty product). -/
  memUnit : mem PUnit.{u + 1}

namespace Pseudovariety

variable (V : Pseudovariety.{u})

/-- Closed under isomorphism (a special case of `quot`). -/
theorem mem_of_mulEquiv {M N : Type u} [Monoid M] [Monoid N] [Finite M] [Finite N]
    (e : M ≃* N) (h : V.mem M) : V.mem N :=
  V.quot (f := e.toMonoidHom) e.surjective h

end Pseudovariety

/-- The **pseudovariety of aperiodic monoids** `A` — the algebraic counterpart of the star-free
languages ([schutzenberger-1965]). The four closure obligations are the corresponding
`Monoid.IsAperiodic` lemmas. -/
def aperiodicVariety : Pseudovariety.{u} where
  mem M := IsAperiodic M
  sub hf h := h.of_injective hf
  quot hf h := h.of_surjective hf
  prod hM hN := hM.prod hN
  memUnit := IsAperiodic.of_subsingleton

@[simp] theorem mem_aperiodicVariety {M : Type u} [Monoid M] :
    aperiodicVariety.mem M ↔ IsAperiodic M := Iff.rfl

end Monoid
