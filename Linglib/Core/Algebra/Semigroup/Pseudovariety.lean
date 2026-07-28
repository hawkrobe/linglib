/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Semigroup.Pseudovariety`.
-/
import Linglib.Core.Algebra.Semigroup.IdempotentPower
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.PUnit

/-!
# Pseudovarieties of finite semigroups

A **pseudovariety of finite semigroups** ([eilenberg-1976]) is a class of finite semigroups closed
under subsemigroups, quotients, and finite direct products. It is the semigroup-side counterpart of
`Monoid.Pseudovariety`, and the two are not interchangeable: the classes `D`, `K` and `LI` below
are semigroup varieties that collapse over monoids, since applying their defining condition to the
idempotent `1` forces triviality.

The conditions are stated on idempotents, as Eilenberg states them: `D` is `Se = e`
([eilenberg-1976] VIII.4.1) and `LI` is `eSe = e` (VIII.5.1), with `K` the left-right dual of `D`.
Quotient closure is where the semigroup case departs from the monoid one — a preimage of an
idempotent need not be idempotent — and is discharged by
`Semigroup.exists_isIdempotentElem_map_eq`.

## Main definitions

* `Semigroup.Pseudovariety`: a class of finite semigroups closed under subsemigroup, quotient,
  product.
* `Semigroup.IsDefinite`, `IsReverseDefinite`, `IsLocallyTrivial`: the defining conditions of
  `D`, `K`, `LI`.
* `Semigroup.definiteVariety`, `reverseDefiniteVariety`, `locallyTrivialVariety`: the bundled
  pseudovarieties.

## Implementation notes

`mem` is a total predicate over `Type u` semigroups, mirroring `Monoid.Pseudovariety`; the
finiteness characteristic of a *pseudo*variety lives on the closure-field hypotheses. The variety
`N` of nilpotent semigroups is the intersection of `D` and `K` and is not bundled here.
-/

universe u

namespace Semigroup

/-- A **pseudovariety of finite semigroups**: a class closed under subsemigroups, quotients, and
finite products. Closure is phrased via injective/surjective `MulHom`s (the divisor form). -/
structure Pseudovariety where
  /-- The semigroups belonging to the pseudovariety. -/
  mem : ∀ (S : Type u) [Semigroup S], Prop
  /-- Closed under subsemigroups: an injective homomorphism into a member has member domain. -/
  sub : ∀ {S T : Type u} [Semigroup S] [Semigroup T] [Finite S] [Finite T] {f : S →ₙ* T},
    Function.Injective f → mem T → mem S
  /-- Closed under quotients: a surjective homomorphism from a member has member codomain. -/
  quot : ∀ {S T : Type u} [Semigroup S] [Semigroup T] [Finite S] [Finite T] {f : S →ₙ* T},
    Function.Surjective f → mem S → mem T
  /-- Closed under binary products. -/
  prod : ∀ {S T : Type u} [Semigroup S] [Semigroup T] [Finite S] [Finite T],
    mem S → mem T → mem (S × T)
  /-- Contains the trivial semigroup (the empty product). -/
  memUnit : mem PUnit.{u + 1}

namespace Pseudovariety

variable (V : Pseudovariety.{u})

/-- Closed under isomorphism (a special case of `quot`). -/
theorem mem_of_mulEquiv {S T : Type u} [Semigroup S] [Semigroup T] [Finite S] [Finite T]
    (e : S ≃* T) (h : V.mem S) : V.mem T :=
  V.quot (f := e.toMulHom) e.surjective h

end Pseudovariety

variable {S T : Type*} [Semigroup S] [Semigroup T]

/-! ### The conditions defining `D`, `K` and `LI` -/

/-- A finite semigroup is **definite** when every idempotent absorbs on the left: `Se = e`
([eilenberg-1976] VIII.4.1). -/
def IsDefinite (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, s * e = e

/-- A finite semigroup is **reverse definite** when every idempotent absorbs on the right — the
left-right dual of `IsDefinite`. -/
def IsReverseDefinite (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, e * s = e

/-- A finite semigroup is **locally trivial** when every idempotent absorbs on both sides at once:
`eSe = e` ([eilenberg-1976] VIII.5.1). This is the condition behind the generalized definite
languages. -/
def IsLocallyTrivial (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, e * s * e = e

/-- The image of an idempotent is idempotent. -/
private theorem isIdempotentElem_map {e : S} (he : IsIdempotentElem e) (f : S →ₙ* T) :
    IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, he]

/-! ### Closure properties -/

theorem IsDefinite.of_injective {f : S →ₙ* T} (hf : Function.Injective f) (h : IsDefinite T) :
    IsDefinite S := fun e he s => hf <| by rw [map_mul, h (f e) (isIdempotentElem_map he f) (f s)]

theorem IsReverseDefinite.of_injective {f : S →ₙ* T} (hf : Function.Injective f)
    (h : IsReverseDefinite T) : IsReverseDefinite S := fun e he s => hf <| by
  rw [map_mul, h (f e) (isIdempotentElem_map he f) (f s)]

theorem IsLocallyTrivial.of_injective {f : S →ₙ* T} (hf : Function.Injective f)
    (h : IsLocallyTrivial T) : IsLocallyTrivial S := fun e he s => hf <| by
  rw [map_mul, map_mul, h (f e) (isIdempotentElem_map he f) (f s)]

theorem IsDefinite.prod (hS : IsDefinite S) (hT : IsDefinite T) : IsDefinite (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

theorem IsReverseDefinite.prod (hS : IsReverseDefinite S) (hT : IsReverseDefinite T) :
    IsReverseDefinite (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

theorem IsLocallyTrivial.prod (hS : IsLocallyTrivial S) (hT : IsLocallyTrivial T) :
    IsLocallyTrivial (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

/-- A definite semigroup is locally trivial: apply `Se = e` at the element `e * s`. -/
theorem IsDefinite.isLocallyTrivial (h : IsDefinite S) : IsLocallyTrivial S :=
  fun e he s => h e he (e * s)

/-- A reverse definite semigroup is locally trivial: apply `eS = e` twice. -/
theorem IsReverseDefinite.isLocallyTrivial (h : IsReverseDefinite S) : IsLocallyTrivial S :=
  fun e he s => by rw [h e he s, h e he e]

variable [Finite S]

theorem IsDefinite.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f) (h : IsDefinite S) :
    IsDefinite T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, h e he s]

theorem IsReverseDefinite.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f)
    (h : IsReverseDefinite S) : IsReverseDefinite T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, h e he s]

theorem IsLocallyTrivial.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f)
    (h : IsLocallyTrivial S) : IsLocallyTrivial T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, ← map_mul, h e he s]

/-! ### The bundled pseudovarieties -/

/-- The pseudovariety **D** of definite semigroups. -/
def definiteVariety : Pseudovariety.{u} where
  mem S := IsDefinite S
  sub hf h := h.of_injective hf
  quot hf h := h.of_surjective hf
  prod hS hT := hS.prod hT
  memUnit _ _ _ := rfl

/-- The pseudovariety **K** of reverse definite semigroups. -/
def reverseDefiniteVariety : Pseudovariety.{u} where
  mem S := IsReverseDefinite S
  sub hf h := h.of_injective hf
  quot hf h := h.of_surjective hf
  prod hS hT := hS.prod hT
  memUnit _ _ _ := rfl

/-- The pseudovariety **LI** of locally trivial semigroups. -/
def locallyTrivialVariety : Pseudovariety.{u} where
  mem S := IsLocallyTrivial S
  sub hf h := h.of_injective hf
  quot hf h := h.of_surjective hf
  prod hS hT := hS.prod hT
  memUnit _ _ _ := rfl

@[simp] theorem mem_definiteVariety {S : Type u} [Semigroup S] :
    definiteVariety.mem S ↔ IsDefinite S := Iff.rfl

@[simp] theorem mem_reverseDefiniteVariety {S : Type u} [Semigroup S] :
    reverseDefiniteVariety.mem S ↔ IsReverseDefinite S := Iff.rfl

@[simp] theorem mem_locallyTrivialVariety {S : Type u} [Semigroup S] :
    locallyTrivialVariety.mem S ↔ IsLocallyTrivial S := Iff.rfl

end Semigroup
