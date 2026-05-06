/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Range
import Mathlib.GroupTheory.Congruence.Hom

/-!
# Syntactic Monoid

The *syntactic monoid* of a language `L : Language α` is the quotient of
the free monoid `FreeMonoid α` by the *syntactic congruence* `~_S`,
where `u ~_S v` iff no two-sided context distinguishes them as
`L`-members: `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.

This file is the two-sided dual of `Mathlib.Computability.MyhillNerode`,
which constructs the right-Nerode quotient (`Language.leftQuotient`)
and proves regularity ↔ finitely many left quotients. The syntactic
monoid is a strictly more refined invariant: it carries a *monoid*
structure (not just a setoid of states), and the bidirectional version
of the Myhill–Nerode theorem is

> `L.IsRegular ↔ Finite L.syntacticMonoid`

(Myhill 1957; see e.g. Pin's *Mathematical Foundations of Automata
Theory*, Chapter I).

The empty word `[] : FreeMonoid α` becomes the identity of
`syntacticMonoid L`. Some classical references (e.g. the Lambert (2026)
phonology consumer of this file) work with the syntactic *semigroup*
instead, omitting the empty word; the two characterisations coincide
for the regularity ↔ finiteness statement, but the monoid version is
mathlib-natural via `Con (FreeMonoid α)`.

## Main definitions

* `Language.SyntacticEquiv L u v` — the two-sided context-equivalence
  relation on words.
* `Language.syntacticCon L : Con (FreeMonoid α)` — the syntactic
  congruence, packaged as a multiplicative congruence on the free
  monoid (concatenation).
* `Language.syntacticMonoid L` — the quotient monoid
  `(syntacticCon L).Quotient`.
* `Language.toSyntacticMonoid L : FreeMonoid α →* L.syntacticMonoid`
  — the canonical projection (`(syntacticCon L).mk'`).

## Main results

* `Language.SyntacticEquiv.leftQuotient_eq` — the syntactic equivalence
  refines the right-Nerode equivalence (a syntactic-equivalent pair has
  the same left quotient). The reverse implication does *not* hold.
* `Language.IsRegular.finite_syntacticMonoid` — Myhill direction A: if
  `L` is regular then its syntactic monoid is finite. Proved via the
  injection `[u] ↦ (Q ↦ Q.leftQuotient u)` from `syntacticMonoid L`
  into the function space `LQ → LQ` where `LQ = Set.range L.leftQuotient`
  is finite by `Language.IsRegular.finite_range_leftQuotient`.

The reverse direction (finite syntactic monoid ⟹ regular) is
classical and follows from the syntactic monoid acting on itself; it is
left as a TODO since it needs additional substrate (a `Finite`-bounded
DFA construction from a finite monoid action).

## Implementation notes

`FreeMonoid α` is `def`-equal to `List α`, but Lean's typeclass
elaborator does not unfold the `def`. The `SyntacticEquiv` predicate is
stated on `List α` (so that `++` and `Language.leftQuotient` work
without coercion gymnastics) and the `Con (FreeMonoid α)` upgrade reuses
the `Setoid` via the definitional equality. Inside `mul'`, the
`Mul`-on-`FreeMonoid` operation is bridged to `List.append` by way of
`FreeMonoid.toList`, which is an `Equiv.refl _`.

## References

* Myhill (1957), Nerode (1958)
* Pin, *Mathematical Foundations of Automata Theory*, Chapter I.

## Mathlib placement note

This file is structured to be promotable to mathlib as a sibling of
`Mathlib.Computability.MyhillNerode`. The `Language.SyntacticEquiv`
relation uses only `++` and `Language` membership; the `Con` packaging
uses only `Mathlib.GroupTheory.Congruence.Defs`. The
finite-syntactic-monoid theorem composes with mathlib's existing
`IsRegular.finite_range_leftQuotient` and `leftQuotient_append`.
-/

namespace Language

variable {α : Type*}

-- ============================================================================
-- § 1. Syntactic equivalence (on words)
-- ============================================================================

/-- Two words `u, v : List α` are *syntactically equivalent* w.r.t. `L`
iff no two-sided context `(x, y)` distinguishes them as `L`-members.
The largest left- and right-concatenation-stable equivalence contained
in `(· ∈ L)`. -/
def SyntacticEquiv (L : Language α) (u v : List α) : Prop :=
  ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

namespace SyntacticEquiv

variable {L : Language α} {u v w : List α}

@[refl] protected theorem refl (u : List α) : SyntacticEquiv L u u :=
  fun _ _ => Iff.rfl

@[symm] protected theorem symm (h : SyntacticEquiv L u v) :
    SyntacticEquiv L v u :=
  fun x y => (h x y).symm

@[trans] protected theorem trans
    (h1 : SyntacticEquiv L u v) (h2 : SyntacticEquiv L v w) :
    SyntacticEquiv L u w :=
  fun x y => (h1 x y).trans (h2 x y)

/-- Specialising the two-sided test to `x = []` shows that the syntactic
equivalence refines the right-Nerode equivalence: equivalent words have
the same `Language.leftQuotient`. -/
theorem leftQuotient_eq (h : SyntacticEquiv L u v) :
    L.leftQuotient u = L.leftQuotient v := by
  ext y
  have := h [] y
  simpa using this

end SyntacticEquiv

-- ============================================================================
-- § 2. Syntactic congruence and syntactic monoid
-- ============================================================================

/-- The syntactic equivalence as a `Setoid` on `FreeMonoid α`. The
underlying carrier is `FreeMonoid α := List α` definitionally, so
`SyntacticEquiv L : List α → List α → Prop` reuses without coercion. -/
def syntacticSetoid (L : Language α) : Setoid (FreeMonoid α) where
  r := SyntacticEquiv L
  iseqv := ⟨SyntacticEquiv.refl, SyntacticEquiv.symm, SyntacticEquiv.trans⟩

/-- The *syntactic congruence* of `L`: the syntactic equivalence,
upgraded with the multiplicative-congruence law (closure under
two-sided concatenation). The proof of `mul'` reassociates a two-sided
context using `List.append_assoc`; `FreeMonoid.toList` (an
`Equiv.refl _`) bridges `*`-on-`FreeMonoid` to `++`-on-`List`. -/
def syntacticCon (L : Language α) : Con (FreeMonoid α) where
  toSetoid := syntacticSetoid L
  mul' := by
    intro w x y z hwx hyz a b
    -- `(w * y).toList = w.toList ++ y.toList` by `rfl`.
    show a ++ (FreeMonoid.toList w ++ FreeMonoid.toList y) ++ b ∈ L ↔
         a ++ (FreeMonoid.toList x ++ FreeMonoid.toList z) ++ b ∈ L
    have h1 := hwx a (FreeMonoid.toList y ++ b)
    have h2 := hyz (a ++ FreeMonoid.toList x) b
    -- Reassociate both sides to chain h1 and h2.
    simp only [List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2

/-- The *syntactic monoid* of `L`: the quotient of `FreeMonoid α` by the
syntactic congruence. The `abbrev` is deliberate so `Monoid` typeclass
search resolves through `Con.Quotient`. -/
abbrev syntacticMonoid (L : Language α) : Type _ := (syntacticCon L).Quotient

/-- The canonical monoid homomorphism from the free monoid to the
syntactic monoid: each word is sent to its syntactic-equivalence class.
A renamed alias of the underlying `Con.mk'`. -/
def toSyntacticMonoid (L : Language α) : FreeMonoid α →* L.syntacticMonoid :=
  (syntacticCon L).mk'

@[simp] lemma toSyntacticMonoid_apply (L : Language α) (u : FreeMonoid α) :
    L.toSyntacticMonoid u = (syntacticCon L).toQuotient u := rfl

/-- **L is saturated by the syntactic congruence**: if `u ∈ L` and `u`
is syntactically equivalent to `v`, then `v ∈ L`. Direct specialisation
of `SyntacticEquiv` to the trivial two-sided context (`x = y = []`).
This is the core property of the syntactic congruence — it is the
*coarsest* congruence on `FreeMonoid α` for which `L` is a union of
classes. -/
theorem mem_iff_of_syntacticEquiv {L : Language α} {u v : List α}
    (h : SyntacticEquiv L u v) : u ∈ L ↔ v ∈ L := by
  simpa using h [] []

-- ============================================================================
-- § 3. Universal property: every L-recognising hom factors through the
--     syntactic monoid
-- ============================================================================

/-- A monoid hom `φ : FreeMonoid α →* M` *recognises* a language `L`
when `L` is a union of `φ`-fibres: there is some accepting set `S ⊆ M`
with `L = φ⁻¹ S`. Equivalently, membership in `L` depends only on the
`φ`-image. The standard textbook definition (Pin, *Mathematical
Foundations of Automata Theory*, Chapter I). -/
def Recognises {α : Type*} {M : Type*} [Monoid M]
    (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = φ ⁻¹' S

/-- **Universal property** (kernel direction): every L-recognising hom's
kernel is contained in the syntactic congruence. The syntactic
congruence is the *coarsest* congruence on `FreeMonoid α` saturating
`L`; any other saturating congruence (such as `Con.ker φ` for a
recognising `φ`) is finer. Composing with mathlib's `Con.lift` then
gives the factoring `MonoidHom`:
`(syntacticCon L).lift φ syntacticCon_ge_ker_of_recognises`. -/
theorem syntacticCon_ge_ker_of_recognises {L : Language α} {M : Type*}
    [Monoid M] {φ : FreeMonoid α →* M} (hrec : Recognises φ L) :
    Con.ker φ ≤ syntacticCon L := by
  obtain ⟨S, hS⟩ := hrec
  intro u v huv
  -- `huv : Con.ker φ u v` unfolds to `φ u = φ v` (via `Setoid.ker`).
  -- Goal `SyntacticEquiv L u v` unfolds (via defEq `List α = FreeMonoid α`)
  -- to `∀ x y : FreeMonoid α, x * u * y ∈ L ↔ x * v * y ∈ L`.
  change ∀ x y : FreeMonoid α, x * u * y ∈ L ↔ x * v * y ∈ L
  intro x y
  have step : ∀ w : FreeMonoid α, w ∈ L ↔ φ w ∈ S := fun w => by rw [hS]; rfl
  rw [step, step, φ.map_mul, φ.map_mul, φ.map_mul, φ.map_mul, huv]

-- ============================================================================
-- § 4. Regularity ⟹ finite syntactic monoid
-- ============================================================================

/-- **Myhill direction A**: a regular language has a finite syntactic
monoid. Proved by injecting `syntacticMonoid L` into the finite function
space `LQ → LQ`, where `LQ = Set.range L.leftQuotient` (finite by
`IsRegular.finite_range_leftQuotient`). The action `[u] ↦ (Q ↦
Q.leftQuotient u)` is well-defined on the syntactic congruence (by
`SyntacticEquiv.leftQuotient_eq` lifted to all left contexts) and
injective (because two `u, v` with the same action are syntactically
equivalent — every two-sided test factors through some left quotient). -/
theorem IsRegular.finite_syntacticMonoid {L : Language α} (h : L.IsRegular) :
    Finite L.syntacticMonoid := by
  classical
  set LQ : Set (Language α) := Set.range L.leftQuotient with hLQ_def
  haveI : Finite LQ := h.finite_range_leftQuotient.to_subtype
  -- The action `Q ↦ Q.leftQuotient u` sends LQ to LQ via `leftQuotient_append`.
  let action : FreeMonoid α → (LQ → LQ) := fun u Q =>
    ⟨Q.val.leftQuotient (FreeMonoid.toList u), by
      obtain ⟨x, hx⟩ := Q.prop
      exact ⟨x ++ FreeMonoid.toList u, by
        rw [← hx, ← Language.leftQuotient_append]⟩⟩
  -- Action descends to the syntactic monoid.
  have action_well_defined :
      ∀ u v : FreeMonoid α, SyntacticEquiv L u v → action u = action v := by
    intro u v huv
    funext Q
    obtain ⟨x, hx⟩ := Q.prop
    apply Subtype.ext
    show Q.val.leftQuotient (FreeMonoid.toList u) =
         Q.val.leftQuotient (FreeMonoid.toList v)
    rw [← hx, ← Language.leftQuotient_append, ← Language.leftQuotient_append]
    -- Reduce to: L.leftQuotient (x ++ u) = L.leftQuotient (x ++ v).
    have hxshift : SyntacticEquiv L
        (x ++ FreeMonoid.toList u) (x ++ FreeMonoid.toList v) := by
      intro a b
      have := huv (a ++ x) b
      simpa [List.append_assoc] using this
    exact hxshift.leftQuotient_eq
  -- Lift the action through the quotient.
  let phi : L.syntacticMonoid → (LQ → LQ) := fun cls =>
    Quotient.liftOn' cls action action_well_defined
  -- Injectivity: equal action ⇒ syntactic equivalent.
  have phi_inj : Function.Injective phi := by
    rintro ⟨u⟩ ⟨v⟩ huv
    apply Quotient.sound
    intro a b
    -- Specialise the action equality at `Q := L.leftQuotient a`.
    have hQ : L.leftQuotient a ∈ LQ := ⟨a, rfl⟩
    have heq : (action u) ⟨L.leftQuotient a, hQ⟩ =
               (action v) ⟨L.leftQuotient a, hQ⟩ :=
      congr_fun huv ⟨L.leftQuotient a, hQ⟩
    have key : L.leftQuotient (a ++ FreeMonoid.toList u) =
               L.leftQuotient (a ++ FreeMonoid.toList v) := by
      have hsub : (L.leftQuotient a).leftQuotient (FreeMonoid.toList u) =
                  (L.leftQuotient a).leftQuotient (FreeMonoid.toList v) :=
        congr_arg Subtype.val heq
      rw [← Language.leftQuotient_append, ← Language.leftQuotient_append] at hsub
      exact hsub
    show b ∈ L.leftQuotient (a ++ FreeMonoid.toList u) ↔
         b ∈ L.leftQuotient (a ++ FreeMonoid.toList v)
    rw [key]
  exact Finite.of_injective phi phi_inj

-- ============================================================================
-- § 4. Finite syntactic monoid ⟹ regularity (reverse Myhill direction)
-- ============================================================================

/-- **Myhill direction B**: a language with finite syntactic monoid is
regular. Composes with mathlib's `Language.IsRegular.of_finite_range_leftQuotient`
via the canonical factoring of `L.leftQuotient` through the syntactic
monoid: `L.leftQuotient` is constant on syntactic-equivalence classes
(by `SyntacticEquiv.leftQuotient_eq`), so it descends to a function
`f : L.syntacticMonoid → Language α` whose range coincides with
`Set.range L.leftQuotient`. Finiteness of `L.syntacticMonoid` then
implies `Set.Finite (Set.range f) = Set.Finite (Set.range L.leftQuotient)`
via `Set.finite_range`, closing the right-Nerode finiteness condition. -/
theorem IsRegular.of_finite_syntacticMonoid {L : Language α}
    [Finite L.syntacticMonoid] : L.IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient
  -- The forgetful map `[u] ↦ L.leftQuotient u`, well-defined on classes.
  let f : L.syntacticMonoid → Language α := fun cls =>
    Quotient.liftOn' cls L.leftQuotient
      (fun _ _ huv => SyntacticEquiv.leftQuotient_eq huv)
  -- `Set.range L.leftQuotient = Set.range f` (factorisation through quotient).
  have hrange : Set.range L.leftQuotient = Set.range f := by
    ext L'
    refine ⟨fun ⟨u, hu⟩ => ⟨(syntacticCon L).toQuotient u, hu⟩, ?_⟩
    rintro ⟨cls, hcls⟩
    induction cls using Quotient.inductionOn' with
    | _ u => exact ⟨u, hcls⟩
  rw [hrange]
  exact Set.finite_range f

/-- **Myhill–Nerode (syntactic-monoid form)**: a language is regular iff
its syntactic monoid is finite. The bidirectional bundling of
`IsRegular.finite_syntacticMonoid` and `IsRegular.of_finite_syntacticMonoid`. -/
theorem isRegular_iff_finite_syntacticMonoid {L : Language α} :
    L.IsRegular ↔ Finite L.syntacticMonoid :=
  ⟨IsRegular.finite_syntacticMonoid, fun _ => IsRegular.of_finite_syntacticMonoid⟩

end Language
