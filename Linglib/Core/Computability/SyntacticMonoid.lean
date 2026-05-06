/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.GroupTheory.Congruence.Defs

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

(Myhill 1957; see e.g. @cite{pin-2020} §I.5).

## Main definitions

* `Language.SyntacticEquiv L u v` — the two-sided context-equivalence
  relation on words.
* `Language.syntacticCon L : Con (FreeMonoid α)` — the syntactic
  congruence, packaged as a multiplicative congruence on the free
  monoid (concatenation).
* `Language.syntacticMonoid L` — the quotient monoid
  `(syntacticCon L).Quotient`.

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
the `Setoid` via the definitional equality (`Setoid (List α)` is `Setoid
(FreeMonoid α)` definitionally). Inside `mul'`, the `Mul`-on-`FreeMonoid`
operation is bridged to `List.append` by way of `FreeMonoid.toList`,
which is an `Equiv.refl _` — every use of `FreeMonoid.toList` is
definitionally a no-op, but it makes the elaborator's job explicit.

## References

* @cite{myhill-1957}
* @cite{nerode-1958}
* @cite{pin-2020}, Chapter I (algebraic preliminaries on syntactic
  monoids and the syntactic-monoid characterization of star-free
  languages — the "Schützenberger theorem").

## Mathlib placement note

This file is structured to be promotable to mathlib as a sibling of
`Mathlib.Computability.MyhillNerode`. The `Language.SyntacticEquiv`
relation uses only `++` and `Language` membership; the `Con` packaging
uses only `Mathlib.GroupTheory.Congruence.Defs`. The
finite-syntactic-monoid theorem composes with mathlib's existing
`IsRegular.finite_range_leftQuotient`.
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
`Equiv.refl _`) bridges the `Mul`-on-`FreeMonoid` operation to
`List.append`. -/
def syntacticCon (L : Language α) : Con (FreeMonoid α) where
  toSetoid := syntacticSetoid L
  mul' := by
    intro w x y z hwx hyz a b
    -- Bridge `*` (FreeMonoid mul) to `++` (List append) via `toList`.
    show a ++ FreeMonoid.toList (w * y) ++ b ∈ L ↔
         a ++ FreeMonoid.toList (x * z) ++ b ∈ L
    -- `toList (u * v) = toList u ++ toList v` definitionally.
    have hwy : FreeMonoid.toList (w * y) =
        FreeMonoid.toList w ++ FreeMonoid.toList y := rfl
    have hxz : FreeMonoid.toList (x * z) =
        FreeMonoid.toList x ++ FreeMonoid.toList z := rfl
    rw [hwy, hxz]
    -- hwx : SyntacticEquiv L w x; treat w, x as List α via defEq.
    have h1 := hwx a (FreeMonoid.toList y ++ b)
    -- h1 : a ++ w ++ (toList y ++ b) ∈ L ↔ a ++ x ++ (toList y ++ b) ∈ L
    have h2 := hyz (a ++ FreeMonoid.toList x) b
    -- h2 : (a ++ toList x) ++ y ++ b ∈ L ↔ (a ++ toList x) ++ z ++ b ∈ L
    -- Reassociate the two sides of the goal so they match h1's LHS / h2's RHS.
    have lhs_assoc : a ++ (FreeMonoid.toList w ++ FreeMonoid.toList y) ++ b =
        a ++ FreeMonoid.toList w ++ (FreeMonoid.toList y ++ b) := by
      simp [List.append_assoc]
    have rhs_assoc : a ++ (FreeMonoid.toList x ++ FreeMonoid.toList z) ++ b =
        a ++ FreeMonoid.toList x ++ (FreeMonoid.toList z ++ b) := by
      simp [List.append_assoc]
    rw [lhs_assoc, rhs_assoc]
    have h2' : a ++ FreeMonoid.toList x ++ (FreeMonoid.toList y ++ b) ∈ L ↔
               a ++ FreeMonoid.toList x ++ (FreeMonoid.toList z ++ b) ∈ L := by
      have eql : (a ++ FreeMonoid.toList x) ++ FreeMonoid.toList y ++ b =
          a ++ FreeMonoid.toList x ++ (FreeMonoid.toList y ++ b) :=
        List.append_assoc _ _ _
      have eqr : (a ++ FreeMonoid.toList x) ++ FreeMonoid.toList z ++ b =
          a ++ FreeMonoid.toList x ++ (FreeMonoid.toList z ++ b) :=
        List.append_assoc _ _ _
      rw [← eql, ← eqr]; exact h2
    exact h1.trans h2'

/-- The *syntactic monoid* of `L`: the quotient of `FreeMonoid α` by the
syntactic congruence. Carries a `Monoid` structure inherited from
`Con.Quotient`. -/
abbrev syntacticMonoid (L : Language α) : Type _ := (syntacticCon L).Quotient

@[simp] lemma syntacticCon_apply (L : Language α) (u v : List α) :
    (syntacticCon L) u v ↔ SyntacticEquiv L u v := Iff.rfl

-- ============================================================================
-- § 3. Regularity ⟹ finite syntactic monoid
-- ============================================================================

/-- The action of a word on a left quotient: `(L.leftQuotient x).leftQuotient u
= L.leftQuotient (x ++ u)`. The closure-under-shift identity that makes
the syntactic-monoid action well-defined on `Set.range L.leftQuotient`. -/
private lemma leftQuotient_leftQuotient (L : Language α) (x u : List α) :
    (L.leftQuotient x).leftQuotient u = L.leftQuotient (x ++ u) := by
  ext y
  simp only [Language.mem_leftQuotient, List.append_assoc]

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
  haveI hfin : Finite LQ := h.finite_range_leftQuotient.to_subtype
  -- The action `Q ↦ Q.leftQuotient u` sends LQ to LQ.
  let action : FreeMonoid α → (LQ → LQ) := fun u Q =>
    ⟨Q.val.leftQuotient (FreeMonoid.toList u), by
      obtain ⟨x, hx⟩ := Q.prop
      refine ⟨x ++ FreeMonoid.toList u, ?_⟩
      rw [← hx, leftQuotient_leftQuotient]⟩
  -- Action descends to the syntactic monoid.
  have action_well_defined :
      ∀ u v : FreeMonoid α, SyntacticEquiv L u v → action u = action v := by
    intro u v huv
    funext Q
    obtain ⟨x, hx⟩ := Q.prop
    apply Subtype.ext
    show Q.val.leftQuotient (FreeMonoid.toList u) =
         Q.val.leftQuotient (FreeMonoid.toList v)
    rw [← hx, leftQuotient_leftQuotient, leftQuotient_leftQuotient]
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
      rw [leftQuotient_leftQuotient, leftQuotient_leftQuotient] at hsub
      exact hsub
    show a ++ FreeMonoid.toList u ++ b ∈ L ↔
         a ++ FreeMonoid.toList v ++ b ∈ L
    show b ∈ L.leftQuotient (a ++ FreeMonoid.toList u) ↔
         b ∈ L.leftQuotient (a ++ FreeMonoid.toList v)
    rw [key]
  exact Finite.of_injective phi phi_inj

end Language
