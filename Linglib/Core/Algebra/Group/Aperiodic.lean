/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Nat.Init
import Mathlib.Order.MinMax

/-!
# Aperiodic monoids

A monoid is **aperiodic** (group-free) when some power stabilises every element:
`∃ n, ∀ x, x ^ (n + 1) = x ^ n`. [schutzenberger-1965] introduced these as the monoids
with only trivial subgroups (his condition `γ fⁿ = γ fⁿ⁺¹`); they are the algebraic side
of the star-free / counter-free / `FO[<]`-definable languages ([pin-mfa],
[mcnaughton-papert-1971]).

`[UPSTREAM]`: mathlib has `Monoid.IsTorsion` but no aperiodicity notion; this is a
candidate for `Mathlib/Algebra/Group/`.

## Main results

* `Monoid.IsAperiodic.of_subsingleton` — subsingleton monoids are aperiodic.
* `Monoid.IsAperiodic.pow_stabilizes` — once a stabilising power is reached, all higher
  powers stabilise too.
* `Monoid.IsAperiodic.of_surjective` — aperiodicity passes along surjective homs.
* `Monoid.IsAperiodic.of_injective` — aperiodicity is inherited by submonoids.
* `Monoid.IsAperiodic.prod` — a product of aperiodic monoids is aperiodic.
* `Monoid.IsAperiodic.of_mulEquiv` — aperiodicity transports across isomorphisms.
-/

namespace Monoid

variable (M : Type*) [Monoid M]

/-- A monoid is **aperiodic** when some uniform power stabilises every element:
`∃ n, ∀ x, x ^ (n + 1) = x ^ n` — equivalently, it has only trivial subgroups
([schutzenberger-1965]). -/
def IsAperiodic : Prop := ∃ n : ℕ, ∀ x : M, x ^ (n + 1) = x ^ n

variable {M}

/-- A subsingleton monoid is aperiodic (take `n = 0`). -/
theorem IsAperiodic.of_subsingleton [Subsingleton M] : IsAperiodic M :=
  ⟨0, fun _ => Subsingleton.elim _ _⟩

/-- If `x ^ (n + 1) = x ^ n` then the power stabilises at every `m ≥ n`. -/
theorem IsAperiodic.pow_stabilizes {x : M} {n : ℕ} (h : x ^ (n + 1) = x ^ n) :
    ∀ m, n ≤ m → x ^ (m + 1) = x ^ m := by
  refine fun m hm => Nat.le_induction h (fun k _ hk => ?_) m hm
  rw [pow_succ x (k + 1), hk, ← pow_succ, hk]

/-- Aperiodicity passes along a surjective monoid hom: the same exponent works for the image. -/
theorem IsAperiodic.of_surjective {N : Type*} [Monoid N] {f : M →* N}
    (hf : Function.Surjective f) (hM : IsAperiodic M) : IsAperiodic N := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_pow, ← map_pow, hn]

/-- Aperiodicity is inherited by submonoids: if `f : M →* N` is injective and `N` is aperiodic
then so is `M` (the same exponent works, pulled back through `f`). -/
theorem IsAperiodic.of_injective {N : Type*} [Monoid N] {f : M →* N}
    (hf : Function.Injective f) (hN : IsAperiodic N) : IsAperiodic M := by
  obtain ⟨n, hn⟩ := hN
  exact ⟨n, fun x => hf (by rw [map_pow, map_pow, hn])⟩

/-- A binary product of aperiodic monoids is aperiodic (take the larger exponent). -/
theorem IsAperiodic.prod {N : Type*} [Monoid N] (hM : IsAperiodic M) (hN : IsAperiodic N) :
    IsAperiodic (M × N) := by
  obtain ⟨nM, hnM⟩ := hM
  obtain ⟨nN, hnN⟩ := hN
  refine ⟨max nM nN, fun x => Prod.ext ?_ ?_⟩
  · exact pow_stabilizes (hnM x.1) _ (le_max_left _ _)
  · exact pow_stabilizes (hnN x.2) _ (le_max_right _ _)

/-- Aperiodicity transports across a monoid isomorphism. -/
theorem IsAperiodic.of_mulEquiv {N : Type*} [Monoid N] (e : M ≃* N) (hM : IsAperiodic M) :
    IsAperiodic N :=
  hM.of_surjective (f := e.toMonoidHom) e.surjective

end Monoid
