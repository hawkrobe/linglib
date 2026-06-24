/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Forall2
import Mathlib.Logic.Function.Basic

/-!
# Featural Bundles
[lionnet-2022] [pulleyblank-1986] [yip-1980]
[clements-1985] [mielke-2008]

A **feature bundle** is a partial assignment over a feature index space — a
general primitive of autosegmental / featural phonology: many feature theories
(Snider Register Tier Theory [snider-1999] [snider-1990]; Lionnet's subtonal
features [lionnet-2022]; vowel or consonant harmony; nasal, laryngeal, place
tiers) specialize `FeatureBundle F V` for some feature index `F` and value type
`V`. (Element Theory's privative elements fit as a finite `F`, but its
headedness is *extra* structure carried separately — see `ElementTheory.lean`.)

## Design

A bundle is a *partial* assignment `F → Option V`:

- `none` at `f` means **underspecified** — the language assigns no value
  to that feature on that bearer, leaving it open to fill in by default,
  spread, or remain underspecified at the surface.
- `some v` at `f` means **specified** with value `v`.

The value type `V` is parametric:

- `Bool` recovers classical binary features `[±F]` (Snider, Lionnet 2022,
  most generative phonology).
- `ℚ` or `ℝ` recovers Gradient Symbolic Computation [smolensky-goldrick-2016]
  and probabilistic / weighted feature theories [pater-2009].
- A finite enum recovers privative / multivalued features.

## Why this is the right primitive

1. [mielke-2008]'s Emergent Feature Theory argues feature inventories are
   language-particular (emergent from the contrasts a language draws).
   Parameterising over `F` is exactly the right move: the feature *space* is
   data, not built into the type.

2. The autosegmental tier is just a sequence of bundles
   (`List (FeatureBundle F V)`). Association to bearers and
   no-crossing constraints can be added on top without changing the bundle
   algebra.

3. Tonal Root Nodes (Snider, Lionnet) are bundles over a tonal feature
   space (`Subtonal := {upper, raised}` for Lionnet 2022). H/M/L are not
   primitive types — they are *named* bundles.

4. Operations on bundles (merge for OCP, spread for assimilation, delete
   for replaceness) are pure functions on the parametric type, so each
   specialization inherits them.

## Connection to existing infrastructure

- `Core/Computability/StringHom.lean` (Kleisli morphisms of `Option`) is exactly the
  type of tier-projection homomorphisms
  `List (FeatureBundle F V) → List (FeatureBundle F' V')`.
- `Core/Order/PullbackPreorder.lean` gives the satisfaction preorder on
  bundles when `V` carries an order.
- `Phonology/TierProjection.lean` provides the erasing tier-projection
  morphism (`TierProjection`) that the bundle algebra slots into.
-/

namespace Phonology

universe u v

section Definitions

/-- A **feature bundle**: a partial assignment of values from `V` to
    features in `F`. `none` is underspecified, `some v` is specified.

    For binary features, take `V = Bool`. For gradient / probabilistic
    features, take `V = ℚ` or `ℝ`. For privative features, take `V = Unit`
    (presence vs absence). -/
abbrev FeatureBundle (F : Type u) (V : Type v) : Type (max u v) :=
  F → Option V

end Definitions

namespace FeatureBundle

variable {F : Type u} {V : Type v}

section BasicOps

/-- The empty bundle: every feature is underspecified. -/
def empty : FeatureBundle F V := fun _ => none

/-- A bundle that specifies a single feature `f` with value `v` and
    leaves everything else underspecified. Defined via `Function.update`
    so that `Function.update_self` and `Function.update_of_ne` lemmas apply. -/
def single [DecidableEq F] (f : F) (v : V) : FeatureBundle F V :=
  Function.update empty f (some v)

/-- Test whether a bundle specifies feature `f` (i.e. assigns it some
    value rather than `none`). -/
def isSpec (b : FeatureBundle F V) (f : F) : Bool :=
  (b f).isSome

/-- Test whether two bundles agree on feature `f`: either both leave it
    unspecified, or both assign it the same value. Conflict (one specifies
    `v₁`, the other `v₂` with `v₁ ≠ v₂`) returns `false`. -/
def agreesOn [DecidableEq V] (b₁ b₂ : FeatureBundle F V) (f : F) : Bool :=
  match b₁ f, b₂ f with
  | none,    none    => true
  | some v₁, some v₂ => decide (v₁ = v₂)
  | _,       _       => false

end BasicOps

section AlgebraicOps

/-- **Bundle merger** (OCP-style): combine two bundles, taking the value
    from `b₁` where it is specified and falling back to `b₂` otherwise.
    Underspecification on both sides remains underspecified.

    Used for OCP merger of adjacent identical features
    ([lionnet-2022] ex. 53–54) and for default-fill operations. -/
def merge (b₁ b₂ : FeatureBundle F V) : FeatureBundle F V :=
  fun f => (b₁ f).orElse (fun _ => b₂ f)

/-- Merging a bundle with itself is the identity: `merge` is idempotent on equal
    arguments. -/
@[simp] theorem merge_self (b : FeatureBundle F V) : merge b b = b := by
  funext f
  simp only [merge]
  cases b f <;> rfl

/-- **Subtonal / featural assimilation** at feature `f`: the target bundle
    `tgt` adopts whatever value `src` specifies for `f` (if any). All other
    features of `tgt` are unchanged.

    This is the building block of M-lowering in Laal ([lionnet-2022]
    §5.2): a `[-raised]` value spreads from a trigger bundle to a target
    bundle on the `[raised]` feature alone, leaving `[upper]` untouched. -/
def assimilate [DecidableEq F]
    (f : F) (src tgt : FeatureBundle F V) : FeatureBundle F V :=
  Function.update tgt f (src f)

/-- **Feature deletion** at `f`: zero out the assignment, returning to
    underspecified. The complement to `assimilate`. -/
def delete [DecidableEq F]
    (f : F) (b : FeatureBundle F V) : FeatureBundle F V :=
  Function.update b f none

/-- **Bundle override**: set feature `f` to `some v`, regardless of the
    current value. Useful for floating features that dock onto a target. -/
def set [DecidableEq F]
    (f : F) (v : V) (b : FeatureBundle F V) : FeatureBundle F V :=
  Function.update b f (some v)

end AlgebraicOps

end FeatureBundle

end Phonology
