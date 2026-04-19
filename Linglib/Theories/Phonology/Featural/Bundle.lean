import Mathlib.Data.List.Forall2
import Mathlib.Logic.Function.Basic

/-!
# Featural Bundles
@cite{lionnet-2022} @cite{pulleyblank-1986} @cite{yip-1980}
@cite{clements-1985} @cite{reiss-2017}

A **feature bundle** is a partial assignment over a feature index space.
This is the most general primitive of autosegmental / featural phonology:
every concrete feature theory (Snider Register Tier Theory @cite{snider-1999}
@cite{snider-1990}; Lionnet's subtonal features @cite{lionnet-2022}; vowel
or consonant harmony; nasal, laryngeal, place tiers) is a specialization
of `FeatureBundle F V` for some feature index `F` and value type `V`.

## Design

A bundle is a *partial* assignment `F → Option V`:

- `none` at `f` means **underspecified** — the language assigns no value
  to that feature on that bearer, leaving it open to fill in by default,
  spread, or remain underspecified at the surface.
- `some v` at `f` means **specified** with value `v`.

The value type `V` is parametric:

- `Bool` recovers classical binary features `[±F]` (Snider, Lionnet 2022,
  most generative phonology).
- `ℚ` or `ℝ` recovers Gradient Symbolic Computation @cite{smolensky-goldrick-2016}
  and probabilistic / weighted feature theories @cite{pater-2009}.
- A finite enum recovers privative / multivalued features.

## Why this is the right primitive

1. @cite{reiss-2017}'s Substance-Free Phonology argues features are
   language-particular. Parameterising over `F` is exactly the right move:
   the feature *space* is data, not built into the type.

2. The autosegmental tier is just a sequence of bundles
   (`Tier F V := List (FeatureBundle F V)`). Association to bearers and
   no-crossing constraints can be added on top without changing the bundle
   algebra.

3. Tonal Root Nodes (Snider, Lionnet) are bundles over a tonal feature
   space (`Subtonal := {upper, raised}` for Lionnet 2022). H/M/L are not
   primitive types — they are *named* bundles.

4. Operations on bundles (merge for OCP, spread for assimilation, delete
   for replaceness) are pure functions on the parametric type, so each
   specialization inherits them.

## Connection to existing infrastructure

- `Core/StringHom.lean` (Kleisli morphisms of `Option`) is exactly the
  type of tier-projection homomorphisms `Tier F V → Tier F' V'`.
- `Core/Order/FeaturePreorder.lean` gives the satisfaction preorder on
  bundles when `V` carries an order.
- `Theories/Phonology/Autosegmental/Tier.lean` (already present) collects
  tier-rule infrastructure that the bundle algebra slots into.
-/

namespace Phonology.Featural

universe u v

section Definitions

/-- A **feature bundle**: a partial assignment of values from `V` to
    features in `F`. `none` is underspecified, `some v` is specified.

    For binary features, take `V = Bool`. For gradient / probabilistic
    features, take `V = ℚ` or `ℝ`. For privative features, take `V = Unit`
    (presence vs absence). -/
abbrev FeatureBundle (F : Type u) (V : Type v) : Type (max u v) :=
  F → Option V

/-- A **tier** is a sequence of bundles over the same feature space. The
    sequence captures *paradigmatic* feature content; *syntagmatic*
    relations (adjacency, no-crossing, association to a TBU tier) are
    layered on top. -/
abbrev Tier (F : Type u) (V : Type v) : Type (max u v) :=
  List (FeatureBundle F V)

end Definitions

namespace FeatureBundle

variable {F : Type u} {V : Type v}

section BasicOps

/-- The empty bundle: every feature is underspecified. -/
def empty : FeatureBundle F V := fun _ => none

/-- A bundle that specifies a single feature `f` with value `v` and
    leaves everything else underspecified. Defined via `Function.update`
    so that `Function.update_same`/`update_noteq` lemmas apply. -/
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
    (@cite{lionnet-2022} ex. 53–54) and for default-fill operations. -/
def merge (b₁ b₂ : FeatureBundle F V) : FeatureBundle F V :=
  fun f => (b₁ f).orElse (fun _ => b₂ f)

/-- **Subtonal / featural assimilation** at feature `f`: the target bundle
    `tgt` adopts whatever value `src` specifies for `f` (if any). All other
    features of `tgt` are unchanged.

    This is the building block of M-lowering in Laal (@cite{lionnet-2022}
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

namespace Tier

variable {F : Type u} {V : Type v}

/-- **Tier-level merger** at adjacent positions: pairwise `merge` between
    the bundle at position `i` and the bundle at position `i+1`. This is
    the primitive operation behind the OCP — a constraint that drives
    merger of adjacent identical features. -/
def mergeAdjacent : Tier F V → Tier F V
  | []               => []
  | [b]              => [b]
  | b₁ :: b₂ :: rest => FeatureBundle.merge b₁ b₂ :: mergeAdjacent (b₂ :: rest)

/-- **Local assimilation along a tier** at feature `f`: each bundle takes
    its value at `f` from its left neighbour (when the left neighbour
    specifies `f`). Models leftward-trigger spreading. -/
def assimilateLeftward [DecidableEq F] (f : F) : Tier F V → Tier F V
  | []               => []
  | [b]              => [b]
  | b₁ :: b₂ :: rest =>
      b₁ :: assimilateLeftward f (FeatureBundle.assimilate f b₁ b₂ :: rest)

end Tier

end Phonology.Featural
