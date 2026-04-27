import Linglib.Theories.Syntax.Minimalism.ExtendedProjection.Basic

set_option autoImplicit false

/-!
# Mereological Syntax
@cite{adger-2025}

Core formalization of mereological syntax (@cite{adger-2025}), where
syntactic structures are built by subjoin (establishing parthood) rather
than merge (creating sets). Each syntactic object is an independent
entity with a label; no projection or labeling algorithm is needed.

## Core Concepts

1. **Subjoin**: `x < y` — x is proper part of y. No new label is created
   (contrast merge, which unions two objects and requires labeling).
2. **Dimensionality**: Max 2 subjunctions per object.
   First → 1-part (≈ complement, dimension 1).
   Second → 2-part (≈ specifier, dimension 2).
3. **Parthood axioms**: Irreflexive, within-dimension transitive, asymmetric.
   Transitivity does NOT cross dimensions.
4. **Spell-out**: Objects in a complementation line (1-part chain) can
   collectively spell out at the topmost node.

## Axioms Enforced by the Type

- **Dimensionality** (max 2): three constructors — `leaf` (0), `sub₁` (1), `sub₁₂` (2).
- **Irreflexivity / asymmetry**: enforced by the tree structure (no cycles).
- **Within-dimension transitivity**: `labelInOnePartChain` follows only 1-parts.
- **No cross-dimension transitivity**: 2-parts are not traversed.

## Extended Projection Bridge

Label sequences along the 1-part chain correspond to @cite{grimshaw-2005}'s
Extended Projection. `MLabel.toCat?` maps mereological labels to
`Minimalism.Cat` where possible, and the EP bridge theorems (§ 8) verify
that standard 1-part chains are category-consistent and F-monotone.

## Limitations

`angularLocalityOK` operates on labels rather than node identities. When
multiple nodes share a label, this is lossy. For node-identity-based AL
(supporting multiparthood), see `SynGraph.satisfiesAL` in `SynGraph.lean`.

-/

namespace MereologicalSyntax

-- ════════════════════════════════════════════════════
-- § 1. Labels
-- ════════════════════════════════════════════════════

/-- Category labels for syntactic objects in mereological syntax.

    Labels that overlap with `Minimalism.Cat` (N, V, D, Q, etc.) are
    bridged via `MLabel.toCat?`. Labels specific to @cite{adger-2025}'s
    analysis (Cl, Deg, Adv, O, Pred) have no `Cat` equivalent. -/
inductive MLabel where
  | N     -- noun
  | Cl    -- classifier
  | Q     -- quantity
  | Num   -- numeral
  | D     -- determiner / referentiality
  | Mod   -- modification (introduces 的 *de*)
  | Deg   -- degree
  | A     -- adjective
  | Adv   -- adverb
  | V     -- verb
  | v     -- light verb
  | T     -- tense
  | C     -- complementizer
  | Asp   -- aspect
  | O     -- object (VP-internal)
  | Pred  -- predicate (degree constructions)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 1b. Bridge to Minimalism.Cat
-- ════════════════════════════════════════════════════

open Minimalism in
/-- Map mereological labels to `Minimalism.Cat` where possible.

    Labels shared with the Minimalist framework map to their `Cat`
    equivalent. Labels specific to mereological syntax return `none`. -/
def MLabel.toCat? : MLabel → Option Cat
  | .N => some .N
  | .V => some .V
  | .v => some .v
  | .T => some .T
  | .C => some .C
  | .D => some .D
  | .Q => some .Q
  | .Num => some .Num
  | .A => some .A
  | .Asp => some .Asp
  | .Mod => some .Mod
  | .Cl | .Deg | .Adv | .O | .Pred => none

-- ════════════════════════════════════════════════════
-- § 2. Syntactic Objects
-- ════════════════════════════════════════════════════

/-- A syntactic object in mereological syntax.

    Each object has a label and at most two subparts, enforcing
    Dimensionality (@cite{adger-2025}):

    - **`leaf l`**: bare object, no parts (0 dimensions)
    - **`sub₁ l x`**: `x` is 1-part of `l` (complement, dim 1)
    - **`sub₁₂ l x y`**: `x` is 1-part, `y` is 2-part (specifier, dim 2)

    The first subjunction is always dimension 1; the second dimension 2.
    No third subjunction is possible (the type has no 3-part constructor).

    In projectionist terms: 1-part ≈ complement, 2-part ≈ specifier. -/
inductive SynObj where
  | leaf : MLabel → SynObj
  | sub₁ : MLabel → SynObj → SynObj
  | sub₁₂ : MLabel → SynObj → SynObj → SynObj
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 3. Accessors
-- ════════════════════════════════════════════════════

def SynObj.label : SynObj → MLabel
  | .leaf l | .sub₁ l _ | .sub₁₂ l _ _ => l

def SynObj.onePart : SynObj → Option SynObj
  | .leaf _ => none
  | .sub₁ _ x | .sub₁₂ _ x _ => some x

def SynObj.twoPart : SynObj → Option SynObj
  | .leaf _ | .sub₁ _ _ => none
  | .sub₁₂ _ _ y => some y

/-- Whether the object has reached its dimensional maximum (2 parts). -/
def SynObj.isFull : SynObj → Bool
  | .sub₁₂ _ _ _ => true
  | _ => false

-- ════════════════════════════════════════════════════
-- § 4. Subjoin
-- ════════════════════════════════════════════════════

/-- Subjoin `x` to `y`: make `x` a part of `y` in the next available
    dimension. Returns `none` if `y` already has two parts
    (dimensionality violation).

    - First subjunction → 1-part (dimension 1)
    - Second subjunction → 2-part (dimension 2) -/
def subjoin (x y : SynObj) : Option SynObj :=
  match y with
  | .leaf l => some (.sub₁ l x)
  | .sub₁ l o => some (.sub₁₂ l o x)
  | .sub₁₂ _ _ _ => none

-- ════════════════════════════════════════════════════
-- § 5. Complementation Line and Visibility
-- ════════════════════════════════════════════════════

/-- The complementation line (1-part chain): labels reachable by iterating
    the 1-part relation. Objects in this line can collectively spell out
    at the topmost node (marked by @ in @cite{wang-sun-2026}). -/
def SynObj.compLine : SynObj → List MLabel
  | .leaf l => [l]
  | .sub₁ l one => l :: one.compLine
  | .sub₁₂ l one _ => l :: one.compLine

/-- Is there an object with label `l` in `root`'s 1-part chain?

    Captures within-dimension-1 transitivity: if A <₁ B <₁ C, then
    A is reachable from C. Crucially, 2-parts of objects in the chain
    are NOT traversed — this restricted transitivity prevents
    cross-dimensional visibility (@cite{adger-2025}). -/
def labelInOnePartChain (l : MLabel) : SynObj → Bool
  | .leaf _ => false
  | .sub₁ _ one => one.label == l || labelInOnePartChain l one
  | .sub₁₂ _ one _ => one.label == l || labelInOnePartChain l one

/-- Does `root` contain a sub-object with label `l` at any depth,
    in any dimension? Traverses both 1-parts and 2-parts. -/
def SynObj.containsLabel (l : MLabel) : SynObj → Bool
  | .leaf l' => l == l'
  | .sub₁ l' one => l == l' || one.containsLabel l
  | .sub₁₂ l' one two => l == l' || one.containsLabel l || two.containsLabel l

-- ════════════════════════════════════════════════════
-- § 6. Within-Dimension Chains
-- ════════════════════════════════════════════════════

/-- Is there an object with label `l` in `root`'s 2-part chain?

    Follows only 2-part edges: if A <₂ B <₂ C, then A is reachable
    from C via this chain. 1-parts are NOT traversed — the dual of
    `labelInOnePartChain`. -/
def labelInTwoPartChain (l : MLabel) : SynObj → Bool
  | .leaf _ | .sub₁ _ _ => false
  | .sub₁₂ _ _ two => two.label == l || labelInTwoPartChain l two

/-- Is label `l` a within-dimension transitive part of `root`?

    True when `l` is reachable by following ONLY 1-part edges or ONLY
    2-part edges from `root`, never crossing dimensions
    (@cite{adger-2025}). This is the parthood relation
    relevant to Angular Locality. -/
def labelWithinDimPartOf (l : MLabel) (root : SynObj) : Bool :=
  labelInOnePartChain l root || labelInTwoPartChain l root

-- ════════════════════════════════════════════════════
-- § 7. Angular Locality
-- ════════════════════════════════════════════════════

/-- Collect all `SynObj` nodes along the transitive 1-part chain of
    `root` (not including `root` itself). -/
def SynObj.onePartChainObjs : SynObj → List SynObj
  | .leaf _ => []
  | .sub₁ _ one => one :: one.onePartChainObjs
  | .sub₁₂ _ one _ => one :: one.onePartChainObjs

/-- Angular Locality (@cite{adger-2025}, definition 29):

    γ can subjoin to β only if there is an α such that γ is a
    within-dimension transitive n-part of α AND α is a transitive
    1-part of β.

    **Caveat**: This operates on labels, not node identities. When
    multiple nodes share a label, this function is an approximation.
    For node-identity-based AL with multiparthood support, see
    `SynGraph.satisfiesAL` in `SynGraph.lean`. -/
def angularLocalityOK (l : MLabel) (target : SynObj) : Bool :=
  target.onePartChainObjs.any (labelWithinDimPartOf l ·)

-- ════════════════════════════════════════════════════
-- § 8. Extended Projection Bridge
-- ════════════════════════════════════════════════════

open Minimalism in
/-- The nominal 1-part chain [N, Q, D] (leaf-to-root order), after
    mapping through `toCat?`, is a valid Extended Projection: all
    categories share [-V, +N] features (category-consistent) and
    F-values increase monotonically (N=0 ≤ Q=2 ≤ D=4).

    The classifier label Cl is filtered out (no Cat equivalent). This
    does not affect EP validity — Cl spells out at Q and is not a
    separate EP layer in @cite{grimshaw-2005}'s system. -/
theorem nominal_ep_valid :
    let cats := [MLabel.N, .Q, .D].filterMap MLabel.toCat?
    allCategoryConsistent cats = true ∧
    allFMonotone cats = true := by decide

open Minimalism in
/-- The verbal 1-part chain [V, v, T, C] is a valid Extended Projection:
    all categories share [+V, -N] features and F-values increase
    (V=0 ≤ v=1 ≤ T=2 ≤ C=6). -/
theorem verbal_ep_valid :
    let cats := [MLabel.V, .v, .T, .C].filterMap MLabel.toCat?
    allCategoryConsistent cats = true ∧
    allFMonotone cats = true := by decide

open Minimalism in
/-- All MLabel-to-Cat mappings preserve EP family: nominal labels map to
    the nominal family, verbal labels to the verbal family. -/
theorem toCat_preserves_family :
    (MLabel.N.toCat?.map catFamily = some .nominal) ∧
    (MLabel.Q.toCat?.map catFamily = some .nominal) ∧
    (MLabel.Num.toCat?.map catFamily = some .nominal) ∧
    (MLabel.D.toCat?.map catFamily = some .nominal) ∧
    (MLabel.V.toCat?.map catFamily = some .verbal) ∧
    (MLabel.v.toCat?.map catFamily = some .verbal) ∧
    (MLabel.T.toCat?.map catFamily = some .verbal) ∧
    (MLabel.C.toCat?.map catFamily = some .verbal) := by decide

open Minimalism in
/-- Nominal and verbal labels map to different EP families — confirming
    that cross-EP 1-part chains would fail category consistency. -/
theorem nominal_verbal_disjoint :
    (MLabel.N.toCat?.map catFamily ≠ MLabel.V.toCat?.map catFamily) ∧
    (MLabel.D.toCat?.map catFamily ≠ MLabel.C.toCat?.map catFamily) := by decide

end MereologicalSyntax
