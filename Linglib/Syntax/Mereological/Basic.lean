import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Syntactic objects of mereological syntax

Mereological syntax builds structure by Subjoin, which makes one syntactic object a part of
another, rather than by Merge, which collects two objects into a set: no new object is created,
so no labeling algorithm is needed. Dimensionality allows each object one 1-part, the
extended-projection complement, and one 2-part, the specifier.

This file defines the tree-shaped syntactic objects `SynObj` over the category labels `MLabel`,
Subjoin on them, the complementation line (the 1-part chain, along which objects spell out
together), and the correspondence of that line with the extended projection. Object identity
across positions, and hence movement and Angular Locality, need the general parthood structure
`Parthood` of `Mereological/Parthood.lean`.

## Main definitions

* `MereologicalSyntax.MLabel`, `MLabel.toCat?` — category labels and their `Minimalist.Cat`
  counterparts.
* `MereologicalSyntax.SynObj`, `MereologicalSyntax.subjoin` — objects with at most two parts
  and Subjoin in the next free dimension.
* `SynObj.compLine`, `MereologicalSyntax.labelInOnePartChain` — the complementation line and
  visibility along it.

## References

* [adger-2025]
* [grimshaw-2005]
* [wang-sun-2026]
-/

namespace MereologicalSyntax

/-! ### Labels -/

/-- Category labels for syntactic objects in mereological syntax.

    Labels that overlap with `Minimalist.Cat` (N, V, D, Q, etc.) are
    bridged via `MLabel.toCat?`. Labels specific to [adger-2025]'s
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

/-! ### Bridge to Minimalist.Cat -/

open Minimalist in
/-- Map mereological labels to `Minimalist.Cat` where possible.

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

/-! ### Syntactic Objects -/

/-- A syntactic object in mereological syntax.

    Each object has a label and at most two subparts, enforcing
    Dimensionality ([adger-2025]):

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

/-! ### Accessors -/

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

/-! ### Subjoin -/

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

/-! ### Complementation Line and Visibility -/

/-- The complementation line (1-part chain): labels reachable by iterating
    the 1-part relation. Objects in this line can collectively spell out
    at the topmost node (marked by @ in [wang-sun-2026]). -/
def SynObj.compLine : SynObj → List MLabel
  | .leaf l => [l]
  | .sub₁ l one => l :: one.compLine
  | .sub₁₂ l one _ => l :: one.compLine

/-- Is there an object with label `l` in `root`'s 1-part chain?

    Captures within-dimension-1 transitivity: if A <₁ B <₁ C, then
    A is reachable from C. Crucially, 2-parts of objects in the chain
    are NOT traversed — this restricted transitivity prevents
    cross-dimensional visibility ([adger-2025]). -/
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

/-! ### Extended Projection Bridge -/

open Minimalist in
/-- The nominal 1-part chain [N, Q, D] (leaf-to-root order), after
    mapping through `toCat?`, is a valid Extended Projection: all
    categories share [-V, +N] features (category-consistent) and
    F-values increase monotonically (N=0 ≤ Q=2 ≤ D=4).

    The classifier label Cl is filtered out (no Cat equivalent). This
    does not affect EP validity — Cl spells out at Q and is not a
    separate EP layer in [grimshaw-2005]'s system. -/
theorem nominal_ep_valid :
    let cats := [MLabel.N, .Q, .D].filterMap MLabel.toCat?
    allCategoryConsistent cats = true ∧
    allFMonotone cats = true := by decide

open Minimalist in
/-- The verbal 1-part chain [V, v, T, C] is a valid Extended Projection:
    all categories share [+V, -N] features and F-values increase
    (V=0 ≤ v=1 ≤ T=2 ≤ C=6). -/
theorem verbal_ep_valid :
    let cats := [MLabel.V, .v, .T, .C].filterMap MLabel.toCat?
    allCategoryConsistent cats = true ∧
    allFMonotone cats = true := by decide

open Minimalist in
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

open Minimalist in
/-- Nominal and verbal labels map to different EP families — confirming
    that cross-EP 1-part chains would fail category consistency. -/
theorem nominal_verbal_disjoint :
    (MLabel.N.toCat?.map catFamily ≠ MLabel.V.toCat?.map catFamily) ∧
    (MLabel.D.toCat?.map catFamily ≠ MLabel.C.toCat?.map catFamily) := by decide

end MereologicalSyntax
