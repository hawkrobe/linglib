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

## Integration

Label sequences along the 1-part chain correspond to @cite{grimshaw-2005}'s
Extended Projection. The ordering N < Cl < Q < D emerges from successive
1-part relations, matching the F-value hierarchy in `ExtendedProjection/`.
Semantic effects (CUM→QUA at Q) connect via `Borer2005.lean`.

-/

namespace MereologicalSyntax

-- ════════════════════════════════════════════════════
-- § 1. Labels
-- ════════════════════════════════════════════════════

/-- Category labels for syntactic objects in mereological syntax.

    Unlike `Minimalism.Cat`, these are not projection-based: each label
    identifies an independent syntactic object. The sequence of labels
    in a complementation line (1-part chain) corresponds to the extended
    projection (@cite{grimshaw-2005}). -/
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
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Syntactic Objects
-- ════════════════════════════════════════════════════

/-- A syntactic object in mereological syntax.

    Each object has a label and at most two subparts, enforcing
    Dimensionality (@cite{adger-2025}: 44):

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
  deriving Repr

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
    cross-dimensional visibility (@cite{adger-2025}: 42). -/
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
-- § 6. Angular Locality
-- ════════════════════════════════════════════════════

/-- Angular Locality (@cite{adger-2025}: 89):

    γ can subjoin to β only if there is an α such that γ is an n-part
    of α and α is a 1-part of β.

    This prevents subjunction from crossing more than one dimension.
    For wh-movement: the moving element must originate from within
    β's immediate 1-part, forcing cyclic movement through 1-parts
    (≈ specifiers of phases in Minimalism). -/
def angularLocalityOK (l : MLabel) (target : SynObj) : Bool :=
  match target.onePart with
  | none => false
  | some alpha => alpha.containsLabel l

end MereologicalSyntax
