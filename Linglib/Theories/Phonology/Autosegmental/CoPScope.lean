import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone

/-!
# CoP-Scope: Cophonological Domain Scope Hierarchy
@cite{rolle-2018}

The **CoP-scope hierarchy** is @cite{rolle-2018}'s solution to the
**scope problem** for grammatical tone: what determines the domain over
which a GT operation applies?

## The hierarchy

Within a cophonological domain (CoP), structural positions are ordered
by scope:

> **Spec ϕ > Head ϕ > Complement**

A VI in specifier position scopes over the head, and a VI in head
position scopes over its complement. At spell-out, syntactic structure
is mapped to a morpho-phonological tree via **hierarchy exchange**,
which preserves this asymmetric c-command ordering.

## Deriving the dominant GT asymmetry

The **dominant GT asymmetry** (@cite{rolle-2018} §3.4.1) states
that dominant GT triggers are always dependents (affixes, modifiers) and
targets are always lexical heads. Here we **derive** it from the
CoP-scope hierarchy rather than stipulating it:

1. Dominant GT requires the trigger to scope over the target
2. The target occupies Head position (it's the lexical head)
3. CoP-scope orders Spec > Head > Complement
4. Only Spec scopes over Head (Complement does not)
5. Spec is a dependent position
6. Therefore dominant triggers must be dependents

The key non-trivial prediction: complements are dependents but CANNOT
be dominant triggers, because Complement does not scope over Head.
This rules out outward dominance from complements.
-/

namespace Theories.Phonology.Autosegmental.CoPScope

open Theories.Phonology.Autosegmental.GrammaticalTone

-- ============================================================================
-- § 1: CoP-Scope Positions
-- ============================================================================

/-- Structural positions within a cophonological domain (CoP), ordered
    by scope. The ordering Spec > Head > Complement determines which
    VI's cophonology takes precedence within the domain.

    @cite{rolle-2018} Ch 6 §6.2: each VI has cophonology-scope over
    all inwardly located morphemes, and cophonologies apply cyclically
    up the tree, producing layered grammatical tone effects. -/
inductive CoPPosition where
  /-- Specifier: outermost scope. Dependents (modifiers, possessors)
      typically occupy this position. -/
  | spec
  /-- Head: middle scope. Lexical heads (roots, stems) occupy this
      position. -/
  | head
  /-- Complement: innermost scope. Complements and some affixes
      occupy this position. -/
  | complement
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Scope Ordering
-- ============================================================================

/-- Numeric rank for scope ordering: higher rank = wider scope.
    Spec (2) > Head (1) > Complement (0). -/
def CoPPosition.rank : CoPPosition → Nat
  | .spec       => 2
  | .head       => 1
  | .complement => 0

/-- Does position `a` scope over position `b`? -/
def scopesOver (a b : CoPPosition) : Bool := a.rank > b.rank

/-- Specifiers scope over heads. -/
theorem spec_scopes_over_head : scopesOver .spec .head = true := rfl

/-- Heads scope over complements. -/
theorem head_scopes_over_complement : scopesOver .head .complement = true := rfl

/-- Specifiers scope over complements (transitivity). -/
theorem spec_scopes_over_complement : scopesOver .spec .complement = true := rfl

/-- No position scopes over itself. -/
theorem no_self_scope (p : CoPPosition) : scopesOver p p = false := by
  cases p <;> rfl

/-- Heads do not scope over specifiers (asymmetry). -/
theorem head_not_over_spec : scopesOver .head .spec = false := rfl

/-- Complements do not scope over heads (asymmetry). -/
theorem complement_not_over_head : scopesOver .complement .head = false := rfl

-- ============================================================================
-- § 3: Dependency Status (Derived from Position)
-- ============================================================================

/-- Whether a position is a dependent position. Derived from the CoP
    structure: specifiers and complements are dependents; heads are not.

    This is not an independent stipulation — it follows from the
    structural definition of the CoP, where the head is the structural
    center and specifiers/complements are its dependents. -/
def CoPPosition.isDependent : CoPPosition → Bool
  | .spec       => true
  | .head       => false
  | .complement => true

/-- Specifiers are dependents. -/
theorem spec_is_dependent : CoPPosition.isDependent .spec = true := rfl

/-- Heads are not dependents. -/
theorem head_is_not_dependent : CoPPosition.isDependent .head = false := rfl

/-- Complements are dependents. -/
theorem complement_is_dependent : CoPPosition.isDependent .complement = true := rfl

-- ============================================================================
-- § 4: CoP Node — Morpho-Phonological Tree Node
-- ============================================================================

/-- A node in a morpho-phonological tree within a cophonological domain.
    Each node represents a morpheme at a structural position, with an
    optional grammatical tone specification.

    Dependency status is **derived from position** via
    `CoPPosition.isDependent`, not independently stipulated. After
    hierarchy exchange (@cite{rolle-2018} Ch 4), syntactic structure
    maps to a CoP tree where scope ordering determines evaluation order:
    outer-scoping VIs' cophonologies apply after (and thus override)
    inner-scoping ones. -/
structure CoPNode where
  /-- Structural position within the CoP. -/
  position : CoPPosition
  /-- Optional GT specification. `none` if this morpheme has no
      grammatical tone. -/
  gtSpec : Option GTSpec := none
  deriving Repr

/-- Derived dependency status: a node is a dependent iff its position
    is Spec or Complement. -/
def CoPNode.isDependent (n : CoPNode) : Bool := n.position.isDependent

-- ============================================================================
-- § 5: Hierarchy Exchange
-- ============================================================================

/-- **Hierarchy exchange**: map a set of morphemes (from syntactic
    structure) to a cophonological evaluation order. The result is
    sorted by scope rank (highest first), so outer-scoping cophonologies
    are evaluated last — their effects take precedence.

    @cite{rolle-2018} Ch 4: hierarchy exchange preserves the inside-out
    derivational history of the syntactic module by referencing
    asymmetrical c-command, mediated through the CoP-scope ordering. -/
def hierarchyExchange (nodes : List CoPNode) : List CoPNode :=
  nodes.mergeSort (λ a b => a.position.rank ≥ b.position.rank)

/-- Hierarchy exchange preserves the node set (it only reorders). -/
theorem hierarchyExchange_perm (nodes : List CoPNode) :
    (hierarchyExchange nodes).length = nodes.length := by
  simp [hierarchyExchange, List.length_mergeSort]

-- ============================================================================
-- § 6: Deriving the Dominant GT Asymmetry
-- ============================================================================

/-- **The key lemma**: if a position scopes over Head, it must be Spec.

    Complement has lower rank than Head, so it cannot scope over Head.
    Head cannot scope over itself. Only Spec (rank 2 > 1) qualifies.

    This is the structural backbone of the dominant GT asymmetry:
    if dominant GT requires scoping over the head, and only Spec
    scopes over Head, then dominant triggers must be at Spec. -/
theorem scopes_over_head_implies_spec (p : CoPPosition)
    (h : scopesOver p .head = true) : p = .spec := by
  cases p with
  | spec => rfl
  | head => exact absurd h (by decide)
  | complement => exact absurd h (by decide)

/-- A position that scopes over Head is a dependent position.

    Follows from `scopes_over_head_implies_spec` (it must be Spec)
    and `spec_is_dependent` (Spec is a dependent). -/
theorem scopes_over_head_is_dependent (p : CoPPosition)
    (h : scopesOver p .head = true) : p.isDependent = true := by
  have := scopes_over_head_implies_spec p h
  subst this; rfl

/-- **The dominant GT asymmetry derived from CoP-scope.**

    Hypotheses:
    1. The target is at Head position (it's the lexical head)
    2. The trigger scopes over the target (required for dominance)

    From these two facts alone, the CoP-scope hierarchy determines:
    - The trigger is at Spec (only Spec scopes over Head)
    - Spec is a dependent position
    - Head is not a dependent position

    Therefore `DominantGTAsymmetry.holds` is satisfied: the trigger
    is a dependent and the target is a head. The Bool values are
    **computed from positions**, not independently stipulated.

    Non-trivial prediction: complements are dependents but cannot be
    dominant triggers, because Complement does not scope over Head. -/
theorem dominant_gt_asymmetry_from_scope (triggerPos targetPos : CoPPosition)
    (hTarget : targetPos = .head)
    (hScope : scopesOver triggerPos targetPos = true) :
    DominantGTAsymmetry.holds
      ⟨triggerPos.isDependent, !targetPos.isDependent⟩ = true := by
  subst hTarget
  have := scopes_over_head_implies_spec triggerPos hScope
  subst this; rfl

/-- Complements cannot be dominant triggers despite being dependents:
    Complement does not scope over Head. This is a non-trivial prediction
    of the CoP-scope account — the asymmetry is not simply "dependents
    dominate heads" but specifically "dependents that scope over heads
    dominate heads." -/
theorem complement_cannot_dominate_head :
    scopesOver .complement .head = false := rfl

/-- Heads cannot impose dominant GT on specifiers (outward dominance). -/
theorem head_cannot_dominate_spec :
    scopesOver .head .spec = false := rfl

end Theories.Phonology.Autosegmental.CoPScope
