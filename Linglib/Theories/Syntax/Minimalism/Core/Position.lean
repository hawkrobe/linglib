import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Features

/-!
# Derivational Positions
@cite{abels-2012} @cite{erlewine-2016} @cite{erlewine-2018} @cite{chomsky-1995}

Derives positional information (specifier vs. complement) from merge
history, following the Minimalist view that position is derivational,
not representational.

In bare phrase structure, `node X Y` does not encode which daughter is
the specifier and which is the complement. That information lives in
the *derivation*: the first external Merge into a projection creates
the complement; the second creates the specifier; internal Merge
(movement) always creates a specifier/edge.

This module defines `MergeEvent` records that track derivational
position and derives anti-locality constraints and the predicate-
fronting extraction restriction from them.

## Anti-Locality

Two variants are formalized:

1. **Complement-to-Spec**: the complement of a head H
   cannot move to Spec,HP. Restated positionally here; the original
   formulation is in `Phase.lean`.

2. **Spec-to-Spec** (@cite{erlewine-2016}): movement
   from Spec,XP to Spec,YP is blocked when YP immediately dominates XP
   (no intervening maximal projection). Originally proposed for Agent Focus
   in Kaqchikel (@cite{erlewine-2016}). Also interacts with
   Toba Batak clause structure (@cite{erlewine-2018}).

-/

namespace Minimalism

-- ============================================================================
-- § 1: Merge Types
-- ============================================================================

/-- How a constituent came to occupy its position in the tree.

    This is a derivational property: it records which Merge operation
    placed the constituent, not where it sits in the final tree. -/
inductive MergeType where
  /-- First external merge into a projection: complement position.
      E.g., V merges with DP_obj → DP_obj is complement of V. -/
  | extComp
  /-- Second external merge into a projection: specifier position.
      E.g., DP_subj merges with v' → DP_subj is specifier of vP. -/
  | extSpec
  /-- Internal merge (movement): specifier/edge position.
      E.g., wh-phrase moves to Spec,CP. -/
  | intSpec
  deriving Repr, DecidableEq

/-- Is this a specifier position (external or via movement)? -/
def MergeType.isSpec : MergeType → Bool
  | .extSpec | .intSpec => true
  | .extComp => false

/-- Was this position created by movement? -/
def MergeType.isMovement : MergeType → Bool
  | .intSpec => true
  | _ => false

-- ============================================================================
-- § 2: Merge Events
-- ============================================================================

/-- A record of one Merge operation's positional consequence.

    Given a derivation, each Merge step produces a MergeEvent recording
    what was merged, into which projection, and what positional slot
    the merged element occupies.

    The `result` field stores the SO after this merge — useful for
    inspecting the representational state at any derivational point. -/
structure MergeEvent where
  /-- The projection being extended (the "target" of Merge) -/
  target   : SyntacticObject
  /-- The constituent merged into that projection -/
  daughter : SyntacticObject
  /-- The resulting SO after this Merge -/
  result   : SyntacticObject
  /-- What positional slot the daughter occupies -/
  mtype    : MergeType
  deriving Repr, DecidableEq

-- ============================================================================
-- § 3: Positional Queries
-- ============================================================================

/-- X is a specifier of Y in event history `events`:
    some merge placed X into Y's projection as a specifier. -/
def isSpecIn (events : List MergeEvent) (x y : SyntacticObject) : Prop :=
  ∃ e ∈ events, e.daughter = x ∧ e.target = y ∧
    (e.mtype = .extSpec ∨ e.mtype = .intSpec)

/-- X is a complement of Y in event history `events`. -/
def isCompIn (events : List MergeEvent) (x y : SyntacticObject) : Prop :=
  ∃ e ∈ events, e.daughter = x ∧ e.target = y ∧ e.mtype = .extComp

/-- X moved to the specifier of Y via internal merge. -/
def movedToSpecOf (events : List MergeEvent) (x y : SyntacticObject) : Prop :=
  ∃ e ∈ events, e.daughter = x ∧ e.target = y ∧ e.mtype = .intSpec

-- ============================================================================
-- § 4: Anti-Locality
-- ============================================================================

/-- Complement-to-Spec anti-locality, restated positionally.

    If X is the complement of H, then X cannot move to Spec,HP.
    This is the positional restatement of `Phase.antiLocality`. -/
def compToSpecAntiLocality
    (events : List MergeEvent) (x h : SyntacticObject) : Prop :=
  isCompIn events x h → ¬movedToSpecOf events x h

/-- Spec-to-Spec anti-locality.

    Movement from Spec,XP to Spec,YP is blocked when YP immediately
    dominates XP — i.e., when there is no intervening maximal projection.
    This is "too local": Ā-movement must cross at least one full
    projection boundary.

    In Toba Batak, this prevents the pivot in Spec,TP from moving to
    Spec,CP clause-internally (fn. 24, @cite{erlewine-2018}), though the
    primary extraction restriction derives from nominal licensing. -/
def specToSpecAntiLocality
    (events : List MergeEvent) (mover xP yP : SyntacticObject) : Prop :=
  isSpecIn events mover xP →
  immediatelyContains yP xP →
  ¬movedToSpecOf events mover yP

-- ============================================================================
-- § 5: Predicate Fronting
-- ============================================================================

/-- Predicate fronting: VP/vP moves to Spec,CP via internal merge.

    This derives V-initial word order in languages like Toba Batak.
    The predicate occupies a specifier (edge) position in the C-domain,
    leaving the subject/pivot stranded in Spec,TP. -/
structure PredicateFronting where
  /-- The predicate phrase that fronts (VP or vP) -/
  predicate : SyntacticObject
  /-- The C-domain projection it fronts to -/
  cProjection : SyntacticObject
  /-- The derivation events -/
  events : List MergeEvent
  /-- The predicate was internal-merged to Spec,CP -/
  fronted : movedToSpecOf events predicate cProjection

/-- After predicate fronting, a constituent X is "stranded" if it is
    NOT inside the fronted predicate. Stranded elements remain accessible
    for further operations (e.g., extraction by a higher probe). -/
def isStranded (pf : PredicateFronting) (x : SyntacticObject) : Prop :=
  ¬contains pf.predicate x

/-- After predicate fronting, a constituent X is "trapped" if it IS
    inside the fronted predicate. Trapped elements are inaccessible:
    the fronted phrase is a moved constituent and acts as a freezing
    domain. -/
def isTrapped (pf : PredicateFronting) (x : SyntacticObject) : Prop :=
  contains pf.predicate x

/-- Stranded and trapped are complementary: every constituent of the
    clause is either stranded or trapped (tertium non datur). -/
theorem stranded_or_trapped (pf : PredicateFronting) (x : SyntacticObject) :
    isStranded pf x ∨ isTrapped pf x :=
  em (contains pf.predicate x) |>.elim (Or.inr) (Or.inl)

-- ============================================================================
-- § 6: Extraction Restriction (@cite{erlewine-2018})
-- ============================================================================

/-- The extraction restriction in predicate-fronting languages:
    only stranded elements (those outside the fronted predicate)
    can undergo further Ā-extraction. -/
def extractionRestriction (pf : PredicateFronting) (extractee : SyntacticObject) : Prop :=
  isStranded pf extractee

/-- The pivot: the element stranded by predicate fronting. It sits in
    Spec,TP, outside the fronted VP, and is therefore the only argument
    accessible for extraction. -/
structure Pivot where
  /-- The pivot element -/
  element : SyntacticObject
  /-- The TP whose specifier it occupies -/
  tProjection : SyntacticObject
  /-- Derivation events -/
  events : List MergeEvent
  /-- The pivot sits in Spec,TP -/
  inSpecTP : isSpecIn events element tProjection

/-- The pivot satisfies the extraction restriction: it is stranded
    (outside the fronted predicate), hence extractable. -/
theorem pivot_is_stranded
    (pf : PredicateFronting) (pivot : Pivot)
    (h_outside : ¬contains pf.predicate pivot.element) :
    extractionRestriction pf pivot.element := h_outside

/-- Non-pivot arguments are trapped (inside the fronted predicate),
    hence not extractable. -/
theorem nonpivot_trapped
    (pf : PredicateFronting) (x : SyntacticObject)
    (h_inside : contains pf.predicate x) :
    ¬extractionRestriction pf x := by
  intro h_stranded
  exact h_stranded h_inside

/-- Anti-locality prevents the pivot from moving to Spec,CP in its
    own clause: Spec,TP → Spec,CP is too local.

    The pivot thus stays in Spec,TP. It does NOT move clause-internally,
    but it remains accessible to a higher probe because it sits at the
    edge of its clause, outside the fronted predicate. -/
theorem pivot_blocked_by_anti_locality
    (events : List MergeEvent) (pivot tP cP : SyntacticObject)
    (h_spec : isSpecIn events pivot tP)
    (h_imm : immediatelyContains cP tP)
    (h_anti : specToSpecAntiLocality events pivot tP cP) :
    ¬movedToSpecOf events pivot cP :=
  h_anti h_spec h_imm

-- ============================================================================
-- § 7: Successive-Cyclic Positions
-- ============================================================================

/-- A successive-cyclic position: an intermediate landing site in
    Ā-movement. Each such site is a Spec of a phase head (Spec,vP
    or Spec,CP) that the moving element passes through.

    In Toba Batak, each intermediate C checks [+Pred] against the
    passing wh-copy, yielding extraction morphology. In Mam, each
    intermediate Voice⁰ Agrees [+oblique], yielding =(y)a'. Both
    are modeled as entries in a CyclicChain.

    The `agreeResult` field records whether Agree occurred at this
    position. When the mover passes through a phase head that probes
    for features (e.g., Voice with [uOblique]), Agree values the
    probe's features. The valued features can then be spelled out
    morphologically — this is how multiple =(y)a' arise in Mam
    long-distance extraction (one per Voice along the chain). -/
structure CyclicPosition where
  /-- The moving element -/
  mover : SyntacticObject
  /-- The projection whose specifier it temporarily occupies -/
  projection : SyntacticObject
  /-- Derivation events -/
  events : List MergeEvent
  /-- Evidence that the mover passed through this spec -/
  passedThrough : movedToSpecOf events mover projection
  /-- Features on the probe head at this position after Agree, if
      Agree occurred. `none` = no probe at this position (e.g., a
      non-phase edge). `some fb` = the probe's valued features,
      ready for Spellout (e.g., [+oblique] on Voice → =(y)a'). -/
  agreeResult : Option FeatureBundle := none

/-- A successive-cyclic chain: the ordered sequence of intermediate
    landing sites an element occupies during long-distance movement. -/
structure CyclicChain where
  /-- The moving element -/
  mover : SyntacticObject
  /-- Intermediate positions, ordered from lowest to highest -/
  positions : List CyclicPosition
  /-- All positions involve the same mover -/
  sameMover : ∀ p ∈ positions, p.mover = mover

/-- Count cyclic positions where Agree occurred (features were valued).
    In Mam, this equals the number of =(y)a' morphemes expected in
    long-distance extraction: one per Voice/Dir along the chain. -/
def CyclicChain.agreeCount (chain : CyclicChain) : Nat :=
  chain.positions.filter (·.agreeResult.isSome) |>.length

/-- Extract the agreed feature bundles from a chain, in order.
    Each `some fb` corresponds to a position where Agree occurred,
    yielding features that will be spelled out at PF. -/
def CyclicChain.agreedFeatures (chain : CyclicChain) : List FeatureBundle :=
  chain.positions.filterMap (·.agreeResult)

end Minimalism
