import Linglib.Theories.Syntax.Minimalism.Core.Modification

/-!
# Input Correspondence Principle
@cite{ackema-neeleman-2004}

The ICP constrains the phonological realization of affixes: an affix must
take as its phonological host the head of the phrase it selects. This
means affixes are always linearly adjacent to their syntactic selectee.

## Consequences for Modification

When the attributivizer (Attr) is realized as an affix, the ICP forces
it to be adjacent to the adjective head A. This means dependents of A
(PPs, CPs, AdvPs) cannot linearly intervene between A and N, because
they would separate the affix from its host.

When Attr is a clitic or free word, the ICP does not apply, and
dependents may intervene freely.

## Affix Continuity Constraint (70)

For null affixes, the ICP is extended: a null affix Z taking input head
Y must form a continuous morphological chain. The Affix Continuity
Constraint ensures null affixes behave like overt affixes with respect
to adjacency requirements.
-/

namespace Morphology.ICP

open Minimalism.Modification

-- ============================================================================
-- § 1: The ICP as an Adjacency Predicate
-- ============================================================================

/-- Does the morphophonological status of Attr impose adjacency between
    Attr and the adjective head? The ICP applies to affixes (overt and
    null); clitics and free words are not constrained. -/
def imposesAdjacency : AttrStatus → Bool
  | .affix    => true
  | .null     => true   -- null affixes: Affix Continuity Constraint (70)
  | .clitic   => false
  | .freeWord => false

/-- When adjacency is imposed, dependents of A cannot intervene between
    A and the modified N. This is the morphophonological factor of the MAG.
    Returns `true` when intervention IS blocked by the ICP. -/
def icpBlocksIntervention (status : AttrStatus) : Bool :=
  imposesAdjacency status

/-- Affixal Attr blocks intervention. -/
theorem affix_blocks : icpBlocksIntervention .affix = true := rfl

/-- Null Attr blocks intervention (Affix Continuity Constraint). -/
theorem null_blocks : icpBlocksIntervention .null = true := rfl

/-- Clitic Attr does not block intervention. -/
theorem clitic_permits : icpBlocksIntervention .clitic = false := rfl

/-- Free-word Attr does not block intervention. -/
theorem freeWord_permits : icpBlocksIntervention .freeWord = false := rfl

-- ============================================================================
-- § 2: Connection to MAG Condition (b)
-- ============================================================================

/-- MAG condition (b) is exactly the negation of ICP adjacency:
    intervention is licensed when Attr does NOT impose adjacency. -/
theorem magCondB_is_not_icp (status : AttrStatus) :
    (match status with
     | .clitic | .freeWord => true
     | .affix  | .null     => false) = !icpBlocksIntervention status := by
  cases status <;> rfl

end Morphology.ICP
