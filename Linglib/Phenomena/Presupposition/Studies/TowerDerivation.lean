import Linglib.Phenomena.Presupposition.Basic
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Presupposition: ContextTower Bridge
@cite{heim-1983} @cite{karttunen-1974} @cite{schlenker-2009}

End-to-end derivation chain connecting the ContextTower infrastructure to
presupposition projection phenomena via @cite{schlenker-2009}'s local context
computation.

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, depth)
    ↓
Core.Context.Shifts (attitudeShift)
    ↓
Theories.Semantics.Presupposition.LocalContext (LocalCtx, depth, filtering)
    ↓
This file: tower depth = local context depth, projection patterns
    ↓
Phenomena.Presupposition.Basic (king example, factive verbs, projection patterns)
```

## Key Results

1. **Tower depth = local context depth**: each embedding operator increments both
2. **Negation preserves projection**: tower push for negation doesn't change
   the context set, only depth — matching `negation_preserves_projection`
3. **Conditional filtering via tower**: the antecedent's assertion enters the
   local context at tower depth 0, filtering the consequent's presupposition
4. **Belief embedding = attitudeShift**: attitude verbs push a shift, creating
   a tower of depth 1 where OLE triggers project to the attitude holder's beliefs

-/

namespace Phenomena.Presupposition.Studies.TowerDerivation

open Core.Context
open Semantics.Presupposition.LocalContext
open Phenomena.Presupposition

-- ============================================================================
-- § Depth Correspondence
-- ============================================================================

/-- A presupposition context: simple KContext for tracking embedding depth.
    World type is `KingWorld` so we can connect to concrete examples. -/
abbrev PresupCtx := KContext KingWorld Unit Unit Unit

/-- Speech-act context: the world where the king exists. -/
def speechCtx : PresupCtx :=
  { world := .kingExists, agent := (), addressee := (), time := (), position := () }

/-- Root tower: no embedding, depth 0. -/
def rootTower : ContextTower PresupCtx := ContextTower.root speechCtx

/-- Initial local context at depth 0. -/
def initialLC : LocalCtx KingWorld :=
  initialLocalCtx (λ _ => True)

/-- Tower depth and local context depth agree at the root. -/
theorem root_depths_agree :
    rootTower.depth = initialLC.depth := rfl

-- ============================================================================
-- § Negation: Depth Increments in Parallel
-- ============================================================================

/-- A negation shift: preserves the context, increments depth. This mirrors
    `localCtxNegation` which preserves the context set but increments depth.

    Negation doesn't change what world we're evaluating in — it just wraps
    the embedded proposition. The tower models this as a no-op shift (like
    identityShift) with a depth increment. -/
def negationShift : ContextShift PresupCtx where
  apply := id
  label := .generic

/-- Tower after one negation. -/
def negTower : ContextTower PresupCtx :=
  rootTower.push negationShift

/-- Local context after one negation. -/
def negLC : LocalCtx KingWorld := localCtxNegation initialLC

/-- After negation, tower depth = 1. -/
theorem neg_tower_depth : negTower.depth = 1 := rfl

/-- After negation, local context depth = 1. -/
theorem neg_lc_depth : negLC.depth = 1 := rfl

/-- Tower depth and local context depth agree after negation. -/
theorem neg_depths_agree :
    negTower.depth = negLC.depth := rfl

/-- Double negation: tower depth = 2 = local context depth. -/
def doubleNegTower : ContextTower PresupCtx :=
  negTower.push negationShift

def doubleNegLC : LocalCtx KingWorld := localCtxNegation negLC

theorem double_neg_depths_agree :
    doubleNegTower.depth = doubleNegLC.depth := rfl

-- ============================================================================
-- § Negation Preserves Context (and Presupposition)
-- ============================================================================

/-- Under negation, the innermost context is unchanged (identity shift).
    This is the tower-theoretic reason negation preserves presuppositions:
    the evaluation context doesn't change, only the polarity flips. -/
theorem negation_preserves_context :
    negTower.innermost = rootTower.innermost := rfl

/-- This parallels the phenomenon: negation doesn't filter presuppositions. -/
theorem negation_preserves_presup_phenomenon :
    Phenomena.Presupposition.negationPattern.projects = true := rfl

-- ============================================================================
-- § Belief Embedding = Attitude Shift (Depth 1)
-- ============================================================================

/-- "John believes that..." pushes an attitude shift. The tower has depth 1,
    matching the local context depth under one belief embedding. -/
def beliefTowerConcrete : ContextTower PresupCtx :=
  rootTower.push (attitudeShift () .noKing)

/-- The belief tower has depth 1. -/
theorem belief_tower_depth : beliefTowerConcrete.depth = 1 := rfl

/-- Under belief embedding, the world coordinate shifts to the attitude
    holder's belief world. This is why presuppositions of the complement
    can project to the attitude holder's beliefs rather than the speaker's. -/
theorem belief_shifts_world :
    beliefTowerConcrete.innermost.world = .noKing := rfl

/-- The origin world is preserved — the speaker's actual world is still
    accessible. This matters for OLE=no triggers (expressives) which project
    to the speaker, not the attitude holder. -/
theorem belief_origin_preserved :
    beliefTowerConcrete.origin.world = .kingExists := rfl

/-- The concrete belief tower depth matches the generic `beliefTower`
    construction from LocalContext.lean. Both have depth 1. -/
theorem belief_depth_matches_generic :
    beliefTowerConcrete.depth =
    (beliefTower speechCtx (attitudeShift () .noKing)).depth := rfl

-- ============================================================================
-- § Conditional Filtering via Tower Origin
-- ============================================================================

/-- The conditional "If the king exists, the king is bald" is modeled as:
    - Antecedent evaluated at depth 0 (origin)
    - Consequent evaluated at depth 0 with updated context

    The tower structure is flat (depth 0) because conditionals don't push
    a new shift — they update the local context. This matches the data:
    conditionals filter presuppositions, unlike negation which projects them. -/
theorem conditional_is_depth_zero :
    rootTower.depth = 0 := rfl

/-- Conditional filtering matches the projection pattern data. -/
theorem conditional_filters_phenomenon :
    Phenomena.Presupposition.conditionalPattern.projects = false := rfl

/-- Negation projects (depth change, no context change). -/
theorem negation_projects_phenomenon :
    Phenomena.Presupposition.negationPattern.projects = true := rfl

/-- The king example's presupposition is indeed filtered. -/
theorem king_example_filtered :
    Phenomena.Presupposition.ifKingThenBald.presup = λ _ => true :=
  Phenomena.Presupposition.ifKingThenBald_no_presup

-- ============================================================================
-- § Projection Pattern Summary
-- ============================================================================

/-- The connective-specific projection patterns from Basic.lean correspond
    to different tower/local-context operations:

    | Connective   | Tower operation           | Projects? |
    |--------------|---------------------------|-----------|
    | Negation     | push identity (depth +1)  | yes       |
    | Conditional  | update context set        | no        |
    | Conjunction  | update context set (L→R)  | no        |
    | Disjunction  | update with ¬P            | no        |

    The key insight: projecting connectives (negation) push shifts that
    don't change the context set. Filtering connectives (conditional,
    conjunction) update the context set, potentially satisfying
    presuppositions of later material.
-/
theorem projection_pattern_summary :
    negationPattern.projects = true ∧
    conditionalPattern.projects = false ∧
    conjunctionPattern.projects = false ∧
    disjunctionPattern.projects = false := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Presupposition.Studies.TowerDerivation
