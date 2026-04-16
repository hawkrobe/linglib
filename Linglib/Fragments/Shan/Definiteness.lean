import Linglib.Core.Definiteness
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Dayal2004

/-!
# Shan Definiteness Fragment
@cite{moroney-2021}

Language-specific parameters for definiteness in Shan (Southwestern Tai,
Kra-Dai). Shan has no overt definite or indefinite articles — bare nouns
express both unique and anaphoric definiteness via unblocked covert
type-shifting.

## Key Properties

1. **No articles**: `hasUniqueForm = false`, `hasAnaphoricForm = false`
2. **Unmarked strategy**: `DefMarkingStrategy.unmarked` — bare nouns
   cover all @cite{schwarz-2009} use types
3. **Unblocked type-shifts**: ι, ι^x, ∩, and ∃ are all available
4. **Demonstratives**: *nâj* (proximal) and *nân* (distal) are optional
   in anaphoric contexts, required in no context

## Demonstrative Semantics

@cite{moroney-2021} §2.1.3:
- ⟦nâj⟧ = λP : |P_s| = 1. ιx[P_s(x) ∧ CLOSE.TO.SPEAKER(x)]
- ⟦nân⟧ = λP : |P_s| = 1. ιx[P_s(x) ∧ FAR.FROM.SPEAKER(x)]

Both carry a cardinality presupposition (unique satisfier in the
situation) and add spatial content to the presupposition filter.
-/

namespace Fragments.Shan.Definiteness

open Core.Definiteness
open Semantics.Lexical.Noun.Kind

-- ============================================================================
-- §1: Article Inventory and Blocking
-- ============================================================================

/-- Shan blocking principle: no overt determiners block any type-shift. -/
def blocking : Chierchia1998.BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

/-- Shan marking parameters: no overt forms for either definiteness type. -/
def markingParams : DefMarkingParams :=
  { hasUniqueForm := false
  , hasAnaphoricForm := false }

/-- Shan is classified as unmarked in @cite{moroney-2021}'s typology. -/
theorem strategy : deriveStrategy markingParams = .unmarked := rfl

/-- Shan maps to ArticleType.none_ (no articles). -/
theorem articleType :
    strategyToArticleType (deriveStrategy markingParams) = .none_ := rfl

-- ============================================================================
-- §2: Type-Shift Contexts
-- ============================================================================

/-- Type-shift context for Shan number-neutral bare nouns with a
    non-kind-compatible predicate (e.g., *mǎa* 'dog' in episodic context).
    ι is selected: definite reading. -/
def neutralNonKindCtx : Dayal2004.TypeShiftContext :=
  { number := .neutral
  , downDefined := false
  , iotaBlocked := false
  , iotaAnaphoricBlocked := false
  , existsBlocked := false
  , instantiationAccessible := true }

/-- Type-shift context for Shan number-neutral bare nouns with a
    kind-compatible predicate (e.g., *mǎa* 'dog' in generic context).
    ∩ is selected: kind reading. -/
def neutralKindCtx : Dayal2004.TypeShiftContext :=
  { number := .neutral
  , downDefined := true
  , iotaBlocked := false
  , iotaAnaphoricBlocked := false
  , existsBlocked := false
  , instantiationAccessible := true }

/-- Non-kind context yields definite (ι) reading. -/
theorem neutral_nonkind_is_iota :
    Dayal2004.selectShift neutralNonKindCtx = some .iota := rfl

/-- Kind context yields kind (∩) reading. -/
theorem neutral_kind_is_down :
    Dayal2004.selectShift neutralKindCtx = some .down := rfl

/-- All three high-ranked shifts (∩, ι, ι^x) are available in kind context. -/
theorem all_shifts_available :
    .down ∈ Dayal2004.availableShifts neutralKindCtx ∧
    .iota ∈ Dayal2004.availableShifts neutralKindCtx ∧
    .iotaAnaphoric ∈ Dayal2004.availableShifts neutralKindCtx ∧
    .exists ∈ Dayal2004.availableShifts neutralKindCtx := by
  simp [Dayal2004.availableShifts, neutralKindCtx]

-- ============================================================================
-- §3: Demonstrative Semantics (@cite{moroney-2021} §2.1.3)
-- ============================================================================

/-- Spatial relation for demonstratives. -/
inductive SpatialRelation where
  | proximal  -- close to speaker
  | distal    -- far from speaker
  deriving DecidableEq, Repr

/-- Shan demonstrative entry: form, gloss, and spatial content.
    Demonstratives in Shan appear in the structure [N Clf Dem]. -/
structure ShanDemonstrative where
  form : String
  gloss : String
  spatial : SpatialRelation
  deriving Repr

/-- *nâj* — proximal demonstrative ('this'). -/
def naj : ShanDemonstrative :=
  { form := "nâj", gloss := "this", spatial := .proximal }

/-- *nân* — distal demonstrative ('that'). -/
def nan : ShanDemonstrative :=
  { form := "nân", gloss := "that", spatial := .distal }

/-- Demonstrative denotation as a `DefiniteDesc` with spatial presupposition
    filter.

    ⟦DEM⟧(P) = ιx[P(x) ∧ SPATIAL(x)]

    The demonstrative combines the restrictor P with a spatial filter
    encoding proximity to the speaker. The cardinality presupposition
    (|P_s| = 1) is handled by the `evalDefinite` machinery, which
    requires a unique satisfier. -/
def demDenotation {E : Type} (dem : ShanDemonstrative)
    (restrictor : E → Bool) (spatialPred : SpatialRelation → E → Bool) :
    DefiniteDesc E :=
  .anaphoric restrictor (spatialPred dem.spatial)

/-- Demonstrative descriptions are anaphoric (strong article layer). -/
theorem dem_is_anaphoric (dem : ShanDemonstrative) {E : Type}
    (restrictor : E → Bool) (spatialPred : SpatialRelation → E → Bool) :
    (demDenotation dem restrictor spatialPred).presupFilter =
      spatialPred dem.spatial := rfl

/-- A bare definite description (no demonstrative) uses a trivial filter:
    any entity satisfying the restrictor is a candidate, regardless of
    spatial location. This is the uniqueness-based (weak) reading. -/
def bareDefinite {E : Type} (restrictor : E → Bool) : DefiniteDesc E :=
  .unique restrictor

/-- The demonstrative adds information beyond the bare definite: it
    restricts candidates to those satisfying the spatial predicate.
    Bare definites are a special case where the filter is vacuous. -/
theorem dem_refines_bare {E : Type}
    (restrictor : E → Bool) (spatialPred : SpatialRelation → E → Bool)
    (dem : ShanDemonstrative) :
    (bareDefinite restrictor).presupFilter = (fun _ => true) ∧
    (demDenotation dem restrictor spatialPred).presupFilter =
      spatialPred dem.spatial :=
  ⟨rfl, rfl⟩

end Fragments.Shan.Definiteness
