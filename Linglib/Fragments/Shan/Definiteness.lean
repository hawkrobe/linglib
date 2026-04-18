import Linglib.Core.Definiteness
import Linglib.Core.Deixis.Feature
import Linglib.Core.Nominal.ArticleInventory
import Linglib.Core.Nominal.Maximality
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Noun.Kind.Dayal2004

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
open Core.Presupposition (PrProp)
open Semantics.Noun.Kind

-- ============================================================================
-- §1: Article Inventory and Blocking
-- ============================================================================

/-- Shan blocking principle: no overt determiners block any type-shift. -/
def blocking : Chierchia1998.BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

/-- Shan @cite{moroney-2021}: no overt definite or indefinite article.
    Demonstratives *nâj/nân* are optional in anaphoric contexts; bare nouns
    can express both unique and anaphoric definiteness. `articleInventory`
    is the canonical upstream object from which both
    `DefMarkingParams` (boolean triple) and `DefMarkingStrategy` (Moroney
    cell) are derived via projection — see `toMarkingParams` /
    `toMarkingStrategy`. -/
def articleInventory : Core.Nominal.ArticleInventory :=
  { hasIndefinite             := false
    hasUniqueArticle          := false
    hasAnaphoricArticle       := false
    hasDemonstrative          := true
    hasPossessive             := true }

/-- Shan's inventory projects to the `.unmarked` Moroney cell. -/
theorem articleInventory_marking :
    articleInventory.toMarkingStrategy = .unmarked := rfl

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

/-- Shan demonstrative entry: form, gloss, and deictic content.
    Demonstratives in Shan appear in the structure [N Clf Dem].
    The `spatial` field reuses the framework-agnostic `Core.Deixis.Feature`
    (promoted from the former local `SpatialRelation` enum, 0.229.890). -/
structure ShanDemonstrative where
  form : String
  gloss : String
  spatial : Core.Deixis.Feature
  deriving Repr

/-- *nâj* — proximal demonstrative ('this'). -/
def naj : ShanDemonstrative :=
  { form := "nâj", gloss := "this", spatial := .proximal }

/-- *nân* — distal demonstrative ('that'). -/
def nan : ShanDemonstrative :=
  { form := "nân", gloss := "that", spatial := .distal }

/-- Demonstrative denotation as a referent selector with spatial filter.

    ⟦DEM⟧(P) = ιx[P(x) ∧ SPATIAL(x)]

    The demonstrative combines the restrictor P with a spatial filter
    encoding proximity to the speaker. The cardinality presupposition
    (|P_s| = 1) is handled by `Core.Nominal.russellIotaList` returning
    `none` when no unique satisfier exists. -/
def demDenotation {E : Type} (domain : List E) (dem : ShanDemonstrative)
    (restrictor : E → Bool) (spatialPred : Core.Deixis.Feature → E → Bool) :
    Option E :=
  Core.Nominal.russellIotaList domain
    (fun e => restrictor e && spatialPred dem.spatial e)

/-- A bare definite description (no demonstrative) uses no filter:
    any entity satisfying the restrictor is a candidate, regardless of
    spatial location. This is the uniqueness-based (weak) reading. -/
def bareDefinite {E : Type} (domain : List E) (restrictor : E → Bool) :
    Option E :=
  Core.Nominal.russellIotaList domain restrictor

/-- The demonstrative refines the bare definite: when the bare description
    selects a referent that also satisfies the spatial predicate, both
    selectors agree; the demonstrative can additionally select among
    multiple bare-restrictor satisfiers when the spatial filter narrows
    them to a singleton. -/
theorem dem_refines_bare {E : Type} (domain : List E)
    (restrictor : E → Bool) (spatialPred : Core.Deixis.Feature → E → Bool)
    (dem : ShanDemonstrative) (e : E)
    (hBare : bareDefinite domain restrictor = some e)
    (hSpatial : spatialPred dem.spatial e = true) :
    demDenotation domain dem restrictor spatialPred = some e := by
  rw [bareDefinite, Core.Nominal.russellIotaList_eq_some_iff] at hBare
  rw [demDenotation, Core.Nominal.russellIotaList_eq_some_iff]
  have : domain.filter (fun e' => restrictor e' && spatialPred dem.spatial e') =
         (domain.filter restrictor).filter (fun e' => spatialPred dem.spatial e') := by
    rw [List.filter_filter]
    congr 1; funext e'; exact Bool.and_comm _ _
  rw [this, hBare]; simp [hSpatial]

/-- Lift a referent selector to a `PrProp Unit` via the canonical
    `presupOfReferent` combinator. The presupposition is referent
    definedness; the assertion is the scope applied to the referent. -/
def liftToPrProp {E : Type} (selector : Option E) (scope : E → Bool) :
    PrProp Unit :=
  PrProp.presupOfReferent (fun _ : Unit => selector) (fun e _ => scope e)

end Fragments.Shan.Definiteness
