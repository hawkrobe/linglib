import Linglib.Semantics.Definiteness.Defs
import Linglib.Features.Deixis
import Linglib.Semantics.Definiteness.Maximality
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Genericity.NominalMappingParameter
import Linglib.Semantics.Genericity.MeaningPreservation

/-!
# Shan Definiteness Fragment

Language-specific parameters for definiteness in Shan (Southwestern Tai,
Kra-Dai). Shan has no overt articles, so bare nouns express both unique and
anaphoric definiteness via unblocked covert type-shifting; the demonstratives
*nâj* (proximal) and *nân* (distal) are optional in anaphoric contexts and
denote referent selectors carrying a uniqueness presupposition plus spatial
content ([moroney-2021] §2.1.3). The declared determiner inventory is
`Shan.Determiners.inventory`.

## References

* [moroney-2021]
-/

namespace Shan.Definiteness

open Semantics.Definiteness
open Semantics.Presupposition (PartialProp)
open Semantics.Kinds

/-! ### Blocking -/

/-- Shan blocking principle: no overt determiners block any type-shift. -/
def blocking : NMP.BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

/-! ### Type-shift contexts -/

/-- Type-shift context for Shan number-neutral bare nouns with a
    non-kind-compatible predicate (e.g., *mǎa* 'dog' in episodic context).
    ι is selected: definite reading. -/
def neutralNonKindCtx : MeaningPreservation.TypeShiftContext :=
  { number := .neutral
  , downDefined := false
  , iotaBlocked := false
  , iotaAnaphoricBlocked := false
  , existsBlocked := false
  , instantiationAccessible := true }

/-- Type-shift context for Shan number-neutral bare nouns with a
    kind-compatible predicate (e.g., *mǎa* 'dog' in generic context).
    ∩ is selected: kind reading. -/
def neutralKindCtx : MeaningPreservation.TypeShiftContext :=
  { number := .neutral
  , downDefined := true
  , iotaBlocked := false
  , iotaAnaphoricBlocked := false
  , existsBlocked := false
  , instantiationAccessible := true }

/-- Non-kind context yields definite (ι) reading. -/
theorem neutral_nonkind_is_iota :
    MeaningPreservation.selectShift neutralNonKindCtx = some .iota := rfl

/-- Kind context yields kind (∩) reading. -/
theorem neutral_kind_is_down :
    MeaningPreservation.selectShift neutralKindCtx = some .down := rfl

/-- All three high-ranked shifts (∩, ι, ι^x) are available in kind context. -/
theorem all_shifts_available :
    .down ∈ MeaningPreservation.availableShifts neutralKindCtx ∧
    .iota ∈ MeaningPreservation.availableShifts neutralKindCtx ∧
    .iotaAnaphoric ∈ MeaningPreservation.availableShifts neutralKindCtx ∧
    .exists ∈ MeaningPreservation.availableShifts neutralKindCtx := by
  simp [MeaningPreservation.availableShifts, neutralKindCtx]

/-! ### Demonstrative semantics -/

/-- Shan demonstrative entry: form, gloss, and deictic content.
    Demonstratives in Shan appear in the structure [N Clf Dem].
    The `spatial` field reuses the framework-agnostic `Features.Deixis.Feature`
    (promoted from the former local `SpatialRelation` enum, 0.229.890). -/
structure ShanDemonstrative where
  form : String
  gloss : String
  spatial : Features.Deixis.Feature
  deriving Repr

/-- A Shan demonstrative is a `Demonstrative` carrier — its `spatial` field *is* the deictic
    contrast the capability exposes. -/
instance : Demonstrative ShanDemonstrative := ⟨ShanDemonstrative.spatial⟩

/-- *nâj* — proximal demonstrative ('this'). -/
def naj : ShanDemonstrative :=
  { form := "nâj", gloss := "this", spatial := .proximal }

/-- *nân* — distal demonstrative ('that'). -/
def nan : ShanDemonstrative :=
  { form := "nân", gloss := "that", spatial := .distal }

/-- Both Shan demonstratives encode a distance contrast (`nâj` proximal, `nân` distal). -/
theorem shan_demonstratives_encode_distance :
    (Demonstrative.deixis naj).EncodesDistance ∧ (Demonstrative.deixis nan).EncodesDistance := by
  decide

/-- Demonstrative denotation as a referent selector with spatial filter.

    ⟦DEM⟧(P) = ιx[P(x) ∧ SPATIAL(x)]

    The demonstrative combines the restrictor P with a spatial filter
    encoding proximity to the speaker. The cardinality presupposition
    (|P_s| = 1) is handled by `Semantics.Definiteness.russellIotaList` returning
    `none` when no unique satisfier exists. -/
def demDenotation {E : Type} (domain : List E) (dem : ShanDemonstrative)
    (restrictor : E → Bool) (spatialPred : Features.Deixis.Feature → E → Bool) :
    Option E :=
  Semantics.Definiteness.russellIotaList domain
    (fun e => restrictor e && spatialPred dem.spatial e)

/-- A bare definite description (no demonstrative) uses no filter:
    any entity satisfying the restrictor is a candidate, regardless of
    spatial location. This is the uniqueness-based (weak) reading. -/
def bareDefinite {E : Type} (domain : List E) (restrictor : E → Bool) :
    Option E :=
  Semantics.Definiteness.russellIotaList domain restrictor

/-- The demonstrative refines the bare definite: when the bare description
    selects a referent that also satisfies the spatial predicate, both
    selectors agree; the demonstrative can additionally select among
    multiple bare-restrictor satisfiers when the spatial filter narrows
    them to a singleton. -/
theorem dem_refines_bare {E : Type} (domain : List E)
    (restrictor : E → Bool) (spatialPred : Features.Deixis.Feature → E → Bool)
    (dem : ShanDemonstrative) (e : E)
    (hBare : bareDefinite domain restrictor = some e)
    (hSpatial : spatialPred dem.spatial e = true) :
    demDenotation domain dem restrictor spatialPred = some e := by
  rw [bareDefinite, Semantics.Definiteness.russellIotaList_eq_some_iff] at hBare
  rw [demDenotation, Semantics.Definiteness.russellIotaList_eq_some_iff]
  have : domain.filter (fun e' => restrictor e' && spatialPred dem.spatial e') =
         (domain.filter restrictor).filter (fun e' => spatialPred dem.spatial e') := by
    rw [List.filter_filter]
    congr 1; funext e'; exact Bool.and_comm _ _
  rw [this, hBare]; simp [hSpatial]

/-- Lift a referent selector to a `PartialProp Unit` via the canonical
    `presupOfReferent` combinator. The presupposition is referent
    definedness; the assertion is the scope applied to the referent. -/
def liftToPartialProp {E : Type} (selector : Option E) (scope : E → Bool) :
    PartialProp Unit :=
  PartialProp.presupOfReferent (fun _ : Unit => selector) (fun e _ => scope e = true)

end Shan.Definiteness
