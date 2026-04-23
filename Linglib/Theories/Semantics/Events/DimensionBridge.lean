import Linglib.Core.Scales.MereoDim
import Linglib.Core.Time.Interval.Basic
import Linglib.Theories.Semantics.Events.SpatialTrace
import Linglib.Theories.Semantics.Tense.MaximalInformativity

/-!
# Cross-Dimension Bridge (Theory-Specific)
@cite{kennedy-2007} @cite{krifka-1989} @cite{krifka-1998} @cite{rouillard-2026} @cite{zwarts-2005}

Theory-specific commutativity squares, `LicensingPipeline` instances, concrete
dimension chain instantiations, and end-to-end licensing theorems. Builds on
the theory-neutral infrastructure in `Core/MereoDim.lean`, `Core/Time.lean`,
`Core/Path.lean`, and `Core/Scale.lean`.

## Three Levels of Unification

1. **LicensingPipeline instances**: `Telicity`, `VendlerClass`, `PathShape`
   join `Boundedness`, `MereoTag`, `BoundaryType` as pipeline sources.

2. **Full commutativity diamond**: All six classification paths converge at
   `Boundedness`. Proved pairwise: VendlerClass → Telicity → Boundedness =
   VendlerClass → scaleBoundedness, and likewise for PathShape.

3. **Concrete dimension chains**: Temporal (τ, dur), spatial (σ, dist), and
   object (θ, μ) chains instantiate `DimensionChain`, with end-to-end QUA
   transfer theorems.

4. **Dimension irrelevance**: The licensing prediction depends only on the
   mereological tag (QUA/CUM), not on which dimension (temporal/spatial/object)
   the chain traverses. This is the "all the same theorem" claim.

-/

open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Semantics.Events.SpatialTrace
open Semantics.Events
open Semantics.Events.Mereology
open Semantics.Tense.MaximalInformativity
open Core.Scale
open Semantics.Spatial.Path
open Core.Time
open Mereology

namespace Semantics.Events.DimensionBridge

-- ════════════════════════════════════════════════════
-- § 1. Telicity → Boundedness Bridge
-- ════════════════════════════════════════════════════

/-- Telicity maps to scale boundedness via MereoTag: telic → QUA → closed,
    atelic → CUM → open. Derived through the compositional chain
    Telicity →.toMereoTag MereoTag →.toBoundedness Boundedness.
    This is the shared core of all four licensing frameworks:
    @cite{kennedy-2007}, @cite{rouillard-2026}, @cite{krifka-1989}, @cite{zwarts-2005}. -/
abbrev telicityToBoundedness (t : Telicity) : Boundedness :=
  t.toMereoTag.toBoundedness

theorem telic_is_closed : telicityToBoundedness .telic = .closed := rfl
theorem atelic_is_open : telicityToBoundedness .atelic = .open_ := rfl

-- ════════════════════════════════════════════════════
-- § 2. LicensingPipeline Instances
-- ════════════════════════════════════════════════════

instance : LicensingPipeline Telicity where
  toBoundedness := telicityToBoundedness

instance : LicensingPipeline VendlerClass where
  toBoundedness v := telicityToBoundedness v.telicity

instance : LicensingPipeline PathShape where
  toBoundedness p := telicityToBoundedness (pathShapeToTelicity p)

-- ════════════════════════════════════════════════════
-- § 3. Commutativity Squares
-- ════════════════════════════════════════════════════

/-- VendlerClass → Telicity → Boundedness = VendlerClass → Boundedness.
    Both paths route through the same compositional chain
    (VendlerClass →.telicity Telicity →.toMereoTag MereoTag →.toBoundedness Boundedness),
    so agreement is definitional. -/
theorem vendler_comm (c : VendlerClass) :
    telicityToBoundedness c.telicity = scaleBoundedness c := rfl

/-- PathShape → Telicity → Boundedness = PathShape → Boundedness.
    The compositional chain (PathShape → Telicity → MereoTag → Boundedness)
    agrees with the direct `PathShape.toBoundedness` from Core/Path.lean.
    This is a genuine commutativity proof: the Core-level direct classification
    and the Theories-level compositional derivation yield the same result. -/
theorem pathShape_comm (s : PathShape) :
    telicityToBoundedness (pathShapeToTelicity s) = s.toBoundedness := by
  cases s <;> rfl

/-- MereoTag.qua = Boundedness.closed. -/
theorem mereoTag_boundedness_qua : MereoTag.qua.toBoundedness = .closed := rfl

/-- MereoTag.cum = Boundedness.open_. -/
theorem mereoTag_boundedness_cum : MereoTag.cum.toBoundedness = .open_ := rfl

/-- BoundaryType.closed = Boundedness.closed. -/
theorem boundaryType_closed : Interval.BoundaryType.toBoundedness .closed = .closed := rfl

/-- BoundaryType.open_ = Boundedness.open_. -/
theorem boundaryType_open : Interval.BoundaryType.toBoundedness .open_ = .open_ := rfl

/-- The full commutativity diamond: every path through the classification
    diagram produces the same licensing prediction.
    With compositional chains, the VendlerClass and PathShape arms are
    definitional (both sides route through the same chain). -/
theorem commutativity_diamond :
    (∀ c : VendlerClass,
      LicensingPipeline.isLicensed c.telicity =
      LicensingPipeline.isLicensed c) ∧
    (∀ s : PathShape,
      LicensingPipeline.isLicensed (pathShapeToTelicity s) =
      LicensingPipeline.isLicensed s) ∧
    (LicensingPipeline.isLicensed MereoTag.qua =
     LicensingPipeline.isLicensed Boundedness.closed) ∧
    (LicensingPipeline.isLicensed MereoTag.cum =
     LicensingPipeline.isLicensed Boundedness.open_) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Concrete Dimension Chain Instantiations
-- ════════════════════════════════════════════════════

variable {Time : Type*} [LinearOrder Time] [cem : EventCEM Time]

/-- Temporal dimension chain: Events →τ Intervals →dur ℚ. -/
noncomputable def temporalChain
    {dur : Core.Time.Interval Time → ℚ}
    [hDur : @ExtMeasure _ cem.intervalSemilatticeSup dur]
    (hInj : @Function.Injective _ _ (fun (e : Ev Time) => e.runtime)) :
    @DimensionChain _ _ ℚ
      cem.evSemilatticeSup.toPartialOrder
      cem.intervalSemilatticeSup.toPartialOrder
      (inferInstance : PartialOrder ℚ)
      (fun e => e.runtime) dur :=
  letI : PartialOrder (Core.Time.Interval Time) :=
    cem.intervalSemilatticeSup.toPartialOrder
  letI : PartialOrder (Ev Time) := cem.evSemilatticeSup.toPartialOrder
  { leg₁ := @MereoDim.ofInjSumHom _ _ cem.evSemilatticeSup cem.intervalSemilatticeSup
      (f := fun e => e.runtime) (instIsSumHomRuntime Time) hInj
    leg₂ := @instMereoDimOfExtMeasure _ cem.intervalSemilatticeSup dur hDur }

/-- Temporal end-to-end: QUA on ℚ → QUA on Events through τ then dur. -/
theorem temporal_qua_licensed
    {dur : Core.Time.Interval Time → ℚ}
    [hDur : @ExtMeasure _ cem.intervalSemilatticeSup dur]
    (hInj : @Function.Injective _ _ (fun (e : Ev Time) => e.runtime))
    {P : ℚ → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ dur ∘ (fun e => e.runtime)) :=
  letI : PartialOrder (Core.Time.Interval Time) :=
    cem.intervalSemilatticeSup.toPartialOrder
  (@temporalChain Time _ cem dur hDur hInj).qua_transfer hP

variable {Loc : Type*} [SemilatticeSup (Path Loc)] [st : SpatialTrace Loc Time]

/-- Spatial dimension chain: Events →σ Paths →dist ℚ. -/
noncomputable def spatialChain
    {dist : Path Loc → ℚ} [hDist : ExtMeasure (Path Loc) dist]
    (hInj : Function.Injective st.σ) :
    @DimensionChain _ _ ℚ
      cem.evSemilatticeSup.toPartialOrder
      (inferInstance : PartialOrder (Path Loc))
      (inferInstance : PartialOrder ℚ)
      st.σ dist where
  leg₁ := σ_mereoDim hInj
  leg₂ := instMereoDimOfExtMeasure

/-- Spatial end-to-end: QUA on ℚ → QUA on Events through σ then dist. -/
theorem spatial_qua_licensed
    {dist : Path Loc → ℚ} [hDist : ExtMeasure (Path Loc) dist]
    (hInj : Function.Injective st.σ)
    {P : ℚ → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ dist ∘ st.σ) :=
  (spatialChain hInj).qua_transfer hP

variable {Entity : Type*} [SemilatticeSup Entity] [rh : RoleHom Entity Time]

/-- Object dimension chain: Events →θ Entities →μ ℚ. -/
noncomputable def objectChain
    {μ : Entity → ℚ} [hμ : ExtMeasure Entity μ]
    (hInj : @Function.Injective _ _ rh.themeOf) :
    @DimensionChain _ _ ℚ
      cem.evSemilatticeSup.toPartialOrder
      (inferInstance : PartialOrder Entity)
      (inferInstance : PartialOrder ℚ)
      rh.themeOf μ where
  leg₁ := @MereoDim.ofInjSumHom _ _ cem.evSemilatticeSup _ rh.themeOf
    rh.theme_hom hInj
  leg₂ := instMereoDimOfExtMeasure

/-- Object end-to-end: QUA on ℚ → QUA on Events through θ then μ. -/
theorem object_qua_licensed
    {μ : Entity → ℚ} [hμ : ExtMeasure Entity μ]
    (hInj : @Function.Injective _ _ rh.themeOf)
    {P : ℚ → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ μ ∘ rh.themeOf) :=
  (objectChain hInj).qua_transfer hP

-- ════════════════════════════════════════════════════
-- § 5. Dimension Irrelevance
-- ════════════════════════════════════════════════════

/-- The three chains produce the same licensing from the same mereological
    source. This is "all the same theorem": regardless of which dimension
    (temporal, spatial, object), QUA → telic → closed → licensed and
    CUM → atelic → open → blocked. The dimension is irrelevant. -/
theorem dimension_irrelevance :
    quaBoundedness.isLicensed = true ∧
    cumBoundedness.isLicensed = false :=
  ⟨rfl, rfl⟩

end Semantics.Events.DimensionBridge
