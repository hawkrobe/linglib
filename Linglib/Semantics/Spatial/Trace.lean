import Linglib.Semantics.Events.CEM
import Linglib.Semantics.Spatial.Path
import Linglib.Features.Aktionsart

/-!
# Spatial Trace Function σ
[gawron-2009] [krifka-1998] [talmy-2000] [zwarts-2005] [zwarts-winter-2000]

The spatial dimension of event structure: σ maps events to their spatial
trajectories (paths). This parallels τ (the temporal trace, `Event.runtime`)
and the thematic-role dimension θ as Krifka/Zwarts trace functions — each a
`Mereology.IsSumHom` into a different domain (intervals, paths, entities).

## Three-Dimension Picture

```
Temporal: Events →τ Intervals →dur ℚ (temporal dimension)
Spatial: Events →σ Paths →dist ℚ (spatial dimension)
Object: Events →θ Entities →μ ℚ (object dimension)
```

All three use the same QUA/CUM pullback mechanism via `MereoDim`.

## Key Results

- **Bounded path → telic VP** (§4): QUA path predicates pull back through σ
  to yield QUA (telic) VP predicates. "Walk to the store" is telic because
  "to the store" denotes a QUA set of paths (no proper subpath of a
  to-the-store path is also to-the-store).

- **Unbounded path → atelic VP** (§4): CUM path predicates pull back through σ
  to yield CUM (atelic) VP predicates. "Walk towards the store" is atelic
  because "towards the store" denotes a CUM set of paths.
-/

open Semantics.Events.CEM
open Semantics.Spatial.Path
open Features
open _root_.Mereology

/-! ### Trace Class -/

namespace Semantics.Spatial

/-- Spatial trace: maps events to their spatial trajectories.
    [zwarts-2005], [gawron-2009]: σ(e) is the path traversed in event e.
    Parallels the temporal trace τ (`Event.runtime`).

    σ is required to be a sum homomorphism: σ(e₁ ⊕ e₂) = σ(e₁) ⊕ σ(e₂).
    This ensures CUM pulls back through σ (atelic paths → atelic VPs).
    For QUA pullback, injectivity must be assumed separately
    (via `σ_mereoDim`), just as for τ. -/
class Trace (Loc Time : Type*) [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)]
    [SemilatticeSup (Path Loc)] where
  /-- Extract the spatial path of an event. -/
  σ : Event Time → Path Loc
  /-- σ preserves sums: σ(e₁ ⊕ e₂) = σ(e₁) ⊕ σ(e₂). -/
  σ_map_sup : ∀ (e₁ e₂ : Event Time), σ (e₁ ⊔ e₂) = σ e₁ ⊔ σ e₂

end Semantics.Spatial

namespace Semantics.Spatial.Trace

/-! ### IsSumHom Instance for σ -/

/-- σ as an `IsSumHom` instance, from `Trace.σ_map_sup`.
    Enables `cum_pullback` to work automatically for σ. -/
noncomputable instance instIsSumHomσ (Loc Time : Type*) [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)]
    [SemilatticeSup (Path Loc)] [st : Trace Loc Time] :
    IsSumHom st.σ :=
  ⟨fun e₁ e₂ => st.σ_map_sup e₁ e₂⟩

/-! ### MereoDim for σ -/

/-- σ with injectivity is a MereoDim: the spatial dimension is a
    mereological morphism, enabling QUA pullback through spatial paths. -/
theorem σ_mereoDim {Loc Time : Type*} [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)]
    [SemilatticeSup (Path Loc)] [st : Trace Loc Time]
    (hinj : Function.Injective st.σ) :
    MereoDim st.σ :=
  MereoDim.ofInjSumHom hinj

/-! ### Telicity Transfer Through σ -/

/-- Bounded path predicate → telic VP.
    "Walk to the store" is telic because "to the store" is QUA
    (no proper subpath of a to-the-store path is also to-the-store)
    and QUA pulls back through σ.
    [zwarts-2005]: bounded PPs yield telic VPs. -/
theorem bounded_path_telic {Loc Time : Type*} [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)]
    [SemilatticeSup (Path Loc)] [st : Trace Loc Time]
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    QUA (P ∘ st.σ) := by
  haveI := σ_mereoDim hinj
  exact qua_pullback_mereoDim hP

/-- Unbounded path predicate → atelic VP.
    "Walk towards the store" is atelic because "towards the store" is CUM
    and CUM pulls back through the σ sum homomorphism.
    [zwarts-2005]: unbounded PPs yield atelic VPs. -/
theorem unbounded_path_atelic {Loc Time : Type*} [LinearOrder Time]
    [Event.Mereology Time] [ClassicalMereology (Event Time)]
    [SemilatticeSup (Path Loc)] [st : Trace Loc Time]
    {P : Path Loc → Prop} (hP : CUM P) :
    CUM (P ∘ st.σ) :=
  cum_pullback (instIsSumHomσ Loc Time) hP

/-! ### PathShape → Telicity Bridge -/

/-- Map PathShape to Telicity: bounded/source → telic, unbounded → atelic.
    [zwarts-2005]: the boundedness of a directional PP determines
    whether the VP it creates is telic or atelic.

    This is the spatial analog of the QUA/CUM ↔ telic/atelic correspondence
    over `Features.VendlerClass.telicity` (see `Features.telic_classes`). -/
def pathShapeToTelicity : PathShape → Telicity
  | .bounded => .telic
  | .source => .telic
  | .unbounded => .atelic

/-- Bounded paths are telic. -/
theorem bounded_telic : pathShapeToTelicity .bounded = .telic := rfl

/-- Source paths are telic. -/
theorem source_telic : pathShapeToTelicity .source = .telic := rfl

/-- Unbounded paths are atelic. -/
theorem unbounded_atelic : pathShapeToTelicity .unbounded = .atelic := rfl

/-- PathShape telicity agrees with PathShape boundedness licensing:
    telic ↔ licensed (closed scale), atelic ↔ blocked (open scale).
    This connects the spatial classification to the scale-theoretic one. -/
theorem telicity_boundedness_agree (s : PathShape) :
    (pathShapeToTelicity s = .telic) ↔ s.toBoundedness.IsLicensed := by
  cases s <;> simp [pathShapeToTelicity, PathShape.toBoundedness,
    Core.Order.Boundedness.IsLicensed]

/-- LicensingPipeline instance for PathShape via the `pathShapeToTelicity`
    bridge. Co-located with the bridge per the convention noted in
    `Core/Scales/Defs.lean` (instances live with their type). -/
instance : Core.Order.LicensingPipeline PathShape where
  toBoundedness p := (pathShapeToTelicity p).toMereoTag.toBoundedness

end Semantics.Spatial.Trace
