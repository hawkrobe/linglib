import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Core.Path
import Linglib.Core.RootDimensions

/-!
# Spatial Trace Function σ

The spatial dimension of event structure: σ maps events to their spatial
trajectories (paths). This parallels τ (temporal trace, `EventCEM.τ_hom`)
and θ (thematic role, `RoleHom`) as the third Krifka/Zwarts dimension.

## Three-Dimension Picture

```
Temporal:  Events →τ Intervals →dur ℚ     (temporal dimension)
Spatial:   Events →σ Paths     →dist ℚ    (spatial dimension)
Object:    Events →θ Entities  →μ   ℚ     (object dimension)
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

## Sections

1. SpatialTrace Class
2. IsSumHom Instance for σ
3. MereoDim for σ
4. Telicity Transfer Through σ
5. PathShape → Telicity Bridge
6. Motion Verb Path Annotations

## References

- Zwarts, J. & Winter, Y. (2000). Vector space semantics: a model-theoretic
  analysis of locative prepositions. *JoLLI* 9, 169–211.
- Zwarts, J. (2005). Prepositional aspect and the algebra of paths.
  *Linguistics and Philosophy* 28, 739–779.
- Gawron, J.M. (2009). Paths and scalar change.
- Talmy, L. (2000). *Toward a Cognitive Semantics*, Vol. II. MIT Press.
- Krifka, M. (1998). The origins of telicity.
-/

open Semantics.Events
open Semantics.Events.Mereology
open Core.Path
open Semantics.Lexical.Verb.Aspect
open _root_.Mereology

-- ════════════════════════════════════════════════════
-- § 1. SpatialTrace Class
-- ════════════════════════════════════════════════════

namespace Semantics.Events

/-- Spatial trace: maps events to their spatial trajectories.
    Zwarts (2005), Gawron (2009): σ(e) is the path traversed in event e.
    Parallels τ (temporal trace) from EventCEM.

    σ is required to be a sum homomorphism: σ(e₁ ⊕ e₂) = σ(e₁) ⊕ σ(e₂).
    This ensures CUM pulls back through σ (atelic paths → atelic VPs).
    For QUA pullback, injectivity must be assumed separately
    (via `σ_mereoDim`), just as for τ. -/
class SpatialTrace (Loc Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    [SemilatticeSup (Path Loc)] where
  /-- Extract the spatial path of an event. -/
  σ : Ev Time → Path Loc
  /-- σ preserves sums: σ(e₁ ⊕ e₂) = σ(e₁) ⊕ σ(e₂). -/
  σ_map_sup : ∀ (e₁ e₂ : Ev Time),
    σ (@SemilatticeSup.sup _ cem.evSemilatticeSup e₁ e₂) =
      σ e₁ ⊔ σ e₂

end Semantics.Events

namespace Semantics.Events.SpatialTrace

-- ════════════════════════════════════════════════════
-- § 2. IsSumHom Instance for σ
-- ════════════════════════════════════════════════════

/-- σ as an `IsSumHom` instance, derived from `SpatialTrace.σ_map_sup`.
    Enables `cum_pullback` to work automatically for σ.
    Parallels `instIsSumHomRuntime` for τ. -/
noncomputable instance instIsSumHomσ (Loc Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time] :
    @IsSumHom _ _ cem.evSemilatticeSup _ st.σ :=
  @IsSumHom.mk _ _ cem.evSemilatticeSup _
    st.σ (fun e₁ e₂ => st.σ_map_sup e₁ e₂)

-- ════════════════════════════════════════════════════
-- § 3. MereoDim for σ
-- ════════════════════════════════════════════════════

/-- σ with injectivity is a MereoDim: the spatial dimension is a
    mereological morphism, enabling QUA pullback through spatial paths.
    Parallels the pattern for τ (injective τ → MereoDim). -/
def σ_mereoDim {Loc Time : Type*} [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time]
    (hinj : Function.Injective st.σ) :
    @MereoDim _ _ cem.evSemilatticeSup.toPartialOrder
      (inferInstance : PartialOrder (Path Loc)) st.σ :=
  @MereoDim.ofInjSumHom _ _ cem.evSemilatticeSup _
    (f := st.σ) (instIsSumHomσ Loc Time) hinj

-- ════════════════════════════════════════════════════
-- § 4. Telicity Transfer Through σ
-- ════════════════════════════════════════════════════

/-- Bounded path predicate → telic VP.
    "Walk to the store" is telic because "to the store" is QUA
    (no proper subpath of a to-the-store path is also to-the-store)
    and QUA pulls back through σ.
    Zwarts (2005): bounded PPs yield telic VPs. -/
theorem bounded_path_telic {Loc Time : Type*} [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time]
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    @QUA _ cem.evSemilatticeSup.toPartialOrder (P ∘ st.σ) := by
  haveI := σ_mereoDim hinj
  exact @qua_pullback_mereoDim _ _ cem.evSemilatticeSup.toPartialOrder
    (inferInstance : PartialOrder (Path Loc)) st.σ _ P hP

/-- Unbounded path predicate → atelic VP.
    "Walk towards the store" is atelic because "towards the store" is CUM
    and CUM pulls back through the σ sum homomorphism.
    Zwarts (2005): unbounded PPs yield atelic VPs. -/
theorem unbounded_path_atelic {Loc Time : Type*} [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup (Path Loc)]
    [st : SpatialTrace Loc Time]
    {P : Path Loc → Prop} (hP : CUM P) :
    @CUM _ cem.evSemilatticeSup (P ∘ st.σ) :=
  @cum_pullback _ _ cem.evSemilatticeSup _ st.σ (instIsSumHomσ Loc Time) _ hP

-- ════════════════════════════════════════════════════
-- § 5. PathShape → Telicity Bridge
-- ════════════════════════════════════════════════════

/-- Map PathShape to Telicity: bounded/source → telic, unbounded → atelic.
    Zwarts (2005): the boundedness of a directional PP determines
    whether the VP it creates is telic or atelic.

    This is the spatial analog of the QUA/CUM ↔ telic/atelic correspondence
    from `vendlerClass_telic_implies_qua_intent` / `vendlerClass_atelic_implies_cum_intent`
    in `Events/Mereology.lean`. -/
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
    (pathShapeToTelicity s = .telic) ↔ (s.toBoundedness.isLicensed = true) := by
  cases s <;> simp [pathShapeToTelicity, PathShape.toBoundedness,
    Core.Scale.Boundedness.isLicensed]

end Semantics.Events.SpatialTrace

-- ════════════════════════════════════════════════════
-- § 6. Motion Verb Path Annotations
-- ════════════════════════════════════════════════════

/-- Whether a verb class inherently specifies a path shape.
    Inherently directed motion verbs (Levin 51.1: arrive, come, go)
    lexicalize a bounded path. Manner-of-motion verbs (51.3: run, walk)
    are path-neutral — the path comes from a PP complement.
    Talmy (2000): verb-framed vs. satellite-framed distinction. -/
def LevinClass.pathSpec : LevinClass → Option Core.Path.PathShape
  | .inherentlyDirectedMotion => some .bounded
  | .leave => some .source
  | .mannerOfMotion => none    -- path from PP
  | .vehicleMotion => none     -- path from PP/context
  | .chase => none             -- path from complement
  | _ => none                  -- non-motion verbs

namespace Semantics.Events.SpatialTrace

/-- Inherently directed motion verbs lexicalize a bounded path. -/
theorem inherentlyDirected_bounded :
    LevinClass.inherentlyDirectedMotion.pathSpec = some .bounded := rfl

/-- Leave verbs lexicalize a source path. -/
theorem leave_source :
    LevinClass.leave.pathSpec = some .source := rfl

/-- Manner-of-motion verbs are path-neutral. -/
theorem mannerOfMotion_neutral :
    LevinClass.mannerOfMotion.pathSpec = none := rfl

end Semantics.Events.SpatialTrace
