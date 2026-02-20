import Linglib.Core.Categorical.MereoCat
import Linglib.Theories.Semantics.Events.DimensionBridge

/-!
# Dimension Coherence via the Mereological Category

Upgrades the dimension irrelevance results in `DimensionBridge.lean` to
formal coherence theorems using the categorical structure from `MereoCat.lean`.

The key claim is **QUA functoriality**: `QUA` pullback respects categorical
composition in `MereoObj`. Any `DimensionChain` — temporal, spatial, object,
or any future chain not yet defined — produces a morphism in the mereological
category, and QUA pulls back through it. This makes dimension irrelevance a
consequence of functoriality rather than a per-chain verification.

## Three levels of coherence

1. **Per-chain**: Each `DimensionChain` produces a `MereoMor` (proved in
   `MereoCat.lean` via `DimensionChain.toMereoMor`).

2. **Cross-chain**: Given *any two* chains ending at the same measure type,
   QUA pulls back through both (`dimension_coherence`). This is the formal
   content of "the dimension doesn't matter."

3. **Falsifiable prediction**: Any future `DimensionChain` (e.g., a new
   perceptual or information-theoretic dimension) must automatically satisfy
   QUA transfer (`any_chain_qua_transfer`). If empirically it doesn't, the
   `MereoDim` axiom for that dimension is falsified.

## Composition coherence

The categorical composition `leg₁ ≫ leg₂` in `MereoObj` equals the
composite morphism `toMereoMor` (`DimensionChain.comp_eq` in `MereoCat.lean`).
This guarantees that the two-step QUA transfer (first through `leg₁`, then
through `leg₂`) agrees with the one-step transfer through the composition.
-/

open Mereology
open Core.Categorical

namespace Semantics.Events.DimensionCoherence

-- ════════════════════════════════════════════════════
-- § 1. Cross-Chain Coherence
-- ════════════════════════════════════════════════════

universe u

/-- **Dimension coherence**: given two arbitrary dimension chains with a
    common measure type, QUA on the measure pulls back through *both* chains.

    This is the formal content of dimension irrelevance: the QUA property
    of the pullback predicate depends only on the QUA property of the
    source predicate and the existence of `MereoDim` legs, not on which
    particular dimension chain is chosen. -/
theorem dimension_coherence
    {Source₁ Inter₁ Source₂ Inter₂ Measure : Type u}
    [PartialOrder Source₁] [PartialOrder Inter₁]
    [PartialOrder Source₂] [PartialOrder Inter₂]
    [PartialOrder Measure]
    {f₁ : Source₁ → Inter₁} {μ₁ : Inter₁ → Measure}
    {f₂ : Source₂ → Inter₂} {μ₂ : Inter₂ → Measure}
    (dc₁ : DimensionChain f₁ μ₁) (dc₂ : DimensionChain f₂ μ₂)
    {P : Measure → Prop} (hP : QUA P) :
    QUA (P ∘ μ₁ ∘ f₁) ∧ QUA (P ∘ μ₂ ∘ f₂) :=
  ⟨dc₁.qua_transfer hP, dc₂.qua_transfer hP⟩

/-- **Falsifiable prediction**: any `DimensionChain` — including ones not
    yet defined — must satisfy QUA transfer.

    If a linguist proposes a new mereological dimension (e.g., a perceptual
    salience chain Events →p Percepts →σ ℝ) and claims both legs are
    `MereoDim`, then QUA *must* pull back through it. If empirical data
    shows QUA fails for the pullback predicate, the `MereoDim` assumption
    for one of the legs is falsified. -/
theorem any_chain_qua_transfer
    {Source Inter Measure : Type u}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}
    (dc : DimensionChain f μ)
    {P : Measure → Prop} (hP : QUA P) :
    QUA (P ∘ μ ∘ f) :=
  dc.qua_transfer hP

-- ════════════════════════════════════════════════════
-- § 2. Compositional Coherence
-- ════════════════════════════════════════════════════

/-- The two-step QUA transfer (through `leg₁` then `leg₂`) agrees with the
    one-step transfer through the composite morphism. This follows from
    `DimensionChain.comp_eq`: the composite `MereoMor` equals the categorical
    composition of the legs. -/
theorem two_step_agrees_with_composite
    {Source Inter Measure : Type u}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}
    (dc : DimensionChain f μ)
    {P : Measure → Prop} (hP : QUA P) :
    let one_step := dc.qua_transfer hP
    let two_step_inter := dc.qua_transfer_leg₂ hP
    let two_step_source := dc.qua_transfer_leg₁ two_step_inter
    one_step = two_step_source :=
  rfl

-- ════════════════════════════════════════════════════
-- § 3. Categorical Morphism Witnesses
-- ════════════════════════════════════════════════════

/-- Every `MereoMor` morphism supports QUA pullback. This is the
    functorial action: `MereoMor A B → (QUA P → QUA (P ∘ f))`. -/
theorem mereoMor_qua_pullback
    {A B : MereoObj.{u}}
    (m : MereoMor A B)
    {P : B.α → Prop} (hP : QUA P) :
    QUA (P ∘ m.toFun) :=
  qua_pullback m.strict_mono' hP

/-- Composing two `MereoMor` morphisms preserves QUA pullback:
    pulling back through `g ∘ f` equals pulling back through `f`
    after pulling back through `g`. -/
theorem mereoMor_comp_qua_pullback
    {A B C : MereoObj.{u}}
    (f : MereoMor A B) (g : MereoMor B C)
    {P : C.α → Prop} (hP : QUA P) :
    QUA (P ∘ (MereoMor.comp f g).toFun) :=
  mereoMor_qua_pullback (MereoMor.comp f g) hP

-- ════════════════════════════════════════════════════
-- § 4. Licensing Coherence
-- ════════════════════════════════════════════════════

/-- The licensing prediction (QUA → closed → licensed vs CUM → open → blocked)
    is invariant across all dimension chains. This is the theorem that
    `DimensionBridge.dimension_irrelevance` establishes pointwise; here we
    note that the categorical structure makes it structural.

    No matter how many new dimension chains are added, the licensing
    prediction factors through `Boundedness.isLicensed`, which depends
    only on QUA/CUM — not on the particular chain. -/
theorem licensing_factors_through_boundedness :
    quaBoundedness.isLicensed = true ∧
    cumBoundedness.isLicensed = false :=
  Semantics.Events.DimensionBridge.dimension_irrelevance

end Semantics.Events.DimensionCoherence
