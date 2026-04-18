/-
@cite{kratzer-1981} Modal Flavors

Epistemic, deontic, bouletic, and teleological flavors parameterize the
modal base and ordering source for different types of modality.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Modality.Basic

namespace Semantics.Modality.Kratzer

variable {W : Type*} [DecidableEq W] [Fintype W]

/--
**Epistemic modality**: what is known/believed.

- Modal base: evidence/knowledge
- Ordering source: empty (or stereotypical for "probably")
-/
structure EpistemicFlavor (W : Type*) where
  evidence : ModalBase W
  ordering : OrderingSource W := emptyBackground

/--
**Deontic modality**: what is required/permitted by norms.

- Modal base: circumstances
- Ordering source: laws/norms
-/
structure DeonticFlavor (W : Type*) where
  circumstances : ModalBase W
  norms : OrderingSource W

/--
**Bouletic modality**: what is wanted/desired.

- Modal base: circumstances
- Ordering source: desires
-/
structure BouleticFlavor (W : Type*) where
  circumstances : ModalBase W
  desires : OrderingSource W

/--
**Teleological modality**: what leads to goals.

- Modal base: circumstances
- Ordering source: goals
-/
structure TeleologicalFlavor (W : Type*) where
  circumstances : ModalBase W
  goals : OrderingSource W


/-! ## Flavor Tags

Each flavor structure maps to the theory-neutral `ModalFlavor` enum from
`Core.IntensionalLogic.RestrictedModality`, bridging Kratzer's parameterized semantics to the
typological meaning space (Imel, Guo, & @cite{imel-guo-steinert-threlkeld-2026}). -/

open Core.Modality (ModalFlavor)

/-- Epistemic modality maps to the epistemic flavor tag. -/
def EpistemicFlavor.flavorTag : ModalFlavor := .epistemic

/-- Deontic modality maps to the deontic flavor tag. -/
def DeonticFlavor.flavorTag : ModalFlavor := .deontic

/-- Bouletic modality maps to the bouletic flavor tag (desire-based ordering). -/
def BouleticFlavor.flavorTag : ModalFlavor := .bouletic

/-- Teleological modality maps to the circumstantial flavor tag
    (teleological is subsumed under circumstantial in the 2×3 space). -/
def TeleologicalFlavor.flavorTag : ModalFlavor := .circumstantial

/-! ## Background Classification (Kratzer 2012)

Each flavor structure maps to a `BackgroundClass` from
@cite{kratzer-2012}'s three-way classification, which refines the
traditional epistemic/circumstantial binary based on the **projection
mode** of the conversational background (@cite{matthewson-2016} Table 18.3). -/

open Core.Modality (BackgroundClass ProjectionMode)

/-- Epistemic modality: factual-evidential by default. -/
def EpistemicFlavor.toBackgroundClass (_ : EpistemicFlavor W) : BackgroundClass :=
  .factualEvidential

def DeonticFlavor.toBackgroundClass (_ : DeonticFlavor W) : BackgroundClass :=
  .factualCircumstantial

def BouleticFlavor.toBackgroundClass (_ : BouleticFlavor W) : BackgroundClass :=
  .factualCircumstantial

def TeleologicalFlavor.toBackgroundClass (_ : TeleologicalFlavor W) : BackgroundClass :=
  .factualCircumstantial

theorem deontic_factual (f : DeonticFlavor W) :
    f.toBackgroundClass.projectionMode = .factual := rfl

theorem bouletic_factual (f : BouleticFlavor W) :
    f.toBackgroundClass.projectionMode = .factual := rfl

theorem teleological_factual (f : TeleologicalFlavor W) :
    f.toBackgroundClass.projectionMode = .factual := rfl

theorem epistemic_default_factual (f : EpistemicFlavor W) :
    f.toBackgroundClass.projectionMode = .factual := rfl

/-! ## Kratzer Parameters -/

structure KratzerParams (W : Type*) where
  base : ModalBase W
  ordering : OrderingSource W

def EpistemicFlavor.toKratzerParams (f : EpistemicFlavor W) : KratzerParams W where
  base := f.evidence
  ordering := f.ordering

def DeonticFlavor.toKratzerParams (f : DeonticFlavor W) : KratzerParams W where
  base := f.circumstances
  ordering := f.norms

def BouleticFlavor.toKratzerParams (f : BouleticFlavor W) : KratzerParams W where
  base := f.circumstances
  ordering := f.desires

def TeleologicalFlavor.toKratzerParams (f : TeleologicalFlavor W) : KratzerParams W where
  base := f.circumstances
  ordering := f.goals

/-! ## Standard parameter configurations -/

def emptyModalBase : ModalBase W := emptyBackground
def emptyOrderingSource : OrderingSource W := emptyBackground

def minimalParams : KratzerParams W where
  base := emptyModalBase
  ordering := emptyOrderingSource

def epistemicParams (evidence : ModalBase W) : KratzerParams W where
  base := evidence
  ordering := emptyBackground

def deonticParams (circumstances : ModalBase W) (norms : OrderingSource W) : KratzerParams W where
  base := circumstances
  ordering := norms

/-! ## Duality (polymorphic)

Modal duality holds directly from `necessity`/`possibility` (Prop-based).
See `Operators.duality` for the proof. -/

/-- Evaluate a `KratzerParams` as necessity (∀ over best worlds). -/
def KratzerParams.necessity (params : KratzerParams W) (p : W → Prop) (w : W) : Prop :=
  Kratzer.necessity params.base params.ordering p w

/-- Evaluate a `KratzerParams` as possibility (∃ over best worlds). -/
def KratzerParams.possibility (params : KratzerParams W) (p : W → Prop) (w : W) : Prop :=
  Kratzer.possibility params.base params.ordering p w

instance (params : KratzerParams W) (p : W → Prop) [DecidablePred p] (w : W) :
    Decidable (params.necessity p w) :=
  inferInstanceAs (Decidable (Kratzer.necessity params.base params.ordering p w))

instance (params : KratzerParams W) (p : W → Prop) [DecidablePred p] (w : W) :
    Decidable (params.possibility p w) :=
  inferInstanceAs (Decidable (Kratzer.possibility params.base params.ordering p w))

/-- Duality: □p ↔ ¬◇¬p for any KratzerParams. -/
theorem KratzerParams.duality (params : KratzerParams W) (p : W → Prop) [DecidablePred p]
    (w : W) :
    params.necessity p w ↔ ¬ params.possibility (fun w' => ¬ p w') w :=
  Kratzer.duality params.base params.ordering p w

/-! ## Bridge to ModalTheory (World-specific)

`ModalTheory` (from `Basic.lean`) is hardcoded to `World`. These definitions
provide `World`-instantiated bridges. -/

section ModalTheoryBridge

open Semantics.Attitudes.Intensional (World allWorlds)
open Semantics.Modality (ModalTheory ModalForce Proposition allWorlds')

/-- Wrap `KratzerParams World` as a `ModalTheory` (Bool-valued evaluation).
    Forces: necessity/weakNecessity use □, possibility uses ◇. -/
def KratzerTheory (params : KratzerParams World) : ModalTheory where
  name := "Kratzer"
  citation := "Kratzer (1981)"
  eval := fun force p w =>
    match force with
    | .necessity | .weakNecessity =>
      decide (Kratzer.necessity params.base params.ordering (fun w' => p w' = true) w)
    | .possibility =>
      decide (Kratzer.possibility params.base params.ordering (fun w' => p w' = true) w)

/-- `KratzerTheory` evaluates weak necessity with the same quantifier as necessity.
    For proper von Fintel & Iatridou (2008) weak necessity, use
    `Directive.weakNecessity`. -/
theorem kratzerTheory_weakNec_eq_nec (params : KratzerParams World) (p : Proposition) (w : World) :
    (KratzerTheory params).eval .weakNecessity p w =
    (KratzerTheory params).eval .necessity p w := rfl

/-- Minimal Kratzer theory: empty base + empty ordering = universal quantification. -/
def KratzerMinimal : ModalTheory := KratzerTheory minimalParams

/-- Duality holds for every `KratzerTheory` instantiation. -/
theorem kratzerTheory_duality (params : KratzerParams World) (p : Proposition) (w : World) :
    (KratzerTheory params).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds KratzerTheory ModalTheory.necessity ModalTheory.possibility
  have hp : (fun w' => ¬ p w' = true) = (fun w' => (!p w') = true) := by
    funext w'; cases p w' <;> simp
  simp only [Kratzer.duality params.base params.ordering (fun w' => p w' = true) w,
    decide_not, hp, beq_self_eq_true]

theorem kratzer_isNormal (params : KratzerParams World) : (KratzerTheory params).isNormal :=
  fun p w => kratzerTheory_duality params p w

theorem kratzerMinimal_isNormal : KratzerMinimal.isNormal :=
  kratzer_isNormal minimalParams

end ModalTheoryBridge

end Semantics.Modality.Kratzer
