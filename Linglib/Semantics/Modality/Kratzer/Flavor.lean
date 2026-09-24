/-
[kratzer-1981] Modal Flavors

Epistemic, deontic, bouletic, and teleological flavors parameterize the
modal base and ordering source for different types of modality.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

module

public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Semantics.Modality.Basic

@[expose] public section

namespace Modality.Kratzer

variable {W : Type*}

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

/-- Duality: □p ↔ ¬◇¬p for any KratzerParams. -/
theorem KratzerParams.duality (params : KratzerParams W) (p : W → Prop)
    (w : W) :
    params.necessity p w ↔ ¬ params.possibility (fun w' => ¬ p w') w :=
  Kratzer.duality params.base params.ordering p w

end Modality.Kratzer
