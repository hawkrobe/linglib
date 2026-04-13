/-
@cite{kratzer-1981} Modal Flavors

Epistemic, deontic, bouletic, and teleological flavors parameterize the
modal base and ordering source for different types of modality.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Modality.Basic

namespace Semantics.Modality.Kratzer

open Semantics.Attitudes.Intensional
open Semantics.Modality (ModalTheory ModalForce Proposition allWorlds')

/--
**Epistemic modality**: what is known/believed.

- Modal base: evidence/knowledge
- Ordering source: empty (or stereotypical for "probably")
-/
structure EpistemicFlavor where
  evidence : ModalBase
  ordering : OrderingSource := emptyBackground

/--
**Deontic modality**: what is required/permitted by norms.

- Modal base: circumstances
- Ordering source: laws/norms
-/
structure DeonticFlavor where
  circumstances : ModalBase
  norms : OrderingSource

/--
**Bouletic modality**: what is wanted/desired.

- Modal base: circumstances
- Ordering source: desires
-/
structure BouleticFlavor where
  circumstances : ModalBase
  desires : OrderingSource

/--
**Teleological modality**: what leads to goals.

- Modal base: circumstances
- Ordering source: goals
-/
structure TeleologicalFlavor where
  circumstances : ModalBase
  goals : OrderingSource


/-! ## Flavor Tags

Each flavor structure maps to the theory-neutral `ModalFlavor` enum from
`Core.ModalLogic`, bridging Kratzer's parameterized semantics to the
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

structure KratzerParams where
  base : ModalBase
  ordering : OrderingSource

/-- Extract `KratzerParams` from an epistemic flavor structure. -/
def EpistemicFlavor.toKratzerParams (f : EpistemicFlavor) : KratzerParams where
  base := f.evidence
  ordering := f.ordering

/-- Extract `KratzerParams` from a deontic flavor structure. -/
def DeonticFlavor.toKratzerParams (f : DeonticFlavor) : KratzerParams where
  base := f.circumstances
  ordering := f.norms

/-- Extract `KratzerParams` from a bouletic flavor structure. -/
def BouleticFlavor.toKratzerParams (f : BouleticFlavor) : KratzerParams where
  base := f.circumstances
  ordering := f.desires

/-- Extract `KratzerParams` from a teleological flavor structure. -/
def TeleologicalFlavor.toKratzerParams (f : TeleologicalFlavor) : KratzerParams where
  base := f.circumstances
  ordering := f.goals

def KratzerTheory (params : KratzerParams) : ModalTheory where
  name := "Kratzer"
  citation := "Kratzer 1981"
  eval := λ force p w =>
    let best := bestWorlds params.base params.ordering w
    match force with
    | .necessity => best.all p
    | .weakNecessity => best.all p  -- Same ∀ as necessity. This is correct:
      -- WN ≡ SN_Xg (@cite{ferreira-2023}) — weak necessity IS strong necessity
      -- with X-marked ordering source. The difference is entirely in the modal
      -- parameters (refined ordering via KratzerParams), not the quantifier.
      -- See `XMarking.wn_equiv_snXg` for the structural equation.
    | .possibility => best.any p

/-- `KratzerTheory` evaluates weak necessity with the same quantifier as necessity.
    This is correct by @cite{ferreira-2023}: WN ≡ SN_Xg — the weak/strong
    distinction is encoded in the ordering source parameters, not the quantifier.
    See `XMarking.wn_equiv_snXg` for the structural equation. -/
theorem eval_weakNecessity_eq_necessity (params : KratzerParams) (p : Proposition) (w : World) :
    (KratzerTheory params).eval .weakNecessity p w =
    (KratzerTheory params).eval .necessity p w := rfl

-- Standard parameter configurations

def emptyModalBase : ModalBase := emptyBackground
def emptyOrderingSource : OrderingSource := emptyBackground

def minimalParams : KratzerParams where
  base := emptyModalBase
  ordering := emptyOrderingSource

def epistemicParams (evidence : ModalBase) : KratzerParams where
  base := evidence
  ordering := emptyBackground

def deonticParams (circumstances : ModalBase) (norms : OrderingSource) : KratzerParams where
  base := circumstances
  ordering := norms

def KratzerMinimal : ModalTheory := KratzerTheory minimalParams

-- Duality for ModalTheory Interface

private theorem list_duality_helper (L : List World) (p : Proposition) :
    (L.all p == !L.any λ w' => !p w') = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

theorem kratzer_duality (params : KratzerParams) (p : Proposition) (w : World) :
    (KratzerTheory params).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds KratzerTheory ModalTheory.necessity ModalTheory.possibility
  exact list_duality_helper (bestWorlds params.base params.ordering w) p

theorem kratzer_isNormal (params : KratzerParams) : (KratzerTheory params).isNormal :=
  λ p w => kratzer_duality params p w

theorem kratzerMinimal_isNormal : KratzerMinimal.isNormal :=
  kratzer_isNormal minimalParams

end Semantics.Modality.Kratzer
