import Linglib.Core.Time.Tense

/-!
# Modal Base Kind
@cite{klecha-2016}

Classification of modal bases by their temporal character. This is the
foundational type underlying the distinction between doxastic (DOX) and
circumstantial (CIR) modal base pronouns.

DOX returns actual histories (ending at eval time) → past/present orientation.
CIR returns future histories (departing from eval time) → future orientation.

This type lives in Core because it is referenced by both theory-layer
modules (`Modality.TemporalConstraint`, `Tense.ModalTense`) and by
phenomena-layer study files. It depends only on `GramTense` from Core.
-/

namespace Core.Modality

open Core.Time.Tense (GramTense)

/-- Classification of modal base temporal character.
    @cite{klecha-2016} (35): DOX returns actual histories 𝒜_t, CIR returns
    future histories ℱ_t. -/
inductive ModalBaseKind where
  /-- Doxastic: accessible histories are actual (end at eval time).
      Yields past/present temporal orientation. -/
  | doxastic
  /-- Circumstantial: accessible histories are future (depart from eval time).
      Yields future temporal orientation. -/
  | circumstantial
  deriving DecidableEq, Repr

/-- The temporal orientation permitted by a modal base kind.
    @cite{klecha-2016} Table 1 and §1.2. -/
def ModalBaseKind.permitsOrientation : ModalBaseKind → GramTense → Bool
  | .doxastic, .past => true
  | .doxastic, .present => true
  | .doxastic, .nonpast => true    -- nonpast includes present
  | .doxastic, .future => false    -- DOX blocks future orientation
  | .circumstantial, .future => true
  | .circumstantial, .nonpast => true  -- CIR permits future part of nonpast
  | .circumstantial, .past => false    -- CIR blocks past orientation
  | .circumstantial, .present => false -- CIR blocks present orientation

/-- Doxastic modal bases block future orientation (the ULC). -/
theorem ModalBaseKind.dox_blocks_future :
    ModalBaseKind.permitsOrientation .doxastic .future = false := rfl

/-- Circumstantial modal bases permit future orientation. -/
theorem ModalBaseKind.cir_permits_future :
    ModalBaseKind.permitsOrientation .circumstantial .future = true := rfl

/-- The upper limit is derived from doxastic temporal character:
    DOX blocks future, permits past and present. -/
theorem ModalBaseKind.upper_limit_from_dox :
    ModalBaseKind.permitsOrientation .doxastic .past = true ∧
    ModalBaseKind.permitsOrientation .doxastic .present = true ∧
    ModalBaseKind.permitsOrientation .doxastic .future = false :=
  ⟨rfl, rfl, rfl⟩

end Core.Modality
