import Linglib.Semantics.Tense.GramTense

/-!
# Modal Base Kind
[klecha-2016]

Classification of modal bases by their temporal character. This is the
foundational type underlying the distinction between doxastic (DOX) and
circumstantial (CIR) modal base pronouns.

DOX returns actual histories (ending at eval time) → past/present orientation.
CIR returns future histories (departing from eval time) → future orientation.

This type is referenced by both theory-layer modules
(`Modality.TemporalConstraint`, `Tense.ModalTense`) and by study files. It depends only on
the `Finset Ordering` tense vocabulary (`Core.Order`, via `Tense`).
-/

open Tense

namespace Semantics.Modality


/-- Classification of modal base temporal character.
    [klecha-2016] (35): DOX returns actual histories 𝒜_t, CIR returns
    future histories ℱ_t. -/
inductive ModalBaseKind where
  /-- Doxastic: accessible histories are actual (end at eval time).
      Yields past/present temporal orientation. -/
  | doxastic
  /-- Circumstantial: accessible histories are future (depart from eval time).
      Yields future temporal orientation. -/
  | circumstantial
  deriving DecidableEq, Repr

/-- The temporal orientation permitted by a modal base kind ([klecha-2016] Table 1, §1.2).

    *Derived, not stipulated.* A doxastic base returns histories ending at the eval time,
    so it permits an orientation iff its comparison cell admits a non-future reference time
    (`lt` or `eq` ∈ the cell); a circumstantial base returns future-departing histories, so it
    permits an orientation iff the cell admits a future reference time (`gt` ∈ the cell). On
    the four named tenses this reproduces Klecha's table — including why DOX permits `nonpast`
    (it contains `eq`) and CIR permits its future part (it contains `gt`). -/
def ModalBaseKind.permitsOrientation : ModalBaseKind → Finset Ordering → Bool
  | .doxastic, s => decide (Ordering.lt ∈ s ∨ Ordering.eq ∈ s)
  | .circumstantial, s => decide (Ordering.gt ∈ s)

/-- Doxastic modal bases block future orientation (the ULC). -/
theorem ModalBaseKind.dox_blocks_future :
    ModalBaseKind.permitsOrientation .doxastic future = false := by decide

/-- Circumstantial modal bases permit future orientation. -/
theorem ModalBaseKind.cir_permits_future :
    ModalBaseKind.permitsOrientation .circumstantial future = true := by decide

/-- The upper limit is derived from doxastic temporal character:
    DOX blocks future, permits past and present. -/
theorem ModalBaseKind.upper_limit_from_dox :
    ModalBaseKind.permitsOrientation .doxastic past = true ∧
    ModalBaseKind.permitsOrientation .doxastic present = true ∧
    ModalBaseKind.permitsOrientation .doxastic future = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Semantics.Modality
