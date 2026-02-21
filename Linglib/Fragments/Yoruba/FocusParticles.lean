import Linglib.Core.Word

/-!
# Yorùbá Focus Particles @cite{aremu-2026}

Focus-marking morphemes across Yorùbá dialects. Standard Yorùbá uses
clause-initial *ni* for ex-situ focus; south-eastern dialects (Ìkálẹ̀,
Oǹdó, Òkìtìpupa) use clause-final *ín* — giving opposite head directions
for FocP within a single language family.

## The head-direction contrast

- Standard Yorùbá: `[FocP Foc(ni) [TP ...]]` — head-initial FocP
- Ìkálẹ̀:          `[FocP XP_F [TP ...] Foc(ín)]` — head-final FocP

The Ìkálẹ̀ pattern places a head-final FocP over a head-initial TP,
creating an apparent FOFC violation (Biberauer, Holmberg & Roberts 2014).

## In-situ focus

All dialects also permit in-situ focus, marked by high tone (H%) on the
focused constituent without movement or a focus particle.

## References

- Aremu, A. (2026). Focus marking in Ìkálẹ̀ (Yorùbá). Glossa 11(1).
- Aboh, E. (2004). The Morphosyntax of Complement-Head Sequences.
- Biberauer, T., Holmberg, A. & Roberts, I. (2014). A syntactic universal
  and its consequences. Linguistic Inquiry 45(2): 169–225.
-/

namespace Fragments.Yoruba.FocusParticles

-- ============================================================================
-- Dialect inventory
-- ============================================================================

/-- Yorùbá dialect grouping relevant to focus marking. -/
inductive Dialect where
  | standard    -- Standard Yorùbá (Ọ̀yọ́-based)
  | ikale       -- Ìkálẹ̀ (south-eastern)
  | ondo        -- Oǹdó (south-eastern)
  | okitipupa   -- Òkìtìpupa (south-eastern)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Focus strategy
-- ============================================================================

/-- How focus is realized. -/
inductive FocusStrategy where
  | exSitu   -- Movement to Spec-FocP + overt focus particle
  | inSitu   -- No movement; prosodic marking (high tone) only
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Focus particle entry
-- ============================================================================

/-- A Yorùbá focus particle lexical entry. -/
structure FocusParticleEntry where
  /-- Surface form -/
  form : String
  /-- Dialect(s) where this particle is attested -/
  dialects : List Dialect
  /-- Head direction of FocP when this particle is used -/
  headDir : HeadDirection
  /-- Focus strategy -/
  strategy : FocusStrategy
  /-- Does the focused XP move to Spec-FocP? -/
  triggersMovement : Bool
  /-- Whether subject focus requires this strategy (vs in-situ) -/
  requiredForSubjectFocus : Bool := false
  /-- Notes -/
  note : String := ""
  deriving Repr, BEq

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- Standard Yorùbá *ni* — clause-initial focus marker.
    "Olú ni ó ra ìwé" = "It is Olú that bought a book." -/
def ni : FocusParticleEntry :=
  { form := "ni"
  , dialects := [.standard]
  , headDir := .headInitial
  , strategy := .exSitu
  , triggersMovement := true
  , requiredForSubjectFocus := true
  , note := "clause-initial; heads FocP, focused XP in Spec-FocP" }

/-- Ìkálẹ̀ *ín* — clause-final focus marker.
    "Olú ó rà ìwé ín" = "It is Olú that bought a book."
    Aremu (2026) ex. (5): head-final Foc⁰. -/
def in_ : FocusParticleEntry :=
  { form := "ín"
  , dialects := [.ikale, .ondo, .okitipupa]
  , headDir := .headFinal
  , strategy := .exSitu
  , triggersMovement := true
  , requiredForSubjectFocus := true
  , note := "clause-final; head-final Foc⁰ over head-initial TP" }

def allParticles : List FocusParticleEntry :=
  [ni, in_]

-- ============================================================================
-- Verification
-- ============================================================================

/-- The two particles have opposite head directions. -/
theorem opposite_head_directions :
    ni.headDir ≠ in_.headDir := by decide

/-- Both particles trigger movement to Spec-FocP. -/
theorem both_trigger_movement :
    allParticles.all (·.triggersMovement) = true := by native_decide

/-- Both particles are required for subject focus. -/
theorem both_required_for_subject :
    allParticles.all (·.requiredForSubjectFocus) = true := by native_decide

/-- Standard Yorùbá uses head-initial FocP. -/
theorem standard_head_initial :
    ni.headDir = .headInitial := rfl

/-- Ìkálẹ̀ uses head-final FocP. -/
theorem ikale_head_final :
    in_.headDir = .headFinal := rfl

end Fragments.Yoruba.FocusParticles
