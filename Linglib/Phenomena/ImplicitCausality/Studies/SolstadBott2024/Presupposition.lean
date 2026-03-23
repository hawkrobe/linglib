import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{solstad-bott-2024} — Presupposition Bridge

@cite{solstad-bott-2024}

Bridge theorems connecting English occasion verb fragment entries to the
presupposition analysis from @cite{solstad-bott-2024}.

For the deeper projectivity analysis (Tonhauser classification, cataphoric
resolution, symmetric filtering), see `Projectivity.lean`.
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024.Presupposition

open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Bridge to Fragment: presupType = softTrigger
-- ════════════════════════════════════════════════════

/-- All occasion verbs have prerequisite presuppositions (soft triggers
    whose content is a causal prerequisite, not complement truth).
    @cite{nadathur-2024} explains this as the presupposition of a
    causally necessary and/or sufficient condition for the complement. -/
theorem all_occasion_verbs_prerequisite :
    manage_occasion.presupType = some .prerequisiteSoft ∧
    dare.presupType = some .prerequisiteSoft ∧
    bother.presupType = some .prerequisiteSoft ∧
    hesitate.presupType = some .prerequisiteSoft :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The default `manage` has a prerequisite presupposition (32i),
    though the prerequisite is underspecified (@cite{nadathur-2024}). -/
theorem manage_default_prerequisite :
    manage.presupType = some .prerequisiteSoft := rfl

/-- Both senses share the same implicative semantics. -/
theorem manage_senses_share_implicative :
    manage.implicativeBuilder = manage_occasion.implicativeBuilder := rfl

-- ════════════════════════════════════════════════════
-- § 2. Bridge to Fragment: Complement Structure
-- ════════════════════════════════════════════════════

/-- All four occasion verbs take infinitival complements. -/
theorem occasion_verbs_infinitival :
    manage_occasion.complementType = .infinitival ∧
    dare.complementType = .infinitival ∧
    bother.complementType = .infinitival ∧
    hesitate.complementType = .infinitival :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All four occasion verbs are subject-control. -/
theorem occasion_verbs_subject_control :
    manage_occasion.controlType = .subjectControl ∧
    dare.controlType = .subjectControl ∧
    bother.controlType = .subjectControl ∧
    hesitate.controlType = .subjectControl :=
  ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.Presupposition
