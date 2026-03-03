import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{solstad-bott-2024} — Presupposition Bridge

@cite{solstad-bott-2024}

Bridge theorems connecting English occasion verb fragment entries to the
presupposition analysis from @cite{solstad-bott-2024}.

For the deeper projectivity analysis (Tonhauser classification, cataphoric
resolution, symmetric filtering), see `ProjectivityBridge.lean`.
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge

open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Bridge to Fragment: presupType = softTrigger
-- ════════════════════════════════════════════════════

/-- All four English occasion verbs are soft presupposition triggers —
    their occasion presupposition can be locally accommodated.
    (@cite{solstad-bott-2024}, Exp 2: no strong contextual felicity). -/
theorem all_occasion_verbs_soft :
    manage_occasion.presupType = some .softTrigger ∧
    dare.presupType = some .softTrigger ∧
    bother.presupType = some .softTrigger ∧
    hesitate.presupType = some .softTrigger :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The default `manage` has no presupType — the occasion presupposition
    is only visible under the @cite{solstad-bott-2024} analysis. -/
theorem manage_default_no_presup :
    manage.presupType = none := rfl

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

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge
