import Linglib.Core.Scales.Scale
import Linglib.Core.Lexical.VerbClass

/-!
# Situation Type Theory Operations

Theory-dependent operations on the Vendler classification types defined in
`Core/Lexical/VerbClass.lean`. This file provides:

- `Telicity.toMereoTag`: links telicity to mereological properties
  (depends on `Core.Scale.MereoTag`)
- Aspectual shift functions (`telicize`, `atelicize`, `duratize`, `statify`)
  modeling compositional coercion (@cite{smith-1997})

Pure classification data (enums, feature accessors, theorems) is in
`Core/Lexical/VerbClass.lean` under `namespace Core.Verbs`.
-/

-- Methods on Core.Verbs types must be in Core.Verbs namespace for dot notation
namespace Core.Verbs

/-- Telicity → MereoTag: telic = quantized.
    Telic predicates are QUA (no proper part of a telic event is telic);
    atelic predicates are CUM (the sum of two atelic events is atelic). -/
def Telicity.toMereoTag : Telicity → Core.Scale.MereoTag
  | .telic  => .qua
  | .atelic => .cum

/-- Telicize: add a natural endpoint to an atelic predicate. -/
def AspectualProfile.telicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .telic }

/-- Atelicize: remove the natural endpoint (progressive effect). -/
def AspectualProfile.atelicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .atelic }

/-- Duratize: stretch a punctual event over time (iterative). -/
def AspectualProfile.duratize (p : AspectualProfile) : AspectualProfile :=
  { p with duration := .durative }

/-- Statify: convert to a stative reading. -/
def AspectualProfile.statify (p : AspectualProfile) : AspectualProfile :=
  { p with dynamicity := .stative }

end Core.Verbs

-- Shift theorems live in the LexicalAspect namespace (theory-level content)
namespace Semantics.Tense.Aspect.LexicalAspect

open Core.Verbs

/-- Telicizing an activity yields an accomplishment. -/
theorem telicize_activity :
    activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/-- Atelicizing an accomplishment yields an activity. -/
theorem atelicize_accomplishment :
    accomplishmentProfile.atelicize.toVendlerClass = .activity := rfl

/-- Duratizing an achievement yields an accomplishment. -/
theorem duratize_achievement :
    achievementProfile.duratize.toVendlerClass = .accomplishment := rfl

/-- Duratizing a semelfactive yields an activity (iterative reading). -/
theorem duratize_semelfactive :
    semelfactiveProfile.duratize.toVendlerClass = .activity := rfl

/-- Telicizing a semelfactive yields an achievement. -/
theorem telicize_semelfactive :
    semelfactiveProfile.telicize.toVendlerClass = .achievement := rfl

/-- Telicize is idempotent. -/
theorem telicize_idempotent (p : AspectualProfile) :
    p.telicize.telicize = p.telicize := rfl

/-- Atelicize is idempotent. -/
theorem atelicize_idempotent (p : AspectualProfile) :
    p.atelicize.atelicize = p.atelicize := rfl

end Semantics.Tense.Aspect.LexicalAspect
