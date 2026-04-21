import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Core.Lexical.Word

/-!
# VP-Level Situation Type Composition
@cite{smith-1997}

Compositional rules for deriving the situation type of a verb constellation
from its component parts (verb, NP, PP). @cite{smith-1997} Ch. 3 §3.3.

## Structure

1. **NP/PP feature types** — count/mass, directional/locative
2. **Basic-level composition** — verb + arguments → verb constellation
3. **External override** — adverbial/viewpoint overrides clashing feature
4. **Verification** — composition matches hand-checked examples

## Key Principle

The verb supplies intrinsic temporal features [±Telic, ±Durative, ±Dynamic].
NP and PP arguments contribute to the composite VP telicity:

- **V[-Telic] + NP[+Count]** → VCon[-Telic] (atelic verbs stay atelic)
- **V[-Telic] + PP[+Dir]** → VCon[+Telic] (directional PP telicizes)
- **V[+Telic] + NP[+Count]** → VCon[+Telic] (telic verbs stay telic)
- **V[+Telic] + NP[-Count]** → VCon[-Telic] (mass NP atelicizes)

The **Principle of External Override** (§3.2.5): when an adverbial's
temporal feature clashes with the verb constellation's, the adverbial wins.

-/

namespace Semantics.Tense.Aspect.Composition

open Core (Situation)

open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open _root_ (MassCount)

-- ════════════════════════════════════════════════════
-- § 1. PP Directionality
-- ════════════════════════════════════════════════════

/-- PP directionality feature. Directional PPs contribute telicity;
    locative PPs do not. @cite{smith-1997} §3.3.1 (50b). -/
inductive PPType where
  | directional  -- "to school", "into the room" → [+Telic]
  | locative     -- "in the park", "at home" → no telicity contribution
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Basic-Level Composition
-- ════════════════════════════════════════════════════

/-- Telicity contribution of an object NP.
    Count NPs preserve verb telicity; mass NPs atelicize.
    @cite{smith-1997} §3.3.1 (50a, 51):
    - V[+Telic] + NP[+Count] → VCon[+Telic]  ("builds a house")
    - V[+Telic] + NP[-Count] → VCon[-Telic]   ("builds houses")
    - V[-Telic] + NP[+Count] → VCon[-Telic]   ("walks the dog")
    - V[-Telic] + NP[-Count] → VCon[-Telic]   ("drinks water") -/
def npTelicityContribution (verbTelic : Telicity) (np : MassCount) : Telicity :=
  match verbTelic, np with
  | .telic, .count => .telic
  | _, _ => .atelic

/-- Compose a verb's aspectual profile with its NP object.
    The object's mass/count feature interacts with verb telicity.
    Duration and dynamicity are inherited from the verb. -/
def composeWithNP (verb : AspectualProfile) (np : MassCount) : AspectualProfile :=
  { verb with telicity := npTelicityContribution verb.telicity np }

/-- Compose a verb's aspectual profile with a directional PP.
    Directional PPs contribute [+Telic]; locative PPs don't change telicity.
    @cite{smith-1997} §3.3.1 (50b):
    "child walk to school" → V[-Telic] + PP[Direct'l] → VCon[+Telic]. -/
def composeWithPP (verb : AspectualProfile) (pp : PPType) : AspectualProfile :=
  match pp with
  | .directional => { verb with telicity := .telic }
  | .locative => verb

-- ════════════════════════════════════════════════════
-- § 3. External Override
-- ════════════════════════════════════════════════════

/-- **Principle of External Override** (@cite{smith-1997} §3.2.5, rule 53):
    VCon[a, b, fα] + Adv[fβ] → DVCon[a, b, fβ].

    When an external form (adverbial, viewpoint) has a temporal feature
    that clashes with the verb constellation's, the external feature overrides.

    This is formalized as: override a single feature of the VCon profile.
    The relevant features are telicity and duration; dynamicity is never
    overridden by adverbials. -/
def overrideTelicity (vcon : AspectualProfile) (ext : Telicity) : AspectualProfile :=
  { vcon with telicity := ext }

/-- Override the duration feature (e.g., "for an hour" forces [+Dur]). -/
def overrideDuration (vcon : AspectualProfile) (ext : Duration) : AspectualProfile :=
  { vcon with duration := ext }

-- ════════════════════════════════════════════════════
-- § 4. Verification: Smith's Examples
-- ════════════════════════════════════════════════════

/-! Verify the compositional rules against Smith's examples from §3.3.1. -/

/-- (50a) "child walks the dog": V[-Telic] + NP[+Count] → VCon[-Telic].
    Activity verb with count NP stays atelic. -/
theorem walk_the_dog :
    (composeWithNP activityProfile .count).toVendlerClass = .activity := rfl

/-- (50b) "child walks to school": V[-Telic] + PP[Dir] → VCon[+Telic].
    Activity verb with directional PP becomes telic accomplishment. -/
theorem walk_to_school :
    (composeWithPP activityProfile .directional).toVendlerClass = .accomplishment := rfl

/-- (51a) "child builds a house": V[+Telic] + NP[+Count] → VCon[+Telic].
    Accomplishment verb with count NP stays telic. -/
theorem build_a_house :
    (composeWithNP accomplishmentProfile .count).toVendlerClass = .accomplishment := rfl

/-- (51b) "child builds houses": V[+Telic] + NP[-Count] → VCon[-Telic].
    Accomplishment verb with mass/bare NP becomes atelic activity.
    This is Krifka's classic telicity transfer: QUA NP → telic VP,
    CUM NP → atelic VP. -/
theorem build_houses :
    (composeWithNP accomplishmentProfile .mass).toVendlerClass = .activity := rfl

/-- (52) "Mary coughed for an hour": VCon[+Dyn,-Telic,-Dur] + Adv[+Dur]
    → DVCon[+Dyn,-Telic,+Dur]. Semelfactive → Activity by duration override. -/
theorem cough_for_an_hour :
    (overrideDuration semelfactiveProfile .durative).toVendlerClass = .activity := rfl

/-- External override: telic VCon + atelic adverbial → atelic DVCon.
    "walked to school for an hour" → activity reading. -/
theorem telic_override_to_atelic :
    (overrideTelicity accomplishmentProfile .atelic).toVendlerClass = .activity := rfl

/-- External override: atelic VCon + telic adverbial → telic DVCon.
    "sang in ten minutes" → accomplishment reading. -/
theorem atelic_override_to_telic :
    (overrideTelicity activityProfile .telic).toVendlerClass = .accomplishment := rfl

-- ════════════════════════════════════════════════════
-- § 5. Composition Properties
-- ════════════════════════════════════════════════════

/-- Count NPs preserve the verb's telicity value. -/
theorem count_np_preserves_telicity (v : AspectualProfile) :
    (composeWithNP v .count).telicity = v.telicity := by
  simp only [composeWithNP, npTelicityContribution]; cases v.telicity <;> rfl

/-- Mass NPs always yield atelic VPs, regardless of verb telicity. -/
theorem mass_np_atelicizes (v : AspectualProfile) :
    (composeWithNP v .mass).telicity = .atelic := by
  simp only [composeWithNP, npTelicityContribution]; cases v.telicity <;> rfl

/-- Directional PPs always yield telic VPs. -/
theorem directional_pp_telicizes (v : AspectualProfile) :
    (composeWithPP v .directional).telicity = .telic := rfl

/-- Locative PPs don't change telicity. -/
theorem locative_pp_preserves (v : AspectualProfile) :
    (composeWithPP v .locative) = v := rfl

/-- Composition preserves duration and dynamicity (only telicity changes). -/
theorem compose_preserves_other_features (v : AspectualProfile) (np : MassCount) :
    (composeWithNP v np).duration = v.duration ∧
    (composeWithNP v np).dynamicity = v.dynamicity := ⟨rfl, rfl⟩

/-- Override is idempotent: overriding with the same feature twice is a no-op. -/
theorem override_telicity_idempotent (v : AspectualProfile) (t : Telicity) :
    overrideTelicity (overrideTelicity v t) t = overrideTelicity v t := rfl

/-- External override + composition commute when they target the same feature.
    Override after composition = override directly (composition is invisible). -/
theorem override_absorbs_composition (v : AspectualProfile) (np : MassCount)
    (ext : Telicity) :
    overrideTelicity (composeWithNP v np) ext = overrideTelicity v ext := rfl

-- ════════════════════════════════════════════════════
-- § 6. Semelfactive Coercion Patterns
-- ════════════════════════════════════════════════════

/-! @cite{smith-1997} §3.2.2, §3.2.5: semelfactives shift to activities
    under duration. This is the same shift captured by `duratize_semelfactive`
    in LexicalAspect.lean, but here derived compositionally via
    external override of the duration feature. -/

/-- Semelfactive + durative adverbial → activity (multiple-event reading).
    "Mary was coughing" / "Guy knocked at the door for 5 minutes".
    Derived from override: [-Dur] → [+Dur] yields Activity profile. -/
theorem semelfactive_durative_is_activity :
    (overrideDuration semelfactiveProfile .durative).toVendlerClass = .activity := rfl

/-- This matches the existing LexicalAspect shift operator. -/
theorem override_agrees_with_shift :
    (overrideDuration semelfactiveProfile .durative).toVendlerClass =
    semelfactiveProfile.duratize.toVendlerClass := rfl

/-- Achievement + durative adverbial → accomplishment (process reading).
    "John was winning the race" presents preliminary stages.
    @cite{smith-1997} §3.2.4. -/
theorem achievement_durative_is_accomplishment :
    (overrideDuration achievementProfile .durative).toVendlerClass = .accomplishment := rfl

end Semantics.Tense.Aspect.Composition
