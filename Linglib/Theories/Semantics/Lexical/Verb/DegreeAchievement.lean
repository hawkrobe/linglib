import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Degree Achievements
@cite{kennedy-levin-2008}

Kennedy & Levin (2007) show that degree achievements (rust, cool, widen, increase)
have **variable telicity** determined by the boundedness of the underlying adjectival
scale:

- Closed-scale adjectives (clean, full, straight) → telic degree achievements
- Open-scale adjectives (long, wide, cool) → atelic degree achievements

A degree achievement V derived from adjective A has a **measure of change** function
mΔ(e) = d(result(e)) - d(init(e)) on A's scale. Telicity = whether mΔ is bounded:
if A's scale has a maximum, mΔ is bounded → telic (accomplishment); if A's scale is
open, mΔ is unbounded → atelic (activity).

This module derives `VendlerClass` from `Boundedness`, connecting to the existing
`LicensingPipeline` infrastructure in `Core/Scales/Scale.lean`.

- Kennedy, C. & Levin, B. (2007). Measure of change: The adjectival core of
  degree achievements. In L. McNally & C. Kennedy (eds.), *Adjectives and Adverbs*,
  156–182. OUP.
-/

namespace Semantics.Lexical.Verb.DegreeAchievement

open Core.Scale (Boundedness LicensingPipeline)
open Semantics.Lexical.Verb.Aspect (VendlerClass Telicity)

/-- A degree achievement's base scale structure (Kennedy & Levin 2007).

    The key claim: the telicity of a degree achievement verb is determined
    by the boundedness of the scale inherited from the base adjective.
    Scales with a maximum (closed, upper-bounded) yield telic VPs;
    scales without a maximum (open, lower-bounded) yield atelic VPs. -/
structure DegreeAchievementScale where
  /-- The adjectival base's scale boundedness (Kennedy 2007). -/
  scaleBoundedness : Boundedness
  /-- The dimension of change (height, temperature, fullness, ...). -/
  dimension : String
  /-- Citation form of the base adjective (if deadjectival). -/
  baseAdjective : Option String := none
  deriving Repr, BEq

instance : Inhabited DegreeAchievementScale where
  default := { scaleBoundedness := .open_, dimension := "" }

/-- Derive default telicity from scale boundedness (K&L 2007 Thm 1).
    Scales with a maximum → telic; scales without → atelic.

    The mapping follows `Boundedness.hasMax`:
    - `.closed` (has max) → `.telic`
    - `.upperBounded` (has max) → `.telic`
    - `.open_` (no max) → `.atelic`
    - `.lowerBounded` (no max) → `.atelic` -/
def DegreeAchievementScale.defaultTelicity (s : DegreeAchievementScale) : Telicity :=
  if s.scaleBoundedness.hasMax then .telic else .atelic

/-- Derive default VendlerClass from scale boundedness.
    All degree achievements are dynamic and durative, so:
    telic → accomplishment, atelic → activity. -/
def DegreeAchievementScale.defaultVendlerClass (s : DegreeAchievementScale) : VendlerClass :=
  if s.scaleBoundedness.hasMax then .accomplishment else .activity

-- ════════════════════════════════════════════════════
-- § Theorems
-- ════════════════════════════════════════════════════

section
variable (d : String) (a : Option String)

/-- Closed scaleBoundedness → telic. -/
theorem closed_scale_telic :
    (DegreeAchievementScale.mk .closed d a).defaultTelicity = .telic := rfl

/-- Open scaleBoundedness → atelic. -/
theorem open_scale_atelic :
    (DegreeAchievementScale.mk .open_ d a).defaultTelicity = .atelic := rfl

/-- Upper-bounded → telic (has max → bounded mΔ). -/
theorem upperBounded_telic :
    (DegreeAchievementScale.mk .upperBounded d a).defaultTelicity = .telic := rfl

/-- Lower-bounded → atelic (no max → unbounded mΔ). -/
theorem lowerBounded_atelic :
    (DegreeAchievementScale.mk .lowerBounded d a).defaultTelicity = .atelic := rfl

/-- Closed scaleBoundedness → accomplishment. -/
theorem closed_scale_accomplishment :
    (DegreeAchievementScale.mk .closed d a).defaultVendlerClass = .accomplishment := rfl

/-- Open scaleBoundedness → activity. -/
theorem open_scale_activity :
    (DegreeAchievementScale.mk .open_ d a).defaultVendlerClass = .activity := rfl

end

/-- defaultVendlerClass always returns .accomplishment or .activity —
    degree achievements are always dynamic and durative. -/
theorem default_vendler_is_dynamic (s : DegreeAchievementScale) :
    s.defaultVendlerClass = .accomplishment ∨ s.defaultVendlerClass = .activity := by
  simp only [DegreeAchievementScale.defaultVendlerClass]
  cases h : s.scaleBoundedness.hasMax <;> simp

/-- defaultTelicity agrees with the telicity of defaultVendlerClass. -/
theorem telicity_vendler_agree (s : DegreeAchievementScale) :
    s.defaultVendlerClass.telicity = s.defaultTelicity := by
  simp only [DegreeAchievementScale.defaultVendlerClass, DegreeAchievementScale.defaultTelicity]
  cases h : s.scaleBoundedness.hasMax <;> simp [VendlerClass.telicity]

-- ════════════════════════════════════════════════════
-- § LicensingPipeline instance
-- ════════════════════════════════════════════════════

/-- LicensingPipeline instance for DegreeAchievementScale:
    maps through scaleBoundedness directly. hasMax → closed, else open. -/
instance : LicensingPipeline DegreeAchievementScale where
  toBoundedness s := if s.scaleBoundedness.hasMax then .closed else .open_

end Semantics.Lexical.Verb.DegreeAchievement
