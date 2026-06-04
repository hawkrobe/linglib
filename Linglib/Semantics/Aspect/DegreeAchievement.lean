import Linglib.Core.Scales.Scale
import Linglib.Semantics.Aspect.Dimension
import Linglib.Features.Aktionsart

/-!
# Degree Achievements
[kennedy-levin-2008]

[kennedy-levin-2008] show that degree achievements (rust, cool, widen, increase)
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
-/

namespace Features.DegreeAchievement

open Core.Scale (Boundedness LicensingPipeline)
open Features
open Features

/-- A degree achievement's base scale structure.

    The key claim: the telicity of a degree achievement verb is determined
    by the boundedness of the scale inherited from the base adjective.
    Scales with a maximum (closed, upper-bounded) yield telic VPs;
    scales without a maximum (open, lower-bounded) yield atelic VPs. -/
structure DegreeAchievementScale where
  /-- The scalar dimension the base adjective measures. Its boundedness is the
      order-mixin profile of the dimension's degree type, recovered by the derived
      `scaleBoundedness` below — not stored. -/
  dimension : ScalarTelicity.Dimension
  /-- Citation form of the base adjective (if deadjectival). -/
  baseAdjective : Option String := none
  deriving Repr, BEq

/-- The base scale's boundedness, as a derived view of the dimension (the scale's
    shape is read off the dimension's order structure, not stored per verb). -/
def DegreeAchievementScale.scaleBoundedness (s : DegreeAchievementScale) : Boundedness :=
  s.dimension.boundedness

instance : Inhabited DegreeAchievementScale where
  default := { dimension := .unspecified }

/-- Derive default telicity from scale boundedness — the central claim of
    [kennedy-levin-2008]. Scales with a maximum → telic; scales without → atelic.

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
variable (a : Option String)

/-- A closed dimension (e.g. *straightness*) → telic. -/
theorem closed_dimension_telic :
    (DegreeAchievementScale.mk .straightness a).defaultTelicity = .telic := rfl

/-- An open dimension (e.g. *width*) → atelic. -/
theorem open_dimension_atelic :
    (DegreeAchievementScale.mk .width a).defaultTelicity = .atelic := rfl

/-- A closed dimension → accomplishment. -/
theorem closed_dimension_accomplishment :
    (DegreeAchievementScale.mk .straightness a).defaultVendlerClass = .accomplishment := rfl

/-- An open dimension → activity. -/
theorem open_dimension_activity :
    (DegreeAchievementScale.mk .width a).defaultVendlerClass = .activity := rfl

end

/-- defaultVendlerClass always returns.accomplishment or.activity —
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

end Features.DegreeAchievement
