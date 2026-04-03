/-!
# Iconicity: Empirical Data

Theory-neutral observations about iconic meaning in sign language,
focusing on classifier predicates and their spatial interpretation.

## Key Observations

1. Sign language classifiers have iconic content: their position,
   orientation, and movement in signing space are interpreted relative
   to a viewpoint.

2. Classifiers denoting static objects can move in signing space to
   represent relative motion — the object appears to move from the
   perspective of a moving character (the "traveling shot" effect).

3. The direction of classifier movement determines the inferred path
   of the character, not absolute object motion.
-/

namespace Phenomena.Iconicity

-- ════════════════════════════════════════════════════════════════
-- § Classifier Motion
-- ════════════════════════════════════════════════════════════════

/-- Direction of a classifier's movement in signing space. -/
inductive ClassifierDirection where
  | passingLeft    -- classifier moves past the signer's head on the left
  | passingRight   -- classifier moves past the signer's head on the right
  | approaching    -- classifier moves toward the signer
  | receding       -- classifier moves away from the signer
  | stationary     -- classifier does not move
  deriving DecidableEq, Repr

/-- Whether classifier movement is dynamic (involves motion). -/
def ClassifierDirection.isDynamic : ClassifierDirection → Bool
  | .stationary => false
  | _ => true

-- ════════════════════════════════════════════════════════════════
-- § Relative Motion
-- ════════════════════════════════════════════════════════════════

/-- The type of motion interpretation triggered by a classifier. -/
inductive MotionType where
  | absolute  -- the object itself moves (standard interpretation)
  | relative  -- the object appears to move from a moving viewpoint
  deriving DecidableEq, Repr

/-- A relative motion reading: the object class and how it appears
    to move from the character's perspective. -/
structure RelativeMotionReading where
  /-- The class of object (tree, pole, house, etc.) -/
  objectClass : String
  /-- The apparent direction of the object's motion -/
  apparentDirection : ClassifierDirection
  /-- Whether the object is actually static in the world -/
  objectIsStatic : Bool

-- ════════════════════════════════════════════════════════════════
-- § Core Generalizations
-- ════════════════════════════════════════════════════════════════

/-- The traveling shot generalization: when a classifier denoting a
    static object moves in signing space, the movement is interpreted
    as relative motion from a moving viewpoint, not as absolute motion
    of the object. -/
structure TravelingShotEffect where
  /-- The static object class -/
  objectClass : String
  /-- The classifier's direction in signing space -/
  classifierDirection : ClassifierDirection
  /-- The motion type is relative, not absolute -/
  motionType : MotionType
  /-- The classifier direction determines the character's inferred path -/
  classifierDirection_isDynamic : classifierDirection.isDynamic = true
  motionType_isRelative : motionType = .relative

/-- Role Shift status of a classifier construction. -/
inductive RoleShiftStatus where
  | strict     -- body rotation, eyegaze shift, agreement changes
  | broad      -- signer's body represents another character (no rotation)
  | absent     -- no Role Shift markers
  deriving DecidableEq, Repr

end Phenomena.Iconicity
