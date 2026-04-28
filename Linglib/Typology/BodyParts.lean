import Linglib.Datasets.WALS.Features.F129A
import Linglib.Datasets.WALS.Features.F130A
import Linglib.Datasets.WALS.Features.F130B

/-!
# Body-part terminology — substrate types and WALS data
@cite{wals-2013} (Chs 129, 130) @cite{brown-2013}
@cite{brown-1976} @cite{andersen-1978}

Type-level enums + per-language profile struct for cross-linguistic
body-part lexicalization across @cite{wals-2013} chapters 129–130
(Brown, drawing on @cite{andersen-1978} and @cite{brown-1976}). Two
mereologically-related contrasts: 'hand' vs 'arm' and 'finger' vs 'hand'.

## Schema

- `HandArmRelation` (Ch 129): one term for hand+arm, or distinct terms
- `FingerHandRelation` (Ch 130A): one term for finger+hand, or distinct
- `BodyPartProfile`: per-language bundle

Per-language data lives in `Fragments/{Lang}/BodyParts.lean`.
-/

set_option autoImplicit false

namespace Typology

-- ============================================================================
-- WALS Ch 129: Hand and arm
-- ============================================================================

/-- Whether a language uses the same or different lexemes for 'hand' and 'arm'
    (WALS Ch 129, @cite{brown-2013}). Many languages use a single term covering
    both (e.g., Japanese *te*, Russian *ruka*); others lexically distinguish
    (e.g., English *hand* vs *arm*). -/
inductive HandArmRelation where
  /-- The same word covers both 'hand' and 'arm'. -/
  | identical
  /-- Distinct words for 'hand' and 'arm'. -/
  | different
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 130A: Finger and hand
-- ============================================================================

/-- Whether a language uses the same or different lexemes for 'finger' and
    'hand' (WALS Ch 130A, @cite{brown-2013}). Identity is rare cross-
    linguistically (12% of sample) and correlates with subsistence type
    per Ch 130B. -/
inductive FingerHandRelation where
  /-- The same word covers both 'finger' and 'hand'. -/
  | identical
  /-- Distinct words for 'finger' and 'hand'. -/
  | different
  deriving DecidableEq, Repr

-- ============================================================================
-- Per-language profile
-- ============================================================================

/-- A language's body-part lexicalization profile across @cite{wals-2013}
    Chs 129–130. -/
structure BodyPartProfile where
  language : String
  iso : String := ""
  family : String := ""
  /-- Ch 129: hand-arm relation. -/
  handArm : Option HandArmRelation := none
  /-- Ch 130A: finger-hand relation. -/
  fingerHand : Option FingerHandRelation := none
  deriving Repr

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert WALS 129A hand-arm values into the substrate enum. -/
def fromWALS129A : Datasets.WALS.F129A.HandAndArm → HandArmRelation
  | .identical => .identical
  | .different => .different

/-- Convert WALS 130A finger-hand values into the substrate enum. -/
def fromWALS130A : Datasets.WALS.F130A.FingerAndHand → FingerHandRelation
  | .identical => .identical
  | .different => .different

-- ============================================================================
-- WALS distribution data
-- ============================================================================

/-- WALS Ch 129 distribution: hand-arm patterns
    (@cite{brown-2013}, n = 617). -/
structure HandArmCounts where
  identical : Nat
  different : Nat
  deriving Repr

def HandArmCounts.total (c : HandArmCounts) : Nat :=
  c.identical + c.different

/-- WALS Ch 129 counts (617 languages). -/
def walsHandArm : HandArmCounts :=
  { identical := 228
  , different := 389 }

/-- WALS Ch 130A distribution: finger-hand patterns
    (@cite{brown-2013}, n = 593). -/
structure FingerHandCounts where
  identical : Nat
  different : Nat
  deriving Repr

def FingerHandCounts.total (c : FingerHandCounts) : Nat :=
  c.identical + c.different

/-- WALS Ch 130A counts (593 languages). -/
def walsFingerHand : FingerHandCounts :=
  { identical := 72
  , different := 521 }

/-- WALS Ch 130B: cultural categories of languages with finger=hand identity
    (@cite{brown-2013}, n = 72). The classic cross-cultural correlation:
    hunter-gatherer societies dominate the finger=hand identity pattern. -/
structure FingerHandCulturalCounts where
  hunterGatherers : Nat
  farmerForagers : Nat
  fullFledgedFarmers : Nat
  deriving Repr

def FingerHandCulturalCounts.total (c : FingerHandCulturalCounts) : Nat :=
  c.hunterGatherers + c.farmerForagers + c.fullFledgedFarmers

/-- WALS Ch 130B counts (72 languages with finger=hand identity). -/
def walsFingerHandCultural : FingerHandCulturalCounts :=
  { hunterGatherers := 46
  , farmerForagers := 18
  , fullFledgedFarmers := 8 }

-- ============================================================================
-- Cross-linguistic generalizations
-- ============================================================================

/-- Most languages distinguish 'hand' from 'arm': 389 of 617 (63%) have
    distinct terms, while 228 (37%) use a single term covering both. -/
theorem hand_arm_different_majority :
    walsHandArm.different > walsHandArm.identical := by decide

/-- Finger-hand identity is rare cross-linguistically: only 72 of 593
    (~12%) of languages use one term for both. The strong default is to
    distinguish them. -/
theorem finger_hand_identity_rare :
    walsFingerHand.identical * 8 < walsFingerHand.total := by decide

/-- Among languages with finger=hand identity, hunter-gatherers dominate:
    46 of 72 (~64%) — the classic Brown (1976) / Andersen (1978)
    correlation between subsistence and lexicalization. -/
theorem finger_hand_hunter_gatherer_majority :
    walsFingerHandCultural.hunterGatherers * 2 >
      walsFingerHandCultural.total := by decide

/-- Hunter-gatherers are more numerous than full-fledged farmers among
    finger=hand languages by a factor of ~5.7 (46 vs 8). -/
theorem hunter_gatherer_dominates_farmer :
    walsFingerHandCultural.hunterGatherers >
      walsFingerHandCultural.fullFledgedFarmers * 5 := by decide

end Typology
