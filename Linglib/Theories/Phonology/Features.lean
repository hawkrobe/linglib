/-!
# Phonological Features

Phonological feature inventory and segment representation, following
the standard feature-geometric model (Clements 1985; Sagey 1986;
Halle 1992). Features are organized into major class, laryngeal,
and place categories.

This module provides the feature inventory consumed by OT and
autosegmental analyses. Housing it in `Theories/Phonology/` rather
than `Core/` follows the convention that theory-specific types live
in `Theories/`; it can be promoted to `Core/` if multiple phonological
frameworks consume it.
-/

namespace Theories.Phonology

-- ============================================================================
-- § 1: Feature Inventory
-- ============================================================================

/-- Distinctive phonological features (binary-valued).

    Organized by the standard feature geometry:
    - **Major class**: consonantal, sonorant, continuant, nasal, lateral, strident
    - **Laryngeal**: voice, spreadGlottis, constrGlottis
    - **Place (Labial)**: labial, round
    - **Place (Coronal)**: coronal, anterior, distributed
    - **Place (Dorsal)**: dorsal, high, low, back, atr -/
inductive Feature where
  -- Major class
  | consonantal
  | sonorant
  | continuant
  | nasal
  | lateral
  | strident
  -- Laryngeal
  | voice
  | spreadGlottis
  | constrGlottis
  -- Place: Labial
  | labial
  | round
  -- Place: Coronal
  | coronal
  | anterior
  | distributed
  -- Place: Dorsal
  | dorsal
  | high
  | low
  | back
  | atr
  deriving DecidableEq, BEq, Repr

/-- A feature value: `some true` = [+F], `some false` = [−F], `none` = unspecified. -/
abbrev FeatureVal := Option Bool

-- ============================================================================
-- § 2: Feature Classification
-- ============================================================================

/-- Is this a major class feature? -/
def Feature.isMajorClass : Feature → Bool
  | .consonantal | .sonorant | .continuant | .nasal | .lateral | .strident => true
  | _ => false

/-- Is this a laryngeal feature? -/
def Feature.isLaryngeal : Feature → Bool
  | .voice | .spreadGlottis | .constrGlottis => true
  | _ => false

/-- Is this a place feature (any articulator node)? -/
def Feature.isPlace : Feature → Bool
  | .labial | .round | .coronal | .anterior | .distributed
  | .dorsal | .high | .low | .back | .atr => true
  | _ => false

/-- Is this a dorsal place feature? -/
def Feature.isDorsal : Feature → Bool
  | .dorsal | .high | .low | .back | .atr => true
  | _ => false

-- ============================================================================
-- § 3: Segment Representation
-- ============================================================================

/-- A segment represented as a (partial) specification of features.
    Unspecified features return `none`. -/
structure Segment where
  spec : Feature → FeatureVal

/-- Is feature `f` specified (either [+F] or [−F])? -/
def Segment.specified (s : Segment) (f : Feature) : Bool :=
  s.spec f |>.isSome

/-- Does feature `f` have value `v`? -/
def Segment.hasValue (s : Segment) (f : Feature) (v : Bool) : Bool :=
  s.spec f == some v

-- ============================================================================
-- § 4: Exhaustive Feature List
-- ============================================================================

/-- All features in declaration order. -/
def Feature.allFeatures : List Feature :=
  [.consonantal, .sonorant, .continuant, .nasal, .lateral, .strident,
   .voice, .spreadGlottis, .constrGlottis,
   .labial, .round,
   .coronal, .anterior, .distributed,
   .dorsal, .high, .low, .back, .atr]

theorem allFeatures_length : Feature.allFeatures.length = 19 := rfl

end Theories.Phonology
