/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Phonological Features

The distinctive-feature atom: the 26 binary features of [hayes-2009]
*Introductory Phonology*, Ch 4, organized into manner (root), laryngeal, and
place (labial, coronal, dorsal) categories, with the flat classification
predicates and the exhaustive feature list.

Prosodic features [stress] and [long] are excluded — Hayes treats stress as a
syllable-level property (Ch 14), not a segmental feature.

`Segment` (the bundle over `Feature`) and its predicate API live in
`Phonology/Segment.lean`.

[hayes-2009]
-/

namespace Phonology

/-! ### Feature inventory -/

/-- Distinctive phonological features (binary-valued).

    Complete segmental inventory from [hayes-2009]:

    - **Manner (root)**: syllabic, consonantal, sonorant, approximant,
      continuant, delayedRelease, nasal, lateral, strident, tap, trill
    - **Laryngeal**: voice, spreadGlottis, constrGlottis
    - **Place (Labial)**: labial, round, labiodental
    - **Place (Coronal)**: coronal, anterior, distributed
    - **Place (Dorsal)**: dorsal, high, low, front, back, tense

    **Note**: The grouping above follows Hayes's flat classification.
    The hierarchical feature geometry (`FeatureGeometry.lean`) re-maps
    some of these features to different nodes: [nasal] → soft palate,
    [continuant] → supralaryngeal, [lateral]/[strident] → coronal.
    The flat `isMajorClass` predicate has no single geometric counterpart
    — see subsumption theorems in `FeatureGeometry.lean` §6.

    A feature decomposition consistent with Hayes's sonority discussion:
    [±sonorant] > [±approximant] > [±consonantal] > [±syllabic],
    yielding 5 natural classes (obstruent, nasal, liquid, glide, vowel). -/
inductive Feature where
  -- Manner / root
  | syllabic         -- [+syll] = vowels
  | consonantal      -- [+cons] = oral constriction
  | sonorant         -- [+son] = spontaneous voicing
  | approximant      -- [+approx] = no turbulence
  | continuant       -- [+cont] = airflow continues
  | delayedRelease   -- [+del.rel.] = affricates
  | nasal            -- [+nasal] = lowered velum
  | lateral          -- [+lat] = lateral airflow
  | strident         -- [+strid] = high-amplitude noise
  | tap              -- [+tap] = ballistic gesture
  | trill            -- [+trill] = aerodynamic vibration
  -- Laryngeal
  | voice            -- [+voice] = vocal cord vibration
  | spreadGlottis    -- [+s.g.] = aspiration
  | constrGlottis    -- [+c.g.] = glottal constriction
  -- Place: Labial
  | labial           -- [+lab] = lips involved
  | round            -- [+round] = lip rounding
  | labiodental      -- [+labiodental] = lower lip to upper teeth
  -- Place: Coronal
  | coronal          -- [+cor] = tongue blade/tip
  | anterior         -- [+ant] = alveolar ridge or forward
  | distributed      -- [+dist] = laminal contact
  -- Place: Dorsal
  | dorsal           -- [+dor] = tongue body
  | high             -- tongue body raised
  | low              -- tongue body lowered
  | front            -- tongue body fronted
  | back             -- tongue body backed
  | tense            -- tense vowel quality
  deriving DecidableEq, Repr

/-- A feature value: `some true` = [+F], `some false` = [−F], `none` = unspecified. -/
abbrev FeatureVal := Option Bool

/-! ### Feature classification -/

/-- Is this a manner / root feature? -/
def Feature.IsMajorClass : Feature → Prop
  | .syllabic | .consonantal | .sonorant | .approximant
  | .continuant | .delayedRelease | .nasal | .lateral
  | .strident | .tap | .trill => True
  | _ => False

instance : DecidablePred Feature.IsMajorClass := fun f => by
  cases f <;> unfold Feature.IsMajorClass <;> infer_instance

/-- Is this a laryngeal feature? -/
def Feature.IsLaryngeal : Feature → Prop
  | .voice | .spreadGlottis | .constrGlottis => True
  | _ => False

instance : DecidablePred Feature.IsLaryngeal := fun f => by
  cases f <;> unfold Feature.IsLaryngeal <;> infer_instance

/-- Is this a place feature (any articulator node)? -/
def Feature.IsPlace : Feature → Prop
  | .labial | .round | .labiodental
  | .coronal | .anterior | .distributed
  | .dorsal | .high | .low | .front | .back | .tense => True
  | _ => False

instance : DecidablePred Feature.IsPlace := fun f => by
  cases f <;> unfold Feature.IsPlace <;> infer_instance

/-- Is this a labial place feature? -/
def Feature.IsLabial : Feature → Prop
  | .labial | .round | .labiodental => True
  | _ => False

instance : DecidablePred Feature.IsLabial := fun f => by
  cases f <;> unfold Feature.IsLabial <;> infer_instance

/-- Is this a coronal place feature? -/
def Feature.IsCoronal : Feature → Prop
  | .coronal | .anterior | .distributed => True
  | _ => False

instance : DecidablePred Feature.IsCoronal := fun f => by
  cases f <;> unfold Feature.IsCoronal <;> infer_instance

/-- Is this a dorsal place feature? -/
def Feature.IsDorsal : Feature → Prop
  | .dorsal | .high | .low | .front | .back | .tense => True
  | _ => False

instance : DecidablePred Feature.IsDorsal := fun f => by
  cases f <;> unfold Feature.IsDorsal <;> infer_instance

/-! ### Exhaustive feature list -/

/-- All 26 features in declaration order. -/
def Feature.allFeatures : List Feature :=
  [.syllabic, .consonantal, .sonorant, .approximant,
   .continuant, .delayedRelease, .nasal, .lateral, .strident, .tap, .trill,
   .voice, .spreadGlottis, .constrGlottis,
   .labial, .round, .labiodental,
   .coronal, .anterior, .distributed,
   .dorsal, .high, .low, .front, .back, .tense]

theorem allFeatures_length : Feature.allFeatures.length = 26 := rfl

/-- Every `Feature` constructor appears in `allFeatures`. -/
theorem allFeatures_complete (f : Feature) : f ∈ Feature.allFeatures := by
  cases f <;> simp [Feature.allFeatures]

end Phonology
