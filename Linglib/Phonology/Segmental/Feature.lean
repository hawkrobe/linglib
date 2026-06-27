/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Phonological features

The distinctive-feature atom: the 26 binary features of [hayes-2009], grouped
into manner/root, laryngeal, and the labial/coronal/dorsal place articulators.

## Main definitions

* `Feature`: the 26 binary distinctive features.
* `Feature.category`: the articulator category of a feature; the single source
  of truth for the `Feature.IsLaryngeal`, `Feature.IsDorsal`, and
  `Feature.IsPlace` predicates.
* `Feature.allFeatures`: the exhaustive feature list (`allFeatures_complete`).

## Implementation notes

The stress and length features ([stress], [long]) are excluded: Hayes treats
stress as a syllable-level property, not a segmental feature.

`Segment` (the bundle over `Feature`) and its predicate API live in
`Phonology/Segmental/Basic.lean`; the hierarchical re-grouping of these features into
autosegmental tiers lives in `Phonology/Segmental/FeatureGeometry.lean`, bridged to the
flat classification here by subsumption theorems.
-/

namespace Phonology

/-! ### Feature inventory -/

/-- A binary distinctive phonological feature, following [hayes-2009]'s segmental inventory. -/
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

/-! ### Feature classification -/

/-- The articulator category of a feature: manner/root, laryngeal, or place. -/
inductive Feature.Category where
  | manner | laryngeal | labial | coronal | dorsal
  deriving DecidableEq, Repr

/-- The articulator category of each distinctive feature. -/
def Feature.category : Feature → Feature.Category
  | .syllabic | .consonantal | .sonorant | .approximant
  | .continuant | .delayedRelease | .nasal | .lateral
  | .strident | .tap | .trill                        => .manner
  | .voice | .spreadGlottis | .constrGlottis         => .laryngeal
  | .labial | .round | .labiodental                  => .labial
  | .coronal | .anterior | .distributed              => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

/-- Is this a laryngeal feature? -/
abbrev Feature.IsLaryngeal (f : Feature) : Prop := f.category = .laryngeal

/-- Is this a dorsal place feature? -/
abbrev Feature.IsDorsal (f : Feature) : Prop := f.category = .dorsal

/-- Is this a place feature (any articulator node)? -/
abbrev Feature.IsPlace (f : Feature) : Prop :=
  f.category = .labial ∨ f.category = .coronal ∨ f.category = .dorsal

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
