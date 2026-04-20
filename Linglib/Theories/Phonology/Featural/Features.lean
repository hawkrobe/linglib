/-!
# Phonological Features

Complete segmental feature inventory following @cite{hayes-2009} *Introductory
Phonology*, Ch 4. The 26 binary features are organized into manner (root),
laryngeal, and place (labial, coronal, dorsal) categories.

Prosodic features [stress] and [long] are excluded — Hayes treats stress as
a syllable-level property (Ch 14), not a segmental feature.

This module provides the feature inventory consumed by OT, autosegmental,
and syllable analyses.

@cite{hayes-2009}
-/

namespace Phonology

-- ============================================================================
-- § 1: Feature Inventory
-- ============================================================================

/-- Distinctive phonological features (binary-valued).

    Complete segmental inventory from @cite{hayes-2009}:

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

    The sonority hierarchy (Hayes Table 4.1) is decomposed as:
    [±sonorant] > [±approximant] > [±consonantal] > [±syllabic],
    yielding 5 natural classes (obstruent, nasal, liquid, glide, vowel). -/
inductive Feature where
  -- Manner / root
  | syllabic         -- [+syll] = vowels (Hayes §4.4.3)
  | consonantal      -- [+cons] = oral constriction (Hayes §4.4.2)
  | sonorant         -- [+son] = spontaneous voicing (Hayes §4.4.1)
  | approximant      -- [+approx] = no turbulence (Hayes §4.4.1)
  | continuant       -- [+cont] = airflow continues (Hayes §4.4.5)
  | delayedRelease   -- [+del.rel.] = affricates (Hayes §4.4.7)
  | nasal            -- [+nasal] = lowered velum (Hayes §4.4.8)
  | lateral          -- [+lat] = lateral airflow (Hayes §4.4.9)
  | strident         -- [+strid] = high-amplitude noise (Hayes §4.4.10)
  | tap              -- [+tap] = ballistic gesture (Hayes §4.4.6)
  | trill            -- [+trill] = aerodynamic vibration (Hayes §4.4.6)
  -- Laryngeal
  | voice            -- [+voice] = vocal cord vibration (Hayes §4.7)
  | spreadGlottis    -- [+s.g.] = aspiration (Hayes §4.7)
  | constrGlottis    -- [+c.g.] = glottal constriction (Hayes §4.7)
  -- Place: Labial
  | labial           -- [+lab] = lips involved (Hayes §4.6.1)
  | round            -- [+round] = lip rounding (Hayes §4.6.1)
  | labiodental      -- [+labiodental] = lower lip to upper teeth (Hayes §4.6.1)
  -- Place: Coronal
  | coronal          -- [+cor] = tongue blade/tip (Hayes §4.6.2)
  | anterior         -- [+ant] = alveolar ridge or forward (Hayes §4.6.2)
  | distributed      -- [+dist] = laminal contact (Hayes §4.6.2)
  -- Place: Dorsal
  | dorsal           -- [+dor] = tongue body (Hayes §4.6.3)
  | high             -- tongue body raised (Hayes §4.5.1)
  | low              -- tongue body lowered (Hayes §4.5.1)
  | front            -- tongue body fronted (Hayes §4.5.1)
  | back             -- tongue body backed (Hayes §4.5.1)
  | tense            -- tense vowel quality (Hayes §4.5.3)
  deriving DecidableEq, Repr

/-- A feature value: `some true` = [+F], `some false` = [−F], `none` = unspecified. -/
abbrev FeatureVal := Option Bool

-- ============================================================================
-- § 2: Feature Classification
-- ============================================================================

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

-- ============================================================================
-- § 3: Segment Representation
-- ============================================================================

/-- A segment represented as a (partial) specification of features.
    Unspecified features return `none`. -/
structure Segment where
  spec : Feature → FeatureVal

/-- Is feature `f` specified (either [+F] or [−F])? -/
def Segment.Specified (s : Segment) (f : Feature) : Prop :=
  (s.spec f).isSome = true

instance (s : Segment) : DecidablePred (Segment.Specified s) := fun _ =>
  inferInstanceAs (Decidable (_ = true))

/-- Does feature `f` have value `v`? -/
def Segment.HasValue (s : Segment) (f : Feature) (v : Bool) : Prop :=
  s.spec f = some v

instance (s : Segment) (f : Feature) (v : Bool) :
    Decidable (Segment.HasValue s f v) :=
  inferInstanceAs (Decidable (_ = _))

-- ============================================================================
-- § 4: Exhaustive Feature List
-- ============================================================================

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

-- ============================================================================
-- § 5: Segment Equality
-- ============================================================================

/-- Segment equality by checking all 26 features.
    Two segments are BEq-equal iff they agree on every feature value. -/
instance : BEq Segment where
  beq s1 s2 := Feature.allFeatures.all λ f => s1.spec f == s2.spec f

/-- Decidable equality on segments via exhaustive feature comparison.
    Enables `native_decide` on segment-level goals and OT tableaux
    over `List Segment` candidates. -/
instance : DecidableEq Segment := fun s1 s2 =>
  if h : (Feature.allFeatures.all fun f => s1.spec f == s2.spec f) = true
  then isTrue (by
    cases s1; cases s2; congr; funext f
    exact eq_of_beq (List.all_eq_true.mp h f (allFeatures_complete f)))
  else isFalse (fun heq => by
    subst heq
    exact h (List.all_eq_true.mpr fun f _ => beq_self_eq_true (s1.spec f)))

end Phonology
