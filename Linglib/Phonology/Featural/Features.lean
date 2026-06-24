/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Featural.Bundle

/-!
# Phonological Features

Complete segmental feature inventory following [hayes-2009] *Introductory
Phonology*, Ch 4. The 26 binary features are organized into manner (root),
laryngeal, and place (labial, coronal, dorsal) categories.

Prosodic features [stress] and [long] are excluded — Hayes treats stress as
a syllable-level property (Ch 14), not a segmental feature.

This module provides the feature inventory consumed by OT, autosegmental,
and syllable analyses.

[hayes-2009]
-/

namespace Phonology

-- ============================================================================
-- § 1: Feature Inventory
-- ============================================================================

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

/-- A segment: a `FeatureBundle Feature Bool` — a partial binary-feature
    specification (`none` = unspecified). -/
structure Segment where
  spec : FeatureBundle Feature Bool

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

/-- Decidable equality on segments via exhaustive feature comparison.
    Enables `decide` on segment-level goals and OT tableaux
    over `List Segment` candidates. -/
instance : DecidableEq Segment := fun s1 s2 =>
  if h : (Feature.allFeatures.all fun f => s1.spec f == s2.spec f) = true
  then isTrue (by
    cases s1; cases s2; congr; funext f
    exact eq_of_beq (List.all_eq_true.mp h f (allFeatures_complete f)))
  else isFalse (fun heq => by
    subst heq
    exact h (List.all_eq_true.mpr fun f _ => beq_self_eq_true (s1.spec f)))

-- ============================================================================
-- § 6: Pattern Matching and Feature Changes
-- ============================================================================

/-- Build a segment from a list of (feature, value) pairs.
    Unmentioned features are unspecified (`none`), giving natural-class
    semantics: `ofSpecs [(continuant, false)]` matches all [-cont] segments. -/
def Segment.ofSpecs (specs : List (Feature × Bool)) : Segment where
  spec f := match specs.find? (λ p => p.1 == f) with
    | some (_, v) => some v
    | none => none

/-- Bool: does segment `s` match natural-class pattern `p`? True when every
    feature specified in `p` agrees with `s`; unspecified features in `p`
    match anything. -/
def Segment.matchesPattern (s : Segment) (p : Segment) : Bool :=
  Feature.allFeatures.all λ f =>
    match p.spec f with
    | none => true
    | some v => s.spec f == some v

/-- Prop wrapper around `matchesPattern` (mirrors `Segment.HasValue` from
    § 3). Lets consumers write mathlib-style universally-quantified theorems
    with Decidable inference via the Bool computation. -/
def Segment.MatchesPattern (s p : Segment) : Prop := s.matchesPattern p = true

instance (s p : Segment) : Decidable (Segment.MatchesPattern s p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Merge feature changes from `change` into `s`: features specified in
    `change` override `s`'s values; unspecified features in `change` are
    preserved. Implements the SPE structural change `A → B` when `B` is a
    partial feature bundle. -/
def Segment.applyChanges (s change : Segment) : Segment :=
  ⟨FeatureBundle.merge change.spec s.spec⟩

/-- Two segments are equal iff their `spec` functions agree on every feature. -/
@[ext] theorem Segment.ext {s t : Segment} (h : ∀ f, s.spec f = t.spec f) :
    s = t := by
  cases s; cases t; congr; funext f; exact h f

/-- Every segment matches itself as a pattern. -/
@[simp] theorem Segment.matchesPattern_self (s : Segment) :
    s.matchesPattern s = true := by
  unfold Segment.matchesPattern
  rw [List.all_eq_true]
  intro f _
  cases s.spec f
  · rfl
  · exact beq_self_eq_true _

/-- Applying the empty change list is the identity. -/
@[simp] theorem Segment.applyChanges_ofSpecs_nil (s : Segment) :
    s.applyChanges (Segment.ofSpecs []) = s := by
  ext f; simp [Segment.applyChanges, Segment.ofSpecs, FeatureBundle.merge]

/-- Applying the same change twice equals applying it once. -/
@[simp] theorem Segment.applyChanges_idem (s change : Segment) :
    (s.applyChanges change).applyChanges change = s.applyChanges change := by
  ext f
  simp only [Segment.applyChanges, FeatureBundle.merge]
  cases change.spec f <;> rfl

end Phonology
