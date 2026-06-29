/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.Nat
import Linglib.Features.Basic

/-!
# Segmental representation: definitions

The distinctive feature and the segment built over it. A **feature** is one of the
26 binary distinctive features of [hayes-2009]; a **segment** is a partial
specification of those features — each `+`, `−`, or unspecified — ordered by
specificity (the unification-grammar subsumption order, inherited as a feature
bundle), with the unspecified archisegment least and natural-class generalization
as meet.

This file collects definitions only — the feature inventory, the segment and its
valuation/pattern/change API, the natural-class predicates, and the sonority
scales. The theorems about them live in `Phonology/Segmental/Basic.lean`.

[hayes-2009] [chomsky-halle-1968] [clements-1990] [parker-2002]
-/

namespace Phonology

/-! ### Feature inventory -/

/-- A binary distinctive phonological feature, following [hayes-2009]'s segmental
    inventory. (The stress and length features are excluded: [hayes-2009] treats
    stress as a syllable-level property, not a segmental feature.) -/
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
  deriving DecidableEq, Repr, Fintype

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

/-! ### The segment bundle -/

/-- A **segment**: a partial specification of the distinctive features — each
    feature is `+`, `−`, or left unspecified. Segments are ordered by specificity:
    one refines another when it agrees on every feature the other commits to, and
    possibly more. The fully unspecified segment is least; the most specific class
    common to two segments is their meet. -/
abbrev Segment := Feature → Flat Bool

/-- Does feature `f` have value `v`? -/
def Segment.HasValue (s : Segment) (f : Feature) (v : Bool) : Prop :=
  s f = some v

instance (s : Segment) (f : Feature) (v : Bool) :
    Decidable (Segment.HasValue s f v) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Pattern matching and feature changes -/

/-- Build a segment from a list of (feature, value) pairs.
    Unmentioned features are unspecified (`none`), giving natural-class
    semantics: `ofSpecs [(continuant, false)]` matches all [-cont] segments. -/
def Segment.ofSpecs (specs : List (Feature × Bool)) : Segment :=
  fun f => match specs.find? (λ p => p.1 == f) with
    | some (_, v) => some v
    | none => none

/-- Bool: does segment `s` match natural-class pattern `p`? True when every
    feature specified in `p` agrees with `s`; unspecified features in `p`
    match anything — i.e. when `p` subsumes `s` (`matchesPattern_iff_le`). -/
def Segment.matchesPattern (s : Segment) (p : Segment) : Bool :=
  Feature.allFeatures.all fun f => decide (p f ≤ s f)

/-- Prop wrapper around `matchesPattern` (mirrors `Segment.HasValue`). Lets
    consumers write mathlib-style universally-quantified theorems with
    Decidable inference via the Bool computation. -/
def Segment.MatchesPattern (s p : Segment) : Prop := s.matchesPattern p = true

instance (s p : Segment) : Decidable (Segment.MatchesPattern s p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Merge feature changes from `change` into `s`: features specified in
    `change` override `s`'s values; unspecified features in `change` are
    preserved. Implements the SPE structural change `A → B` (when `B` is a
    partial bundle) as the shared `Features.Bundle.merge`. -/
def Segment.applyChanges (s change : Segment) : Segment :=
  Features.Bundle.merge change s

/-! ### Natural-class predicates

Language-neutral natural-class membership predicates, by the SPE feature
decompositions standard since [chomsky-halle-1968] and codified in textbook
form by [hayes-2009]. Pure substrate: they project information already encoded
in a segment, consumed by per-language Fragment files rather than redefined
locally. -/

/-- A segment is a vowel iff it is [+syllabic]. -/
def Segment.IsVowel (s : Segment) : Prop := s.HasValue .syllabic true

instance (s : Segment) : Decidable s.IsVowel := by
  unfold Segment.IsVowel; infer_instance

/-- A segment is a consonant iff it is [+consonantal]. -/
def Segment.IsConsonant (s : Segment) : Prop := s.HasValue .consonantal true

instance (s : Segment) : Decidable s.IsConsonant := by
  unfold Segment.IsConsonant; infer_instance

/-- A segment is an oral stop iff it is [+cons, -son, -cont]. -/
def Segment.IsStop (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant false

instance (s : Segment) : Decidable s.IsStop := by
  unfold Segment.IsStop; infer_instance

/-- A segment is a fricative iff it is [+cons, -son, +cont]. -/
def Segment.IsFricative (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant true

instance (s : Segment) : Decidable s.IsFricative := by
  unfold Segment.IsFricative; infer_instance

/-- A segment is a nasal iff it is [+nasal]. -/
def Segment.IsNasal (s : Segment) : Prop := s.HasValue .nasal true

instance (s : Segment) : Decidable s.IsNasal := by
  unfold Segment.IsNasal; infer_instance

/-- A segment is a liquid iff it is [+cons, +son] and one of
[+lateral], [+trill], [+tap] — admitting the lateral /l/, the trill /r/,
and the flap /ɾ/ under a single textbook class. -/
def Segment.IsLiquid (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant true ∧
    (s.HasValue .lateral true ∨ s.HasValue .trill true ∨ s.HasValue .tap true)

instance (s : Segment) : Decidable s.IsLiquid := by
  unfold Segment.IsLiquid; infer_instance

/-- A segment is a glide iff it is [-cons, -syllabic, +approximant]. -/
def Segment.IsGlide (s : Segment) : Prop :=
  s.HasValue .consonantal false ∧ s.HasValue .syllabic false ∧
    s.HasValue .approximant true

instance (s : Segment) : Decidable s.IsGlide := by
  unfold Segment.IsGlide; infer_instance

/-! ### Underspecification

The segment-level operations are thin lifts of the shared `Features.Bundle`
algebra. Three-valued (`+ / − / ∅`) specification is standard in [keating-1988],
[inkelas-orgun-1995], and [steriade-1995]; `fillFeature` is default-fill,
preserving existing values, per [kiparsky-1982] [archangeli-1988], while
`setFeature` overrides. The Latin coda /l/ analysis in [sen-2015] is a worked
example. -/

namespace Segment

/-- A segment is **unspecified** for feature `f` iff its value there is `none`. -/
def Unspecified (s : Segment) (f : Feature) : Prop := s f = none

instance (s : Segment) (f : Feature) : Decidable (s.Unspecified f) :=
  inferInstanceAs (Decidable (_ = none))

/-- Remove the specification of feature `f` from `s` (the
    `Features.Bundle.delete` slot operation). The result is unspecified for `f`
    and agrees with `s` on every other feature. -/
def unsetFeature (s : Segment) (f : Feature) : Segment :=
  Features.Bundle.delete f s

/-- Set feature `f` to value `v`, overriding any existing specification
    (the `Features.Bundle.set` slot operation). For default-fill semantics that
    only assigns when `f` is currently unspecified, use `fillFeature`. -/
def setFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  Features.Bundle.set f v s

/-- Fill feature `f` with value `v` only if `s` is currently unspecified
    for `f`; existing specifications are preserved. This implements the
    default-fill semantics of feature-filling rules in lexical phonology
    [kiparsky-1982] [archangeli-1988]. -/
def fillFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  Features.Bundle.merge s (Features.Bundle.single f v)

/-- Categorical feature spreading from context: the target `s`, when
    unspecified for `f`, takes the `f`-value of `ctx`; already-specified
    targets and features other than `f` are untouched. When `ctx` is
    itself unspecified for `f`, the target stays unspecified.

    This is a [keating-1988] *context rule*: the target acquires a categorical
    feature value from its neighbour and that value blocks further
    interactions. It is **distinct from** her gradient phonetic interpolation
    (her unspecified /h/ example), in which an unspecified segment stays
    unspecified and the phonetics builds a continuous trajectory through it;
    gradient phonetic interpolation is out of scope at this categorical-featural
    substrate. -/
def fillFromContext (s : Segment) (f : Feature) (ctx : Segment) : Segment :=
  Features.Bundle.merge s (Function.update (⊥ : Segment) f (ctx f))

end Segment

/-! ### Sonority -/

/-- The abstract sonority hierarchy ([clements-1990]): what the synchronic
    grammar operates on, ordering segments from least to most sonorous.

    | Rank | Class     |
    |------|-----------|
    |  0   | Stop      |
    |  1   | Fricative |
    |  2   | Nasal     |
    |  3   | Liquid    |
    |  4   | Glide     |
    |  5   | Vowel     |

    For the finer 8-level scale that splits obstruents by voice, see
    `Sonority.Class`. -/
inductive Sonority where
  | stop
  | fricative
  | nasal
  | liquid
  | glide
  | vowel
  deriving DecidableEq, Repr

namespace Sonority

/-- Numeric rank (0 = least sonorous). -/
def rank : Sonority → Nat
  | .stop => 0 | .fricative => 1 | .nasal => 2
  | .liquid => 3 | .glide => 4 | .vowel => 5

instance : LinearOrder Sonority :=
  LinearOrder.lift' rank fun a b h => by cases a <;> cases b <;> simp_all [rank]

/-- The sonority of a segment, read off its features
    ([hayes-2009], [clements-1990]). -/
def ofSegment (s : Segment) : Sonority :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then .fricative else .stop
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-! ### The Parker sonority scale -/

/-- The 8-level Parker sonority partition ([parker-2002]) — a refinement of
    `Sonority` that splits obstruents by [±continuant] and [±voice]. This is the
    sonority *scale*; it is distinct from the natural-class predicates above
    (`Segment.IsVowel` &c.), which are feature membership.

    Crucially [parker-2002] ranks voiced stops above voiceless fricatives
    (`vds = 3 > vlf = 2`) — his intensity-based default universal, reversible in
    particular languages. The finer granularity is needed for sonority-
    conditioned gradient phenomena such as Tarifit intrusive vowels
    ([afkir-zellou-2025]). -/
inductive Class where
  | vls    -- voiceless stops: [−son, −cont, −voice]
  | vds    -- voiced stops: [−son, −cont, +voice]
  | vlf    -- voiceless fricatives: [−son, +cont, −voice]
  | vdf    -- voiced fricatives: [−son, +cont, +voice]
  | nasal  -- nasals: [+son, −approx]
  | liquid -- liquids/taps: [+son, +approx, +cons]
  | glide  -- glides: [+son, +approx, −cons, −syll]
  | vowel  -- vowels: [+son, +approx, −cons, +syll]
  deriving DecidableEq, Repr

/-- Parker's default universal 8-level ranking ([parker-2002]): voiced stops
    (`vds = 3`) outrank voiceless fricatives (`vlf = 2`). -/
def Class.parkerRank : Class → Nat
  | .vls => 1 | .vlf => 2 | .vds => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

/-- Classify a segment on the Parker 8-level scale: as `Sonority.ofSegment`,
    but additionally splitting obstruents by [±voice] ([parker-2002]). -/
def Class.ofSegment (s : Segment) : Class :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then
      if s.HasValue .voice true then .vdf else .vlf
    else
      if s.HasValue .voice true then .vds else .vls
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-- Coarsen to the substance-free `Sonority`, collapsing the voicing split. -/
def Class.toSonority : Class → Sonority
  | .vls | .vds => .stop
  | .vlf | .vdf => .fricative
  | .nasal => .nasal
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel

end Sonority

end Phonology
