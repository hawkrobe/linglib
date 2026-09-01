/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Tone.Basic

/-!
# Hyman (2006): word-prosodic typology

[hyman-2006] cuts word-prosodic systems along two independent properties rather than into
three types: **tone** — pitch enters the lexical realization of some morphemes (definition
(3)) — and **stress accent** — words carry an obligatory, culminative metrical head
(definition (5)); "pitch accent" is no third prototype but a pick-and-choose of properties
from the two, and its classic cases are reclassified as tonal. Since the two properties are
independent, all four combinations occur (Table I); restricted-H systems attest all four
combinations of obligatoriness and culminativity (Table II), and the deepest typological cut
is OBLHEAD, obligatoriness of the metrical head (§7). The profile `Tone.WordProsody`
records the two dimensions.
-/

namespace Hyman2006

open Tone

/-! ### The two prototypes -/

/-- The four cells of Table I. -/
inductive ProsodicQuadrant where
  | toneAndStress
  | toneOnly
  | stressOnly
  | neither
  deriving DecidableEq, Repr

/-- The cell of Table I a profile falls in. -/
def quadrant (p : WordProsody) : ProsodicQuadrant :=
  match p.tone, p.stressAccent with
  | true, true => .toneAndStress
  | true, false => .toneOnly
  | false, true => .stressOnly
  | false, false => .neither

/-- The two definitional criteria of stress accent (definition (5)): obligatoriness — every
lexical word has a primary stress — and culminativity — at most one. Obligatoriness is the
definitional one (p. 232); culminativity fails in some alleged pitch-accent systems. -/
structure StressAccentCriteria where
  obligatoriness : Bool
  culminativity : Bool
  deriving DecidableEq, Repr

/-- A prototypical stress-accent system meets both criteria. -/
def StressAccentCriteria.isPrototypicalSA (c : StressAccentCriteria) : Bool :=
  c.obligatoriness && c.culminativity

/-- Properties that cluster with the stress-accent prototype without defining it (p. 234):
privativity, subordination, demarcation, rhythmicity. -/
structure ClusteringProperties where
  privativity : Bool
  subordination : Bool
  demarcation : Bool
  rhythmicity : Bool
  deriving DecidableEq, Repr

/-- The prototype shows all four. -/
def prototypicalSACluster : ClusteringProperties :=
  { privativity := true, subordination := true, demarcation := true, rhythmicity := true }

/-! ### Table I -/

/-- A language of Table I (p. 237) with its profile. -/
structure TypologyEntry where
  name : String
  profile : WordProsody
  deriving Repr

/-- Table I. -/
def tableI : List TypologyEntry :=
  [ ⟨"Ma'ya", ⟨true, true⟩⟩, ⟨"Usarufa", ⟨true, true⟩⟩, ⟨"Fasu", ⟨true, true⟩⟩,
    ⟨"Serbo-Croatian", ⟨true, true⟩⟩, ⟨"Swedish-Norwegian", ⟨true, true⟩⟩,
    ⟨"Ayutla Mixtec", ⟨true, true⟩⟩,
    ⟨"Yoruba", ⟨true, false⟩⟩, ⟨"Igbo", ⟨true, false⟩⟩, ⟨"Kuki-Thaadow", ⟨true, false⟩⟩,
    ⟨"Skou", ⟨true, false⟩⟩,
    ⟨"English", ⟨false, true⟩⟩, ⟨"Russian", ⟨false, true⟩⟩, ⟨"Turkish", ⟨false, true⟩⟩,
    ⟨"Finnish", ⟨false, true⟩⟩,
    ⟨"Bella Coola", ⟨false, false⟩⟩, ⟨"French", ⟨false, false⟩⟩, ⟨"Tamazight", ⟨false, false⟩⟩,
    ⟨"Bengali", ⟨false, false⟩⟩ ]

/-- All four cells are attested. -/
theorem all_quadrants_attested :
    ∀ q ∈ [ProsodicQuadrant.toneAndStress, .toneOnly, .stressOnly, .neither],
      ∃ e ∈ tableI, quadrant e.profile = q := by
  decide

/-! ### Table II -/

/-- A restricted-H system of Table II (p. 245) with its criteria. -/
structure RestrictedHToneEntry where
  name : String
  criteria : StressAccentCriteria
  deriving Repr

/-- Table II. -/
def tableII : List RestrictedHToneEntry :=
  [ ⟨"Kinga", ⟨true, true⟩⟩, ⟨"Creek", ⟨true, false⟩⟩, ⟨"Somali", ⟨false, true⟩⟩,
    ⟨"Seneca", ⟨false, false⟩⟩ ]

/-- Obligatoriness and culminativity are independent: all four combinations occur. -/
theorem all_oblig_culm_combos :
    ∀ c ∈ [(⟨true, true⟩ : StressAccentCriteria), ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩],
      ∃ e ∈ tableII, e.criteria = c := by
  decide

/-- Only Kinga meets both criteria. -/
theorem only_kinga_prototypical_sa :
    ∀ e ∈ tableII, e.criteria.isPrototypicalSA = true ↔ e.name = "Kinga" := by
  decide

/-! ### Pitch accent is not a type -/

/-- The three properties that have been called pitch accent, (13): none defines a prototype
parallel to (3) and (5). -/
inductive PALikeProperty where
  /-- (13a) An underlying prosody abstractly different from its surface realizations. -/
  | abstractDifferent
  /-- (13b) A system combining tone and stress. -/
  | combinesToneAndStress
  /-- (13c) Restricted, sparse or privative tone. -/
  | restrictedTone
  deriving DecidableEq, Repr

/-- The classic pitch-accent languages, reclassified: pitch enters lexical realization, so
they are tonal, and without stress accent. -/
def tokyoJapanese : WordProsody := ⟨true, false⟩
def somali : WordProsody := ⟨true, false⟩
def westernBasque : WordProsody := ⟨true, false⟩

theorem pa_languages_are_tonal :
    quadrant tokyoJapanese = .toneOnly ∧ quadrant somali = .toneOnly ∧
      quadrant westernBasque = .toneOnly := ⟨rfl, rfl, rfl⟩

/-! ### The two dimensions read off WALS

WALS 13A ([maddieson-2013]) codes tone by the size of the level inventory — the partition
Hyman's functional definition replaces — and WALS 14A ([goedemans-van-der-hulst-2013])
codes fixed stress location, presupposing an obligatory head. Both map onto the two
dimensions, with a known loss on the stress side. -/

/-- WALS 13A. -/
inductive WalsToneSystem where
  | none | simple | complex
  deriving DecidableEq, Repr

/-- WALS 14A. -/
inductive StressLocation where
  | noFixed | initial | second | third | antepenultimate | penultimate | ultimate
  deriving DecidableEq, Repr

/-- The profile of a WALS coding: any tone system is tone; any 14A value — fixed or free
stress — is stress accent, and absence from 14A is read as no stress accent. -/
def ofWals (t : WalsToneSystem) (s : Option StressLocation) : WordProsody :=
  ⟨t ≠ .none, s.isSome⟩

def english : WordProsody := ofWals .none (some .noFixed)
def german : WordProsody := ofWals .none (some .noFixed)
def finnish : WordProsody := ofWals .none (some .initial)
def turkish : WordProsody := ofWals .none (some .ultimate)
def russian : WordProsody := ofWals .none (some .noFixed)
def french : WordProsody := ofWals .none (some .noFixed)
def spanish : WordProsody := ofWals .none (some .penultimate)
def japanese : WordProsody := ofWals .simple none
def mandarin : WordProsody := ofWals .complex (some .noFixed)
def hindi : WordProsody := ofWals .none (some .noFixed)
def georgian : WordProsody := ofWals .none (some .initial)
def hungarian : WordProsody := ofWals .none (some .initial)
def swahili : WordProsody := ofWals .none (some .penultimate)
def yoruba : WordProsody := ofWals .complex none
def maori : WordProsody := ofWals .none (some .initial)
def zulu : WordProsody := ofWals .simple (some .penultimate)

theorem english_stress_only : quadrant english = .stressOnly := by decide
theorem finnish_stress_only : quadrant finnish = .stressOnly := by decide
theorem yoruba_tone_only : quadrant yoruba = .toneOnly := by decide
theorem japanese_tone_only : quadrant japanese = .toneOnly := by decide
theorem mandarin_tone_and_stress : quadrant mandarin = .toneAndStress := by decide
theorem zulu_tone_and_stress : quadrant zulu = .toneAndStress := by decide

/-- WALS reaches three cells: 14A codes stress location, not its absence, so the −T−SA
cell never appears from WALS alone. -/
theorem wals_covers_three_quadrants :
    ∀ q ∈ [ProsodicQuadrant.toneAndStress, .toneOnly, .stressOnly],
      ∃ p ∈ [english, german, finnish, turkish, russian, french, spanish, japanese, mandarin,
        hindi, georgian, hungarian, swahili, yoruba, maori, zulu], quadrant p = q := by
  decide

/-- French is −T−SA in Table I but has free stress in WALS 14A, which reads as +SA: 14A
does not distinguish free word stress from no word stress (French's is phrase-final). The
−SA classification needs language-specific analysis beyond WALS. -/
theorem french_wals_mismatch :
    quadrant french = .stressOnly ∧
      ∀ e ∈ tableI, e.name = "French" → quadrant e.profile = .neither := by
  decide

/-! ### OBLHEAD as the deepest cut -/

/-- The most significant cut (§7): whether every word obligatorily carries a metrical head.
Stress-accent systems, with or without tone, are OBLHEAD systems; tone-only and −T−SA
systems (Bella Coola, which lacks syllables) are not. -/
def IsOblHeadSystem (p : WordProsody) : Prop := p.stressAccent = true

instance (p : WordProsody) : Decidable (IsOblHeadSystem p) := inferInstanceAs (Decidable (_ = _))

/-- OBLHEAD separates stress accent, with or without tone, from its absence. -/
theorem isOblHeadSystem_iff (p : WordProsody) : IsOblHeadSystem p ↔ p.stressAccent = true :=
  Iff.rfl

/-- OBLHEAD partitions Table I along the stress-accent dimension alone. -/
theorem oblhead_partitions_tableI :
    ∀ e ∈ tableI, IsOblHeadSystem e.profile ↔
      quadrant e.profile = .toneAndStress ∨ quadrant e.profile = .stressOnly := by
  decide

end Hyman2006
