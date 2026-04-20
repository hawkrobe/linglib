import Linglib.Theories.Semantics.Verb.VerbEntry
import Linglib.Theories.Phonology.Autosegmental.RegisterTier

/-!
# Hausa Verb Grades (Parsons System) — mathlib-style
@cite{newman-2000}

Hausa verbs are organised by the **Parsons grade system** (Parsons
1960b, codified in @cite{newman-2000} ch. 74): a closed inventory of
derivational stem-templates (gr0–gr7) defined by a fixed pairing of
**tone melody**, **final-vowel template**, and **derivational function**. Each grade also has up to four
**syntactic forms** (A/B/C/D) selected by the post-verbal environment.

## Architectural shape (mathlib analogy)

This file is the *interpretation* of two existing Theory interfaces in
Hausa, not a parallel hierarchy:

- `Theories/Semantics/Verb/VerbEntry.VerbCore` carries argument
  structure, voice, and Vendler class. A Hausa verb is a `VerbCore`
  *plus* a Parsons grade.
- `Theories/Phonology/Autosegmental/RegisterTier.TRN` carries
  the autosegmental tone primitives. A grade's tone melody is a list
  of `TRN`s, not a fresh enum.

The grade itself is a **record of predictions** (`StemTemplate`): tone,
final-vowel template, derivational function, and the argument-structure
defaults the grade entails. Concrete verbs derive their `VerbCore`
fields from their grade by default; per-verb overrides are explicit.

The named theorems below are **universal claims about the grade system
or about Hausa verb lists**, not `rfl` checks on per-verb stipulations.
Per-cell verifications appear as `example`s.
-/

namespace Fragments.Hausa.VerbGrades

open Phonology.Autosegmental.RegisterTier (TRN)
open Core.Verbs (VerbCore VoiceType ComplementType)

-- ============================================================================
-- § 1: Form Inventory (A/B/C/D — @cite{newman-2000} §74.2)
-- ============================================================================

/-- The four syntactic forms selected by the post-verbal environment.
    A/B/C are pre-pause / pre-pronoun / pre-noun direct object; D is
    pre-indirect-object (host of the *-aC H* pre-dative suffix). -/
inductive SynForm where
  | A | B | C | D
  deriving DecidableEq, Repr, Inhabited

namespace SynForm

/-- The four forms in canonical order. -/
def all : List SynForm := [.A, .B, .C, .D]

theorem all_length : all.length = 4 := by decide

end SynForm

-- ============================================================================
-- § 2: Final-Vowel Templates
-- ============================================================================

/-- Final vowel of a verb stem in a given form. We use Newman's
    citation glyphs; the gr5 *-ar*/*-ad* allomorphy and the lexical
    monoverb vowels are collapsed to one constructor each. -/
inductive FinalVowel
  | aa | a | ee | i | oo | u | ar | lex
  deriving DecidableEq, Repr, Inhabited

/-- A final-vowel template is a *function* from syntactic forms to
    final vowels. The empirical content of a grade's vowel pattern is
    its image and how it varies across `SynForm.all`. -/
abbrev FVTemplate := SynForm → FinalVowel

/-- A template is **three-way changing** iff its A, B, C images are
    pairwise distinct. The Parsons system has exactly one three-way
    changing template — gr2 (A: ā, B: ē, C: i). gr4 has a *two-way*
    split A/D = ē vs C = i; only gr2 is three-way. -/
def FVTemplate.threeWayChanging (t : FVTemplate) : Prop :=
  t .A ≠ t .B ∧ t .B ≠ t .C ∧ t .A ≠ t .C

instance (t : FVTemplate) : Decidable t.threeWayChanging :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- ============================================================================
-- § 3: Stem Templates (tone × vowel × function × VerbCore defaults)
-- ============================================================================

/-- Coarse derivational function of a grade (@cite{newman-2000}
    §74.3–74.10). A grade may have several uses; the *primary* function
    fixes the default argument structure. Secondary uses (e.g. gr1's
    actor-intransitive sub-use) appear as per-verb overrides. -/
inductive GradeFunction where
  | basic | applicative | intransitive | totality
  | efferential | ventive | sustentative
  deriving DecidableEq, Repr

/-- Default `VerbCore.complementType` predicted by the grade's primary
    function. -/
def GradeFunction.defaultCT : GradeFunction → ComplementType
  | .intransitive | .sustentative => .none
  | _                              => .np

/-- Default `VerbCore.voiceType` predicted by the grade's primary
    function. The sustentative (passive-like) gr7 selects nonThematic
    Voice; everything else introduces an external argument. -/
def GradeFunction.defaultVoice : GradeFunction → VoiceType
  | .sustentative => .nonThematic
  | _             => .agentive

/-- A **stem template** bundles the four invariants that pick out a
    grade: tone melody on a disyllabic stem, final-vowel template
    across A/B/C/D, derivational function, and a label.
    The argument-structure defaults are *derived* from `function`,
    not stored. -/
structure StemTemplate where
  /-- Display label (e.g. "gr2"). -/
  label    : String
  /-- Tone melody on the disyllabic stem; empty for monoverbs (gr0)
      whose tone is lexical. -/
  tones    : List TRN
  /-- Final-vowel template across A/B/C/D. -/
  fv       : FVTemplate
  /-- Primary derivational function. -/
  function : GradeFunction

/-- Predicted complement type from the template's function. -/
def StemTemplate.defaultCT (t : StemTemplate) : ComplementType :=
  t.function.defaultCT

/-- Predicted voice type from the template's function. -/
def StemTemplate.defaultVoice (t : StemTemplate) : VoiceType :=
  t.function.defaultVoice

-- ============================================================================
-- § 4: The Parsons Grades (the registry)
-- ============================================================================

/-- gr0: lexically-toned monoverbs (*ci, shā, sō, jā*). -/
def gr0 : StemTemplate where
  label := "gr0"; tones := []; function := .basic
  fv    := fun _ => .lex

/-- gr1: H–L stems with -ā throughout (basic + applicative + actor-intr.). -/
def gr1 : StemTemplate where
  label := "gr1"; tones := [.H, .L]; function := .basic
  fv    := fun _ => .aa

/-- gr2: L–H "changing" verbs — A: -ā, B: -ē, C: -i, D: -ā. The unique
    grade with a non-constant final-vowel template. -/
def gr2 : StemTemplate where
  label := "gr2"; tones := [.L, .H]; function := .basic
  fv    := fun
    | .A => .aa | .B => .ee | .C => .i | .D => .aa

/-- gr3: L–H intransitive (-a). -/
def gr3 : StemTemplate where
  label := "gr3"; tones := [.L, .H]; function := .intransitive
  fv    := fun _ => .a

/-- gr4: H–L totality (-ē; "short C" -i). -/
def gr4 : StemTemplate where
  label := "gr4"; tones := [.H, .L]; function := .totality
  fv    := fun
    | .C => .i
    | _  => .ee

/-- gr5: H–H efferential / causative (-ar or -ad). -/
def gr5 : StemTemplate where
  label := "gr5"; tones := [.H, .H]; function := .efferential
  fv    := fun _ => .ar

/-- gr6: H–H ventive (-ō). -/
def gr6 : StemTemplate where
  label := "gr6"; tones := [.H, .H]; function := .ventive
  fv    := fun _ => .oo

/-- gr7: L–H sustentative / "passive" (-u). -/
def gr7 : StemTemplate where
  label := "gr7"; tones := [.L, .H]; function := .sustentative
  fv    := fun _ => .u

/-- The Parsons registry: all eight grades in canonical order. The
    universal theorems below quantify over this list, not over a
    pattern-match-based enum. -/
def parsons : List StemTemplate :=
  [gr0, gr1, gr2, gr3, gr4, gr5, gr6, gr7]

-- ============================================================================
-- § 5: Hausa Verb Entries (extending VerbCore)
-- ============================================================================

/-- A Hausa verb extends `VerbCore` with its Parsons grade and its
    A-form citation tones (which may be lexical for gr0). All other
    morphological data is **derived** from the grade. -/
structure HausaVerb extends VerbCore where
  /-- The Parsons grade fixing tone, final vowel, and argument-structure
      defaults. -/
  grade    : StemTemplate
  /-- For gr0 monoverbs only: lexically-specified tone(s). Empty list
      otherwise (the grade fixes the tones). -/
  lexTones : List TRN := []

/-- The verb's tone melody: from the grade unless the grade is
    lexically-toned (gr0), in which case from `lexTones`. -/
def HausaVerb.tones (v : HausaVerb) : List TRN :=
  match v.grade.tones with
  | [] => v.lexTones
  | ts => ts

/-- The verb's final vowel in a given syntactic form. -/
def HausaVerb.fv (v : HausaVerb) (f : SynForm) : FinalVowel :=
  v.grade.fv f

/-- A verb is **canonical** iff its `VerbCore` argument-structure
    fields agree with the defaults predicted by its grade. Per-verb
    overrides break canonicity (and become explicit empirical claims). -/
def HausaVerb.canonical (v : HausaVerb) : Prop :=
  v.complementType = v.grade.defaultCT ∧
  v.voiceType = some v.grade.defaultVoice

instance (v : HausaVerb) : Decidable v.canonical :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Smart constructor: builds a canonical `HausaVerb` from form and
    grade by filling `VerbCore` from the grade's defaults. Concrete
    verb definitions use this; per-verb overrides spell out which
    field departs from the default. -/
def mkVerb (form : String) (g : StemTemplate)
    (lexTones : List TRN := []) : HausaVerb where
  form           := form
  complementType := g.defaultCT
  voiceType      := some g.defaultVoice
  grade          := g
  lexTones       := lexTones

-- Concrete entries (citation forms after @cite{newman-2000} §74)

def ci    : HausaVerb := mkVerb "ci"    gr0 (lexTones := [.H])
def shaa  : HausaVerb := mkVerb "shā"   gr0 (lexTones := [.H])
def soo   : HausaVerb := mkVerb "sō"    gr0 (lexTones := [.H])
def saya  : HausaVerb := mkVerb "sayā"  gr1
def sayi  : HausaVerb := mkVerb "sayi"  gr2
def fita  : HausaVerb := mkVerb "fita"  gr3
def kashe : HausaVerb := mkVerb "kashē" gr4
/-- gr5 efferential of *sayā* 'buy' — *sayař* 'sell'. Same root as
    `saya` (gr1 basic) — minimal pair illustrating the efferential
    derivation (@cite{newman-2000} §74.9). -/
def sayar : HausaVerb := mkVerb "sayař" gr5
/-- gr6 ventive *kōmō* 'return here' (@cite{newman-2000} §74.11).
    Note: *zō* 'come' is **irregular** (v*) and not gr6, despite
    semantic overlap with the ventive function. -/
def koomoo : HausaVerb := mkVerb "kōmō"  gr6
/-- gr7 sustentative *tāru* 'meet' / 'be assembled' (@cite{newman-2000}
    §74.13). gr7 derives a passive-like reading: the action is
    successfully sustained, with no external argument introduced. -/
def taaru : HausaVerb := mkVerb "tāru"  gr7

/-- Canonical Hausa verbs. Each entry is generated by `mkVerb`, so
    every entry is canonical by construction (see
    `mkVerb_is_canonical` below). -/
def lexicon : List HausaVerb :=
  [ci, shaa, soo, saya, sayi, fita, kashe, sayar, koomoo, taaru]

/-- **Override demonstration.** Some gr1 verbs have an *actor-intransitive*
    sub-use (@cite{newman-2000} §74.4): morphologically gr1 (H–L, -ā)
    but syntactically intransitive. We model this by overriding
    `complementType` while keeping the gr1 grade. The override breaks
    canonicity — making the empirical claim "gr1 has an intransitive
    sub-use" *visible* in the type system rather than buried in prose. -/
def gangara : HausaVerb :=
  { mkVerb "gangarā" gr1 with complementType := .none }

-- ============================================================================
-- § 6: Universal Theorems About the Grade System
-- ============================================================================

/-- **Changing-verb theorem (positive).** gr2 has pairwise-distinct
    A/B/C final vowels: this is the empirical diagnostic of the
    "changing" verb class. -/
theorem gr2_three_way_changing : gr2.fv.threeWayChanging := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Changing-verb theorem (uniqueness).** No other Parsons grade has
    pairwise-distinct A/B/C final vowels. Together with
    `gr2_three_way_changing`, this characterises gr2 by the property
    of being three-way changing. -/
theorem only_gr2_three_way_changing :
    ∀ g ∈ parsons, g.fv.threeWayChanging → g.label = "gr2" := by
  intro g hg
  simp only [parsons, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Tone-fibre cardinality.** The Parsons registry uses exactly three
    distinct disyllabic tone melodies (HL, LH, HH); gr0 contributes the
    empty melody. So the registry partitions into 4 tone-fibres. -/
theorem tone_fibre_count :
    (parsons.map (·.tones)).dedup.length = 4 := by decide

/-- **Minimal pair gr5 / gr6.** The two H–H grades differ in A-form
    final vowel and in derivational function — making them a tonally-
    matched minimal pair. -/
theorem hh_minimal_pair :
    gr5.tones = gr6.tones ∧
    gr5.fv .A ≠ gr6.fv .A ∧
    gr5.function ≠ gr6.function :=
  ⟨rfl, by decide, by decide⟩

/-- **gr3 is intransitive by template.** Any verb whose grade is gr3
    and which is canonical has empty complement type. This is the
    universal claim that grade choice constrains argument structure;
    the per-verb verification (`fita.complementType = .none`) is
    demoted to an `example` below. -/
theorem gr3_intransitive (v : HausaVerb)
    (hg : v.grade = gr3) (hc : v.canonical) :
    v.complementType = .none := by
  rw [hc.1, hg]; rfl

/-- **gr7 suppresses the external argument.** Any canonical gr7 verb
    has `nonThematic` Voice. -/
theorem gr7_nonThematic (v : HausaVerb)
    (hg : v.grade = gr7) (hc : v.canonical) :
    v.voiceType = some .nonThematic := by
  rw [hc.2, hg]; rfl

/-- **`mkVerb` always yields a canonical verb.** Hence every entry in
    `lexicon` is canonical by construction — no per-verb checking
    needed. -/
theorem mkVerb_is_canonical (form : String) (g : StemTemplate)
    (lexTones : List TRN := []) :
    (mkVerb form g lexTones).canonical :=
  ⟨rfl, rfl⟩

/-- **Grades 5 and 6 introduce an external argument.** The two H–H
    grades are both agentive at the `VerbCore` level. -/
theorem hh_grades_agentive :
    gr5.defaultVoice = .agentive ∧ gr6.defaultVoice = .agentive :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Per-Verb Verifications (demoted to `example`s)
-- ============================================================================

/-- Per-cell facts that follow from the grade-system theorems above. -/
example : fita.complementType = .none :=
  gr3_intransitive fita rfl (mkVerb_is_canonical _ _)

example : taaru.voiceType = some .nonThematic :=
  gr7_nonThematic taaru rfl (mkVerb_is_canonical _ _)

example : sayi.fv .A = .aa ∧ sayi.fv .B = .ee ∧ sayi.fv .C = .i :=
  ⟨rfl, rfl, rfl⟩

example : sayar.tones = [.H, .H] := rfl

/-- Every entry in the lexicon is canonical (corollary of
    `mkVerb_is_canonical` since `lexicon` is built from `mkVerb`). -/
example : ∀ v ∈ lexicon, v.canonical := by decide

/-- The override `gangara` is *not* canonical: its `complementType` no
    longer matches `gr1.defaultCT`. The empirical override registers
    as a structural deviation. -/
example : ¬ gangara.canonical := by decide

/-- But the override still classifies as gr1 morphologically — the
    grade and tone melody are unchanged. -/
example : gangara.grade = gr1 ∧ gangara.tones = [.H, .L] := ⟨rfl, rfl⟩

end Fragments.Hausa.VerbGrades
