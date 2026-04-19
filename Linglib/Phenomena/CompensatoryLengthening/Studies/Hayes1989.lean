import Linglib.Theories.Phonology.Prosodic.Moraic.CompensatoryLengthening
import Linglib.Theories.Phonology.Process.RuleBased.Defs

/-!
# Hayes (1989): Compensatory Lengthening in Moraic Phonology

@cite{hayes-1989}

Bruce Hayes. "Compensatory Lengthening in Moraic Phonology."
*Linguistic Inquiry* 20(2): 253–306.

This study file formalizes the empirical core of Hayes 1989: the typology of
compensatory lengthening (CL) and its three central arguments for moraic theory
over segmental prosodic theories (X theory, CV theory).

## Core Claims Formalized

1. CL is governed by a **prosodic frame** provided by moraic structure (not by
   constraints on association line rearrangements).

2. **Onset Deletion Asymmetry**: CL from coda deletion is common (38 rules,
   26 languages); CL from onset deletion is unattested. Moraic theory derives
   this from the universal non-moraicity of onsets.

3. **Weight Prerequisite**: CL occurs only in languages with a syllable weight
   distinction. Moraic theory derives this from language-specific moraic
   structure: only languages with bimoraic syllables have morae to strand.

4. **Moraic Conservation**: CL conserves total mora count. This follows
   automatically from the representations — no stipulation needed.

## Languages Covered

- Latin (s-deletion: *kasnus → ka:nus; onset s-deletion: *smereo → mereo)
- Middle English (vowel loss: ⟨talə⟩ → [ta:l])
- Lardil (no WBP: CL impossible — derived from `syllableToMoraic`)
- Estonian (trimoraic syllables, Q1/Q2/Q3 quantity system)
-/

namespace Hayes1989

open Phonology (Segment Feature Segment.ofSpecs)
open Phonology.Moraic
open Phonology.Moraic.CL

-- ============================================================================
-- § 1: Segment Inventory (minimal, for derivations)
-- ============================================================================

-- Vowels
private def a : Segment := .ofSpecs [(.syllabic, true), (.sonorant, true),
  (.approximant, true), (.consonantal, false), (.low, true)]
private def e : Segment := .ofSpecs [(.syllabic, true), (.sonorant, true),
  (.approximant, true), (.consonantal, false), (.front, true)]
private def o : Segment := .ofSpecs [(.syllabic, true), (.sonorant, true),
  (.approximant, true), (.consonantal, false), (.back, true)]
private def u : Segment := .ofSpecs [(.syllabic, true), (.sonorant, true),
  (.approximant, true), (.consonantal, false), (.high, true), (.back, true)]

-- Consonants
private def k : Segment := .ofSpecs [(.consonantal, true), (.dorsal, true)]
private def t : Segment := .ofSpecs [(.consonantal, true), (.coronal, true),
  (.anterior, true)]
private def s : Segment := .ofSpecs [(.consonantal, true), (.coronal, true),
  (.anterior, true), (.continuant, true), (.strident, true)]
private def n : Segment := .ofSpecs [(.consonantal, true), (.sonorant, true),
  (.nasal, true), (.coronal, true), (.anterior, true)]
private def l : Segment := .ofSpecs [(.consonantal, true), (.sonorant, true),
  (.approximant, true), (.lateral, true), (.coronal, true)]

-- ============================================================================
-- § 2: Latin ⟨s⟩-Deletion — Classical CL
-- ============================================================================

section LatinSDeletion

/-- Latin underlying form *kasnus 'gray':
    σ₁ = ⟨kas⟩ (C=onset, a=nucleus[1μ], s=coda[1μ with WBP])
    σ₂ = ⟨nus⟩

    With WBP, the coda ⟨s⟩ bears one mora, making σ₁ heavy. -/
def kasnus_σ₁ : MoraicSyllable := ⟨[k], [⟨a, .one⟩, ⟨s, .one⟩]⟩
def kasnus_σ₂ : MoraicSyllable := ⟨[n], [⟨u, .one⟩, ⟨s, .one⟩]⟩
def kasnus : MoraicForm := ⟨[kasnus_σ₁, kasnus_σ₂]⟩

/-- σ₁ of *kasnus is heavy (2 morae: nucleus + coda with WBP). -/
theorem kasnus_σ₁_heavy : kasnus_σ₁.toSyllWeight = .heavy := rfl

/-- After ⟨s⟩-deletion from σ₁, one mora is stranded. -/
theorem kasnus_s_deletion_strands :
    (deleteMoraic kasnus_σ₁ 1).2 = 1 := rfl

/-- After spreading, the vowel ⟨a⟩ becomes long (2 morae).
    Result: σ₁ = [kaː] with 2 morae — still heavy. -/
def kaanus_σ₁ : MoraicSyllable :=
  let (σ_del, stranded) := deleteMoraic kasnus_σ₁ 1
  spreadToFill σ_del stranded .left

theorem kaanus_σ₁_heavy : kaanus_σ₁.toSyllWeight = .heavy := rfl

/-- Moraic conservation: *kasnus σ₁ and ka:nus σ₁ have the same mora count. -/
theorem kasnus_conservation : kasnus_σ₁.moraCount = kaanus_σ₁.moraCount := rfl

/-- Latin *kosmis → ko:mis 'courteous': same pattern. -/
def kosmis_σ₁ : MoraicSyllable := ⟨[k], [⟨o, .one⟩, ⟨s, .one⟩]⟩

theorem kosmis_conservation :
    kosmis_σ₁.moraCount =
    (spreadToFill (deleteMoraic kosmis_σ₁ 1).1 (deleteMoraic kosmis_σ₁ 1).2 .left).moraCount :=
  rfl

end LatinSDeletion

-- ============================================================================
-- § 3: Latin Word-Initial ⟨s⟩-Deletion — No CL
-- ============================================================================

section LatinOnsetDeletion

/-- Latin *smereo → mereo: ⟨s⟩ deletes word-initially (onset position).
    Since onset ⟨s⟩ has no mora, no CL occurs. -/
def smereo_σ₁ : MoraicSyllable := ⟨[s], [⟨e, .one⟩]⟩

/-- Onset deletion does not change the mora count. -/
theorem smereo_onset_no_cl :
    (deleteOnset smereo_σ₁ 0).moraCount = smereo_σ₁.moraCount := rfl

/-- The mora count after onset deletion is still 1 (light syllable). -/
theorem smereo_remains_light :
    (deleteOnset smereo_σ₁ 0).toSyllWeight = .light := rfl

end LatinOnsetDeletion

-- ============================================================================
-- § 4: Middle English Vowel Loss CL
-- ============================================================================

section MiddleEnglishVowelLoss

/-- Middle English ⟨talə⟩ 'tale' (original disyllabic form):
    σ₁ = ⟨ta⟩ (open, light), σ₂ = ⟨lə⟩ (open, light).

    When word-final schwa deletes, Parasitic Delinking removes σ₂'s structure,
    stranding a mora. Spreading from the left fills it, lengthening ⟨a⟩. -/
def tale_σ₁ : MoraicSyllable := ⟨[t], [⟨a, .one⟩]⟩
def tale_σ₂ : MoraicSyllable := ⟨[l], [⟨e, .one⟩]⟩  -- schwa (using ⟨e⟩)
def tale_input : MoraicForm := ⟨[tale_σ₁, tale_σ₂]⟩

/-- Input ⟨talə⟩ has 2 total morae (one per syllable). -/
theorem tale_input_morae : tale_input.totalMorae = 2 := rfl

/-- After schwa deletion from σ₂, one mora is stranded. -/
theorem tale_schwa_strands :
    (deleteMoraic tale_σ₂ 0).2 = 1 := rfl

/-- CL result: ⟨a⟩ becomes long, ⟨l⟩ resyllabifies as coda.
    Output σ = [taːl] with 2 morae. -/
def tale_output : MoraicSyllable := ⟨[t], [⟨a, .two⟩, ⟨l, .zero⟩]⟩

/-- Conservation: input total morae = output morae. -/
theorem tale_conservation :
    tale_input.totalMorae = tale_output.moraCount := rfl

end MiddleEnglishVowelLoss

-- ============================================================================
-- § 5: Weight Prerequisite — CL Requires Bimoraic Syllables
-- ============================================================================

section WeightPrerequisite

/-- In a language without WBP (e.g., Lardil), `syllableToMoraic` produces
    non-moraic codas. Deleting the coda strands zero morae → no CL. -/
def lardil_cvc : MoraicSyllable :=
  syllableToMoraic { wbp := false } ⟨[t], [a], [k]⟩

theorem lardil_cvc_is_light : lardil_cvc.toSyllWeight = .light := rfl

theorem lardil_no_cl_from_coda :
    (deleteMoraic lardil_cvc 1).2 = 0 := rfl

/-- In a language with WBP (e.g., Latin), `syllableToMoraic` produces
    moraic codas. Deleting the coda strands one mora → CL is possible. -/
def latin_cvc : MoraicSyllable :=
  syllableToMoraic { wbp := true } ⟨[t], [a], [k]⟩

theorem latin_cvc_is_heavy : latin_cvc.toSyllWeight = .heavy := rfl

theorem latin_cl_from_coda :
    (deleteMoraic latin_cvc 1).2 = 1 := rfl

/-- The weight prerequisite: the difference between Latin (CL possible)
    and Lardil (CL impossible) is exactly the WBP parameter. -/
theorem weight_determines_cl :
    (deleteMoraic latin_cvc 1).2 ≠ (deleteMoraic lardil_cvc 1).2 := by
  rw [latin_cl_from_coda, lardil_no_cl_from_coda]; omega

end WeightPrerequisite

-- ============================================================================
-- § 6: Estonian Trimoraic Syllables
-- ============================================================================

section EstonianTrimoraic

/-- Estonian Q1/Q2/Q3 (short/long/overlong) syllables demonstrate the
    three-way weight distinction that moraic theory encodes directly
    as 1μ/2μ/3μ. -/
def estonian_q1 : MoraicSyllable := ⟨[k], [⟨a, .one⟩]⟩           -- Q1: light
def estonian_q2 : MoraicSyllable := ⟨[k], [⟨a, .two⟩]⟩           -- Q2: heavy
def estonian_q3 : MoraicSyllable := ⟨[k], [⟨a, .two⟩, ⟨l, .one⟩]⟩ -- Q3: superheavy

theorem q1_is_light : estonian_q1.toSyllWeight = .light := rfl
theorem q2_is_heavy : estonian_q2.toSyllWeight = .heavy := rfl
theorem q3_is_superheavy : estonian_q3.toSyllWeight = .superheavy := rfl

/-- Q3 → Q2 grade shift: removing the third mora.
    The moraic account: Q3 has 3 morae, Q2 has 2. The shift is simply
    "remove the third mora," which automatically eliminates gemination
    when the third mora belonged to a geminate consonant. -/
theorem q3_to_q2_loses_one_mora :
    estonian_q3.moraCount = estonian_q2.moraCount + 1 := rfl

/-- Estonian gemination loss: Q3 ⟨paːt.ti⟩ → Q2 ⟨paː.ti⟩.
    σ₁ goes from 3μ to 2μ; the geminate loses its second mora. -/
def paat_ti_q3 : MoraicSyllable := ⟨[k], [⟨a, .two⟩, ⟨t, .one⟩]⟩  -- 3μ
def paa_ti_q2 : MoraicSyllable := ⟨[k], [⟨a, .two⟩]⟩               -- 2μ

theorem gemination_loss_removes_mora :
    paat_ti_q3.moraCount = paa_ti_q2.moraCount + 1 := rfl

end EstonianTrimoraic

-- ============================================================================
-- § 7: Integration — Prosodic Pipeline
-- ============================================================================

section ProsodicPipeline

/-- The full phonological pipeline for Latin *ka:nus* after CL:
    moraic syllabification → weight profile → prosodic word.

    This demonstrates the chain that moraic theory creates:
    segments + WBP → `MoraicSyllable` → `SyllWeight` → `PrWd`

    CL output: σ₁ = [ka:] (bimoraic = heavy), σ₂ = [nus] (bimoraic = heavy).
    Weight profile: [H, H]. -/
def kaanus_form : MoraicForm := ⟨[kaanus_σ₁, kasnus_σ₂]⟩

/-- CL output has the weight profile [heavy, heavy]. -/
theorem kaanus_weight_profile :
    kaanus_form.toPrWd = ⟨[.heavy, .heavy]⟩ := rfl

/-- CL output satisfies the bimoraic minimal word constraint (4μ ≥ 2μ). -/
theorem kaanus_satisfies_minword :
    kaanus_form.toPrWd.satisfiesMinWord = true := rfl

/-- Middle English: CL preserves the bimoraic minimum across syllable
    restructuring. Input ⟨talə⟩ = [L, L] (2μ); output [ta:l] = [H] (2μ).
    Both satisfy the bimoraic minimum.

    This follows from Moraic Conservation (Rule (64), @cite{hayes-1989}):
    CL does not change total mora count, so it cannot cause a minimal word
    violation that wasn't already present. -/
theorem tale_minword_preserved :
    tale_input.toPrWd.satisfiesMinWord = true ∧
    (MoraicForm.mk [tale_output]).toPrWd.satisfiesMinWord = true :=
  ⟨rfl, rfl⟩

end ProsodicPipeline

end Hayes1989
