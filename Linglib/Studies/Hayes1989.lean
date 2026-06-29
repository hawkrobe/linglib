import Linglib.Phonology.Prosody.Syllable
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Hayes (1989): Compensatory Lengthening in Moraic Phonology

[hayes-1989]

Bruce Hayes. "Compensatory Lengthening in Moraic Phonology."
*Linguistic Inquiry* 20(2): 253–306.

This study file formalizes the empirical core of Hayes 1989: the typology of
compensatory lengthening (CL) and its three central arguments for moraic theory
over segmental prosodic theories (X theory, CV theory).

## Core claims formalized

1. CL is governed by a **prosodic frame** provided by moraic structure (not by
   constraints on association line rearrangements).

2. **Onset-deletion asymmetry**: CL from coda deletion is common; CL from onset
   deletion is unattested. Moraic theory derives this from the universal
   non-moraicity of onsets — onset deletion strands no μ
   (`Syllable.deleteOnset_strandedCount`).

3. **Weight prerequisite**: CL occurs only in languages with a syllable-weight
   distinction. Only languages with bimoraic syllables (`Syllable.ofCV … wbp`)
   have a coda μ to strand.

4. **Moraic conservation**: CL conserves total mora count. Because a stranded μ
   *survives* deletion, this follows from `Syllable.strand_moraCount` /
   `Syllable.relicense_moraCount` rather than stipulation.

## Languages covered

- Latin (s-deletion: *kasnus → ka:nus*; onset s-deletion: *smereo → mereo*)
- Middle English (vowel loss: *talə → ta:l*)
- Lardil (no WBP: CL impossible)
- Estonian (trimoraic syllables, Q1/Q2/Q3 quantity system)
-/

namespace Hayes1989

open Phonology (Segment Feature Segment.ofSpecs)
open Prosody

/-! ### The CL typology ([hayes-1989]) -/

/-- The seven attested compensatory-lengthening types ([hayes-1989]). Each is a deletion
    trigger plus a re-association target; all share the moraic mechanism — *deletion
    strands a mora, which is then re-associated to an adjacent segment* (the substrate
    `Syllable.strand` ∘ `relicense`/`relicenseLeft`). -/
inductive CLType where
  /-- Vowel lengthens when a following coda consonant deletes (Latin *kasnus → kaːnus*). -/
  | classical
  /-- Total consonant assimilation, formally equivalent to CL (*asta → atta*). -/
  | totalAssimilation
  /-- Glide formation frees a mora that lengthens a neighbour (*tia → tyaː*). -/
  | glideFormation
  /-- Prenasalization absorbs a mora from the following stop (Bantu *amba → aːmba*). -/
  | prenasalization
  /-- Non-adjacent CL via double flop (Ancient Greek *odwos → oːdos*). -/
  | doubleFlop
  /-- A following vowel deletes; the preceding vowel lengthens (Middle English *talə → taːl*). -/
  | vowelLoss
  /-- A vowel shortens, lengthening the following consonant (Luganda *aika → akka*). -/
  | inverseCL
  deriving DecidableEq, Repr

/-- Whether a CL type re-associates the stranded μ within one syllable
    (`Syllable.relicense`) or moves it across a syllable boundary
    (`Syllable.relicenseLeft`). -/
inductive Locality where
  | tautosyllabic
  | heterosyllabic
  deriving DecidableEq, Repr

/-- The locality of each attested CL type ([hayes-1989]): vowel loss and the double flop
    strand a μ that a *next-syllable* vowel picks up; the rest re-link within the
    deletion's own syllable. -/
def CLType.locality : CLType → Locality
  | .vowelLoss | .doubleFlop => .heterosyllabic
  | .classical | .totalAssimilation | .glideFormation
  | .prenasalization | .inverseCL => .tautosyllabic

/-! ### Segment inventory (minimal, for derivations) -/

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

/-! ### Latin s-deletion — classical CL -/

section LatinSDeletion

/-- Latin underlying form *kasnus 'gray': σ₁ = ⟨kas⟩ — onset ⟨k⟩, a nucleus μ,
    and a coda ⟨s⟩ μ (Weight-by-Position), making σ₁ heavy. -/
def kasnus_σ₁ : Syllable := Syllable.ofMorae [k] [Mora.of a, Mora.of s]
def kasnus_σ₂ : Syllable := Syllable.ofMorae [n] [Mora.of u, Mora.of s]
def kasnus : List Syllable := [kasnus_σ₁, kasnus_σ₂]

/-- σ₁ of *kasnus is heavy (2 morae: nucleus + coda with WBP). -/
theorem kasnus_σ₁_heavy : kasnus_σ₁.weight = .heavy := rfl

/-- Deleting the coda ⟨s⟩ from σ₁ strands one mora. -/
theorem kasnus_s_deletion_strands :
    (kasnus_σ₁.strand 1).strandedCount = 1 := rfl

/-- After spreading, the vowel ⟨a⟩ becomes long: σ₁ = [ka:] with 2 morae. -/
def kaanus_σ₁ : Syllable := (kasnus_σ₁.strand 1).relicense

theorem kaanus_σ₁_heavy : kaanus_σ₁.weight = .heavy := rfl

/-- Moraic conservation: *kasnus σ₁ and ka:nus σ₁ have the same mora count —
    derived from the general stranding/spreading conservation lemmas. -/
theorem kasnus_conservation : kasnus_σ₁.moraCount = kaanus_σ₁.moraCount := by
  rw [kaanus_σ₁, Syllable.relicense_moraCount, Syllable.strand_moraCount]

/-- Latin *kosmis → ko:mis 'courteous': same pattern. -/
def kosmis_σ₁ : Syllable := Syllable.ofMorae [k] [Mora.of o, Mora.of s]

theorem kosmis_conservation :
    kosmis_σ₁.moraCount = ((kosmis_σ₁.strand 1).relicense).moraCount := by
  rw [Syllable.relicense_moraCount, Syllable.strand_moraCount]

end LatinSDeletion

/-! ### Latin word-initial s-deletion — no CL -/

section LatinOnsetDeletion

/-- Latin *smereo → mereo: ⟨s⟩ deletes word-initially (onset position).
    Onset ⟨s⟩ bears no mora, so no CL occurs. -/
def smereo_σ₁ : Syllable := Syllable.ofMorae [s] [Mora.of e]

/-- Onset deletion strands no mora — the onset-deletion asymmetry. -/
theorem smereo_onset_no_cl :
    (smereo_σ₁.deleteOnset 0).strandedCount = smereo_σ₁.strandedCount := rfl

/-- The mora count after onset deletion is still 1 (light syllable). -/
theorem smereo_remains_light :
    (smereo_σ₁.deleteOnset 0).weight = .light := rfl

end LatinOnsetDeletion

/-! ### Middle English vowel-loss CL -/

section MiddleEnglishVowelLoss

/-- Middle English ⟨talə⟩ 'tale' (original disyllabic form): σ₁ = ⟨ta⟩ (open,
    light), σ₂ = ⟨lə⟩ (open, light). When word-final schwa deletes, Parasitic
    Delinking strands a mora, filled by leftward spreading that lengthens ⟨a⟩. -/
def tale_σ₁ : Syllable := Syllable.ofMorae [t] [Mora.of a]
def tale_σ₂ : Syllable := Syllable.ofMorae [l] [Mora.of e]  -- schwa (using ⟨e⟩)
def tale_input : List Syllable := [tale_σ₁, tale_σ₂]

/-- Input ⟨talə⟩ has 2 total morae (one per syllable). -/
theorem tale_input_morae : (Yield.ofSyllables tale_input).moraCount = 2 := rfl

/-- Deleting σ₂'s schwa strands one mora. -/
theorem tale_schwa_strands : (tale_σ₂.strand 0).strandedCount = 1 := rfl

/-- Vowel loss is **heterosyllabic** CL (`CLType.vowelLoss`): Parasitic Delinking
    deletes the de-nucleated σ₂ (its nucleus mora is stranded by Schwa Drop), and that
    mora migrates left onto σ₁, lengthening ⟨a⟩ to ⟨a:⟩ so σ₁ becomes heavy. -/
theorem tale_migrate_lengthens_σ₁ :
    (tale_σ₁.relicenseLeft (tale_σ₂.strand 0)).1.weight = .heavy := by decide

/-- The migration conserves total weight — derived from `Syllable.relicenseLeft_conserves`, not
    a stipulated output: the de-nucleated σ₂ deletes (`none`) and its mora is gained by σ₁. -/
theorem tale_vowel_loss_conserves :
    (tale_σ₁.relicenseLeft (tale_σ₂.strand 0)).1.moraCount
      + ((tale_σ₁.relicenseLeft (tale_σ₂.strand 0)).2.map Syllable.moraCount).getD 0
      = tale_σ₁.moraCount + (tale_σ₂.strand 0).moraCount :=
  Syllable.relicenseLeft_conserves _ _ (by decide) (by decide)

/-- CL result: ⟨a⟩ becomes long and ⟨l⟩ resyllabifies as a non-moraic coda
    riding on the second mora. Output σ = [ta:l] with 2 morae. -/
def tale_output : Syllable := Syllable.ofMorae [t] [Mora.of a, ⟨[a, l]⟩]

/-- Conservation: input total morae = output morae. -/
theorem tale_conservation :
    (Yield.ofSyllables tale_input).moraCount = tale_output.moraCount := rfl

end MiddleEnglishVowelLoss

/-! ### Weight prerequisite — CL requires bimoraic syllables -/

section WeightPrerequisite

/-- Without WBP (e.g. Lardil), `Syllable.ofCV` leaves the coda non-moraic
    (riding on the nucleus μ). There is no coda μ to strand → no CL. -/
def lardil_cvc : Syllable := Syllable.ofCV [t] [a] [k] false

theorem lardil_cvc_is_light : lardil_cvc.weight = .light := rfl

theorem lardil_no_cl_from_coda : (lardil_cvc.strand 1).strandedCount = 0 := rfl

/-- With WBP (e.g. Latin), `Syllable.ofCV` gives the coda its own mora.
    Stranding it strands one mora → CL is possible. -/
def latin_cvc : Syllable := Syllable.ofCV [t] [a] [k] true

theorem latin_cvc_is_heavy : latin_cvc.weight = .heavy := rfl

theorem latin_cl_from_coda : (latin_cvc.strand 1).strandedCount = 1 := rfl

/-- The weight prerequisite: Latin (CL possible) vs Lardil (CL impossible) is
    exactly the WBP parameter. -/
theorem weight_determines_cl :
    (latin_cvc.strand 1).strandedCount ≠ (lardil_cvc.strand 1).strandedCount := by
  rw [latin_cl_from_coda, lardil_no_cl_from_coda]; omega

end WeightPrerequisite

/-! ### Estonian trimoraic syllables -/

section EstonianTrimoraic

/-- Estonian Q1/Q2/Q3 (short/long/overlong) syllables realize the three-way
    weight distinction as 1μ/2μ/3μ directly — a long vowel is two morae, an
    overlong rime three. -/
def estonian_q1 : Syllable := Syllable.ofMorae [k] [Mora.of a]                          -- Q1: 1μ
def estonian_q2 : Syllable := Syllable.ofMorae [k] [Mora.of a, Mora.of a]               -- Q2: 2μ
def estonian_q3 : Syllable := Syllable.ofMorae [k] [Mora.of a, Mora.of a, Mora.of l]    -- Q3: 3μ

theorem q1_is_light : estonian_q1.weight = .light := rfl
theorem q2_is_heavy : estonian_q2.weight = .heavy := rfl
theorem q3_is_superheavy : estonian_q3.weight = .superheavy := rfl

/-- Q3 → Q2 grade shift: removing the third mora. -/
theorem q3_to_q2_loses_one_mora :
    estonian_q3.moraCount = estonian_q2.moraCount + 1 := rfl

/-- Estonian gemination loss: Q3 ⟨pa:t.ti⟩ → Q2 ⟨pa:.ti⟩; σ₁ goes from 3μ to
    2μ as the geminate loses its mora. -/
def paat_ti_q3 : Syllable := Syllable.ofMorae [k] [Mora.of a, Mora.of a, Mora.of t]
def paa_ti_q2 : Syllable := Syllable.ofMorae [k] [Mora.of a, Mora.of a]

theorem gemination_loss_removes_mora :
    paat_ti_q3.moraCount = paa_ti_q2.moraCount + 1 := rfl

end EstonianTrimoraic

/-! ### Integration — the prosodic pipeline -/

section ProsodicPipeline

/-- The full pipeline for Latin *ka:nus* after CL: moraic syllables → weight
    profile → prosodic word. σ₁ = [ka:] (heavy), σ₂ = [nus] (heavy), so the
    weight profile is [H, H]. -/
def kaanus_form : List Syllable := [kaanus_σ₁, kasnus_σ₂]

/-- CL output has the weight profile [heavy, heavy]. -/
theorem kaanus_weight_profile :
    Yield.ofSyllables kaanus_form = [.heavy, .heavy] := rfl

/-- CL output satisfies the bimoraic minimal-word constraint (4μ ≥ 2μ). -/
theorem kaanus_satisfies_minword :
    (Yield.ofSyllables kaanus_form).satisfiesMinWord := by decide

/-- Middle English: CL preserves the bimoraic minimum across syllable
    restructuring. Input ⟨talə⟩ = [L, L] (2μ); output [ta:l] = [H] (2μ). Both
    satisfy the bimoraic minimum — a consequence of moraic conservation. -/
theorem tale_minword_preserved :
    (Yield.ofSyllables tale_input).satisfiesMinWord ∧
    (Yield.ofSyllables [tale_output]).satisfiesMinWord :=
  ⟨by decide, by decide⟩

end ProsodicPipeline

end Hayes1989
