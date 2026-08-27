import Linglib.Fragments.Mwaghavul.Basic
import Linglib.Morphology.Morph
import Linglib.Phonology.Autosegmental.Floating
import Linglib.Phonology.Tone.Constraints
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Data.Examples.AkinboFwangwar2026

/-!
# Akinbo & Fwangwar 2026: grammatical tone targeting ideophones

Mwaghavul derives verbs from ideophones by two segmentally null verbalisers whose exponents
are the tonal melodies M and M-H; pluractional verbs reduplicate the ideophone and realise M
on every TBU of the reduplicant and H on every TBU of the base, a tonal disharmony that
iconically depicts distinguishable identity. Each tone of a verbaliser takes a root as host and
every TBU of that root as its valuation window, which morpheme-specific LEFT/RIGHT-ANCHOR
and INTEGRITY constraints ([finley-2009]) derive under `L-ANCH-Mᵥ, R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫
L-ANCH-Hᵥ ≫ MAX-Tone`. The derived verbs keep their ideophonic expressiveness despite full
morphosyntactic integration, against the inverse correlation of [dingemanse-akita-2017].

This file builds the paper's three tableaux (24)–(26) over `FloatingForm` candidates with the
substrate's `leftAnchorTone`/`rightAnchorTone`/`integrityTone`, checking every printed
violation profile, and shows the winners' surface melodies are the fragment's overwrites
(`winners_agree_with_overwrite`). The descriptive generalisations (13) are checked over the
fragment's dataset (`m_verbs_uniform`, `mh_verbs_nonfinal_final`, `pluractional_disharmony`,
`alternation_lexical`), and the morphosyntactic parallel (11)–(12) over the rows.

## References

* [akinbo-fwangwar-2026]
* [finley-2009]
* [rolle-2018]
* [dingemanse-akita-2017]
* [dingemanse-thompson-2020]
* [potts-2007]
-/

namespace AkinboFwangwar2026

open OptimalityTheory Constraints Autosegmental Mwaghavul
open Tone (TRN TBU GTSpec integrityTone leftAnchorTone rightAnchorTone)
open Morphology (Morph)

/-! ### Morphemes and autosegments -/

/-- The Mwaghavul autosegmental form: syllable TBUs, tones, morpheme sponsors. -/
abbrev Form := FloatingForm Syl TRN Morph

def rootMorph : Morph := .root "root"
def vbzMorph : Morph := .root "vbz"
def redMorph : Morph := .root "red"
def baseMorph : Morph := .root "base"

def seg (m : Morph) (s : String) : SegSpec Syl Morph := { seg := ⟨s⟩, morpheme := m }
def tone (m : Morph) (t : TRN) : TierSpec TRN Morph := { value := t, morpheme := m }

/-- MAX-Tone ((23)): one violation per deleted input tone. -/
def maxTone : Constraint Form := fun f => f.countUpper f.IsDeleted

/-- The surface melody: the tones linked to each TBU, left to right. -/
def surfaceMelody (f : Form) : List TRN := (List.range f.lower.len).flatMap f.tierValues

/-! ### (24): the M verbaliser and an unreduplicated ideophone -/

namespace Tableau24

/-- `(wùlàʃ)₁ + M₂ᵥ`: one lexical L multi-linked to both TBUs, the verbaliser's M floating. -/
def input : Form :=
  FloatingForm.mkInput [seg rootMorph "wù", seg rootMorph "làʃ"]
    [tone rootMorph .L, tone vbzMorph .M] {(0, 0), (0, 1)}

/-- (24a) `(wùlàʃ)₁ M₂`, (24b) `(wùlàʃ)₁`, (24c) `(wù)₁(làʃ)₂`, (24d) `(wū)₂(làʃ)₁`,
(24e) `(wūlāʃ)₂`, (24f) `(wū)₂(lāʃ)₂` with two M autosegments. -/
def candA : Form := input
def candB : Form := input.deleteTierElem 1
def candC : Form := input.deleteLink 0 1 |>.insertLink 1 1
def candD : Form := input.deleteLink 0 0 |>.insertLink 1 0
def candE : Form := input.deleteTierElem 0 |>.insertLink 1 0 |>.insertLink 1 1
def candF : Form :=
  { input with
    upper := .ofList [tone rootMorph .L, tone vbzMorph .M, tone vbzMorph .M]
    deletedTier := {0}
    surfaceLinks := {(1, 0), (2, 1)} }

def candidates : List Form := [candA, candB, candC, candD, candE, candF]

/-- `INTEG-Mᵥ ≫ L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ ≫ MAX-Tone`. -/
def ranking : List (Constraint Form) :=
  [integrityTone vbzMorph .M, leftAnchorTone vbzMorph .M [rootMorph],
    rightAnchorTone vbzMorph .M [rootMorph], maxTone]

/-- The printed profiles of (24); (24f)'s MAX-Tone mark, from the deleted lexical L, is not
printed. -/
theorem profiles :
    candidates.map (fun c => ranking.map (· c)) =
      [[0, 2, 2, 0], [0, 2, 2, 1], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 1]] := by
  decide

/-- Spreading the M over the root wins; copying it loses to INTEGRITY. -/
theorem optimal : (Tableau.ofRanking candidates ranking).optimal = {candE} := by decide

end Tableau24

/-! ### (25): the M-H verbaliser and an unreduplicated ideophone -/

namespace Tableau25

/-- `(háŋláɣáp)₁ + M₂H₃ᵥ`. -/
def input : Form :=
  FloatingForm.mkInput [seg rootMorph "háŋ", seg rootMorph "lá", seg rootMorph "ɣáp"]
    [tone rootMorph .H, tone vbzMorph .M, tone vbzMorph .H] {(0, 0), (0, 1), (0, 2)}

/-- (25a) `(háŋláɣáp)₁`, (25b) `(hāŋlā)₂(ɣáp)₁`, (25c) `(háŋláɣáp)₃`, (25d) `(hāŋlāɣāp)₂`,
(25e) `(hāŋlā)₂(ɣáp)₃`, (25f) `(hāŋ)₂(láɣáp)₃`, (25g) `(hāŋ)₂(lá)₁(ɣáp)₃`. -/
def candA : Form := input.deleteTierElem 1 |>.deleteTierElem 2
def candB : Form :=
  input.deleteLink 0 0 |>.deleteLink 0 1 |>.insertLink 1 0 |>.insertLink 1 1 |>.deleteTierElem 2
def candC : Form :=
  input.deleteTierElem 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 1 |>.insertLink 2 2
def candD : Form :=
  input.deleteTierElem 0 |>.deleteTierElem 2 |>.insertLink 1 0 |>.insertLink 1 1 |>.insertLink 1 2
def candE : Form := input.deleteTierElem 0 |>.insertLink 1 0 |>.insertLink 1 1 |>.insertLink 2 2
def candF : Form := input.deleteTierElem 0 |>.insertLink 1 0 |>.insertLink 2 1 |>.insertLink 2 2
def candG : Form := input.deleteLink 0 0 |>.deleteLink 0 2 |>.insertLink 1 0 |>.insertLink 2 2

def candidates : List Form := [candA, candB, candC, candD, candE, candF, candG]

/-- `L-ANCH-Mᵥ, R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ ≫ MAX-Tone`. -/
def ranking : List (Constraint Form) :=
  [leftAnchorTone vbzMorph .M [rootMorph], rightAnchorTone vbzMorph .H [rootMorph],
    rightAnchorTone vbzMorph .M [rootMorph], leftAnchorTone vbzMorph .H [rootMorph], maxTone]

/-- The printed profiles of (25). -/
theorem profiles :
    candidates.map (fun c => ranking.map (· c)) =
      [[3, 3, 3, 3, 2], [0, 3, 1, 3, 1], [3, 0, 3, 0, 2], [0, 3, 0, 3, 2], [0, 0, 1, 2, 1],
        [0, 0, 2, 1, 1], [0, 0, 2, 2, 0]] := by
  decide

/-- M on the nonfinal TBUs and H on the final one wins: the same surface tones as (25b),
distinguished by which H — the verbaliser's — the anchors count. -/
theorem optimal : (Tableau.ofRanking candidates ranking).optimal = {candE} := by decide

end Tableau25

/-! ### (26): the M-H verbaliser and a reduplicated ideophone -/

namespace Tableau26

/-- `(jàlpàt)₁ + (jàlpàt)₂ + M₃H₄ᵥ`: two root morphemes, each with its own multi-linked L. -/
def input : Form :=
  FloatingForm.mkInput
    [seg redMorph "jàl", seg redMorph "pàt", seg baseMorph "jàl", seg baseMorph "pàt"]
    [tone redMorph .L, tone baseMorph .L, tone vbzMorph .M, tone vbzMorph .H]
    {(0, 0), (0, 1), (1, 2), (1, 3)}

/-- (26a) `(jàlpàt)₁(jàlpàt)₂`, (26b) `(jàl)₁(pāt)₃(jàl)₂(pát)₄`, (26c) `(jāl)₃(pàt)₁(jál)₄(pàt)₂`,
(26d) `(jālpāt)₃(jálpát)₄`, (26e) `(jāl)₃(pát)₄(jàlpàt)₂`, (26f) `(jālpāt jāl)₃(pát)₄`,
(26g) `(jāl)₃(pàt)₁(jāl)₃(pát)₄`. -/
def candA : Form := input
def candB : Form := input.deleteLink 0 1 |>.insertLink 2 1 |>.deleteLink 1 3 |>.insertLink 3 3
def candC : Form := input.deleteLink 0 0 |>.insertLink 2 0 |>.deleteLink 1 2 |>.insertLink 3 2
def candD : Form :=
  input.deleteTierElem 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 1
    |>.insertLink 3 2 |>.insertLink 3 3
def candE : Form := input.deleteTierElem 0 |>.insertLink 2 0 |>.insertLink 3 1
def candF : Form :=
  input.deleteTierElem 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 1
    |>.insertLink 2 2 |>.insertLink 3 3
def candG : Form :=
  input.deleteLink 0 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 2 |>.insertLink 3 3

def candidates : List Form := [candA, candB, candC, candD, candE, candF, candG]

/-- The ranking of (25), each anchor now over both roots. -/
def ranking : List (Constraint Form) :=
  [leftAnchorTone vbzMorph .M [redMorph, baseMorph],
    rightAnchorTone vbzMorph .H [redMorph, baseMorph],
    rightAnchorTone vbzMorph .M [redMorph, baseMorph],
    leftAnchorTone vbzMorph .H [redMorph, baseMorph], maxTone]

/-- The printed profiles of (26): an anchor counts the host on which the tone comes closest to
its edge, and all eight TBUs when the tone is realised on neither root. -/
theorem profiles :
    candidates.map (fun c => ranking.map (· c)) =
      [[4, 4, 4, 4, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 2], [0, 0, 1, 1, 1],
        [0, 0, 0, 1, 2], [0, 0, 1, 1, 1]] := by
  decide

/-- M on every TBU of the reduplicant and H on every TBU of the base wins. -/
theorem optimal : (Tableau.ofRanking candidates ranking).optimal = {candD} := by decide

end Tableau26

/-- The three winners surface with exactly the fragment's overwrites: `deriveVerb` for the
singular verbs and `derivePluractional` for the pluractional. -/
theorem winners_agree_with_overwrite :
    surfaceMelody Tableau24.candE = (deriveVerb wulash).getD [] ∧
      surfaceMelody Tableau25.candE = (deriveVerb hanlaghap).getD [] ∧
      surfaceMelody Tableau26.candD = derivePluractional jalpat := by
  decide

/-! ### The verbalisers as grammatical tone
[rolle-2018] -/

/-- VBZ₁ and VBZ₂ are replacive-dominant, word-level, and tone is their sole exponent. -/
def verbM_GT : GTSpec :=
  { verbM with dominance := .replaciveDominant, level := .word, exponence := .independent }
def verbMH_GT : GTSpec :=
  { verbMH with dominance := .replaciveDominant, level := .word, exponence := .independent }

theorem verbalizers_dominant : verbM_GT.dominance.IsDominant ∧ verbMH_GT.dominance.IsDominant :=
  ⟨by decide, by decide⟩

/-! ### The descriptive generalisations (13) -/

/-- (13b): the M verbaliser puts M on every TBU. -/
theorem m_verbs_uniform :
    ∀ i ∈ ideophones, i.singular = some .m → deriveVerb i = some (i.tones.map fun _ => .M) := by
  decide

/-- (13c): the M-H verbaliser puts M on every nonfinal TBU and H on the final one. -/
theorem mh_verbs_nonfinal_final :
    ∀ i ∈ ideophones, i.singular = some .mh →
      deriveVerb i = some (i.tones.dropLast.map (fun _ => .M) ++ [.H]) := by
  decide

/-- (13d): the alternation is lexical — two L-L bisyllables take different verbalisers. -/
theorem alternation_lexical :
    ∃ i ∈ ideophones, ∃ j ∈ ideophones, i.tones = j.tones ∧ i.singular ≠ j.singular :=
  ⟨wulash, by decide, bishol, by decide, by decide⟩

/-- (13e–f): every pluractional verb, whatever its singular's verbaliser, has M throughout the
reduplicant and H throughout the base — corresponding TBUs never agree in tone. -/
theorem pluractional_disharmony :
    ∀ i ∈ ideophones,
      (derivePluractional i).take i.tones.length = i.tones.map (fun _ => .M) ∧
        (derivePluractional i).drop i.tones.length = i.tones.map (fun _ => .H) ∧
        List.Forall₂ (· ≠ ·) ((derivePluractional i).take i.tones.length)
          ((derivePluractional i).drop i.tones.length) := by
  decide

/-- Reduplication alone ((9)) keeps the lexical tones; the pluractional verb replaces them. -/
theorem intensity_ne_pluractional : ∀ i ∈ ideophones, intensity i ≠ derivePluractional i := by
  decide

/-! ### Morphosyntactic integration ((11)–(12)) -/

open Examples in
/-- Every construction attested with the underived verb of (11) is attested with the derived
verb of (12): tense, focus, serial verbs, negation. -/
theorem derived_verbs_integrated :
    ∀ row ∈ Examples.all, row.feature? "verb" = some "underived" →
      ∃ row' ∈ Examples.all, row'.feature? "verb" = some "derived" ∧
        row'.feature? "construction" = row.feature? "construction" := by
  decide

end AkinboFwangwar2026
