import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.RuleBased.Defs

/-!
# Finnish Consonant Gradation @cite{karlsson-2017}
@cite{hayes-2009}

Consonant gradation is a morphophonological alternation affecting stops at
morpheme-internal syllable boundaries in Finnish (@cite{karlsson-2017}, Chs. 4–5).
The **strong grade** appears in open syllables; the **weak grade** appears
in closed syllables (i.e., before a coda consonant).

## Quantitative gradation

Geminate stops shorten:
- pp → p, tt → t, kk → k

## Qualitative gradation

Single stops weaken:
- p → v, t → d, k → ∅ (deletion)
- mp → mm, nk → ng, lt → ll, rt → rr (assimilatory weakening)

## Formalization

We model the quantitative and qualitative rules as SPE `PhonRule`s. The
conditioning environment — closed vs. open syllable — is approximated by
right context: a following consonant signals a closed syllable.

-/

namespace Fragments.Finnish.ConsonantGradation

open Theories.Phonology (Segment Feature Segment.ofSpecs)
open Theories.Phonology.RuleBased

-- ============================================================================
-- § 1: Natural Classes
-- ============================================================================

/-- Voiceless bilabial stop /p/: [−cont, −voice, +labial, −coronal, −dorsal]. -/
def p_stop : Segment := Segment.ofSpecs
  [(Feature.continuant, false), (Feature.voice, false),
   (Feature.labial, true), (Feature.coronal, false), (Feature.dorsal, false),
   (Feature.consonantal, true), (Feature.syllabic, false)]

/-- Voiceless alveolar stop /t/: [−cont, −voice, +coronal, +anterior]. -/
def t_stop : Segment := Segment.ofSpecs
  [(Feature.continuant, false), (Feature.voice, false),
   (Feature.coronal, true), (Feature.anterior, true), (Feature.labial, false),
   (Feature.consonantal, true), (Feature.syllabic, false)]

/-- Voiceless velar stop /k/: [−cont, −voice, +dorsal, −labial, −coronal]. -/
def k_stop : Segment := Segment.ofSpecs
  [(Feature.continuant, false), (Feature.voice, false),
   (Feature.dorsal, true), (Feature.labial, false), (Feature.coronal, false),
   (Feature.consonantal, true), (Feature.syllabic, false)]

/-- Voiced labial continuant /v/: [+cont, +voice, +labial]. -/
def v_fricative : Segment := Segment.ofSpecs
  [(Feature.continuant, true), (Feature.voice, true),
   (Feature.labial, true), (Feature.consonantal, true),
   (Feature.syllabic, false)]

/-- Voiced alveolar stop /d/: [−cont, +voice, +coronal, +anterior]. -/
def d_stop : Segment := Segment.ofSpecs
  [(Feature.continuant, false), (Feature.voice, true),
   (Feature.coronal, true), (Feature.anterior, true),
   (Feature.consonantal, true), (Feature.syllabic, false)]

/-- A consonant: [+cons, −syll] (natural class for right context). -/
def consonant : Segment := Segment.ofSpecs
  [(Feature.consonantal, true), (Feature.syllabic, false)]

-- ============================================================================
-- § 2: Gradation Rules
-- ============================================================================

/-- **Quantitative** pp → p: geminate voiceless bilabial shortens before a
    consonant. Modeled as: the second /p/ of a geminate is deleted when
    followed by a consonant (closed syllable). -/
def ppGradation : PhonRule where
  name := "pp → p (quantitative)"
  target := p_stop
  effect := .delete
  leftContext := [.seg p_stop]
  rightContext := [.seg consonant]

/-- **Quantitative** tt → t: geminate voiceless alveolar shortens. -/
def ttGradation : PhonRule where
  name := "tt → t (quantitative)"
  target := t_stop
  effect := .delete
  leftContext := [.seg t_stop]
  rightContext := [.seg consonant]

/-- **Quantitative** kk → k: geminate voiceless velar shortens. -/
def kkGradation : PhonRule where
  name := "kk → k (quantitative)"
  target := k_stop
  effect := .delete
  leftContext := [.seg k_stop]
  rightContext := [.seg consonant]

/-- **Qualitative** p → v: single voiceless bilabial becomes a voiced
    labial continuant before a consonant. -/
def pGradation : PhonRule where
  name := "p → v (qualitative)"
  target := p_stop
  effect := .changeFeatures (Segment.ofSpecs
    [(Feature.continuant, true), (Feature.voice, true)])
  rightContext := [.seg consonant]

/-- **Qualitative** t → d: single voiceless alveolar becomes voiced
    before a consonant. -/
def tGradation : PhonRule where
  name := "t → d (qualitative)"
  target := t_stop
  effect := .changeFeatures (Segment.ofSpecs [(Feature.voice, true)])
  rightContext := [.seg consonant]

/-- **Qualitative** k → ∅: single voiceless velar deletes before a consonant. -/
def kGradation : PhonRule where
  name := "k → ∅ (qualitative)"
  target := k_stop
  effect := .delete
  rightContext := [.seg consonant]

-- ============================================================================
-- § 3: Gradation Type Classification
-- ============================================================================

/-- Classification of a gradation rule: quantitative (geminate shortening)
    or qualitative (quality change or deletion). -/
inductive GradationType where
  | quantitative  -- geminate shortening (pp→p, tt→t, kk→k)
  | qualitative   -- quality change or deletion (p→v, t→d, k→∅)
  deriving DecidableEq, Repr

/-- A consonant gradation pair: strong and weak grades with classification. -/
structure GradationPair where
  strong : String
  weak : String
  gradationType : GradationType
  deriving Repr, BEq

/-- The six principal gradation patterns (Karlsson §4.1). -/
def principalPairs : List GradationPair :=
  [ ⟨"pp", "p", .quantitative⟩
  , ⟨"tt", "t", .quantitative⟩
  , ⟨"kk", "k", .quantitative⟩
  , ⟨"p",  "v", .qualitative⟩
  , ⟨"t",  "d", .qualitative⟩
  , ⟨"k",  "",  .qualitative⟩ ]

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- There are exactly 3 quantitative gradation pairs. -/
theorem quantitative_count :
    (principalPairs.filter (·.gradationType == .quantitative)).length = 3 := by
  native_decide

/-- There are exactly 3 qualitative gradation pairs. -/
theorem qualitative_count :
    (principalPairs.filter (·.gradationType == .qualitative)).length = 3 := by
  native_decide

/-- All quantitative pairs involve geminate shortening (strong form is
    longer than weak form by exactly 1 character). -/
theorem quantitative_shortening :
    (principalPairs.filter (·.gradationType == .quantitative)).all
      (fun p => p.strong.length == p.weak.length + 1) = true := by
  native_decide

/-- The k → ∅ qualitative alternation is the only deletion (empty weak grade). -/
theorem k_deletion_unique :
    (principalPairs.filter (fun p => p.weak == "")).length = 1 := by
  native_decide

/-- p → v rule changes voiceless to voiced + continuant. -/
theorem p_gradation_voices :
    pGradation.effect = .changeFeatures (Segment.ofSpecs
      [(Feature.continuant, true), (Feature.voice, true)]) := rfl

/-- t → d rule changes only voicing. -/
theorem t_gradation_voices :
    tGradation.effect = .changeFeatures (Segment.ofSpecs
      [(Feature.voice, true)]) := rfl

/-- k → ∅ rule deletes. -/
theorem k_gradation_deletes : kGradation.effect = .delete := rfl

end Fragments.Finnish.ConsonantGradation
