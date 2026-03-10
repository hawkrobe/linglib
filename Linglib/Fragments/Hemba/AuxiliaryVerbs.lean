import Linglib.Core.Lexical.MorphRule

/-!
# Hemba Auxiliary Verb Fragment
@cite{anderson-2006}

Hemba (Bantu, Democratic Republic of Congo) exhibits a **split/doubled**
AVC pattern. In the progressive/past construction, subject agreement is
**doubled** (marked on both auxiliary and lexical verb), while tense appears
only on the auxiliary and indicative mood appears only on the lexical verb.

## Example

*tw-a-li tu-tib-a muti*
1PL-PST-AUX 1PL-cut-FV/IND tree
'we were cutting the tree'
(Aksenova 1997: 27)

## Distribution

| Category | AUX | LV |
|----------|-----|-----|
| Agreement (subject) | yes | yes |
| Tense | yes | no |
| Mood (indicative) | no | yes |

This is the canonical split/doubled pattern: agreement is doubled across
both elements while tense and mood are split between them.
-/

namespace Fragments.Hemba.AuxiliaryVerbs

open Core.Morphology (MorphCategory InflDistribution)

/-- Hemba progressive/past AVC form. -/
def form : String := "tw-a-li tu-tib-a muti"

/-- Interlinear gloss. -/
def gloss : String := "1PL-PST-AUX 1PL-cut-FV/IND tree"

/-- Inflectional distribution: agreement doubled, tense on AUX, mood on LV. -/
def inflDistribution : InflDistribution :=
  { onAux := [.agreement, .tense]
  , onLex := [.agreement, .mood] }

/-! ## Verification -/

theorem form_nonempty : form ≠ "" := by decide

/-- Agreement is doubled: it appears on both AUX and LV. -/
theorem agreement_doubled :
    inflDistribution.onAux.contains .agreement = true ∧
    inflDistribution.onLex.contains .agreement = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- Tense is split to AUX only. -/
theorem tense_on_aux_only :
    inflDistribution.onAux.contains .tense = true ∧
    inflDistribution.onLex.contains .tense = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- Mood is split to LV only. -/
theorem mood_on_lex_only :
    inflDistribution.onAux.contains .mood = false ∧
    inflDistribution.onLex.contains .mood = true := by
  exact ⟨by native_decide, by native_decide⟩

end Fragments.Hemba.AuxiliaryVerbs
