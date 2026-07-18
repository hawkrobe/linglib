import Linglib.Morphology.Periphrasis

/-!
# Hemba Auxiliary Verb Fragment
[anderson-2006]

Hemba (Bantu, Democratic Republic of Congo) exhibits a **split/doubled**
AVC pattern. In the progressive/past construction, subject agreement is
**doubled** (marked on both auxiliary and lexical verb), while tense appears
only on the auxiliary and indicative mood appears only on the lexical verb.

## Example

*tw-a-li tu-tib-a muti*
1PL-TNS-AUX 1PL-cut-FV/IND tree
'we were cutting the tree'
([anderson-2006] ex. 105, p. 215; Aksenova 1997: 27)

## Distribution

| Category | AUX | LV |
|----------|-----|-----|
| Agreement (subject) | yes | yes |
| Tense | yes | no |
| Mood (indicative) | no | yes |

This is the canonical split/doubled pattern: agreement is doubled across
both elements while tense and mood are split between them.
-/

namespace Hemba.AuxiliaryVerbs

open Morphology (MorphCategory InflDistribution)

/-- Hemba progressive/past AVC form. -/
def form : String := "tw-a-li tu-tib-a muti"

/-- Interlinear gloss (Anderson's: `1pl-tns-aux 1pl-cut-fv/ind tree`). -/
def gloss : String := "1PL-TNS-AUX 1PL-cut-FV/IND tree"

/-- Inflectional distribution: agreement doubled, tense on AUX, mood on LV. -/
def inflDistribution : InflDistribution :=
  { onAux := [.agreement .subj, .tense]
  , onLex := [.agreement .subj, .mood] }

/-! ## Verification -/

theorem form_nonempty : form ≠ "" := by decide

/-- Agreement is doubled: subject agreement appears on both AUX and LV. -/
theorem agreement_doubled :
    inflDistribution.onAux.contains (.agreement .subj) = true ∧
    inflDistribution.onLex.contains (.agreement .subj) = true := by
  exact ⟨by decide, by decide⟩

/-- Tense is split to AUX only. -/
theorem tense_on_aux_only :
    inflDistribution.onAux.contains .tense = true ∧
    inflDistribution.onLex.contains .tense = false := by
  exact ⟨by decide, by decide⟩

/-- Mood is split to LV only. -/
theorem mood_on_lex_only :
    inflDistribution.onAux.contains .mood = false ∧
    inflDistribution.onLex.contains .mood = true := by
  exact ⟨by decide, by decide⟩

end Hemba.AuxiliaryVerbs
