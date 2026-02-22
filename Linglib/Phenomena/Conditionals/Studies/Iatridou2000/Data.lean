/-!
# Iatridou (2000) — Morphological Data @cite{iatridou-2000}

Theory-neutral cross-linguistic data on counterfactual morphology from
Iatridou (2000) "The Grammatical Ingredients of Counterfactuality",
*Linguistic Inquiry* 31(2): 231–270.

## Key Empirical Generalizations

1. **Past morphology is uniform**: FLV, PresCF, and PastCF all use past
   morphology, but differ in the *number* of past layers.
2. **Imperfective is not universal**: languages that lack imperfective
   (e.g., English) omit it in CFs; languages with imperfective (e.g., Greek)
   use it in all CF types.
3. **Subjunctive mirrors past subjunctive availability**: a CF can contain
   subjunctive only if the language has a distinct past subjunctive form
   (generalization 42).

## Data Sources

- Tables 1–2 of Iatridou (2000)
- Example sentences from §2
-/

namespace Phenomena.Conditionals.Studies.Iatridou2000

-- ════════════════════════════════════════════════════════════════
-- § Datum Structures
-- ════════════════════════════════════════════════════════════════

/-- A morphological datum for counterfactual conditionals.

Each datum records the verb morphology in the antecedent and consequent
of a specific counterfactual type in a specific language. -/
structure CFMorphologyDatum where
  /-- Language name -/
  language : String
  /-- Counterfactual type: "FLV", "PresCF", or "PastCF" -/
  cfType : String
  /-- Verb morphology in the antecedent -/
  antecedentForm : String
  /-- Verb morphology in the consequent -/
  consequentForm : String
  /-- Whether past morphology is present -/
  hasPastMorph : Bool
  /-- Whether imperfective morphology is present -/
  hasImpfMorph : Bool
  /-- Whether subjunctive morphology is present -/
  hasSubjMorph : Bool
  /-- Number of past morpheme layers -/
  pastLayers : Nat
  /-- Gloss of the example -/
  gloss : String
  deriving Repr

/-- A datum for whether a language requires subjunctive in counterfactuals.

Iatridou's generalization: a language requires subjunctive in CFs iff it
has a morphologically distinct past subjunctive. -/
structure SubjRequirementDatum where
  /-- Language name -/
  language : String
  /-- Whether the language has a distinct past subjunctive form -/
  hasPastSubjunctive : Bool
  /-- Whether counterfactuals require subjunctive morphology -/
  cfRequiresSubjunctive : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § English Data
-- ════════════════════════════════════════════════════════════════

/-- English FLV: "If he were to take the exam tomorrow, ..." -/
def english_flv : CFMorphologyDatum where
  language := "English"
  cfType := "FLV"
  antecedentForm := "were to V"
  consequentForm := "would V"
  hasPastMorph := true
  hasImpfMorph := false
  hasSubjMorph := false
  pastLayers := 1
  gloss := "If he were to take the exam tomorrow, he would pass."

/-- English PresCF: "If he knew the answer, ..." -/
def english_presCF : CFMorphologyDatum where
  language := "English"
  cfType := "PresCF"
  antecedentForm := "V-ed"
  consequentForm := "would V"
  hasPastMorph := true
  hasImpfMorph := false
  hasSubjMorph := false
  pastLayers := 1
  gloss := "If he knew the answer, he would tell us."

/-- English PastCF: "If he had taken the exam, ..." -/
def english_pastCF : CFMorphologyDatum where
  language := "English"
  cfType := "PastCF"
  antecedentForm := "had V-ed"
  consequentForm := "would have V-ed"
  hasPastMorph := true
  hasImpfMorph := false
  hasSubjMorph := false
  pastLayers := 2
  gloss := "If he had taken the exam yesterday, he would have passed."

-- ════════════════════════════════════════════════════════════════
-- § Greek Data
-- ════════════════════════════════════════════════════════════════

/-- Greek FLV: "An + past + impf, tha + past + impf"

Based on Iatridou (2000, p.234), example (6). Greek FLV and PresCF have
identical morphological form; the FLV/PresCF distinction is made by
predicate type and temporal adverbials, not by morphology. -/
def greek_flv : CFMorphologyDatum where
  language := "Greek"
  cfType := "FLV"
  antecedentForm := "an + past + impf"
  consequentForm := "tha + past + impf"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "An eperne to siropi tu avrio, tha yinotan kala."

/-- Greek PresCF: "An + past + impf, tha + past + impf"

Based on Iatridou (2000, p.234), example (6). Morphologically identical
to FLV in Greek; the counterfactual reading arises from the stative
predicate. -/
def greek_presCF : CFMorphologyDatum where
  language := "Greek"
  cfType := "PresCF"
  antecedentForm := "an + past + impf"
  consequentForm := "tha + past + impf"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "An eperne to siropi tu, tha yinotan kala."

/-- Greek PastCF: "An + past + past + impf, tha + past + past + impf"

Based on Iatridou (2000, p.234), example (6c). The additional past
layer (the pluperfect ixe + participle) distinguishes PastCF from
PresCF/FLV. -/
def greek_pastCF : CFMorphologyDatum where
  language := "Greek"
  cfType := "PastCF"
  antecedentForm := "an + past + past + impf"
  consequentForm := "tha + past + past + impf"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 2
  gloss := "An ixe pari to siropi tu xthes, tha ixe yini kala."

-- ════════════════════════════════════════════════════════════════
-- § French Data
-- ════════════════════════════════════════════════════════════════

/-- French FLV: "imparfait, conditionnel" -/
def french_flv : CFMorphologyDatum where
  language := "French"
  cfType := "FLV"
  antecedentForm := "imparfait"
  consequentForm := "conditionnel"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "S'il passait l'examen demain, il réussirait."

/-- French PresCF: "imparfait, conditionnel" -/
def french_presCF : CFMorphologyDatum where
  language := "French"
  cfType := "PresCF"
  antecedentForm := "imparfait"
  consequentForm := "conditionnel"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "S'il savait la réponse, il nous le dirait."

/-- French PastCF: "plus-que-parfait, conditionnel passé" -/
def french_pastCF : CFMorphologyDatum where
  language := "French"
  cfType := "PastCF"
  antecedentForm := "plus-que-parfait"
  consequentForm := "conditionnel passé"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 2
  gloss := "S'il avait passé l'examen hier, il aurait réussi."

-- ════════════════════════════════════════════════════════════════
-- § Subjunctive Requirement Data
-- ════════════════════════════════════════════════════════════════

/-- English: no distinct past subjunctive, no subjunctive required. -/
def english_subj : SubjRequirementDatum where
  language := "English"
  hasPastSubjunctive := false
  cfRequiresSubjunctive := false

/-- Greek: no past subjunctive, no subjunctive required in CFs.

Greek CFs use past + imperfective morphology (indicative), not subjunctive.
Greek has a subjunctive-like particle (na), but this is not used in
counterfactual conditionals (Iatridou 2000, p.244–245). -/
def greek_subj : SubjRequirementDatum where
  language := "Greek"
  hasPastSubjunctive := false
  cfRequiresSubjunctive := false

/-- French: no productive past subjunctive, no subjunctive required in CFs.

French CFs use the indicative imparfait ("si j'avais..."), not the
subjonctif. French has a literary past subjunctive (subjonctif imparfait),
but it is not used productively in counterfactuals. -/
def french_subj : SubjRequirementDatum where
  language := "French"
  hasPastSubjunctive := false
  cfRequiresSubjunctive := false

/-- Italian: has distinct past subjunctive, subjunctive required in CFs.

Italian CFs require the congiuntivo (subjunctive), which has a robust
past form (congiuntivo trapassato). This is one of the positive cases
for Iatridou's generalization (42): "A CF can contain a subjunctive
morpheme only if that subjunctive morpheme has a past tense form."
(Iatridou 2000, p.247) -/
def italian_subj : SubjRequirementDatum where
  language := "Italian"
  hasPastSubjunctive := true
  cfRequiresSubjunctive := true

-- ════════════════════════════════════════════════════════════════
-- § Basic Data Theorems
-- ════════════════════════════════════════════════════════════════

/-- All CF types use past morphology. -/
theorem all_cfs_have_past :
    english_flv.hasPastMorph = true ∧
    english_presCF.hasPastMorph = true ∧
    english_pastCF.hasPastMorph = true ∧
    greek_flv.hasPastMorph = true ∧
    greek_presCF.hasPastMorph = true ∧
    greek_pastCF.hasPastMorph = true ∧
    french_flv.hasPastMorph = true ∧
    french_presCF.hasPastMorph = true ∧
    french_pastCF.hasPastMorph = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- PastCF has more past layers than PresCF/FLV. -/
theorem pastCF_has_more_layers :
    english_pastCF.pastLayers > english_presCF.pastLayers ∧
    greek_pastCF.pastLayers > greek_presCF.pastLayers ∧
    french_pastCF.pastLayers > french_presCF.pastLayers := by
  decide

end Phenomena.Conditionals.Studies.Iatridou2000
