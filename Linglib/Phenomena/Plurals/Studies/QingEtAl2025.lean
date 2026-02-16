/-
# Qing et al. (2025) Empirical Data

Data from: "When can non-veridical preferential attitude predicates take questions?"
Authors: Qing, Özyıldız, Roelofsen, Romero, Uegaki (February 2025)

## Architecture

This file imports verb entries from `Fragments/` and records empirical observations.
The lexical properties (valence, C-distributivity, NVP class) come from the fragments;
only the empirical acceptability judgments are specified here.

## Findings

The paper identifies three classes of NVPs based on:
1. **C-distributivity**: Does `x V Q` ⟺ `∃p ∈ Q. x V that p`?
2. **Valence**: Evaluatively positive vs. negative
3. **TSP**: Threshold Significance Presupposition

| Class | C-dist | Valence | TSP | Takes Q? |
|-------|--------|---------|-----|----------|
| 1 | ✗ | any | any | ✓ |
| 2 | ✓ | negative | ✗ | ✓ |
| 3 | ✓ | positive | ✓ | ✗ |

## References

- Qing, C., Özyıldız, D., Roelofsen, F., Romero, M., & Uegaki, W. (2025).
  When can non-veridical preferential attitude predicates take questions?
-/

import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Mandarin.Predicates
import Linglib.Fragments.Japanese.Predicates
import Linglib.Fragments.Turkish.Predicates

namespace Phenomena.QingEtAl2025

-- Language Type

/-- Languages represented in the data -/
inductive Language where
  | english
  | mandarin
  | japanese
  | turkish
  deriving DecidableEq, Repr, BEq

-- Empirical Observation Records

/--
An empirical observation: predicate name, language, and acceptability.

The semantic properties are stored in the corresponding Fragment entry.
Here we just record the empirical acceptability judgments.
-/
structure Observation where
  /-- Predicate form -/
  form : String
  /-- Language -/
  language : Language
  /-- English gloss (for non-English) -/
  gloss : String := ""
  /-- Empirical: Does it take polar questions? -/
  takesPolQ : Bool
  /-- Empirical: Does it take wh-questions? -/
  takesWhQ : Bool
  /-- Additional notes -/
  notes : String := ""
  deriving Repr, BEq

-- English Observations

def hopeEn : Observation := ⟨"hope", .english, "", false, false,
  "Class 3: C-dist + positive + TSP → anti-rogative"⟩

def wishEn : Observation := ⟨"wish", .english, "", false, false, ""⟩

def expectEn : Observation := ⟨"expect", .english, "", false, false, ""⟩

def fearEn : Observation := ⟨"fear", .english, "", true, true,
  "Class 2: C-dist + negative → no TSP → takes questions"⟩

def dreadEn : Observation := ⟨"dread", .english, "", true, true, ""⟩

def worryEn : Observation := ⟨"worry", .english, "", true, true,
  "Class 1: non-C-dist → takes questions"⟩

def englishObs : List Observation := [hopeEn, wishEn, expectEn, fearEn, dreadEn, worryEn]

-- Mandarin Observations

def qidaiZh : Observation := ⟨"qidai", .mandarin, "look forward to", true, true,
  "Class 1: positive but non-C-dist, so takes questions"⟩

def danxinZh : Observation := ⟨"danxin", .mandarin, "worry", true, true, ""⟩

def xiwangZh : Observation := ⟨"xiwang", .mandarin, "hope", false, false,
  "Class 3: anti-rogative like English hope"⟩

def haipaZh : Observation := ⟨"haipa", .mandarin, "fear", true, true, ""⟩

def mandarinObs : List Observation := [qidaiZh, danxinZh, xiwangZh, haipaZh]

-- Japanese Observations

def tanosimiJa : Observation := ⟨"tanosimi", .japanese, "looking forward to", true, true,
  "Class 1: positive but non-C-dist"⟩

def osoreJa : Observation := ⟨"osore", .japanese, "fear", true, true, ""⟩

def kitaiJa : Observation := ⟨"kitai", .japanese, "expect/hope", false, false,
  "Class 3: behaves like English hope"⟩

def shinpaiJa : Observation := ⟨"shinpai", .japanese, "worry", true, true, ""⟩

def japaneseObs : List Observation := [tanosimiJa, osoreJa, kitaiJa, shinpaiJa]

-- Turkish Observations

def korkTr : Observation := ⟨"kork-", .turkish, "fear", true, true,
  "Class 2: symmetric interpretation with questions"⟩

def umTr : Observation := ⟨"um-", .turkish, "hope", false, false,
  "Class 3: anti-rogative canonically; diye provides workaround"⟩

def endiselenTr : Observation := ⟨"endişelen-", .turkish, "worry", true, true, ""⟩

def turkishObs : List Observation := [korkTr, umTr, endiselenTr]

-- All Observations

def allObservations : List Observation :=
  englishObs ++ mandarinObs ++ japaneseObs ++ turkishObs

#eval allObservations.length  -- Expected: 17

-- Linking to Fragments (for verification)

/-!
## Verifying Predictions Against Observations

The verb entries in `Fragments/` contain the semantic properties.
We can verify that predictions match observations:

```lean
-- From Theory (BuilderProperties.lean), derived from Fragment entry:
Semantics.Attitudes.BuilderProperties.AttitudeBuilder.nvpClass hope.attitudeBuilder = some .class3_cDist_positive
-- This predicts: canTakeQuestion = false

-- From Phenomena/QingEtAl2025/Data.lean:
hopeEn.takesPolQ = false ∧ hopeEn.takesWhQ = false  ✓
```

### Cross-Linguistic Verification

| Language | Predicate | Class | Predicted | Observed | ✓/✗ |
|----------|-----------|-------|-----------|----------|-----|
| English | hope | 3 | ✗ questions | ✗ | ✓ |
| English | fear | 2 | ✓ questions | ✓ | ✓ |
| English | worry | 1 | ✓ questions | ✓ | ✓ |
| Mandarin | qidai | 1 | ✓ questions | ✓ | ✓ |
| Mandarin | xiwang | 3 | ✗ questions | ✗ | ✓ |
| Japanese | tanosimi | 1 | ✓ questions | ✓ | ✓ |
| Japanese | kitai | 3 | ✗ questions | ✗ | ✓ |
| Turkish | kork- | 2 | ✓ questions | ✓ | ✓ |
| Turkish | um- | 3 | ✗ questions | ✗ | ✓ |
-/

-- Key Examples from the Paper

/-!
## Example: The hope-wh puzzle (Section 1)

Why can't "hope" embed questions in English?

(1) *John hopes whether Mary will come.
(2) *John hopes who will come.

**Explanation (Qing et al.)**:
- hope is C-distributive: "hope Q" ≈ "∃p ∈ Q. hope p"
- hope is positive → has TSP: presupposes ∃p ∈ C. μ(x,p) > θ
- When Q ⊆ C: assertion ⊆ presupposition → trivial!

## Example: Mandarin qidai (Section 3.1)

Why can positive "qidai" embed questions?

(5) Zhangsan qidai shei hui lai.
    "Zhangsan looks forward to who will come."
    ✓ Grammatical (unlike English *"hope who")

**Explanation**:
- qidai is positive (like hope)
- BUT qidai is NON-C-distributive!
- "qidai Q" ≠ "∃p ∈ Q. qidai p"
- Non-C-distributivity breaks the triviality derivation.

## Example: Turkish kork- (Section 3.2)

Why does "kork-" have symmetric interpretation with questions?

(6) Ali kork-uyor kim gel-ecek diye.
    "Ali fears who will come."
    = Ali fears that X will come OR fears that Y will come...

**Explanation**:
- kork- is negative → no bouletic goal
- No preferred outcome → symmetric interpretation
- Contrast with "hopefully" which is asymmetric (positive valence)
-/

end Phenomena.QingEtAl2025
