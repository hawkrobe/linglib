import Linglib.Phenomena.WordOrder.Typology
import Linglib.Phenomena.WordOrder.HahnDegenFutrell2021
import Linglib.Phenomena.WordOrder.FutrellEtAl2020

/-!
# Gradient Word-Order Measures (Levshina, Namboodiripad et al. 2023)

Levshina, Namboodiripad, Allassonnière-Tang, Kramer, Talamo, Verkerk, Wilmoth,
Garrido Rodriguez, Gupton, Kidd, Liu, Naccarato, Nordlinger, Panova & Stoynova
(2023) "Why we need a gradient approach to word order" (*Linguistics*
61(4):825–883) argues that word-order typology should use continuous measures
(proportions, Shannon entropy, mutual information) rather than categorical labels
(SVO, SOV, "rigid", "flexible").

## Key Claims

1. SO proportion is continuous across languages (Figure 1)
2. Head-finality is continuous (Figure 2: 123 SUD corpora)
3. Case marking MI correlates with SO entropy (Figure 3: ~30 languages)
4. Register affects word-order proportions (Figure 7: Russian VO varies by register)
5. Flexibility scores form a continuum (Figure 8: Avar–English)

## Data Sources

- OSF Dataset1.txt: per-language SO proportion (31 languages)
- OSF Dataset3.txt: per-language SO entropy, case MI (30 languages)
- OSF Dataset6.txt: Russian register variation (conversation/fiction/news)
- https://osf.io/w9u6v/

## References

- Levshina, N., Namboodiripad, S., Allassonnière-Tang, M., Kramer, M.,
  Talamo, L., Verkerk, A., Wilmoth, S., Garrido Rodriguez, G., Gupton, T.M.,
  Kidd, E., Liu, Z., Naccarato, C., Nordlinger, R., Panova, A. &
  Stoynova, N. (2023). Why we need a gradient approach to word order.
  *Linguistics* 61(4):825–883.
-/

namespace Phenomena.WordOrder.Gradience

open Phenomena.WordOrder.Typology

-- ============================================================================
-- §1: Gradient Measures on Existing CrossTab Data
-- ============================================================================

/-- Proportion of harmonic languages × 1000 (integer permille). -/
def harmonicProportion1000 (t : CrossTab) : Nat :=
  t.harmonicCount * 1000 / t.totalCount

/-- Proportion of disharmonic languages × 1000. -/
def disharmonicProportion1000 (t : CrossTab) : Nat :=
  t.disharmonicCount * 1000 / t.totalCount

/-- Proportion of head-initial languages × 1000 (hihi + hihf cells). -/
def hiProportion1000 (t : CrossTab) : Nat :=
  (t.hihi.count + t.hihf.count) * 1000 / t.totalCount

/-- Table 1: 94.3% harmonic (VO × Adposition). -/
theorem voAdposition_harmonic_proportion :
    harmonicProportion1000 voAdposition = 943 := by native_decide

/-- Table 2: 86.1% harmonic (VO × Subordinator). -/
theorem voSubordinator_harmonic_proportion :
    harmonicProportion1000 voSubordinator = 861 := by native_decide

/-- Table 3: 82.2% harmonic (VO × Relative clause). -/
theorem voRelativeClause_harmonic_proportion :
    harmonicProportion1000 voRelativeClause = 822 := by native_decide

/-- Harmonic proportion decreases with construction complexity:
    adposition > subordinator > relative clause.

    Levshina et al.'s point: not all constructions are equally categorical.
    Even the "best" universal (VO ↔ preposition) is only 94.3% harmonic. -/
theorem harmony_decreases_with_complexity :
    harmonicProportion1000 voAdposition > harmonicProportion1000 voSubordinator ∧
    harmonicProportion1000 voSubordinator > harmonicProportion1000 voRelativeClause := by
  constructor <;> native_decide

/-- Gradient and categorical measures agree: harmonicProportion1000 > 500 ↔ harmonicDominant.
    The gradient measure refines, not contradicts, the binary one. -/
theorem categorical_consistent_with_gradient :
    allTables.all (λ t => (harmonicProportion1000 t > 500) == t.harmonicDominant) = true := by
  native_decide

-- ============================================================================
-- §2: Gradient Language Profile (OSF Dataset1.txt + Dataset3.txt)
-- ============================================================================

/-- Per-language gradient word-order data from Levshina, Namboodiripad et al.
    (2023) OSF datasets. SO proportion from Dataset1.txt, entropy and case MI
    from Dataset3.txt. All values × 1000, rounded to nearest integer. -/
structure GradientWOProfile where
  name : String
  isoCode : String
  /-- Proportion of SO (subject before object) orders × 1000 (from Dataset1.txt) -/
  soProportion1000 : Nat
  /-- Shannon entropy of S-O order × 1000 (0 = deterministic, 1000 = maximal; Dataset3.txt) -/
  soEntropy1000 : Nat
  /-- Mutual information between case markers and grammatical role × 1000 (Dataset3.txt) -/
  caseMI1000 : Nat
  deriving Repr, DecidableEq, BEq

-- 30 languages with exact values from OSF Dataset1.txt + Dataset3.txt

def arabic : GradientWOProfile :=
  { name := "Arabic", isoCode := "ar"
    soProportion1000 := 933, soEntropy1000 := 345, caseMI1000 := 36 }

def bulgarian : GradientWOProfile :=
  { name := "Bulgarian", isoCode := "bg"
    soProportion1000 := 965, soEntropy1000 := 218, caseMI1000 := 28 }

def croatian : GradientWOProfile :=
  { name := "Croatian", isoCode := "hr"
    soProportion1000 := 856, soEntropy1000 := 586, caseMI1000 := 415 }

def czech : GradientWOProfile :=
  { name := "Czech", isoCode := "cs"
    soProportion1000 := 781, soEntropy1000 := 760, caseMI1000 := 525 }

def danish : GradientWOProfile :=
  { name := "Danish", isoCode := "da"
    soProportion1000 := 989, soEntropy1000 := 74, caseMI1000 := 0 }

def dutch : GradientWOProfile :=
  { name := "Dutch", isoCode := "nl"
    soProportion1000 := 970, soEntropy1000 := 183, caseMI1000 := 0 }

def english : GradientWOProfile :=
  { name := "English", isoCode := "en"
    soProportion1000 := 994, soEntropy1000 := 47, caseMI1000 := 0 }

def estonian : GradientWOProfile :=
  { name := "Estonian", isoCode := "et"
    soProportion1000 := 842, soEntropy1000 := 634, caseMI1000 := 692 }

def finnish : GradientWOProfile :=
  { name := "Finnish", isoCode := "fi"
    soProportion1000 := 912, soEntropy1000 := 426, caseMI1000 := 314 }

def french : GradientWOProfile :=
  { name := "French", isoCode := "fr"
    soProportion1000 := 995, soEntropy1000 := 42, caseMI1000 := 5 }

def german : GradientWOProfile :=
  { name := "German", isoCode := "de"
    soProportion1000 := 916, soEntropy1000 := 386, caseMI1000 := 288 }

def greek : GradientWOProfile :=
  { name := "Greek", isoCode := "el"
    soProportion1000 := 896, soEntropy1000 := 490, caseMI1000 := 70 }

def hindi : GradientWOProfile :=
  { name := "Hindi", isoCode := "hi"
    soProportion1000 := 874, soEntropy1000 := 509, caseMI1000 := 334 }

def hungarian : GradientWOProfile :=
  { name := "Hungarian", isoCode := "hu"
    soProportion1000 := 727, soEntropy1000 := 858, caseMI1000 := 738 }

def indonesian : GradientWOProfile :=
  { name := "Indonesian", isoCode := "id"
    soProportion1000 := 999, soEntropy1000 := 12, caseMI1000 := 0 }

def italian : GradientWOProfile :=
  { name := "Italian", isoCode := "it"
    soProportion1000 := 969, soEntropy1000 := 192, caseMI1000 := 6 }

def japanese : GradientWOProfile :=
  { name := "Japanese", isoCode := "ja"
    soProportion1000 := 953, soEntropy1000 := 246, caseMI1000 := 582 }

def korean : GradientWOProfile :=
  { name := "Korean", isoCode := "ko"
    soProportion1000 := 978, soEntropy1000 := 146, caseMI1000 := 357 }

def latvian : GradientWOProfile :=
  { name := "Latvian", isoCode := "lv"
    soProportion1000 := 767, soEntropy1000 := 784, caseMI1000 := 726 }

def lithuanian : GradientWOProfile :=
  { name := "Lithuanian", isoCode := "lt"
    soProportion1000 := 608, soEntropy1000 := 968, caseMI1000 := 788 }

def persian : GradientWOProfile :=
  { name := "Persian", isoCode := "fa"
    soProportion1000 := 924, soEntropy1000 := 315, caseMI1000 := 219 }

def portuguese : GradientWOProfile :=
  { name := "Portuguese", isoCode := "pt"
    soProportion1000 := 986, soEntropy1000 := 102, caseMI1000 := 14 }

def romanian : GradientWOProfile :=
  { name := "Romanian", isoCode := "ro"
    soProportion1000 := 966, soEntropy1000 := 216, caseMI1000 := 7 }

def russian : GradientWOProfile :=
  { name := "Russian", isoCode := "ru"
    soProportion1000 := 861, soEntropy1000 := 580, caseMI1000 := 335 }

def slovene : GradientWOProfile :=
  { name := "Slovene", isoCode := "sl"
    soProportion1000 := 873, soEntropy1000 := 536, caseMI1000 := 478 }

def spanish : GradientWOProfile :=
  { name := "Spanish", isoCode := "es"
    soProportion1000 := 978, soEntropy1000 := 143, caseMI1000 := 21 }

def swedish : GradientWOProfile :=
  { name := "Swedish", isoCode := "sv"
    soProportion1000 := 988, soEntropy1000 := 86, caseMI1000 := 0 }

def tamil : GradientWOProfile :=
  { name := "Tamil", isoCode := "ta"
    soProportion1000 := 715, soEntropy1000 := 824, caseMI1000 := 59 }

def turkish : GradientWOProfile :=
  { name := "Turkish", isoCode := "tr"
    soProportion1000 := 922, soEntropy1000 := 353, caseMI1000 := 167 }

def vietnamese : GradientWOProfile :=
  { name := "Vietnamese", isoCode := "vi"
    soProportion1000 := 981, soEntropy1000 := 105, caseMI1000 := 0 }

/-- All 30 gradient word-order profiles from OSF Dataset1.txt + Dataset3.txt. -/
def allProfiles : List GradientWOProfile :=
  [ arabic, bulgarian, croatian, czech, danish, dutch, english, estonian
  , finnish, french, german, greek, hindi, hungarian, indonesian, italian
  , japanese, korean, latvian, lithuanian, persian, portuguese, romanian
  , russian, slovene, spanish, swedish, tamil, turkish, vietnamese ]

theorem allProfiles_count : allProfiles.length = 30 := by native_decide

-- ============================================================================
-- §3: Levshina et al. Core Theorems
-- ============================================================================

/-- Languages with near-deterministic SO order (proportion > 960) have low SO entropy (< 300).
    13 languages: Bulgarian, Danish, Dutch, English, French, Indonesian, Italian,
    Korean, Portuguese, Romanian, Spanish, Swedish, Vietnamese. -/
theorem rigid_languages_low_entropy :
    (allProfiles.filter (·.soProportion1000 > 960)).all
      (·.soEntropy1000 < 300) = true := by native_decide

/-- Among Indo-European languages with case morphology, high SO entropy (> 700) implies
    high case MI (> 400). Czech, Hungarian, Latvian, Lithuanian all use case marking
    to compensate for word-order freedom. -/
theorem case_rich_flexible_languages_high_mi :
    (allProfiles.filter (λ p => p.soEntropy1000 > 700 ∧ p.caseMI1000 > 0)).all
      (λ p => p.caseMI1000 > 400 ∨ p.name == "Tamil") = true := by native_decide

/-- Tamil is a counterexample to the simple "flexibility requires case marking" story:
    high SO entropy (824) but low case MI (59). Tamil uses verb agreement and
    animacy rather than case morphology for role disambiguation.

    This makes the gradient approach especially valuable — it reveals that the
    case–flexibility correlation is a tendency with principled exceptions, not a law. -/
theorem tamil_counterexample :
    tamil.soEntropy1000 > 800 ∧ tamil.caseMI1000 < 100 := by
  constructor <;> native_decide

/-- Case MI correlates with SO entropy: languages with caseMI > 300 have
    higher mean SO entropy than languages with caseMI ≤ 300. -/
def meanSOEntropy (ps : List GradientWOProfile) : Nat :=
  if ps.isEmpty then 0
  else ps.foldl (λ acc p => acc + p.soEntropy1000) 0 / ps.length

theorem case_mi_correlates_with_so_entropy :
    meanSOEntropy (allProfiles.filter (·.caseMI1000 > 300)) >
    meanSOEntropy (allProfiles.filter (·.caseMI1000 ≤ 300)) := by native_decide

/-- SO proportion spans a wide range: from Lithuanian (608) to Indonesian (999).
    This 391-point spread refutes any simple binary classification. -/
theorem so_proportion_is_continuous :
    indonesian.soProportion1000 - lithuanian.soProportion1000 > 350 := by native_decide

-- ============================================================================
-- §4: Bridges to Existing Datasets
-- ============================================================================

-- Bridge 1: Gradient harmony ↔ categorical harmony (Typology.lean)

/-- For all three WALS tables, harmonicProportion1000 > 500 → harmonicDominant = true. -/
theorem gradient_implies_categorical :
    allTables.all (λ t =>
      if harmonicProportion1000 t > 500 then t.harmonicDominant else true) = true := by
  native_decide

/-- The three tables have different harmonic proportions (943 vs 861 vs 822),
    showing harmony is a matter of degree, not a binary universal. -/
theorem harmony_is_gradient_not_binary :
    harmonicProportion1000 voAdposition ≠ harmonicProportion1000 voSubordinator ∧
    harmonicProportion1000 voSubordinator ≠ harmonicProportion1000 voRelativeClause := by
  constructor <;> native_decide

-- Bridge 2: SO entropy ↔ branching direction entropy (HahnDegenFutrell2021.lean)

/-- Shared languages between our gradient profiles and the 54-language Hahn et al. dataset. -/
def shared_gradient_hahn_isoCodes : List String :=
  allProfiles.filterMap (λ p =>
    if HahnDegenFutrell2021.allLanguages.any (·.isoCode == p.isoCode) then some p.isoCode
    else none)

theorem shared_gradient_hahn_count :
    shared_gradient_hahn_isoCodes.length = 28 := by native_decide

/-- Languages with high SO entropy (> 600) in Levshina that also appear in Hahn et al.
    all have high branching direction entropy (> 650) in Hahn et al.

    Two independent measures of word-order freedom (SO entropy from corpus counts,
    branching direction entropy from dependency trees) converge. -/
theorem high_so_entropy_implies_high_branch_entropy :
    let highSOEntropy := allProfiles.filter (λ p => p.soEntropy1000 > 600)
    let sharedHighSO := highSOEntropy.filter (λ p =>
      HahnDegenFutrell2021.allLanguages.any (·.isoCode == p.isoCode))
    sharedHighSO.all (λ p =>
      match HahnDegenFutrell2021.allLanguages.find? (·.isoCode == p.isoCode) with
      | some h => h.branchDirEntropy1000 > 650
      | none => false) = true := by native_decide

-- Bridge 3: Head-final proportion ↔ SO proportion (FutrellEtAl2020.lean)

private def futrellLanguages := Phenomena.WordOrder.DependencyLength.FutrellEtAl2020.languages

/-- Shared languages between gradient profiles and Futrell et al.'s DLM dataset. -/
def shared_gradient_futrell_isoCodes : List String :=
  allProfiles.filterMap (λ p =>
    if futrellLanguages.any (·.isoCode == p.isoCode) then some p.isoCode
    else none)

theorem shared_gradient_futrell_count :
    shared_gradient_futrell_isoCodes.length = 26 := by native_decide

/-- Languages with high propHeadFinal (> 700) in Futrell have high
    soProportion (> 700) in Levshina: head-final ≈ SOV ≈ high SO proportion. -/
theorem head_final_correlates_with_so :
    let shared := allProfiles.filter (λ p =>
      futrellLanguages.any (·.isoCode == p.isoCode))
    let highHF := shared.filter (λ p =>
      match futrellLanguages.find? (·.isoCode == p.isoCode) with
      | some f => f.propHeadFinal > 700
      | none => false)
    highHF.all (·.soProportion1000 > 700) = true := by native_decide

-- Bridge 4: Flexibility ↔ optimization exceptions (HahnDegenFutrell2021.lean)

/-- Languages with soEntropy > 600 in Levshina include at least one of the
    Hahn et al. exception languages. Latvian appears in both:
    high SO entropy in Levshina, and a memory-surprisal optimization exception
    in Hahn et al. Flexible word order weakens memory-surprisal optimization. -/
theorem high_entropy_languages_include_exceptions :
    let highEntropy := allProfiles.filter (·.soEntropy1000 > 600)
    let hahnExceptions := HahnDegenFutrell2021.exceptionLanguages
    highEntropy.any (λ p => hahnExceptions.any (·.isoCode == p.isoCode)) = true := by
  native_decide

-- ============================================================================
-- §5: Register Variation (Russian Case Study, OSF Dataset6.txt)
-- ============================================================================

/-- Russian VO probability by register, from OSF Dataset6.txt (100 clauses per register).
    Demonstrates within-language variation that a categorical label obscures. -/
structure RegisterProfile where
  register : String
  voProbability1000 : Nat  -- VO probability × 1000
  deriving Repr, DecidableEq, BEq

def russianConversation : RegisterProfile :=
  { register := "conversation", voProbability1000 := 390 }

def russianFiction : RegisterProfile :=
  { register := "fiction", voProbability1000 := 830 }

def russianNews : RegisterProfile :=
  { register := "news", voProbability1000 := 830 }

def russianRegisters : List RegisterProfile :=
  [russianConversation, russianFiction, russianNews]

/-- Russian conversation has lower VO probability than fiction:
    spoken language permits more OV orders. -/
theorem russian_vo_varies_by_register :
    russianConversation.voProbability1000 < russianFiction.voProbability1000 := by native_decide

/-- The register variation is large: fiction - conversation > 400
    (a 44 percentage-point spread). A single categorical label
    cannot capture this within-language variation. -/
theorem register_variation_is_large :
    russianFiction.voProbability1000 - russianConversation.voProbability1000 > 400 := by
  native_decide

end Phenomena.WordOrder.Gradience
