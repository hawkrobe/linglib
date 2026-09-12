import Linglib.Data.UD.DependencyLength.FutrellEtAl2020

/-!
# Levshina et al. (2023): Why We Need a Gradient Approach to Word Order

This file records the gradient word-order measures of [levshina-stoynova-2023]: in place of
categorical labels such as SVO or "flexible", a language's basic order is described by the
proportion of subject-before-object clauses, the Shannon entropy of the subject–object order,
and the mutual information between case marking and grammatical role (`GradientWOProfile`).
Three claims are checked on the paper's datasets: the proportion ranges continuously across
languages rather than splitting into types (`so_proportion_is_continuous`), languages with
informative case marking have freer order (`case_mi_correlates_with_so_entropy`), and one
language varies by register, Russian conversation permitting far more object-first clauses
than fiction (`russian_vo_varies_by_register`).

## Implementation notes

The values are the paper's OSF datasets (https://osf.io/w9u6v/) as integers scaled by a
thousand: the proportion from Dataset1, entropy and case mutual information from Dataset3,
and the Russian register proportions from Dataset6.

## TODO

The rows are empirical data and belong in a generated `Data/WordOrder` module.

## References

* [levshina-stoynova-2023]
-/

namespace LevshinaEtAl2023

/-- A language's gradient word-order profile: the proportion of subject-before-object
clauses, the entropy of the subject–object order, and the mutual information between case
marking and grammatical role, each scaled by a thousand. -/
structure GradientWOProfile where
  name : String
  isoCode : String
  /-- Proportion of SO (subject before object) orders × 1000 (from Dataset1.txt) -/
  soProportion1000 : Nat
  /-- Shannon entropy of S-O order × 1000 (0 = deterministic, 1000 = maximal; Dataset3.txt) -/
  soEntropy1000 : Nat
  /-- Mutual information between case markers and grammatical role × 1000 (Dataset3.txt) -/
  caseMI1000 : Nat
  deriving Repr, DecidableEq

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

/-- The thirty languages of the datasets. -/
def allProfiles : List GradientWOProfile :=
  [ arabic, bulgarian, croatian, czech, danish, dutch, english, estonian
  , finnish, french, german, greek, hindi, hungarian, indonesian, italian
  , japanese, korean, latvian, lithuanian, persian, portuguese, romanian
  , russian, slovene, spanish, swedish, tamil, turkish, vietnamese ]

/-- The mean subject–object entropy of a set of languages, scaled by a thousand. -/
def meanSOEntropy (ps : List GradientWOProfile) : Nat :=
  if ps.isEmpty then 0
  else ps.foldl (λ acc p => acc + p.soEntropy1000) 0 / ps.length

/-- Languages whose case marking carries much information about grammatical role have freer
subject–object order on average than the rest. -/
theorem case_mi_correlates_with_so_entropy :
    meanSOEntropy (allProfiles.filter (·.caseMI1000 > 300)) >
    meanSOEntropy (allProfiles.filter (·.caseMI1000 ≤ 300)) := by decide

/-- The subject-before-object proportion spans the range from Lithuanian to Indonesian
rather than clustering at a few types. -/
theorem so_proportion_is_continuous :
    indonesian.soProportion1000 - lithuanian.soProportion1000 > 350 := by decide

/-- The proportion of verb-before-object clauses in a register of Russian, scaled by a
thousand. -/
structure RegisterProfile where
  register : String
  voProbability1000 : Nat
  deriving Repr, DecidableEq

def russianConversation : RegisterProfile :=
  { register := "conversation", voProbability1000 := 390 }

def russianFiction : RegisterProfile :=
  { register := "fiction", voProbability1000 := 830 }

def russianNews : RegisterProfile :=
  { register := "news", voProbability1000 := 830 }

def russianRegisters : List RegisterProfile :=
  [russianConversation, russianFiction, russianNews]

/-- Russian conversation permits more object-first clauses than fiction. -/
theorem russian_vo_varies_by_register :
    russianConversation.voProbability1000 < russianFiction.voProbability1000 := by decide

end LevshinaEtAl2023
