import Linglib.Syntax.Negation

/-!
# Turkish Negation Fragment
[miestamo-2005] [haspelmath-2013] [dryer-haspelmath-2013]

Turkish expresses standard negation with the verbal suffix *-mA-*
(/-ma-/ or /-me-/ depending on vowel harmony). The suffix is inserted
between the verb stem and the TAM suffix.

## SymAsy: Symmetric and Asymmetric

Most constructions are **symmetric**: *-mA-* inserts without further change.
But the **aorist** is asymmetric (A/Cat): the affirmative aorist marker
*-(I)r* is replaced by *-z* in the negative.

| Construction | Affirmative | Negative | Symmetric? |
|-------------|-------------|----------|------------|
| Progressive | *gel-iyor* | *gel-m-iyor* | Yes |
| Past definite | *gel-di* | *gel-me-di* | Yes |
| Future | *gel-ecek* | *gel-me-yecek* | Yes |
| Evidential | *gel-miş* | *gel-me-miş* | Yes |
| **Aorist** | *gel-ir* | *gel-me-z* | **No** |

The aorist asymmetry is a paradigmatic change: a different morphological
marker appears, not just insertion of the negative morpheme.
-/

namespace Turkish.Negation

open Syntax.Negation

/-- *-mA-* — Turkish's negative verbal suffix (underlying form).
    Surfaces as *-ma-* (back-vowel stems) or *-me-* (front-vowel stems)
    by vowel harmony. Inserted between the verb stem and the TAM suffix:
    *gel-iyor* → *gel-m-iyor* (come-NEG-PROG). The form here is the
    abstract citation form; the harmony-conditioned alternants are
    captured by the language's morphology layer, not the marker entry. -/
def negSuffix : NegMarkerEntry :=
  { form := "-mA-"
  , morphemeType := .affix
  , position := .morphological }

/-- The Turkish negation system: a single verbal affix.
    The Fragment-side joint consumed by `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "tur" [negSuffix]

/-- A Turkish negation paradigm entry. -/
structure NegParadigmEntry where
  formLabel : String
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  /-- Is this construction symmetric (neg = aff + neg marker, no other change)? -/
  symmetric : Bool
  deriving Repr, BEq, Inhabited

/-- Paradigm for *gelmek* 'come' (3sg forms). -/
def gelParadigm : List NegParadigmEntry :=
  [ { formLabel := "progressive"
    , affirmative := "geliyor", negative := "gelmiyor"
    , glossAff := "come.PROG", glossNeg := "come.NEG.PROG"
    , symmetric := true }
  , { formLabel := "past definite"
    , affirmative := "geldi", negative := "gelmedi"
    , glossAff := "come.PST", glossNeg := "come.NEG.PST"
    , symmetric := true }
  , { formLabel := "future"
    , affirmative := "gelecek", negative := "gelmeyecek"
    , glossAff := "come.FUT", glossNeg := "come.NEG.FUT"
    , symmetric := true }
  , { formLabel := "evidential"
    , affirmative := "gelmiş", negative := "gelmemiş"
    , glossAff := "come.EVID", glossNeg := "come.NEG.EVID"
    , symmetric := true }
  , { formLabel := "aorist"
    , affirmative := "gelir", negative := "gelmez"
    , glossAff := "come.AOR", glossNeg := "come.NEG.AOR"
    , symmetric := false }
  ]

/-! ## Verification -/

theorem gel_paradigm_size : gelParadigm.length = 5 := by decide

/-- Most constructions are symmetric. -/
theorem mostly_symmetric :
    (gelParadigm.filter (·.symmetric)).length = 4 := by decide

/-- The aorist is the only asymmetric construction. -/
theorem aorist_asymmetric :
    (gelParadigm.filter (fun e => !e.symmetric)).length = 1 ∧
    (gelParadigm.filter (fun e => !e.symmetric)).head!.formLabel = "aorist" := by
  exact ⟨by decide, rfl⟩

/-- Turkish negation profile (WALS Ch 112-115 + Greco/JinKoenig fields). -/
def negationProfile : Syntax.Negation.NegationProfile :=
  { language := "Turkish"
  , iso := "tur"
  , morphemeType := .affix
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , negIndefinite := some .cooccur
  , negMarkers := ["-mA-"]
  , negIsHead := none
  , enAttested := none }

end Turkish.Negation
