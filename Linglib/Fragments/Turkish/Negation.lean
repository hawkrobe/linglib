import Linglib.Core.Lexical.Word

/-!
# Turkish Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013}

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

namespace Fragments.Turkish.Negation

/-- The Turkish negative verbal suffix (underlying form).
    Surfaces as *-ma-* or *-me-* by vowel harmony. -/
def negSuffix : String := "-mA-"

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

theorem negSuffix_is_mA : negSuffix = "-mA-" := rfl
theorem gel_paradigm_size : gelParadigm.length = 5 := by native_decide

/-- Most constructions are symmetric. -/
theorem mostly_symmetric :
    (gelParadigm.filter (·.symmetric)).length = 4 := by native_decide

/-- The aorist is the only asymmetric construction. -/
theorem aorist_asymmetric :
    (gelParadigm.filter (fun e => !e.symmetric)).length = 1 ∧
    (gelParadigm.filter (fun e => !e.symmetric)).head!.formLabel = "aorist" := by
  exact ⟨by native_decide, rfl⟩

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The aorist negative marker *-z* differs from the affirmative *-r*:
    this is paradigmatic asymmetry (A/Cat). -/
theorem aorist_different_markers :
    let aor := (gelParadigm.filter (·.formLabel == "aorist")).head!
    hasSubstr aor.affirmative "ir" = true ∧
    hasSubstr aor.negative "ez" = true := by
  exact ⟨by native_decide, by native_decide⟩

end Fragments.Turkish.Negation
