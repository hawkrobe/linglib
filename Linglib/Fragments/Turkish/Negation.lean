import Linglib.Syntax.Negation

/-!
# Turkish Negation Fragment
[miestamo-2005] [haspelmath-2013] [dryer-haspelmath-2013]

Turkish expresses standard negation with the verbal suffix *-mA-*
(*-ma-* ~ *-me-* by vowel harmony). The suffix is inserted between the
verb stem and the TAM suffix.

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
marker appears, not just insertion of the negative morpheme. It is
sharpest outside 3sg: the negative aorist drops the marker entirely in
1sg *gelmem* and 1pl *gelmeyiz*, retaining *-z* only in the second and
third persons.
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

/-- Turkish standard (verbal) negation: a single verbal affix.
    Nonverbal predication negates with copular *değil* and the
    existential with suppletive *yok* (for *var*), both outside
    standard negation in [miestamo-2005]'s sense.
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
  deriving Repr

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

/-- The aorist is the only asymmetric construction in the paradigm. -/
theorem aorist_asymmetric :
    (gelParadigm.filter (fun e => !e.symmetric)).map (·.formLabel)
      = ["aorist"] := rfl

end Turkish.Negation
