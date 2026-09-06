import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Gender.Basic

/-!
# Afar noun gender

Afar (Qafar) has two genders. Nouns denoting males and females take them by sex; for the
rest, the position of the accent decides: a citation form ending in an accented vowel is
feminine, any other masculine, with the pairs *bàxa* 'son' ~ *baxà* 'daughter' carrying both
signals at once ([parker-hayward-1985]; [corbett-1991]).

## References

* [E. M. Parker, R. J. Hayward, *An Afar-English-French Dictionary*
  (1985)][parker-hayward-1985]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

namespace Afar.Gender

/-- The two controller genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- An Afar noun with its gender, whether that gender comes from the referent's sex, and
whether its citation form ends in an accented vowel. -/
structure Noun where
  form : String
  gloss : String
  /-- The agreement the noun takes. -/
  attestedGender : Value
  /-- Whether the gender comes from the referent's sex. -/
  isNaturalGender : Bool
  /-- Whether the citation form ends in an accented vowel. -/
  finalAccentedVowel : Bool
  deriving DecidableEq, Repr

abbrev Noun.gender (n : Noun) : Value := n.attestedGender

def baqla : Noun := ⟨"bàqla", "husband", .masc, true, false⟩
def barra : Noun := ⟨"barrà", "woman, wife", .fem, true, true⟩
def baxa : Noun := ⟨"bàxa", "son", .masc, true, false⟩
def baxa' : Noun := ⟨"baxà", "daughter", .fem, true, true⟩
def toobokoyta : Noun := ⟨"toobokòyta", "brother", .masc, true, false⟩
def toobokoyta' : Noun := ⟨"toobokoytà", "sister", .fem, true, true⟩
def bariseyna : Noun := ⟨"barisèyna", "male teacher", .masc, true, false⟩
def bariseyna' : Noun := ⟨"bariseynà", "female teacher", .fem, true, true⟩
def kuta : Noun := ⟨"kùta", "dog", .masc, true, false⟩
def kuta' : Noun := ⟨"kutà", "bitch", .fem, true, true⟩
def cato : Noun := ⟨"catò", "help", .fem, false, true⟩
def karma : Noun := ⟨"karmà", "autumn", .fem, false, true⟩
def ceder : Noun := ⟨"cedèr", "supper time", .masc, false, false⟩
def gilal : Noun := ⟨"gilàl", "winter", .masc, false, false⟩
def tamu : Noun := ⟨"tàmu", "taste", .masc, false, false⟩
def baanta : Noun := ⟨"baànta", "trumpet", .masc, false, false⟩
/-- *doònik* 'sail-boat': feminine against the accent rule. -/
def doonik : Noun := ⟨"doònik", "sail-boat", .fem, false, false⟩
/-- *abbà* 'father': masculine by sex against the accent rule. -/
def abba : Noun := ⟨"abbà", "father", .masc, true, true⟩
/-- *gabbixeèra* 'slender-waisted female': feminine by sex against the accent rule. -/
def gabbixeera : Noun := ⟨"gabbixeèra", "slender-waisted female", .fem, true, false⟩

def allNouns : List Noun :=
  [baqla, barra, baxa, baxa', toobokoyta, toobokoyta', bariseyna, bariseyna', kuta, kuta', cato,
    karma, ceder, gilal, tamu, baanta, doonik, abba, gabbixeera]

end Afar.Gender
