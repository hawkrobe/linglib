import Linglib.Syntax.Agreement.Allocutive
import Linglib.Syntax.Category.Pronoun.Personal
import Linglib.Syntax.Category.Pronoun.Reciprocal
import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# Japanese pronouns and the addressee-honorific marker

Personal pronouns of Japanese — register-differentiated first-person forms
(*watashi*, *boku*, *ore*; [ochs-1992] on the masculine stance the latter
index), the second-person contrast *kimi* vs *anata*, and the third-person
forms *kare*, *kanojo*, *karera* — the reciprocal *otagai*, the reflexive *zibun*, and the
addressee-honorific verbal marker *-mas-*, which is sensitive to the
complementizer when embedded ([alok-bhalla-2026] (14)–(15), (33)).

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
* [E. Ochs, *Indexing Gender* (1992)][ochs-1992]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

namespace Japanese.Pronouns

/-- 私 *watashi* — 1sg, neutral. -/
def watashi : PersonalPronoun :=
  { form := "watashi", script := some "私", person := some .first, number := some .singular,
    register := .neutral }

/-- 僕 *boku* — 1sg informal, masculine-associated through register rather
    than a gender feature ([ochs-1992]). -/
def boku : PersonalPronoun :=
  { form := "boku", script := some "僕", person := some .first, number := some .singular,
    register := .informal }

/-- 俺 *ore* — 1sg very informal; indexes masculinity through an assertive
    stance ([ochs-1992]). -/
def ore : PersonalPronoun :=
  { form := "ore", script := some "俺", person := some .first, number := some .singular,
    register := .informal }

/-- 私たち *watashitachi* — 1pl. -/
def watashitachi : PersonalPronoun :=
  { form := "watashitachi", script := some "私たち", person := some .first,
    number := some .plural }

/-- 君 *kimi* — 2sg plain. -/
def kimi : PersonalPronoun :=
  { form := "kimi", script := some "君", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- あなた *anata* — 2sg polite. -/
def anata : PersonalPronoun :=
  { form := "anata", script := some "あなた", person := some .second, number := some .singular,
    honorific := some .honorific }

/-- 彼 *kare* — 3sg masculine. -/
def kare : PersonalPronoun :=
  { form := "kare", script := some "彼", person := some .third, number := some .singular,
    gender := some .masculine }

/-- 彼女 *kanojo* — 3sg feminine. -/
def kanojo : PersonalPronoun :=
  { form := "kanojo", script := some "彼女", person := some .third, number := some .singular,
    gender := some .feminine }

/-- 彼ら *karera* — 3pl. -/
def karera : PersonalPronoun :=
  { form := "karera", script := some "彼ら", person := some .third, number := some .plural }

/-- The personal-pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {watashi, boku, ore, watashitachi, kimi, anata, kare, kanojo, karera}

/-- 互い *otagai* — the reciprocal pronoun, distinct from the reflexive *zibun*. -/
def otagai : ReciprocalPronoun :=
  { form := "otagai", script := some "互い", number := some .plural }

/-- 自分 *zibun* — the reflexive, which also takes an antecedent outside its clause when that
    antecedent is a pivot, the point-of-view centre ([sells-1987]). -/
def zibun : ReflexivePronoun :=
  { form := "zibun", script := some "自分", requiredRole := some .pivot }

/-- Any perspectival antecedent licenses *zibun* at a distance: a pivot is the weakest role. -/
theorem zibun_licensedBy (r : Reference.LogophoricRole) : zibun.LicensedBy r :=
  ⟨.pivot, rfl, bot_le (a := r)⟩

/-- *-mas-* — the addressee-honorific marker on the verb. -/
def mas : AllocutiveMarker := { form := "-mas-", honorific := .honorific }

end Japanese.Pronouns
