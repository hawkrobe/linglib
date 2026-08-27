import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Japanese pronouns and the addressee-honorific marker

Personal pronouns of Japanese — register-differentiated first-person forms
(*watashi*, *boku*, *ore*; [ochs-1992] on the masculine stance the latter
index), the second-person contrast *kimi* vs *anata*, and the third-person
forms *kare*, *kanojo*, *karera* — the reciprocal *otagai*, and the
addressee-honorific verbal marker *-mas-*, which is sensitive to the
complementizer when embedded ([alok-bhalla-2026] (14)–(15), (33)).
-/

namespace Japanese.Pronouns

open Pronoun

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
    register := .informal }

/-- あなた *anata* — 2sg polite. -/
def anata : PersonalPronoun :=
  { form := "anata", script := some "あなた", person := some .second, number := some .singular,
    register := .formal }

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
def pronouns : List PersonalPronoun :=
  [watashi, boku, ore, watashitachi, kimi, anata, kare, kanojo, karera]

/-- 互い *otagai* — the reciprocal pronoun, distinct from the reflexive *jibun*. -/
def otagai : Pronoun :=
  { form := "otagai", script := some "互い", number := some .plural,
    bindingClass := some .reciprocal }

/-- *-mas-* — the addressee-honorific marker on the verb. -/
def mas : AllocutiveEntry := { form := "-mas-", register := .formal, gloss := "MAS" }

end Japanese.Pronouns
