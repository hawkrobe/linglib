import Linglib.Syntax.Category.Determiner.Basic

/-!
# Cantonese Definiteness Fragment
[cheng-sybesma-1999] [jenks-2018]

Cantonese (ISO `yue`, Sinitic). [jenks-2018] (§6) analyzes the bare
classifier phrase [Clf-N] as an ambiguous definite, used in both unique and
anaphoric environments like English *the* — the [Clf-N]-as-definite observation
is [cheng-sybesma-1999]'s. Indefinites are [jat-Clf-N] (numeral +
classifier); demonstratives are a separate paradigm. The declared determiner
set derives the [moroney-2021] `.generallyMarked` cell, contrasting with
Mandarin's `.markedAnaphoric` (theoremed in `Studies/Jenks2018.lean`).
-/

namespace Cantonese.Definiteness

/-- Cantonese's determiner inventory: a syncretic [Clf-N] definite `Article`
    spanning both unique and anaphoric uses, a numeral-classifier indefinite
    `Article`, and a demonstrative paradigm. The indefinite is a first-class
    `Article` (exponed by the numeral-classifier construction), not an absent
    `hasIndefinite`. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "Clf-N", definiteness := .definite, exponent := .classifierPhrase,
               uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] },
    .article { form := "jat-Clf-N", definiteness := .indefinite, exponent := .numeralClassifier },
    .demonstrative { form := "nei", deictic := .proximal } ]

/-- Cantonese's determiner set derives the `.generallyMarked` strategy
    ([jenks-2018] Table 2): one definite form (the classifier phrase)
    covers both presupposition types. -/
theorem marking : Determiner.markingStrategy determiners = .generallyMarked := by
  decide

end Cantonese.Definiteness
