import Linglib.Syntax.Category.Determiner.Basic

/-!
# Cantonese determiner inventory

Cantonese (Sinitic, ISO `yue`) marks definiteness with the bare classifier
phrase [Clf-N], which serves unique and anaphoric environments alike, and
marks indefiniteness with the numeral-classifier phrase [jat-Clf-N];
demonstratives form a separate paradigm. The [Clf-N]-as-definite observation
is due to [cheng-sybesma-1999]; [jenks-2018] §6 analyzes [Clf-N] as an
ambiguous definite parallel to English *the*.

## References

* [cheng-sybesma-1999]
* [jenks-2018], §6
-/

namespace Cantonese.Determiners

/-- The Cantonese determiners are the syncretic [Clf-N] definite, the
    [jat-Clf-N] indefinite, and the demonstrative paradigm (*nei*). -/
def inventory : Determiner.Inventory :=
  [ .article { form := "Clf-N", definiteness := .definite, exponent := .classifierPhrase,
               uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] },
    .article { form := "jat-Clf-N", definiteness := .indefinite, exponent := .numeralClassifier },
    .demonstrative { form := "nei", deictic := .proximal } ]

/-- Cantonese derives the `.generallyMarked` Moroney cell. -/
theorem marking : inventory.markingStrategy = .generallyMarked := by decide

end Cantonese.Determiners
