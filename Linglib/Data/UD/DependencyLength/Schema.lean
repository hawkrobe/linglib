/-!
# Dependency length by language: schema

Typed schema for the per-language corpus statistics a paper reports over Universal
Dependencies treebanks: the proportion of head-final dependencies and the mean dependency
length per word at fixed sentence lengths. Generated rows live in
`Data/UD/DependencyLength/<Paper>.lean`, emitted from the canonical `<Paper>.json` by
`scripts/gen_ud_deplength.py`.

This is data: it imports nothing from `Linglib/` and states no theorems. Values are scaled
integers, permille for the head-final proportion and hundredths for dependency lengths, at
the precision the papers print, so that consumers compute over them by `decide`. The language
code is a UD language code, an annotation for cross-study joins rather than a printed value.

## References

* [de-marneffe-zeman-2021]
-/

namespace Data.UD.DependencyLength

/-- One language's head-final proportion and mean dependency length per word at sentence
lengths 10, 15 and 20, over a UD treebank. -/
structure Row where
  /-- The language name as the paper prints it. -/
  language : String
  /-- The UD language code. -/
  isoCode : String
  /-- The proportion of head-final dependencies, in permille. -/
  propHeadFinal1000 : Nat
  /-- Mean dependency length per word at sentence length 10, in hundredths. -/
  depLengthAt10_100 : Nat
  /-- Mean dependency length per word at sentence length 15, in hundredths. -/
  depLengthAt15_100 : Nat
  /-- Mean dependency length per word at sentence length 20, in hundredths. -/
  depLengthAt20_100 : Nat
  deriving DecidableEq, Repr

end Data.UD.DependencyLength
