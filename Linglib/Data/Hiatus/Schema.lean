import Mathlib.Tactic.DeriveFintype

/-!
# Hiatus resolution samples: schema

Typed schema for a paper's survey of which vowel elides where two vowels meet: for each
language of the sample, the kind of juncture and the vowel that elides there. Generated rows
live in `Data/Hiatus/<Paper>.lean`, emitted from the canonical `<Paper>.json` by
`scripts/gen_hiatus.py`.

This is data: it imports nothing from `Linglib/` and states no theorems. A language appears once
for each juncture and elided vowel the paper reports for it, so a language that elides the first
vowel with some suffixes and the second with others has two rows.

## References

* [casali-1997]
-/

namespace Data.Hiatus

/-- The kind of juncture at which two vowels meet. -/
inductive Juncture where
  /-- Between two lexical words. -/
  | lexicalLexical
  /-- Between a lexical word and a following function word. -/
  | lexicalFunction
  /-- Between a prefix of at least a consonant and a vowel and a root. -/
  | prefixRoot
  /-- Between a root and a suffix. -/
  | rootSuffix
  deriving DecidableEq, Repr, Fintype

/-- The vowel that elides, the first or the second of the two. -/
inductive ElidedVowel where
  | first
  | second
  deriving DecidableEq, Repr, Fintype

/-- A language's elision at a kind of juncture, as a paper reports it. -/
structure ElisionRow where
  /-- The language, under the name the paper uses. -/
  language : String
  /-- The kind of juncture. -/
  juncture : Juncture
  /-- The vowel that elides there. -/
  elided : ElidedVowel
  /-- The paper marks the report as uncertain. -/
  tentative : Bool
  deriving DecidableEq, Repr

end Data.Hiatus
