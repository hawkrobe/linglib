import Mathlib.Data.Fin.Rev

/-!
# Bresnan, Kaplan, Peters & Zaenen (1982)
[bresnan-etal-1982]

Cross-Serial Dependencies in Dutch. In *The Formal Complexity of Natural
Language*, 286–319.

In Dutch subordinate clauses, multiple NPs precede multiple verbs with
cross-serial (not nested) dependencies:

  NP₁ NP₂ NP₃ V₁ V₂ V₃
  └────────────┘
      └────────────┘
          └────────────┘

German verb clusters show the nested (context-free) pattern instead:

  NP₁ NP₂ NP₃ V₃ V₂ V₁
  └────────────────────┘
      └────────────┘
          └────┘

## Main declarations

- `VerbClusterExample`: an example sentence with its NP-verb binding
  permutation (`Equiv.Perm (Fin n)`; crossed is `Equiv.refl`, nested `Fin.revPerm`)
- `dutch_2np_2v`, `dutch_3np_3v`, `dutch_4np_4v`, `german_3np_3v`:
  the standard paradigm
- `dutch_3_is_crossSerial`, `german_3_is_nested`: the bindings are the
  canonical crossed and nested permutations

## Attribution

[bresnan-etal-1982] described the Dutch data; their non-context-freeness
argument relied on constituency assumptions. [gazdar-pullum-1982] showed
bare cross-serial word order is context-free (formalized in
`PullumGazdar1982`); [shieber-1985] proved Swiss-German case-marked
cross-serial dependencies non-context-free as a string set (formalized in
`Shieber1985`). The example sentences here are the standard paradigm as
cited in the literature; the exact wording has not been verified against
the 1982 paper.
-/

namespace BresnanEtAl1982

/-- A verb cluster example with NP-verb dependency data.

    Used for both Dutch cross-serial and German nested dependency patterns.
    Surface string, gloss, and translation document the example; the binding
    encodes the structural claim as a permutation σ : Fin n → Fin n. -/
structure VerbClusterExample where
  /-- Number of NP-verb pairs -/
  n : Nat
  /-- Language name -/
  language : String
  /-- Surface string -/
  surface : String
  /-- English gloss -/
  gloss : String
  /-- English translation -/
  translation : String
  /-- NPs in order -/
  nps : List String
  /-- Verbs in order -/
  verbs : List String
  /-- The NP-verb binding permutation -/
  binding : Equiv.Perm (Fin n)

def dutch_2np_2v : VerbClusterExample :=
  { n := 2
  , language := "Dutch"
  , surface := "... dat Jan Piet zag zwemmen"
  , gloss := "... that Jan Piet saw swim"
  , translation := "that Jan saw Piet swim"
  , nps := ["Jan", "Piet"]
  , verbs := ["zag", "zwemmen"]
  , binding := Equiv.refl _
  }

def dutch_3np_3v : VerbClusterExample :=
  { n := 3
  , language := "Dutch"
  , surface := "... dat Jan Piet Marie zag helpen zwemmen"
  , gloss := "... that Jan Piet Marie saw help swim"
  , translation := "that Jan saw Piet help Marie swim"
  , nps := ["Jan", "Piet", "Marie"]
  , verbs := ["zag", "helpen", "zwemmen"]
  , binding := Equiv.refl _
  }

def dutch_4np_4v : VerbClusterExample :=
  { n := 4
  , language := "Dutch"
  , surface := "... dat Jan Piet Marie Karel zag helpen laten zwemmen"
  , gloss := "... that Jan Piet Marie Karel saw help let swim"
  , translation := "that Jan saw Piet help Marie let Karel swim"
  , nps := ["Jan", "Piet", "Marie", "Karel"]
  , verbs := ["zag", "helpen", "laten", "zwemmen"]
  , binding := Equiv.refl _
  }

/-- German contrast: nested dependencies. -/
def german_3np_3v : VerbClusterExample :=
  { n := 3
  , language := "German"
  , surface := "... dass Jan Piet Marie schwimmen helfen sah"
  , gloss := "... that Jan Piet Marie swim help saw"
  , translation := "that Jan saw Piet help Marie swim"
  , nps := ["Jan", "Piet", "Marie"]
  , verbs := ["schwimmen", "helfen", "sah"]
  , binding := Fin.revPerm
  }

def allExamples : List VerbClusterExample :=
  [dutch_2np_2v, dutch_3np_3v, dutch_4np_4v, german_3np_3v]

/-- The Dutch 3-NP binding is the crossed (identity) permutation. -/
theorem dutch_3_is_crossSerial : dutch_3np_3v.binding = Equiv.refl _ := rfl

/-- The German 3-NP binding is the nested (reversal) permutation. -/
theorem german_3_is_nested : german_3np_3v.binding = Fin.revPerm := rfl

end BresnanEtAl1982
