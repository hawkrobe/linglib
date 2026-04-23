import Linglib.Features.VerbCluster
import Linglib.Core.Computability.FormalLanguage

/-!
# Cross-Serial Dependencies
@cite{bresnan-etal-1982}

Empirical data on cross-serial dependencies in Dutch verb clusters,
first described in @cite{bresnan-etal-1982}.

## The Phenomenon

In Dutch subordinate clauses, multiple NPs can precede multiple verbs,
with each NP interpreted as the argument of a corresponding verb:

  "... dat Jan Piet Marie zag helpen zwemmen"
  "... that Jan Piet Marie saw help swim"
  = "that Jan saw Piet help Marie swim"

The dependencies are cross-serial (not nested):
  NP₁ NP₂ NP₃ V₁ V₂ V₃
  └────────────┘
      └────────────┘
          └────────────┘

Cross-serial word order alone is context-free — @cite{gazdar-pullum-1982}
exhibit a CF-PSG (grammar 29) generating the correct Dutch strings with
proper verb subcategorization (formalized in `PullumGazdar1982`).
What takes this beyond CF power is cross-serial order PLUS case agreement:
requiring dative NPs to match dative verbs and accusative NPs to match
accusative verbs across unbounded depth. This was proven for Swiss German
by @cite{shieber-1985} (formalized in `Shieber1985`).
CCG handles the full pattern via generalized composition.

## Contrast with German

German has nested dependencies (can be handled by CFG):
  NP₁ NP₂ NP₃ V₃ V₂ V₁
  └────────────────────┘
      └────────────┘
          └────┘

## Note on attribution

The Dutch cross-serial data is from @cite{bresnan-etal-1982}. The formal
proof that cross-serial dependencies with case-marking are beyond CFG power
is @cite{shieber-1985}, formalized in `Shieber1985`.
The distinction matters: @cite{bresnan-etal-1982}'s argument relied on
constituency assumptions (refuted by @cite{gazdar-pullum-1982}), whereas
@cite{shieber-1985}'s string-set argument via Swiss German case-marking
is purely formal and irrefutable.

-/

namespace Phenomena.WordOrder.CrossSerial

open Features (VerbClusterBinding BindingPattern)

-- Dutch Examples (@cite{bresnan-etal-1982}, @cite{steedman-2000})

/-- A verb cluster example with NP-verb dependency data.

    Used for both Dutch cross-serial and German nested dependency patterns.
    Surface string, gloss, and translation document the example; the binding
    encodes the structural claim as a permutation σ : Fin n → Fin n. The
    dependency pattern is derived from the binding via `binding.pattern`. -/
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
  binding : VerbClusterBinding n
  deriving Repr

def dutch_2np_2v : VerbClusterExample :=
  { n := 2
  , language := "Dutch"
  , surface := "... dat Jan Piet zag zwemmen"
  , gloss := "... that Jan Piet saw swim"
  , translation := "that Jan saw Piet swim"
  , nps := ["Jan", "Piet"]
  , verbs := ["zag", "zwemmen"]
  , binding := VerbClusterBinding.identity 2
  }

def dutch_3np_3v : VerbClusterExample :=
  { n := 3
  , language := "Dutch"
  , surface := "... dat Jan Piet Marie zag helpen zwemmen"
  , gloss := "... that Jan Piet Marie saw help swim"
  , translation := "that Jan saw Piet help Marie swim"
  , nps := ["Jan", "Piet", "Marie"]
  , verbs := ["zag", "helpen", "zwemmen"]
  , binding := VerbClusterBinding.identity 3
  }

def dutch_4np_4v : VerbClusterExample :=
  { n := 4
  , language := "Dutch"
  , surface := "... dat Jan Piet Marie Karel zag helpen laten zwemmen"
  , gloss := "... that Jan Piet Marie Karel saw help let swim"
  , translation := "that Jan saw Piet help Marie let Karel swim"
  , nps := ["Jan", "Piet", "Marie", "Karel"]
  , verbs := ["zag", "helpen", "laten", "zwemmen"]
  , binding := VerbClusterBinding.identity 4
  }

-- German Contrast (Nested)

def german_3np_3v : VerbClusterExample :=
  { n := 3
  , language := "German"
  , surface := "... dass Jan Piet Marie schwimmen helfen sah"
  , gloss := "... that Jan Piet Marie swim help saw"
  , translation := "that Jan saw Piet help Marie swim"
  , nps := ["Jan", "Piet", "Marie"]
  , verbs := ["schwimmen", "helfen", "sah"]
  , binding := VerbClusterBinding.reverse 3
  }

-- The Formal Language Connection

open Core (FormalLanguageType)

/-- Cross-serial dependencies with case agreement require mild
    context-sensitivity.

    Cross-serial word ORDER alone is context-free
    (@cite{gazdar-pullum-1982} grammar 29). The mildly context-sensitive
    classification applies to the full pattern with case-matching,
    proven formally for Swiss German in
    `Shieber1985` via the pumping lemma. -/
def crossSerialRequires : FormalLanguageType := .mildlyContextSensitive

/-- Nested dependencies are context-free. -/
def nestedRequires : FormalLanguageType := .contextFree

-- Collected Data

def allExamples : List VerbClusterExample :=
  [dutch_2np_2v, dutch_3np_3v, dutch_4np_4v, german_3np_3v]

-- Verification

/-- Dutch 3-NP example has cross-serial pattern -/
theorem dutch_3_is_crossSerial :
    dutch_3np_3v.binding.pattern = .crossSerial := by decide

/-- German 3-NP example has nested pattern -/
theorem german_3_is_nested :
    german_3np_3v.binding.pattern = .nested := by decide

end Phenomena.WordOrder.CrossSerial
