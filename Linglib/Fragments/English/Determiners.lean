import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Quantification.Lexicon

/-!
# English Determiners
@cite{horn-1972} @cite{barwise-cooper-1981}

English-specific determiner lexicon. The shared `QuantifierEntry`
structure (and the `QForce`/`Monotonicity`/`Strength` enums) lives in
`Theories/Semantics/Quantification/Lexicon.lean`; this file is the
English instantiation and a small numerical-determiner sublexicon.

## Scope

This file carries only **descriptive lexical data** — facts a reference
grammar of English would record. Per-paper model parameters
(GQT thresholds, prototype-theory prototypes/spreads), compositional
denotations, scalar-paradigm projections, and theory-bridge theorems
all live elsewhere:

- Canonical 6-element ⟨none, few, some, half, most, all⟩ paradigm and
  its B&C-style GQ denotation table:
  `Phenomena/Quantification/Inventory.lean`.
- Compositional GQ denotations (`every_sem`, `both_sem`, `neither_sem`,
  …): `Theories/Semantics/Quantification/Quantifier.lean`.
- GQT/PT meaning operators consuming numerical parameters:
  `Theories/Semantics/Quantification/Quantifier.lean` (`gqtMeaning`),
  `Theories/Semantics/Probabilistic/PrototypeTheory.lean` (`ptMeaning`).
- Per-paper parameter values:
  `Phenomena/ScalarImplicatures/Studies/VanTielEtAl2021.lean`.
-/

namespace Fragments.English.Determiners

export Theories.Semantics.Quantification.Lexicon
  (QForce Monotonicity Strength QuantifierEntry)

def none_ : QuantifierEntry :=
  { form := "none", qforce := .negative, allowsMass := true, monotonicity := .decreasing }

def few : QuantifierEntry :=
  { form := "few", qforce := .proportional, numberRestriction := some .pl
  , monotonicity := .decreasing }

def some_ : QuantifierEntry :=
  { form := "some", qforce := .existential, allowsMass := true, monotonicity := .increasing }

def half : QuantifierEntry :=
  { form := "half", qforce := .proportional, allowsMass := true, monotonicity := .nonMonotone }

/-- "most" - more than half -/
def most : QuantifierEntry :=
  { form := "most"
  , qforce := .proportional
  , numberRestriction := some .pl
  , allowsMass := true
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There are most cats"
  }

/-- "all" - everything satisfies -/
def all : QuantifierEntry :=
  { form := "all"
  , qforce := .universal
  , numberRestriction := some .pl
  , allowsMass := true
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There is all cats"
  }

/-- "every" - universal, singular -/
def every : QuantifierEntry :=
  { form := "every"
  , qforce := .universal
  , numberRestriction := some .sg
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There is every cat"
  }

/-- "each" - universal, distributive -/
def each : QuantifierEntry :=
  { form := "each"
  , qforce := .universal
  , numberRestriction := some .sg
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There is each cat"
  }

/-- "many" - a large number -/
def many : QuantifierEntry :=
  { form := "many"
  , qforce := .proportional
  , numberRestriction := some .pl
  , monotonicity := .increasing
  }

/-! ## Numerical Determiners
@cite{barwise-cooper-1981} @cite{van-de-pol-etal-2023}

Parameterized by a numerical threshold `n`. These are the class of
determiners @cite{van-de-pol-etal-2023} show satisfy all three semantic
universals (and have low MDL).
-/

/-- Numerical determiner entry. -/
structure NumericalDetEntry where
  form : String
  qforce : QForce
  monotonicity : Monotonicity
  /-- The numerical threshold -/
  threshold : Nat
  deriving Repr, BEq

/-- "at least n" — upward monotone in scope, conservative, quantity -/
def atLeast (n : Nat) : NumericalDetEntry :=
  { form := s!"at least {n}", qforce := .proportional
  , monotonicity := .increasing, threshold := n }

/-- "at most n" — downward monotone in scope, conservative, quantity -/
def atMost (n : Nat) : NumericalDetEntry :=
  { form := s!"at most {n}", qforce := .proportional
  , monotonicity := .decreasing, threshold := n }

/-- "exactly n" — non-monotone (neither UE nor DE), conservative, quantity -/
def exactlyN (n : Nat) : NumericalDetEntry :=
  { form := s!"exactly {n}", qforce := .proportional
  , monotonicity := .nonMonotone, threshold := n }

/-- "more than n" — upward monotone, conservative, quantity -/
def moreThan (n : Nat) : NumericalDetEntry :=
  { form := s!"more than {n}", qforce := .proportional
  , monotonicity := .increasing, threshold := n }

/-- "fewer than n" — downward monotone, conservative, quantity -/
def fewerThan (n : Nat) : NumericalDetEntry :=
  { form := s!"fewer than {n}", qforce := .proportional
  , monotonicity := .decreasing, threshold := n }

/-! ## Definite Determiners (less relevant for quantity scales) -/

def the : QuantifierEntry :=
  { form := "the", qforce := .definite, allowsMass := true, strength := .strong }

def this : QuantifierEntry :=
  { form := "this", qforce := .definite, numberRestriction := some .sg, strength := .strong }

def that : QuantifierEntry :=
  { form := "that", qforce := .definite, numberRestriction := some .sg, strength := .strong }

def these : QuantifierEntry :=
  { form := "these", qforce := .definite, numberRestriction := some .pl, strength := .strong }

def those : QuantifierEntry :=
  { form := "those", qforce := .definite, numberRestriction := some .pl, strength := .strong }

def a : QuantifierEntry :=
  { form := "a", qforce := .existential, numberRestriction := some .sg }

def an : QuantifierEntry :=
  { form := "an", qforce := .existential, numberRestriction := some .sg }

/-- "both" - universal dual, presupposes exactly 2.
    K&S (83a): [_Det each of the two] ⇒ both.
    Compositional denotation `both_sem` lives in
    `Theories.Semantics.Quantification.Quantifier`.

    `numberRestriction := some .du` carries the dual core concept
    (@cite{harbour-2014} `[−atomic, +minimal]`); the cardinality clause
    `|R| ≥ 2` on the denotation side reflects the Harbour
    `dualPredOnLattice` reading
    (@cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025}). -/
def both : QuantifierEntry :=
  { form := "both"
  , qforce := .universal
  , numberRestriction := some .du
  , monotonicity := .increasing
  , strength := .strong  -- K&S §3.2: definite dets are strong
  }

/-- "neither" - negative dual, presupposes exactly 2.
    K&S (83b): [_Det (not one) of the two] ⇒ neither.
    Compositional denotation `neither_sem` lives in
    `Theories.Semantics.Quantification.Quantifier`. -/
def neither : QuantifierEntry :=
  { form := "neither"
  , qforce := .negative
  , numberRestriction := some .du
  , monotonicity := .decreasing
  , strength := .strong  -- K&S §3.3: negative strong
  }

/-! ## Lexicon Access -/

/-- All quantifier entries (excluding definites). -/
def allQuantifiers : List QuantifierEntry := [
  none_, few, some_, half, most, all, every, each, many, both, neither
]

/-- All determiner entries (including definites). -/
def allDeterminers : List QuantifierEntry := [
  the, this, that, these, those, a, an
] ++ allQuantifiers

/-- Lookup by form. -/
def lookup (form : String) : Option QuantifierEntry :=
  allDeterminers.find? λ d => d.form == form

end Fragments.English.Determiners
