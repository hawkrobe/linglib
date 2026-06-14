import Linglib.Data.UD.Basic
import Linglib.Semantics.Quantification.Quantifier

/-!
# English Determiners
[horn-1972] [barwise-cooper-1981]

English-specific determiner lexicon. The shared `QuantifierEntry`
structure (and the `QForce`/`Monotonicity`/`Strength` enums) lives in
`Semantics/Quantification/Lexicon.lean`; this file is the
English instantiation, a small numerical-determiner sublexicon, and the
canonical 6-element ⟨none, few, some, half, most, all⟩ quantity scale
(`QuantityWord`) with its B&C-style GQ denotation table.

## Scope

This file carries descriptive lexical data and its projection to the
GQ denotations. Per-paper model parameters (GQT thresholds,
prototype-theory prototypes/spreads) and theory-bridge theorems live
elsewhere:

- Compositional GQ denotations (`every_sem`, `both_sem`, `neither_sem`,
  …): `Semantics/Quantification/Quantifier.lean`.
- GQT/PT meaning operators consuming numerical parameters:
  `Semantics/Quantification/Quantifier.lean` (`gqtMeaning`),
  `Semantics/Probabilistic/PrototypeTheory.lean` (`ptMeaning`).
- Per-paper parameter values:
  `Studies/VanTielEtAl2021.lean`.
-/

namespace English.Determiners

export Quantification.Lexicon
  (QForce Monotonicity Strength QuantifierEntry)

def none_ : QuantifierEntry :=
  { form := "none", qforce := .negative, allowsMass := true, monotonicity := .decreasing }

def few : QuantifierEntry :=
  { form := "few", qforce := .proportional, numberRestriction := some .Plur
  , monotonicity := .decreasing }

def some_ : QuantifierEntry :=
  { form := "some", qforce := .existential, allowsMass := true, monotonicity := .increasing }

def half : QuantifierEntry :=
  { form := "half", qforce := .proportional, allowsMass := true, monotonicity := .nonMonotone }

/-- "most" - more than half -/
def most : QuantifierEntry :=
  { form := "most"
  , qforce := .proportional
  , numberRestriction := some .Plur
  , allowsMass := true
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There are most cats"
  }

/-- "all" - everything satisfies -/
def all : QuantifierEntry :=
  { form := "all"
  , qforce := .universal
  , numberRestriction := some .Plur
  , allowsMass := true
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There is all cats"
  }

/-- "every" - universal, singular -/
def every : QuantifierEntry :=
  { form := "every"
  , qforce := .universal
  , numberRestriction := some .Sing
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There is every cat"
  }

/-- "each" - universal, distributive -/
def each : QuantifierEntry :=
  { form := "each"
  , qforce := .universal
  , numberRestriction := some .Sing
  , monotonicity := .increasing
  , strength := .strong  -- B&C Table II: *"There is each cat"
  }

/-- "many" - a large number -/
def many : QuantifierEntry :=
  { form := "many"
  , qforce := .proportional
  , numberRestriction := some .Plur
  , monotonicity := .increasing
  }

/-! ## Numerical Determiners
[barwise-cooper-1981] [van-de-pol-etal-2023]

Parameterized by a numerical threshold `n`. These are the class of
determiners [van-de-pol-etal-2023] show satisfy all three semantic
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
  { form := "this", qforce := .definite, numberRestriction := some .Sing, strength := .strong }

def that : QuantifierEntry :=
  { form := "that", qforce := .definite, numberRestriction := some .Sing, strength := .strong }

def these : QuantifierEntry :=
  { form := "these", qforce := .definite, numberRestriction := some .Plur, strength := .strong }

def those : QuantifierEntry :=
  { form := "those", qforce := .definite, numberRestriction := some .Plur, strength := .strong }

def a : QuantifierEntry :=
  { form := "a", qforce := .existential, numberRestriction := some .Sing }

def an : QuantifierEntry :=
  { form := "an", qforce := .existential, numberRestriction := some .Sing }

/-- "both" - universal dual, presupposes exactly 2.
    K&S (83a): [_Det each of the two] ⇒ both.
    Compositional denotation `both_sem` lives in
    `Quantification.Quantifier`.

    `numberRestriction := some .Dual` carries the dual core concept
    ([harbour-2014] `[−atomic, +minimal]`); the cardinality clause
    `|R| ≥ 2` on the denotation side reflects the Harbour
    `dualPredOnLattice` reading
    ([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]). -/
def both : QuantifierEntry :=
  { form := "both"
  , qforce := .universal
  , numberRestriction := some .Dual
  , monotonicity := .increasing
  , strength := .strong  -- K&S §3.2: definite dets are strong
  }

/-- "neither" - negative dual, presupposes exactly 2.
    K&S (83b): [_Det (not one) of the two] ⇒ neither.
    Compositional denotation `neither_sem` lives in
    `Quantification.Quantifier`. -/
def neither : QuantifierEntry :=
  { form := "neither"
  , qforce := .negative
  , numberRestriction := some .Dual
  , monotonicity := .decreasing
  , strength := .strong  -- K&S §3.3: negative strong
  }

/-! ## The Canonical Quantity Scale
[barwise-cooper-1981] [van-tiel-franke-sauerland-2021]

The 6-element ⟨none, few, some, half, most, all⟩ scale used cross-paper
to evaluate quantifier theories — empirical implicature studies
([van-tiel-franke-sauerland-2021]), GQ universals ([barwise-cooper-1981]),
and polarity bridges ([von-fintel-1993]).
-/

/-- The canonical 6-element quantity scale. -/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all
  deriving Repr, DecidableEq, Inhabited

instance : Fintype QuantityWord where
  elems := {.none_, .few, .some_, .half, .most, .all}
  complete := fun x => by cases x <;> simp

/-- Lexical entry for each quantity word. -/
def QuantityWord.entry : QuantityWord → QuantifierEntry
  | .none_ => _root_.English.Determiners.none_
  | .few   => _root_.English.Determiners.few
  | .some_ => _root_.English.Determiners.some_
  | .half  => _root_.English.Determiners.half
  | .most  => _root_.English.Determiners.most
  | .all   => _root_.English.Determiners.all

/-- Convenience accessor. -/
def QuantityWord.monotonicity (q : QuantityWord) : Monotonicity :=
  q.entry.monotonicity

/-- All quantity words as a list. -/
def QuantityWord.toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all]

/-- Canonical model-theoretic generalized-quantifier denotation
    (B&C-style), built on `every_sem`/`some_sem`/`no_sem`/etc. from
    `Quantification.Quantifier`. -/
noncomputable def QuantityWord.gqDenotation (q : QuantityWord)
    {α : Type*} [Fintype α] : Quantification.GQ α :=
  open Quantification in
  match q with
  | .none_ => no_sem
  | .some_ => some_sem
  | .all   => every_sem
  | .most  => most_sem
  | .few   => few_sem
  | .half  => half_sem

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

end English.Determiners
