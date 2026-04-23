import Linglib.Fragments.English.Determiners
import Linglib.Theories.Semantics.Quantification.Quantifier

/-!
# Canonical 6-Element Quantifier Paradigm
@cite{barwise-cooper-1981} @cite{van-tiel-franke-sauerland-2021}

The canonical ⟨none, few, some, half, most, all⟩ scale used cross-paper
to evaluate quantifier theories — empirical implicature studies
(@cite{van-tiel-franke-sauerland-2021}), GQ universals
(@cite{barwise-cooper-1981}), polarity bridges
(@cite{von-fintel-1993}), and cross-linguistic typology. Lives at the
top level of `Phenomena/Quantification/` because it is genuinely
cross-paper data, not study-specific.

## Key definitions

- `QuantityWord` — the 6-element enum
- `QuantityWord.entry` — projection to the English `QuantifierEntry`
- `QuantityWord.monotonicity` — convenience accessor
- `QuantityWord.gqDenotation` — canonical model-theoretic denotation
  (B&C-style), built on `every_sem`/`some_sem`/`no_sem`/etc. from
  `Theories.Semantics.Quantification.Quantifier`.

Per-paper PT/GQT parameter values (thresholds, prototypes, spreads)
live in the relevant `Studies/` files, not here.
-/

namespace Phenomena.Quantification.Inventory

open Theories.Semantics.Quantification.Lexicon (QuantifierEntry Monotonicity)
open Core.IntensionalLogic
open Semantics.Quantification.Quantifier

/-- The canonical 6-element quantity scale. -/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all
  deriving Repr, DecidableEq, Inhabited

instance : Fintype QuantityWord where
  elems := {.none_, .few, .some_, .half, .most, .all}
  complete := λ x => by cases x <;> simp

/-- Lexical entry for each quantity word, drawn from the English fragment. -/
def QuantityWord.entry : QuantityWord → QuantifierEntry
  | .none_ => Fragments.English.Determiners.none_
  | .few   => Fragments.English.Determiners.few
  | .some_ => Fragments.English.Determiners.some_
  | .half  => Fragments.English.Determiners.half
  | .most  => Fragments.English.Determiners.most
  | .all   => Fragments.English.Determiners.all

/-- Convenience accessor. -/
def QuantityWord.monotonicity (q : QuantityWord) : Monotonicity :=
  q.entry.monotonicity

/-- All quantity words as a list. -/
def QuantityWord.toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all]

/-- Canonical model-theoretic generalized-quantifier denotation. -/
def QuantityWord.gqDenotation (q : QuantityWord)
    (m : Frame) [Fintype m.Entity] : m.Denot Ty.det :=
  match q with
  | .none_ => no_sem m
  | .some_ => some_sem m
  | .all   => every_sem m
  | .most  => most_sem m
  | .few   => few_sem m
  | .half  => half_sem m

end Phenomena.Quantification.Inventory
