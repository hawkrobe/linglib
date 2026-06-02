import Linglib.Fragments.English.Determiners
import Linglib.Semantics.Quantification.Quantifier

/-!
# Canonical 6-Element Quantifier Paradigm
[barwise-cooper-1981] [van-tiel-franke-sauerland-2021]

The canonical ⟨none, few, some, half, most, all⟩ scale used cross-paper
to evaluate quantifier theories — empirical implicature studies
([van-tiel-franke-sauerland-2021]), GQ universals
([barwise-cooper-1981]), polarity bridges
([von-fintel-1993]), and cross-linguistic typology. Lives at the
top level of `Phenomena/Quantification/` because it is genuinely
cross-paper data, not study-specific.

## Key definitions

- `QuantityWord` — the 6-element enum
- `QuantityWord.entry` — projection to the English `QuantifierEntry`
- `QuantityWord.monotonicity` — convenience accessor
- `QuantityWord.gqDenotation` — canonical model-theoretic denotation
  (B&C-style), built on `every_sem`/`some_sem`/`no_sem`/etc. from
  `Semantics.Quantification.Quantifier`.

Per-paper PT/GQT parameter values (thresholds, prototypes, spreads)
live in the relevant `Studies/` files, not here.
-/

namespace Phenomena.Quantification.Inventory

open Semantics.Quantification.Lexicon (QuantifierEntry Monotonicity)
open Core.Logic.Intensional
open Core.Quantification (GQ)
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
  | .none_ => English.Determiners.none_
  | .few   => English.Determiners.few
  | .some_ => English.Determiners.some_
  | .half  => English.Determiners.half
  | .most  => English.Determiners.most
  | .all   => English.Determiners.all

/-- Convenience accessor. -/
def QuantityWord.monotonicity (q : QuantityWord) : Monotonicity :=
  q.entry.monotonicity

/-- All quantity words as a list. -/
def QuantityWord.toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all]

/-- Canonical model-theoretic generalized-quantifier denotation. -/
noncomputable def QuantityWord.gqDenotation (q : QuantityWord)
    {α : Type*} [Fintype α] : GQ α :=
  match q with
  | .none_ => no_sem
  | .some_ => some_sem
  | .all   => every_sem
  | .most  => most_sem
  | .few   => few_sem
  | .half  => half_sem

end Phenomena.Quantification.Inventory
