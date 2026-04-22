import Mathlib.Data.Nat.Basic
import Linglib.Core.IntensionalLogic.Rigidity

/-!
# Numerals as Type-n Singular Terms
@cite{sudo-2016}

Sudo's central typed-semantic claim: in *all* natural languages, numerals
denote singular terms of type `n` (an abstract numerical type). They are
constant intensions `λw_s. n` (Sudo eq. 2):

  ⟦roku⟧ = ⟦six⟧ = λw_s. 6

In English (and other non-classifier languages), numerals can also be
type-shifted to predicates/modifiers via a phonologically silent
∪-operator (Sudo eq. 10). In Japanese (and other obligatory-classifier
languages), the ∪-operator is *blocked* by the lexical presence of
classifiers (Chierchia 1998's Blocking Principle); numerals must combine
with a classifier to acquire a predicative type.

The inverse ∩-operator maps certain properties back to type-n constants
(Sudo eq. 24). Unlike ∪, ∩ has no overt counterpart in English or
Japanese — it is freely available as a covert type-shift in both.

## Architecture

`NumeralIntens W` is `Intension W ℕ` — a constant intension at a numeral
value is a "type-n singular term" in Sudo's sense. The ∪/∩ operators
specialized to numerals are defined in `Composition.lean`, where they
combine with the classifier denotations from `Defs.lean`.

This file deliberately avoids committing to whether type `n` is "the
naturals" `ℕ`, "the integers" `ℤ`, "abstract amounts" (Scontras 2014),
or "kinds whose extension is a fixed cardinal" — Sudo's empirical
arguments are agnostic about the deep ontology. We use `ℕ` for
formalization convenience.
-/

namespace Semantics.Classifier

universe u

/-- A numeral intension: a function from worlds to natural-number meanings.
    @cite{sudo-2016} (eq. 2) ⟦six⟧ = λw_s. 6 is a `NumeralIntens W` for any
    world type `W`. -/
abbrev NumeralIntens (W : Type u) := Core.Intension W ℕ

/-- The rigid numeral intension: a numeral `n` denotes the constant function
    `λw. n`. This is `Intension.rigid` specialized to `ℕ`. -/
def NumeralIntens.const {W : Type u} (n : ℕ) : NumeralIntens W :=
  Core.Intension.rigid n

@[simp] lemma NumeralIntens.const_apply {W : Type u} (n : ℕ) (w : W) :
    NumeralIntens.const n w = n := rfl

/-- Every constant numeral intension is rigid. Sudo's empirical claim that
    numerals do not vary across worlds is the rigidity of `NumeralIntens.const`. -/
theorem NumeralIntens.const_isRigid {W : Type u} (n : ℕ) :
    Core.Intension.IsRigid (NumeralIntens.const (W := W) n) :=
  Core.Intension.rigid_isRigid n

end Semantics.Classifier
