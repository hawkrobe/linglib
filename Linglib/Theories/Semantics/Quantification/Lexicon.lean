import Linglib.Core.Lexical.Word
import Mathlib.Data.Rat.Defs

/-!
# Quantifier lexicon — shared structure
@cite{horn-1972} @cite{barwise-cooper-1981}

A theory-level structure for quantifier lexical entries shared across
language fragments. Originally defined inside
`Fragments/English/Determiners.lean`, but several theory files
(`Theories/Syntax/HPSG/Core/FromFragments.lean`,
`Theories/Syntax/CCG/Core/FromFragments.lean`,
`Theories/Syntax/Minimalism/Core/FromFragments.lean`) and several
fragments (English, French, Italian) all need it; promoting it here
removes a Theory→Fragment import direction violation and lets all
language fragments share a single `QuantifierEntry` shape.

## Fields

- `form` — surface form
- `qforce` — quantificational force (universal, existential, …)
- `numberRestriction` — `none` (number-neutral), or `some .sg`/`.pl`/`.du`
  (a single grammatical number; `.du` covers items like English *both*
  and French *les deux* whose meaning composition uses the dual core
  concept @cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025})
- `allowsMass` — accepts mass NPs?
- `monotonicity` — increasing / decreasing / non-monotone
- `strength` — weak / strong (Barwise & Cooper §4.3 Table II;
  weak determiners pass `there is/are`)
- `gqtThreshold`, `ptPrototype`, `ptSpread` — generalized-quantifier
  threshold and prototype-theoretic dispersion
-/

set_option autoImplicit false

namespace Theories.Semantics.Quantification.Lexicon

inductive QForce where
  | universal
  | existential
  | definite
  | negative
  | proportional
  deriving DecidableEq, Repr

inductive Monotonicity where
  | increasing
  | decreasing
  | nonMonotone
  deriving DecidableEq, Repr

/-- Weak/strong classification (B&C §4.3, Table II).
Weak determiners allow there-insertion: "There are some cats."
Strong determiners don't: "*There is every cat." -/
inductive Strength where
  | weak
  | strong
  deriving DecidableEq, Repr

/-- Unified lexical entry for quantifiers/determiners. -/
structure QuantifierEntry where
  form : String
  qforce : QForce
  numberRestriction : Option Number := none
  allowsMass : Bool := false
  monotonicity : Monotonicity := .increasing
  strength : Strength := .weak
  gqtThreshold : ℚ := 0
  ptPrototype : ℚ := 0
  ptSpread : ℚ := 2
  deriving Repr, BEq, DecidableEq

/-- Project the lexical entry to a Core `Word`: form, category DET,
and number features inherited from `numberRestriction`. -/
def QuantifierEntry.toWord (d : QuantifierEntry) : Word :=
  { form := d.form
  , cat := .DET
  , features := { number := d.numberRestriction }
  }

end Theories.Semantics.Quantification.Lexicon
