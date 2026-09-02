import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Composition.Ty
import Linglib.Semantics.Composition.LexEntry

/-!
# Covert Operators: Montague-Typed Constructors

[krifka-etal-1995] [carlson-1977] [guerrini-2026]

Covert operators (Gen, DIST, Hab, DPP) are semantically contentful LF nodes
with no overt realization. This module packages them as `LexEntry` values
that compose via FA in `evalTree`.

The *semantics* these wrap is the canonical generalized-quantifier substrate
in `Quantification/Counting.lean` (`everyOn`, `mostOn`, `thresholdOn`,
`prevalenceOn`, …). GEN's threshold reading is `genThreshold`, whose
denotation is `Quantification.thresholdOn` over the atom domain; the
universal reading is `Genericity.traditionalGEN`, grounded on
`Quantification.everyOn`. Earlier versions of this file re-implemented those
quantifiers in an inferior `Bool`/`List`/ℚ representation
(`covertQ`/`measure`/`thresholdQ`); those clones are retired in favour of the
`Counting.lean` API.

## Usage

```
open Quantification.CovertQuantifier (genThreshold dist dpp)

def myLex : Lexicon E W := fun s => match s with
  | "Gen"  => some (genThreshold E W atoms 2 3)
  | "DIST" => some (dist E W atomsOf)
  | _      => none
```
-/

namespace Quantification.CovertQuantifier

/-! ### Montague-Typed Constructors -/

section Compositional

open Semantics.Montague (LexEntry Lexicon)

/-- Gen: `(e→t) → (e→t) → t`. Dyadic generic quantifier.

    `generally` encodes the truth conditions — different theories
    instantiate it differently (threshold, normalcy, probabilistic).
    `traditionalGEN` (in `Genericity/Basic.lean`, grounded on
    `Quantification.everyOn`) and `Quantification.thresholdOn` are specific
    instantiations. -/
def gen (E W : Type)
    (generally : (E → Prop) → (E → Prop) → Prop)
    : LexEntry E W :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, generally⟩

open Classical in
/-- Gen with threshold: true iff ≥ `num/denom` of restrictor-satisfying
    atoms also satisfy scope. Montague-typed wrapper whose denotation is the
    canonical `Quantification.thresholdOn` (cross-multiplied `Nat`, `≥`-form)
    over the atom domain. Noncomputable only because the Montague denotations
    `restr`/`scope` are arbitrary `Prop`-predicates (decided classically). -/
noncomputable def genThreshold (E W : Type) [DecidableEq E] (atoms : List E)
    (num denom : Nat) : LexEntry E W :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun restr scope =>
    Quantification.thresholdOn atoms.toFinset restr scope num denom⟩

/-- DIST: `(e→t) → (e→t)`. Distributive operator.

    `atomsOf x` returns the atomic parts of x — for atomic entities
    it returns `[x]`, for plural/kind entities their parts.
    Montague-typed counterpart of `Distributivity.distMaximal`. -/
def dist (E W : Type) (atomsOf : E → List E)
    : LexEntry E W :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t), fun P x => ∀ a ∈ atomsOf x, P a⟩

/-- DPP: `(e→t) → (e→t) → t`. Derived Property Predication.

    DPP(P)(Q) = ∃x[P(x) ∧ Q(x)]. An existential type-shift for
    kind-denoting NPs combining with stage-level predicates.
    [guerrini-2026] structure (105b). -/
def dpp (E W : Type) (atoms : List E) : LexEntry E W :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun prop pred =>
    ∃ x ∈ atoms, prop x ∧ pred x⟩

/-- EXH: `(s→t) → (s→t)`. Exhaustivity operator (proposition modifier).

    `exhOp` maps a proposition to its exhaustified version — typically
    asserting the prejacent and negating innocently excludable alternatives.
    The canonical implementation is `Exhaustification.exhIE`, decidable over
    finite worlds in `Exhaustification.Finite`. Specific instances are plugged in at
    lexicon construction time with alternatives and world domain baked
    into the closure.

    Unlike Gen/DIST/Hab (which quantify over entities), EXH operates on
    propositions (`s→t`). Both compose via FA in the same tree — the
    Montague type system handles the dispatch:
    - Gen:  `(e→t) → (e→t) → t`  — FA with entity predicates
    - EXH:  `(s→t) → (s→t)`      — FA with propositions -/
def exh (E W : Type) (exhOp : (W → Prop) → (W → Prop))
    : LexEntry E W :=
  ⟨(.intens .t) ⇒ (.intens .t), exhOp⟩

end Compositional

end Quantification.CovertQuantifier
