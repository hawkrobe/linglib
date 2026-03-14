import Linglib.Theories.Semantics.Alternatives.HornScale
import Linglib.Theories.Semantics.Exhaustification.Fox2007

/-!
# Alternative Sources
@cite{katzir-2007} @cite{fox-katzir-2011} @cite{hu-etal-2023}

An `AlternativeSource` maps expressions to their candidate alternatives.
This is a form-level abstraction: it answers "what could the speaker have
said instead?" without computing what those alternatives mean.

## Design

The typeclass separates three concerns:

1. **Support** (this file): which forms are alternatives to a given form?
   Determined by grammar — Horn scale membership, structural complexity
   (@cite{katzir-2007}), syntactic category match.

2. **Weight** (future): how expected is each alternative in context?
   @cite{hu-etal-2023} show that SI rates correlate with LM surprisal
   of the strong scalemate. Weight is context-dependent and can be
   added as a separate `AlternativeWeight` class later.

3. **Meaning** (consumer-provided): what does each alternative mean?
   The consumer provides `interp : Form → World → Bool` to map forms
   to truth-conditional meanings. This keeps `AlternativeSource` agnostic
   about world types and models.

## Instances

Horn scale types (`QuantExpr`, `ConnExpr`, `ModalExpr`, `NumberExpr`)
get canonical instances where alternatives = all scale members.
The assertion itself is always included (standard convention).

## Connection to Exhaustification

`AlternativeSource.exhaust` feeds alternatives through `exhB`
(@cite{fox-2007}), completing the pipeline:

```
AlternativeSource.alternatives : Form → List Form
  ↓ map interp
List (World → Bool)
  ↓ exhB
Exhaustified meaning : World → Bool
```
-/

namespace Alternatives

open Core.Scale
open Exhaustification.Fox2007

/-- An alternative source generates candidate alternatives for an expression.

    Alternatives include the expression itself (standard convention).
    The exhaustification operator (`exhB`) determines which alternatives
    to exclude — the source just provides the candidates. -/
class AlternativeSource (Form : Type) where
  /-- Candidate alternatives to `x`, including `x` itself. -/
  alternatives : Form → List Form

namespace AlternativeSource

variable {Form World : Type}

/-- Interpret alternatives as meaning functions.

    Given `interp : Form → World → Bool`, maps each alternative form
    to its truth-conditional meaning. This is the bridge between
    form-level alternatives and the truth-conditional meanings that
    `exhB` and RSA consume. -/
def meanings [AlternativeSource Form]
    (interp : Form → World → Bool) (x : Form) : List (World → Bool) :=
  (alternatives x).map interp

/-- Exhaustify via @cite{fox-2007}'s innocent exclusion.

    Computes `exhB domain (meanings interp x) (interp x)`: assert `x`
    and negate every innocently excludable alternative. -/
def exhaust [AlternativeSource Form]
    (domain : List World) (interp : Form → World → Bool)
    (x : Form) : World → Bool :=
  exhB domain (meanings interp x) (interp x)

end AlternativeSource


-- ============================================================
-- Horn Scale Instances
-- ============================================================

/-- Quantifier alternatives: {none, some, most, all}. -/
instance : AlternativeSource Quantifiers.QuantExpr where
  alternatives _ := Quantifiers.quantScale.members

/-- Connective alternatives: {or, and}. -/
instance : AlternativeSource Connectives.ConnExpr where
  alternatives _ := Connectives.connScale.members

/-- Modal alternatives: {possible, necessary}. -/
instance : AlternativeSource Modals.ModalExpr where
  alternatives _ := Modals.modalScale.members

/-- Number alternatives: {plural, singular}. -/
instance : AlternativeSource Number.NumberExpr where
  alternatives _ := Number.numberScale.members

/-- Build an `AlternativeSource` from any `HornScale`. -/
def alternativeSourceOfScale {α : Type} (s : HornScale α) :
    AlternativeSource α where
  alternatives _ := s.members


-- ============================================================
-- Worked Example: Quantifier Exhaustification
-- ============================================================

section QuantifierExample

open Quantifiers

/-- The full quantifier scale derives "exactly one" from "some".

    With alternatives {none, some, most, all}, innocent exclusion
    negates `none` (vacuously — contradicts `some`), `most`, AND
    `all`. The result is true only at w1 (count = 1).

    This is *stronger* than the textbook "some but not all" because
    `most` is also excluded. The textbook result arises from the
    two-element scale {some, all} (see `someAllExhaust` below). -/
theorem some_exhaust_full_scale :
    let exh := AlternativeSource.exhaust
      (allWorlds 3) (worldMeaning 3) QuantExpr.some_
    exh ⟨⟨0, by omega⟩⟩ = false ∧
    exh ⟨⟨1, by omega⟩⟩ = true ∧
    exh ⟨⟨2, by omega⟩⟩ = false ∧
    exh ⟨⟨3, by omega⟩⟩ = false := by native_decide

/-- Alternative source with just {some, all} — the classic Horn scale
    without `most` or `none`. -/
def someAllSource : AlternativeSource QuantExpr where
  alternatives _ := [.some_, .all]

/-- The two-element scale {some, all} derives "some but not all".

    Without `most` on the scale, innocent exclusion only negates `all`.
    The result is true at w1 (count = 1) AND w2 (count = 2). -/
theorem someAllExhaust :
    let exh := @AlternativeSource.exhaust QuantExpr (QuantWorld 3)
      someAllSource (allWorlds 3) (worldMeaning 3) QuantExpr.some_
    exh ⟨⟨0, by omega⟩⟩ = false ∧
    exh ⟨⟨1, by omega⟩⟩ = true ∧
    exh ⟨⟨2, by omega⟩⟩ = true ∧
    exh ⟨⟨3, by omega⟩⟩ = false := by native_decide

/-- The choice of alternative source affects exhaustification.

    Full scale: Exh("some") = "exactly one" (too strong)
    Classic scale: Exh("some") = "some but not all" (standard SI)

    This demonstrates that the `AlternativeSource` instance is
    empirically significant — it's not just bookkeeping. -/
theorem scale_choice_matters :
    let full := AlternativeSource.exhaust
      (allWorlds 3) (worldMeaning 3) QuantExpr.some_
    let classic := @AlternativeSource.exhaust QuantExpr (QuantWorld 3)
      someAllSource (allWorlds 3) (worldMeaning 3) QuantExpr.some_
    -- At w2 (count = 2): full scale excludes, classic doesn't
    full ⟨⟨2, by omega⟩⟩ = false ∧ classic ⟨⟨2, by omega⟩⟩ = true := by
  native_decide

end QuantifierExample


-- ============================================================
-- Connective Example
-- ============================================================

section ConnectiveExample

open Connectives

/-- Two truth-value worlds for propositional connectives. -/
inductive PQWorld where
  | tt | tf | ft | ff
  deriving DecidableEq, BEq, Repr

private def pqDomain : List PQWorld := [.tt, .tf, .ft, .ff]

private def connMeaning : ConnExpr → PQWorld → Bool
  | .or_,  .tt | .or_,  .tf | .or_,  .ft => true
  | .and_, .tt => true
  | _, _ => false

/-- Exh("or") = exclusive or: p ∨ q but not p ∧ q. -/
theorem or_exhaust :
    let exh := AlternativeSource.exhaust pqDomain connMeaning ConnExpr.or_
    exh .tt = false ∧ exh .tf = true ∧
    exh .ft = true ∧ exh .ff = false := by native_decide

end ConnectiveExample


-- ============================================================
-- Bridge to HornScale
-- ============================================================

/-! ## Relationship to HornScale

`HornScale` carries an ordering (weaker → stronger). `AlternativeSource`
does not — it just provides the set of alternatives. The ordering emerges
from sentence-level entailment inside `exhB`.

`HornScale.strongerAlternatives` stipulates which items are stronger.
`AlternativeSource` + `exhB` *derives* the same result from meanings.
This follows @cite{geurts-2010}'s argument (p. 58) that alternatives
should be sets, not ordered scales — the ordering comes from semantics,
not from the lexicon.

The four canonical instances (`QuantExpr`, `ConnExpr`, `ModalExpr`,
`NumberExpr`) are built from `HornScale.members` via `alternativeSourceOfScale`.
-/

section HornScaleBridge

open Quantifiers

/-- `AlternativeSource` for `QuantExpr` agrees with `alternativeSourceOfScale`.

    The canonical instance IS the scale-derived one. -/
theorem quant_source_eq_scale :
    (inferInstance : AlternativeSource QuantExpr).alternatives =
    (alternativeSourceOfScale quantScale).alternatives := rfl

/-- The Horn scale records `all` as stronger than `some`. -/
theorem hornscale_all_stronger_some :
    Core.Scale.isStronger quantScale .all .some_ = true := by native_decide

/-- `exhB` via `AlternativeSource` derives the same conclusion: `all` is
    negated in the exhaustified meaning of `some`. No stipulated ordering
    needed — strength emerges from the meanings. -/
theorem exhaust_negates_all :
    let exh := AlternativeSource.exhaust (allWorlds 3) (worldMeaning 3)
    exh QuantExpr.some_ ⟨⟨3, by omega⟩⟩ = false := by native_decide

end HornScaleBridge


end Alternatives
