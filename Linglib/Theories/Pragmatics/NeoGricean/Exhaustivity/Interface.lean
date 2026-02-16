/-
# Unified Exhaustification Interface

Provides a single entry point for applying exhaustification operators at parse positions.
Unifies exhIE (Fox 2007), exhMW (Groenendijk-Stokhof), and connects to Spector 2007.

## Design Principle

Any theory invoking EXH in a parse should use this interface, ensuring:
1. Consistent semantics across RSA, NeoGricean, and other frameworks
2. Easy switching between EXH operators (IE vs MW)
3. Proper connection between Parse positions and EXH application

## Architecture

```
Core/Parse.lean
├── Parse, scopeParses

NeoGricean/Exhaustivity/Interface.lean (this file)
├── ExhPosition (M/O/I), exhParses, parseHasExhAt

NeoGricean/Exhaustivity/Basic.lean
├── exhIE, exhMW (core operators)
├── IE sets, MC-sets
└── Theoretical properties

NeoGricean/Exhaustivity/Interface.lean (this file)
├── ExhOperator enum
├── applyExh (single operator application)
├── applyExhAtParse (parse-guided application)
└── Exhaustifiable typeclass (unified interface)
```

## References

- Spector (2016). Comparing exhaustivity operators. S&P 9(11):1-33.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Spector (2007). Scalar implicatures: exhaustivity and Gricean reasoning.
- Franke & Bergen (2020). Theory-driven statistical modeling.
-/

import Linglib.Core.Parse
import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Basic

namespace NeoGricean.Exhaustivity.Interface

open Core
open NeoGricean.Exhaustivity

/-- Positions where EXH can occur in a doubly-quantified sentence. -/
inductive ExhPosition where
  | M : ExhPosition  -- Matrix (whole sentence)
  | O : ExhPosition  -- Outer quantifier
  | I : ExhPosition  -- Inner quantifier
  deriving DecidableEq, Repr, BEq, Hashable

/-- Convert EXH positions to a parse -/
def parseFromExhPositions (positions : List ExhPosition) : Parse :=
  let id := if positions.isEmpty then "lit"
    else positions.map (λ p => match p with
      | .M => "M" | .O => "O" | .I => "I") |> String.intercalate ""
  let desc := if positions.isEmpty then "Literal (no EXH)"
    else s!"EXH at {id}"
  ⟨id, desc⟩

/-- All 8 EXH parses for doubly-quantified sentences -/
def exhParses : List Parse :=
  [ parseFromExhPositions []
  , parseFromExhPositions [.M]
  , parseFromExhPositions [.O]
  , parseFromExhPositions [.I]
  , parseFromExhPositions [.M, .O]
  , parseFromExhPositions [.M, .I]
  , parseFromExhPositions [.O, .I]
  , parseFromExhPositions [.M, .O, .I]
  ]

/-- Check if a parse includes a specific EXH position -/
def parseHasExhAt (p : Parse) (pos : ExhPosition) : Bool :=
  let char := match pos with | .M => 'M' | .O => 'O' | .I => 'I'
  p.id.any (· == char)

theorem exh_parses_count : exhParses.length = 8 := rfl

/-- Different exhaustification strategies from the literature.

    - `IE`: Innocent Exclusion (Fox 2007, Spector 2016)
      Excludes alternatives that can be consistently excluded in ALL maximal ways.

    - `MW`: Maximal Worlds / Minimal Models (Groenendijk & Stokhof 1984)
      Keeps only minimal worlds relative to the alternative ordering.

    Theorem 9 (Spector 2016): When ALT is closed under ∧, exhIE = exhMW. -/
inductive ExhOperator where
  | IE : ExhOperator  -- Innocent Exclusion
  | MW : ExhOperator  -- Maximal Worlds / Minimal Models
  deriving DecidableEq, Repr, BEq

/-- Apply an exhaustification operator to a proposition given alternatives.

    This is the single entry point for applying EXH to a proposition.
    All theories should use this rather than calling exhIE/exhMW directly. -/
def applyExh {World : Type*} (op : ExhOperator) (ALT : Set (Prop' World))
    (φ : Prop' World) : Prop' World :=
  match op with
  | .IE => exhIE ALT φ
  | .MW => exhMW ALT φ

/-- When ALT is closed under conjunction, both operators agree.
    This is Theorem 9 from Spector (2016). -/
theorem ie_eq_mw_when_closed {World : Type*} (ALT : Set (Prop' World)) (φ : Prop' World)
    (hclosed : ∀ ψ₁ ψ₂, ψ₁ ∈ ALT → ψ₂ ∈ ALT → (ψ₁ ∧ₚ ψ₂) ∈ ALT) :
    applyExh .IE ALT φ = applyExh .MW ALT φ := by
  simp only [applyExh]
  -- This follows from theorem9_main in Basic.lean
  -- For now, we state it as the connection point
  sorry -- TODO: Connect to theorem9_main


/-- Alternatives can vary by EXH position.

    For "Q₁ Xs V'd Q₂ Ys":
    - Position M (matrix): alternatives to the whole sentence
    - Position O (outer): alternatives to Q₁
    - Position I (inner): alternatives to Q₂

    Each position may have different scalar alternatives. -/
abbrev AlternativesAtPosition (World : Type*) := ExhPosition → Set (Prop' World)

/-- Apply EXH at positions indicated by a Parse.

    This is the single entry point for parse-guided exhaustification.

    Given:
    - `op`: Which EXH operator to use (IE or MW)
    - `p`: A parse indicating EXH positions (e.g., "MOI" means EXH at M, O, and I)
    - `base`: The literal meaning (no EXH)
    - `altsAt`: Alternatives at each position

    Returns: The meaning after applying EXH at all indicated positions.

    Application order: I → O → M (innermost first, standard scope convention). -/
def applyExhAtParse {World : Type*} (op : ExhOperator) (p : Parse)
    (base : Prop' World) (altsAt : AlternativesAtPosition World) : Prop' World :=
  -- Apply from innermost to outermost: I, then O, then M
  let withI := if parseHasExhAt p .I then applyExh op (altsAt .I) base else base
  let withO := if parseHasExhAt p .O then applyExh op (altsAt .O) withI else withI
  let withM := if parseHasExhAt p .M then applyExh op (altsAt .M) withO else withO
  withM

/-- Helper: "lit" has no EXH positions -/
private theorem lit_has_no_exh : ∀ pos, parseHasExhAt Parse.literal pos = false := by
  intro pos; cases pos <;> native_decide

/-- The literal parse (no EXH) returns the base meaning unchanged. -/
theorem literal_parse_is_identity {World : Type*} (op : ExhOperator)
    (base : Prop' World) (altsAt : AlternativesAtPosition World) :
    applyExhAtParse op Parse.literal base altsAt = base := by
  simp only [applyExhAtParse, lit_has_no_exh]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- Helper: Parse from single position has that position -/
private theorem single_pos_has_M : parseHasExhAt (parseFromExhPositions [.M]) .M = true := by native_decide
private theorem single_pos_has_O : parseHasExhAt (parseFromExhPositions [.O]) .O = true := by native_decide
private theorem single_pos_has_I : parseHasExhAt (parseFromExhPositions [.I]) .I = true := by native_decide
private theorem single_M_not_O : parseHasExhAt (parseFromExhPositions [.M]) .O = false := by native_decide
private theorem single_M_not_I : parseHasExhAt (parseFromExhPositions [.M]) .I = false := by native_decide
private theorem single_O_not_M : parseHasExhAt (parseFromExhPositions [.O]) .M = false := by native_decide
private theorem single_O_not_I : parseHasExhAt (parseFromExhPositions [.O]) .I = false := by native_decide
private theorem single_I_not_M : parseHasExhAt (parseFromExhPositions [.I]) .M = false := by native_decide
private theorem single_I_not_O : parseHasExhAt (parseFromExhPositions [.I]) .O = false := by native_decide

/-- EXH at a single position applies that operator once. -/
theorem single_position_exh {World : Type*} (op : ExhOperator) (pos : ExhPosition)
    (base : Prop' World) (altsAt : AlternativesAtPosition World) :
    let p := parseFromExhPositions [pos]
    applyExhAtParse op p base altsAt = applyExh op (altsAt pos) base := by
  cases pos
  · simp only [applyExhAtParse, single_pos_has_M, single_M_not_O, single_M_not_I,
               Bool.false_eq_true, ↓reduceIte]
  · simp only [applyExhAtParse, single_pos_has_O, single_O_not_M, single_O_not_I,
               Bool.false_eq_true, ↓reduceIte]
  · simp only [applyExhAtParse, single_pos_has_I, single_I_not_M, single_I_not_O,
               Bool.false_eq_true, ↓reduceIte]


/-- Typeclass for sentence types where EXH can insert at parse positions.

    Design decisions:
    1. `exhOperator`: Which operator to use (default: IE)
    2. `literalMeaning`: Base meaning before any EXH
    3. `alternativesAt`: Position-dependent alternatives

    The meaning under a parse is computed by `meaningAtParse`, which calls
    `applyExhAtParse` with the unified EXH machinery.

    When to use this:
    - RSA models with grammatical ambiguity about EXH placement
    - Any theory that needs to reason about EXH insertion sites

    When not to use this:
    - Scope ambiguity (use `Core.scopeParses` directly)
    - Direct application of EXH (use `applyExh` directly) -/
class Exhaustifiable (Sentence : Type) (World : Type) where
  /-- Which EXH operator to use (default: Innocent Exclusion) -/
  exhOperator : ExhOperator := .IE
  /-- Available EXH parses (typically Core.exhParses) -/
  parses : List Parse := exhParses
  /-- Literal meaning (no EXH applied) -/
  literalMeaning : Sentence → World → Bool
  /-- Alternatives at each EXH position, given a sentence -/
  alternativesAt : Sentence → AlternativesAtPosition World

/-- Compute the meaning of a sentence under a specific parse.

    This uses the unified `applyExhAtParse` machinery, ensuring all
    theories that use `Exhaustifiable` apply EXH consistently. -/
def Exhaustifiable.meaningAtParse {S W : Type} [inst : Exhaustifiable S W]
    (p : Parse) (s : S) : Prop' W :=
  let base : Prop' W := λ w => Exhaustifiable.literalMeaning s w = true
  let altsAt := Exhaustifiable.alternativesAt s
  applyExhAtParse inst.exhOperator p base altsAt

/-- Boolean version for RSA integration. -/
def Exhaustifiable.meaningAtParseBool {S W : Type} [Exhaustifiable S W]
    (p : Parse) (s : S) (w : W) : Bool :=
  -- Note: This requires Decidable; for now, we use the literal meaning
  -- when we can't decide the exhaustified meaning
  -- TODO: Make this properly decidable
  Exhaustifiable.literalMeaning s w

/-- The literal parse gives the literal meaning. -/
theorem Exhaustifiable.literal_is_literal {S W : Type} [inst : Exhaustifiable S W]
    (s : S) : meaningAtParse (W := W) Parse.literal s = λ w => Exhaustifiable.literalMeaning s w = true := by
  simp only [meaningAtParse]
  rw [literal_parse_is_identity]


/-
Spector (2007) defines exhaustification for propositional logic:

  Exhaust(P) = {V ∈ P | ¬∃V' ∈ P, V' ⊂ V}

This is "keep minimal valuations" - equivalent to `exhMW` when:
- Worlds = valuations (Finsets of true atoms)
- The ordering is set inclusion
- ALT = all positive literals

The connection:
- `exhMW` keeps minimal worlds relative to <_ALT
- Spector 2007's `Exhaust` keeps minimal valuations relative to ⊂
- These are the same when the ALT-ordering matches set inclusion

Theorem (Spector 2007): For positive propositions P, Max(P) = {Exhaust(P)},
showing that Gricean reasoning derives exhaustive interpretation.

This provides the theoretical justification for why we exhaustify.
The operators `exhIE` and `exhMW` provide the MECHANISM for how we exhaustify.
-/

/-- Spector 2007's insight: Exhaustification is derivable from Gricean maxims.

    This doesn't add computational content, but documents the theoretical
    connection between:
    - WHY we exhaustify (Gricean reasoning, Spector 2007)
    - HOW we exhaustify (exhIE/exhMW operators, Spector 2016)
    - WHERE we exhaustify (Parse positions, this interface) -/
def griceanJustification : String :=
  "Exhaustification is not arbitrary. Spector (2007) shows that for positive " ++
  "propositions P, the maximally informative Gricean interpretation is exactly " ++
  "Exhaust(P). This provides theoretical grounding for the EXH operators."


/-- Get parses for RSAScenario.ambiguous -/
def getParses (S W : Type) [Exhaustifiable S W] : List Parse :=
  Exhaustifiable.parses (Sentence := S) (World := W)

/-- Convert to RSA meaning function (φ : Interp → World → Utt → Bool) -/
def toRSAMeaning {S W : Type} [Exhaustifiable S W]
    (p : Parse) (w : W) (s : S) : Bool :=
  Exhaustifiable.meaningAtParseBool p s w


end NeoGricean.Exhaustivity.Interface
