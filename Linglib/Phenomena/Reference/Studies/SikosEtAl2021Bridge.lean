import Linglib.Phenomena.Reference.Studies.SikosEtAl2021

/-!
# Bridge: Sikos et al. (2021) -- Structural Model Relationships

This bridge file formalizes the *structural* relationship between the
models compared in Sikos et al. (2021):

1. The baseline model (prior × literal semantics) IS RSA's L0.
2. In trivial contexts (unique referent), L1 = L0.
3. In pragmatically solvable contexts, L1 ≠ L0 -- RSA's recursive reasoning
   makes different predictions.

These are mathematical facts about the models, not empirical claims.

**What this does NOT show:** That RSA is empirically vindicated. Sikos et al.'s
Experiment 3 tested contexts specifically designed to be pragmatically
solvable (where L0 ≠ L1), and RSA still did not significantly outperform the
baseline. The structural fact that L1 ≠ L0 in certain contexts is necessary
but not sufficient for RSA to add empirical value -- humans may not engage
in the recursive reasoning RSA posits, even when it would help.

The honest conclusion: RSA's recursive reasoning is mathematically distinct
from L0 in non-trivial contexts, but whether this distinction matters
empirically for human reference resolution remains an open question.

## Status

RSA evaluation infrastructure (basicL0, basicL1, getScore, boolToRat)
has been removed. Domain types (Color, Shape, Object, Feature),
featureMeaning, context classification, and structural theorem stubs
are preserved. RSA computation and metric sensitivity analysis remain
with `sorry` for future reimplementation.
-/

namespace Phenomena.Reference.Studies.SikosEtAl2021Bridge

open Phenomena.Reference.Studies.SikosEtAl2021


-- ============================================================================
-- Domain Types (Sikos et al. use more features than FG2012)
-- ============================================================================

/-- Colors used in the experiments. -/
inductive Color where
  | blue | green | red
  deriving DecidableEq, BEq, Repr

/-- Shapes used in the experiments. -/
inductive Shape where
  | square | circle | triangle
  deriving DecidableEq, BEq, Repr

/-- An object in the reference game. -/
structure Object where
  color : Color
  shape : Shape
  deriving DecidableEq, BEq, Repr

/-- A feature predicate: either a color or a shape word. -/
inductive Feature where
  | color (c : Color)
  | shape (s : Shape)
  deriving DecidableEq, BEq, Repr

/-- Literal semantics: does the feature apply to the object? -/
def featureMeaning (f : Feature) (o : Object) : Bool :=
  match f with
  | .color c => o.color == c
  | .shape s => o.shape == s


-- ============================================================================
-- Context Classification
-- ============================================================================

/-- How many objects in a context match a given utterance. -/
def nMatches (ctx : List Object) (u : Feature) : Nat :=
  (ctx.filter (featureMeaning u)).length

/-- A context-utterance pair is trivial when exactly one object matches. -/
def isTrivial (ctx : List Object) (u : Feature) : Bool :=
  nMatches ctx u == 1


-- ============================================================================
-- Concrete Contexts
-- ============================================================================

/-- Trivial context: each utterance uniquely identifies its referent.
    {blue_square, green_circle, red_triangle} -/
def trivialCtx : List Object :=
  [⟨.blue, .square⟩, ⟨.green, .circle⟩, ⟨.red, .triangle⟩]

/-- Utterances for the trivial context. -/
def trivialUtts : List Feature :=
  [.color .blue, .color .green, .color .red,
   .shape .square, .shape .circle, .shape .triangle]

/-- FG2012's classic solvable context: {blue_square, blue_circle, green_square}.
    "square" applies to two objects; pragmatic reasoning breaks the tie. -/
def solvableCtx : List Object :=
  [⟨.blue, .square⟩, ⟨.blue, .circle⟩, ⟨.green, .square⟩]

/-- Utterances for the solvable context. -/
def solvableUtts : List Feature :=
  [.color .blue, .color .green, .shape .square, .shape .circle]


-- ============================================================================
-- Structural Theorems (stubs)
-- ============================================================================

/-! ### 1. The baseline IS L0

Sikos et al.'s baseline model computes P(w|u) ∝ prior(w) · ⟦u⟧(w), which
is exactly `basicL0` with uniform priors. This is definitional -- both sides
of the debate agree on this. -/


/-! ### 2. In trivial contexts, L1 = L0

When an utterance uniquely identifies its referent, recursive reasoning
adds nothing. Both Sikos et al. and RSA proponents agree on this. The
critique is that FG2012's stimuli are dominated by such items. -/

/-- "blue" uniquely identifies blue_square in the trivial context. -/
theorem trivial_blue_unique :
    isTrivial trivialCtx (.color .blue) = true := by sorry


/-! ### 3. In solvable contexts, L1 ≠ L0

This is the structural fact: in FG2012's classic context, L1 DOES make
different predictions from L0 for ambiguous utterances.

**However:** The structural difference does not resolve the empirical critique. -/

/-- "square" is ambiguous in the solvable context (matches 2 objects). -/
theorem solvable_square_ambiguous :
    isTrivial solvableCtx (.shape .square) = false := by sorry


/-! ### 4. Context classification verification -/

/-- The trivial context has all utterances trivially predicted. -/
theorem trivial_ctx_all_trivial :
    trivialUtts.all (isTrivial trivialCtx) = true := by sorry

/-- The solvable context has non-trivial utterances. -/
theorem solvable_ctx_has_nontrivial :
    (solvableUtts.filter (λ u => !isTrivial solvableCtx u)).length > 0 := by
  sorry

end Phenomena.Reference.Studies.SikosEtAl2021Bridge
