import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum
import Linglib.Phenomena.MinimalPairs

/-!
# Sprouse, Wagers & Phillips (2012) — Factorial Acceptability Designs

[sprouse-et-al-2012], with the magnitude-estimation groundwork of
[sprouse-2007].

Contract types for the **factorial acceptability-judgment** experimental
paradigm: formal/experimental-syntax studies that elicit sentence
acceptability ratings across a factorial design to test categorical
predictions of grammatical theory. The paradigm is theory-agnostic:
it specifies *what kind of input the experiment provides* and *what
shape of output a theory must produce*; bridge theorems in downstream
`Studies/` files translate theory-native predictions into these types.

## Main declarations

* `FactorialCondition`: a typed cell in a 2-factor factorial design,
  generic over the factor types.
* `DDResult`: a difference-in-differences score (the Maxwell & Delaney
  2003 computation [sprouse-et-al-2012] use as the standard test of
  island effects), stored as ℚ for exact arithmetic.
* `AccountPredictions`: an n-cell prediction tuple from a theoretical
  account, with a decidable `Matches` comparator.
* `SentencePair.toFactorial`: the pre-experimental minimal-pair datum
  (`Linglib/Phenomena/MinimalPairs.lean`) as the degenerate 1×2 case of
  a factorial design.

## Out of scope

- Statistical-model specifications (LME formulae, contrast coding,
  random-effect structures) — analysis-pipeline detail
- Stimulus norming details (filler ratings, balancing constraints) —
  study-internal methodology
- Participant-population metadata (L1, age, dialect) — study metadata
- Raw rating scales / z-score transformations — measurement detail
-/

namespace SprouseEtAl2012

open Features
open Phenomena.MinimalPairs

/-! ### Factorial conditions -/

/-- A typed cell in a 2-factor factorial design ([sprouse-2007]: §2;
    [sprouse-et-al-2012]: §2.1).

    Generic over the two factor types so that the same machinery
    accepts any 2×2/2×3/3×3 design. The `sentence` field carries the
    actual stimulus (verbatim from the paper); `label` is the
    experiment's printed condition name. -/
structure FactorialCondition (F1 F2 : Type) where
  /-- Condition label as printed in the paper (e.g. "WhHell-Situ"). -/
  label : String
  /-- Level of the first factor. -/
  level1 : F1
  /-- Level of the second factor. -/
  level2 : F2
  /-- Verbatim stimulus sentence. -/
  sentence : String
  deriving Repr

/-! ### Difference-in-differences scores -/

/-- A difference-in-differences (DD) score from a 2×2 factorial design,
    using the Maxwell & Delaney (2003) computation: DD = D2 − D1, where
    D1 and D2 are the two main-factor differences. A positive DD reflects
    a **superadditive interaction** — a penalty above and beyond the sum
    of the two main effects. [sprouse-et-al-2012]'s standard test of
    island effects in experimental syntax.

    Stored as ℚ rather than `Float` to respect linglib's exact-arithmetic
    discipline. The `interactionSignificant` flag records the linear
    mixed-effects model's interaction-term p-value (typically p < 0.05). -/
structure DDResult where
  /-- Description of the two-factor contrast (e.g.
      "in-situ vs full movement"). -/
  comparison : String
  /-- DD score. Positive → superadditive interaction; ≈ 0 → additive. -/
  dd : ℚ
  /-- Did the LME model's interaction term reach significance? -/
  interactionSignificant : Bool
  deriving Repr

namespace DDResult

/-- A DD score is *superadditive* if positive — extra penalty beyond
    main effects. -/
def Superadditive (r : DDResult) : Prop := r.dd > 0

/-- A DD score is *additive* if ≈ 0 — no interaction beyond main effects. -/
def Additive (r : DDResult) : Prop := r.dd = 0

instance (r : DDResult) : Decidable r.Superadditive := by
  unfold Superadditive; infer_instance

instance (r : DDResult) : Decidable r.Additive := by
  unfold Additive; infer_instance

end DDResult

/-! ### Account predictions -/

/-- A theoretical account's predicted acceptability pattern across `n`
    cells of a factorial design. Each cell is `True` (predicted acceptable)
    or `False` (predicted unacceptable).

    Used to compare a theory's predictions against the empirical pattern
    via `Matches`. -/
structure AccountPredictions (n : Nat) where
  /-- Per-cell predicted acceptability. -/
  cell : Fin n → Prop
  /-- Each cell is decidable (so pattern comparison is decidable). -/
  decCell : ∀ i, Decidable (cell i)

namespace AccountPredictions

/-- Two prediction tuples match iff they predict the same pattern in
    every cell. -/
def Matches {n : Nat} (a b : AccountPredictions n) : Prop :=
  ∀ i : Fin n, a.cell i ↔ b.cell i

instance {n : Nat} (a b : AccountPredictions n) : Decidable (Matches a b) :=
  have : ∀ i : Fin n, Decidable (a.cell i ↔ b.cell i) := fun i =>
    have : Decidable (a.cell i) := a.decCell i
    have : Decidable (b.cell i) := b.decCell i
    inferInstance
  Fintype.decidableForallFintype

/-- Build a 4-cell `AccountPredictions` from four explicit Props (the
    standard 2×2 case). Convenience for the most common factorial. -/
def of2x2 (p₀₀ p₀₁ p₁₀ p₁₁ : Prop)
    [Decidable p₀₀] [Decidable p₀₁] [Decidable p₁₀] [Decidable p₁₁] :
    AccountPredictions 4 where
  cell := fun i => match i with
    | ⟨0, _⟩ => p₀₀
    | ⟨1, _⟩ => p₀₁
    | ⟨2, _⟩ => p₁₀
    | ⟨3, _⟩ => p₁₁
  decCell := fun i => match i with
    | ⟨0, _⟩ => inferInstance
    | ⟨1, _⟩ => inferInstance
    | ⟨2, _⟩ => inferInstance
    | ⟨3, _⟩ => inferInstance

/-- Build a 3-cell `AccountPredictions` (e.g., a 1×3 strategy contrast). -/
def of3 (p₀ p₁ p₂ : Prop)
    [Decidable p₀] [Decidable p₁] [Decidable p₂] :
    AccountPredictions 3 where
  cell := fun i => match i with
    | ⟨0, _⟩ => p₀
    | ⟨1, _⟩ => p₁
    | ⟨2, _⟩ => p₂
  decCell := fun i => match i with
    | ⟨0, _⟩ => inferInstance
    | ⟨1, _⟩ => inferInstance
    | ⟨2, _⟩ => inferInstance

end AccountPredictions

/-! ### Relation to introspective minimal pairs -/

/-- A `SentencePair` is structurally a 1×2 factorial design: one
    `Unit`-valued first factor, a `Bool`-valued grammaticality factor,
    one cell per Bool value. This makes the relationship between the
    minimal-pair tradition and the factorial discipline explicit:
    `SentencePair` is the degenerate case of `FactorialCondition Unit
    Bool` lifted to a pair of cells. -/
def SentencePair.toFactorial (sp : SentencePair) :
    FactorialCondition Unit Bool × FactorialCondition Unit Bool :=
  (⟨sp.description, (), true,  sp.grammatical⟩,
   ⟨sp.description, (), false, sp.ungrammatical⟩)

end SprouseEtAl2012
