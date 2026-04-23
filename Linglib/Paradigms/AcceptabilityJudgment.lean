import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum
import Linglib.Core.Lexical.Word
import Linglib.Features.ClauseForm

/-!
# Acceptability Judgment Paradigm

@cite{sprouse-2007} @cite{sprouse-et-al-2012}

Shared vocabulary for the **acceptability judgment** experimental
paradigm — formal-syntax / experimental-syntax studies that elicit
sentence acceptability ratings (typically on a Likert or 100-point scale)
to test categorical predictions of grammatical theory.

## Architectural role

`Paradigms/` is the contract layer between `Theories/` and
`Phenomena/Studies/`. Theories produce predictions in their native
types; bridge theorems in `Studies/` translate those predictions into
paradigm-typed predictions and prove they satisfy the empirical patterns
documented in the study file. The paradigm itself is theory-agnostic:
it specifies *what kind of input the experiment provides* and *what
shape of output a theory must produce*.

## What this file provides

1. **`FactorialCondition`**: a typed cell in a 2-factor factorial design.
   Generic over the factor types so that any pair (`Bool × WhStrategy`,
   `Person × Number`, `Animacy × Definiteness`, …) plugs in.
2. **`DDResult`**: a difference-in-differences score (Maxwell & Delaney
   2003 method, used by @cite{sprouse-et-al-2012} for island effects and
   by @cite{chan-shen-2026} for *wh-the-hell* licensing). Stored as ℚ
   for exact arithmetic, with a Boolean `interactionSignificant` flag
   for the linear-mixed-effects model's interaction p-value.
3. **`AccountPredictions`**: an n-cell prediction tuple from a theoretical
   account, with a `matchesPattern` comparator. Generic over `n` so that
   2×2 (4 cells), 2×3 (6 cells), etc. all use the same machinery.

## Out of scope (per `CLAUDE.md` Processing scope)

- Statistical-model specifications (LME formulae, contrast coding,
  random-effect structures) — analysis-pipeline detail
- Stimulus norming details (filler ratings, balancing constraints) —
  study-internal methodology
- Participant-population metadata (L1, age, dialect) — study metadata
- Raw rating scales / z-score transformations — measurement detail

The paradigm specifies the **empirical contract** between an account
and the data — what cells are tested and what pattern is observed —
not the statistical apparatus that produces the pattern.
-/

namespace Paradigms.AcceptabilityJudgment

-- ============================================================================
-- §1. Factorial conditions
-- ============================================================================

/-- A typed cell in a 2-factor factorial design (@cite{sprouse-2007}: §2;
    @cite{sprouse-et-al-2012}: §2.1).

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

-- ============================================================================
-- §2. Difference-in-differences scores
-- ============================================================================

/-- A difference-in-differences (DD) score from a 2×2 factorial design,
    using the Maxwell & Delaney (2003) computation: DD = D2 − D1, where
    D1 and D2 are the two main-factor differences. A positive DD reflects
    a **superadditive interaction** — a penalty above and beyond the sum
    of the two main effects.

    Used by @cite{sprouse-et-al-2012} as the standard test of island
    effects in experimental syntax, and by @cite{chan-shen-2026} for
    *wh-the-hell* licensing.

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

-- ============================================================================
-- §3. Account predictions
-- ============================================================================

/-- A theoretical account's predicted acceptability pattern across `n`
    cells of a factorial design. Each cell is `True` (predicted acceptable)
    or `False` (predicted unacceptable).

    Used to compare a theory's predictions against the empirical pattern
    via `matches`. -/
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

-- ============================================================================
-- §4. Introspective Minimal Pairs (Pre-Experimental)
-- ============================================================================

/-! Minimal pairs as **introspective grammaticality contrasts** —
    the methodological tradition that Sprouse's factorial-design
    machinery above was introduced to discipline. A minimal pair records
    a single (typically the analyst's) judgment per sentence: one is
    grammatical, one is not, and they differ minimally in the property
    being tested.

    Two parallel families:

    * **Word-based** (`MinimalPair`, `PhenomenonData`): sentences are
      `List Word`, requiring feature specifications. Used by analyses
      that operate on parsed/featural representations (HPSG, DG, Minimalism).
    * **String-based** (`SentencePair`, `StringPhenomenonData`): sentences
      are raw strings, parseable by any theory. Used by phenomenon data
      files that should remain free of theoretical commitments. -/

-- §4.1 Word-based

/-- A minimal pair: grammatical vs ungrammatical, with context. -/
structure MinimalPair where
  grammatical : List Word
  ungrammatical : List Word
  clauseType : ClauseForm
  description : String
  citation : Option String := none

/-- Collection of minimal pairs for a phenomenon. -/
structure PhenomenonData where
  name : String
  pairs : List MinimalPair
  generalization : String

/-- Check if a grammaticality predicate captures a minimal pair.

    Captures the pair iff the predicate accepts the grammatical sentence
    and rejects the ungrammatical sentence. -/
def capturesMinimalPairBy (pred : List Word → Bool) (pair : MinimalPair) : Bool :=
  pred pair.grammatical && !pred pair.ungrammatical

/-- Check if a grammaticality predicate captures all minimal pairs in a
    phenomenon dataset. -/
def capturesPhenomenonData (pred : List Word → Bool) (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all (capturesMinimalPairBy pred)

-- §4.2 String-based (theory-neutral)

/-- String-based minimal pair for theory-neutral phenomena.

    Unlike `MinimalPair` which uses `List Word` (requiring feature
    specifications), this type uses raw strings that can be parsed by any
    theory. This keeps empirical data in `Phenomena/` free from
    theoretical commitments. -/
structure SentencePair where
  /-- The grammatical sentence -/
  grammatical : String
  /-- The ungrammatical sentence -/
  ungrammatical : String
  /-- Clause form (declarative, question, etc.) -/
  clauseType : ClauseForm
  /-- Description of what the pair tests -/
  description : String
  /-- Optional citation for the data -/
  citation : Option String := none
  deriving Repr, BEq

/-- String-based phenomenon data for theory-neutral representation.

    This is the string-based analogue of `PhenomenonData`. Phenomena files
    should use this type so that empirical data is decoupled from any
    particular grammatical theory's representation. -/
structure StringPhenomenonData where
  /-- Name of the phenomenon -/
  name : String
  /-- List of minimal pairs -/
  pairs : List SentencePair
  /-- Generalization captured by this data -/
  generalization : String
  deriving Repr

end Paradigms.AcceptabilityJudgment
