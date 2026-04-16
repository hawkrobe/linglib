import Linglib.Theories.Semantics.PIP.Basic
import Linglib.Core.IntensionalLogic.RestrictedModality

/-!
# PIP Expression Language (Full Static Formulation)

@cite{keshet-abney-2024}

PIP is natively a **static, truth-conditional** system: formulas denote
truth values relative to a model, plural assignment set G, and evaluation
world w*. This file defines the full `PIPExpr` type matching the paper's
thesis that PIP is "just predicate calculus with set abstraction."

## Constructors

The propositional fragment (pred, conj, neg, disj, impl, presup) is
extended with:

| Constructor | Paper item | Description |
|-------------|-----------|-------------|
| `exists_` | 43 | ∃x.φ — existential quantification over domain D |
| `forall_` | 43 | ∀x.φ — universal quantification over domain D |
| `labelDef` | 17.3 | X ≡ φ — tautological formula label definition |
| `must` | 28 | □φ — universal modality (EVERY over worlds) |
| `might` | 28 | ◇φ — existential modality (SOME over worlds) |

## Domain Parameter

The full PIPExpr is parameterized by both `W` (worlds) and `D` (individual
domain). Quantifier constructors bind over `D`, modals bind over `W`.
The propositional-only fragment uses `D = Empty` (no quantifiers needed).

## Label Extraction

`PIPExpr.labelDefs` extracts the label assignment from a formula. Since
label definitions are tautologies that float freely, this function collects
all `X ≡ φ` definitions regardless of their structural position.
-/

namespace Semantics.PIP

open Core.IntensionalLogic.RestrictedModality (BAccessRel)
open Core.Proposition (FiniteWorlds)

/-- A finite domain of individuals for PIP quantifier evaluation.
    Mirrors `Core.Proposition.FiniteWorlds` for world types. -/
class FiniteDomain (D : Type*) where
  elements : List D
  complete : ∀ d : D, d ∈ elements


-- ============================================================
-- PIP Expression Language (Full)
-- ============================================================

/--
PIP expressions: the full static formula language.

Parameterized by `W` (possible worlds) and `D` (individual domain).
Each PIP construct from the paper has a constructor.

The propositional fragment (`pred`, `conj`, `neg`, `disj`, `impl`, `presup`)
matches the original `Felicity.PIPExpr`. The quantifier and modal
constructors extend it to the full system.
-/
inductive PIPExprF (W : Type*) (D : Type*) where
  /-- Atomic predicate: P_w(x₁, ..., xₙ). Always felicitous. -/
  | pred (p : W → Bool)
  /-- Conjunction: φ ∧ ψ. Felicity is asymmetric (Karttunen). -/
  | conj (φ ψ : PIPExprF W D)
  /-- Negation: ¬φ. Felicity passes through. -/
  | neg (φ : PIPExprF W D)
  /-- Disjunction: φ ∨ ψ. -/
  | disj (φ ψ : PIPExprF W D)
  /-- Implication: φ → ψ. -/
  | impl (φ ψ : PIPExprF W D)
  /-- Presupposition: φ|ψ. Assert φ, presuppose ψ. -/
  | presup (φ : PIPExprF W D) (ψ : W → Bool)
  /-- Existential quantification: ∃x.φ (paper item 43).
      `body` takes a domain element and returns a formula. -/
  | exists_ (body : D → PIPExprF W D)
  /-- Universal quantification: ∀x.φ (paper item 43).
      `body` takes a domain element and returns a formula. -/
  | forall_ (body : D → PIPExprF W D)
  /-- Formula label definition: X ≡ φ (paper item 17.3).
      Tautological — always true. Registers the label for later retrieval. -/
  | labelDef (label : FLabel) (φ : PIPExprF W D)
  /-- Modal necessity: □_R φ (paper item 28, MUST).
      Universal quantification over R-accessible worlds. -/
  | must (R : BAccessRel W) (φ : PIPExprF W D)
  /-- Modal possibility: ◇_R φ (paper item 28, MIGHT).
      Existential quantification over R-accessible worlds. -/
  | might (R : BAccessRel W) (φ : PIPExprF W D)


-- ============================================================
-- Truth Conditions
-- ============================================================

/--
Truth evaluation for full PIP expressions.

PIP truth conditions are classical: presuppositions play no role
in determining truth values. Quantifiers and modals evaluate as
standard first-order quantification over domains and worlds.

Requires `[Fintype D]` for quantifier evaluation and `[FiniteWorlds W]`
for modal evaluation.
-/
def PIPExprF.truth {W D : Type*} [FiniteDomain D] [FiniteWorlds W] :
    PIPExprF W D → (W → Bool)
  | .pred p => p
  | .conj φ ψ => λ w => φ.truth w && ψ.truth w
  | .neg φ => λ w => (φ.truth w).not
  | .disj φ ψ => λ w => φ.truth w || ψ.truth w
  | .impl φ ψ => λ w => (φ.truth w).not || ψ.truth w
  | .presup φ _ψ => φ.truth
  | .exists_ body => λ w => FiniteDomain.elements.any (λ d => (body d).truth w)
  | .forall_ body => λ w => FiniteDomain.elements.all (λ d => (body d).truth w)
  | .labelDef _label φ => φ.truth  -- label defs are tautological wrt truth
  | .must R φ => λ w =>
      (FiniteWorlds.worlds.filter (R w)).all φ.truth
  | .might R φ => λ w =>
      (FiniteWorlds.worlds.filter (R w)).any φ.truth


-- ============================================================
-- Felicity Conditions (Full F Operator)
-- ============================================================

/--
The F operator: recursive presuppositional felicity (full version).

Extends the propositional fragment with:
- F(∃xφ) iff ∀x.Fφ — felicity is universal over witnesses (item 43)
- F(∀xφ) iff ∀x.Fφ — felicity is universal over witnesses (item 43)
- F(X≡φ) iff Fφ — labels don't affect felicity
- F(□φ) iff ∀w'.Fφ — felicity universal over accessible worlds (item 47)
- F(◇φ) iff ∀w'.Fφ — felicity universal over accessible worlds (item 47)

The universal quantification in the quantifier/modal felicity clauses is
the key insight: an expression is felicitous only if its presuppositions
are met for EVERY possible witness/world, not just some.
-/
def PIPExprF.felicitous {W D : Type*} [FiniteDomain D] [FiniteWorlds W] :
    PIPExprF W D → (W → Bool)
  -- F(P(α₁,...,αₙ)) = true (atoms are always felicitous)
  | .pred _ => λ _ => true
  -- F(φ ∧ ψ) iff Fφ ∧ (φ → Fψ)  [Karttunen's asymmetric conjunction]
  | .conj φ ψ => λ w => φ.felicitous w && ((φ.truth w).not || ψ.felicitous w)
  -- F(¬φ) iff Fφ
  | .neg φ => φ.felicitous
  -- F(φ ∨ ψ) iff Fφ ∧ (¬φ → Fψ)
  | .disj φ ψ => λ w => φ.felicitous w && (φ.truth w || ψ.felicitous w)
  -- F(φ → ψ) iff Fφ ∧ (φ → Fψ)
  | .impl φ ψ => λ w => φ.felicitous w && ((φ.truth w).not || ψ.felicitous w)
  -- F(φ|ψ) iff Fφ ∧ ψ  [presupposition must hold]
  | .presup φ ψ => λ w => φ.felicitous w && ψ w
  -- F(∃xφ) iff ∀x.Fφ  [felicity universal over witnesses, item 43]
  | .exists_ body => λ w => FiniteDomain.elements.all (λ d => (body d).felicitous w)
  -- F(∀xφ) iff ∀x.Fφ
  | .forall_ body => λ w => FiniteDomain.elements.all (λ d => (body d).felicitous w)
  -- F(X≡φ) iff Fφ  [labels don't affect felicity]
  | .labelDef _label φ => φ.felicitous
  -- F(□φ) iff ∀w'.Fφ  [item 47: felicity universal over accessible worlds]
  | .must R φ => λ w =>
      (FiniteWorlds.worlds.filter (R w)).all φ.felicitous
  -- F(◇φ) iff ∀w'.Fφ  [item 47: felicity universal, NOT existential]
  | .might R φ => λ w =>
      (FiniteWorlds.worlds.filter (R w)).all φ.felicitous


-- ============================================================
-- Label Extraction
-- ============================================================

/--
Extract all formula label definitions from an expression.

Since label definitions X ≡ φ are tautologies that float freely (paper §2.3),
we collect them regardless of their structural position (under negation,
modals, etc.). Returns a list of (label, sub-expression) pairs.
-/
def PIPExprF.labelDefs {W D : Type*} : PIPExprF W D → List (FLabel × PIPExprF W D)
  | .pred _ => []
  | .conj φ ψ => φ.labelDefs ++ ψ.labelDefs
  | .neg φ => φ.labelDefs
  | .disj φ ψ => φ.labelDefs ++ ψ.labelDefs
  | .impl φ ψ => φ.labelDefs ++ ψ.labelDefs
  | .presup φ _ => φ.labelDefs
  -- TODO: requires enumerating D; labels inside quantifier bodies
  -- are position-independent (float freely), so in principle we could
  -- collect from body applied to any single witness.
  | .exists_ _body => []
  | .forall_ _body => []
  | .labelDef α φ => (α, φ) :: φ.labelDefs
  | .must _ φ => φ.labelDefs
  | .might _ φ => φ.labelDefs


-- ============================================================
-- Derived Properties
-- ============================================================

section Properties

variable {W D : Type*} [FiniteDomain D] [FiniteWorlds W]

/-- F(¬φ) iff Fφ — negation preserves felicity. -/
theorem felicitousF_neg (φ : PIPExprF W D) (w : W) :
    (PIPExprF.neg φ).felicitous w = φ.felicitous w := rfl

/-- F(φ|ψ) iff Fφ ∧ ψ(w) — presupposition must hold. -/
theorem felicitousF_presup (φ : PIPExprF W D) (ψ : W → Bool) (w : W) :
    (PIPExprF.presup φ ψ).felicitous w = (φ.felicitous w && ψ w) := rfl

/-- F(X≡φ) iff Fφ — label definitions don't affect felicity. -/
theorem felicitousF_labelDef (α : FLabel) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.labelDef α φ).felicitous w = φ.felicitous w := rfl

/-- Presupposition truth-independence: φ|ψ is true iff φ is true. -/
theorem presupF_truth_independent (φ : PIPExprF W D) (ψ : W → Bool) (w : W) :
    (PIPExprF.presup φ ψ).truth w = φ.truth w := rfl

/-- Label definitions are truth-transparent: X≡φ is true iff φ is true. -/
theorem labelDef_truth_transparent (α : FLabel) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.labelDef α φ).truth w = φ.truth w := rfl

/-- Conjunction felicity is asymmetric (Karttunen). -/
theorem felicitousF_conj (φ ψ : PIPExprF W D) (w : W) :
    (PIPExprF.conj φ ψ).felicitous w =
    (φ.felicitous w && ((φ.truth w).not || ψ.felicitous w)) := rfl

/-- Existential felicity is universal over witnesses. -/
theorem felicitousF_exists (body : D → PIPExprF W D) (w : W) :
    (PIPExprF.exists_ body).felicitous w =
    FiniteDomain.elements.all (λ d => (body d).felicitous w) := rfl

/-- Modal necessity felicity is universal over accessible worlds. -/
theorem felicitousF_must (R : BAccessRel W) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.must R φ).felicitous w =
    (FiniteWorlds.worlds.filter (R w)).all φ.felicitous := rfl

end Properties


end Semantics.PIP
