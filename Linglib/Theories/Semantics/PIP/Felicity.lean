import Linglib.Theories.Semantics.PIP.Expr

/-!
# PIP Felicity Conditions (Propositional Fragment)

@cite{keshet-abney-2024} @cite{karttunen-1973}

PIP separates **truth conditions** from **felicity conditions**. Truth is
classical (predicate calculus + set abstraction). Felicity is a separate
recursive predicate F that determines whether presuppositions are met.

This file provides:
1. An inductive `PIPExpr` type representing PIP's **propositional** fragment
2. A recursive `felicitous` function implementing the F operator
3. The key derived theorems from the paper (items 41–42, 44–45c)

## Relationship to `PIP.Expr`

`PIPExprF W D` in `Expr.lean` is the **full** PIP expression type with
quantifiers (`∃x`, `∀x`), modals (`□`, `◇`), label definitions, and
summation. It defines its own `truth` and `felicitous` functions covering
all constructors, including the quantifier felicity clauses (items 43,
47a-d). The propositional `PIPExpr W` here is the restriction to `D = Empty`.
`embedProp` in `Expr.lean` witnesses this embedding.

## The F Operator (Propositional)

F is defined recursively on the structure of PIP expressions.
This file covers the propositional fragment (items 40–42, 44–45c):

| Expression | Felicity condition |
|------------|-------------------|
| φ\|ψ | Fφ ∧ ψ |
| φ ∧ ψ | Fφ ∧ (φ → Fψ) |
| ¬φ | Fφ |
| P(α₁,...,αₙ) | true |

The full quantifier/modal clauses are in `PIPExprF.felicitous` (`Expr.lean`):
- F(∃xφ) iff ∀x.Fφ — felicity universal over witnesses (item 43)
- F(□φ) iff ∀w'.Fφ — felicity universal over accessible worlds (item 47)

The asymmetric conjunction clause (Karttunen's insight) allows the first
conjunct to satisfy presuppositions of the second. This is what makes
"France has a king and the king of France is bald" felicitous.

## Incremental Discourse Felicity

Adding sentence φ to a felicitous discourse γ requires:

  ∀w x (γ → Fφ)

where x ranges over the combined local variables of γ and φ. This
condition ensures that the presuppositions of φ are met in every
world and assignment consistent with γ.

-/

namespace Semantics.PIP.Felicity

variable {W : Type*}


-- ============================================================
-- PIP Expression Language (Static)
-- ============================================================

/--
PIP expressions: the static formula language.

This represents PIP formulas as a data type, enabling recursive
definition of truth and felicity conditions. Each propositional PIP
construct has a constructor.

**Quantifiers omitted.** The paper's ∃x, ∀x, Σx quantify over a domain of
individuals D (paper items 43, 47a-d). A correct encoding requires a separate
domain parameter `D` and `body : D → PIPExpr W`, with:
- F(∃xφ) iff ∀d:D, F(body d)     — felicity universal over witnesses
- T(∃xφ) iff ∃d:D, T(body d)     — truth existential
The propositional fragment (pred, conj, neg, disj, impl, presup) is complete
and correctly implements the F operator for items 41–42, 44–45c.
-/
inductive PIPExpr (W : Type*) where
  /-- Atomic predicate: P_w(x₁, ..., xₙ). Always felicitous. -/
  | pred (p : W → Bool)
  /-- Conjunction: φ ∧ ψ. Felicity is asymmetric (Karttunen). -/
  | conj (φ ψ : PIPExpr W)
  /-- Negation: ¬φ. Felicity passes through. -/
  | neg (φ : PIPExpr W)
  /-- Disjunction: φ ∨ ψ. -/
  | disj (φ ψ : PIPExpr W)
  /-- Implication: φ → ψ. -/
  | impl (φ ψ : PIPExpr W)
  /-- Presupposition: φ|ψ. Assert φ, presuppose ψ. -/
  | presup (φ : PIPExpr W) (ψ : W → Bool)


-- ============================================================
-- Truth Conditions (Classical)
-- ============================================================

/--
Truth evaluation for PIP expressions.

PIP truth conditions are classical: presuppositions play no role
in determining truth values. φ|ψ is true iff φ is true.
-/
def PIPExpr.truth : PIPExpr W → (W → Bool)
  | .pred p => p
  | .conj φ ψ => λ w => φ.truth w && ψ.truth w
  | .neg φ => λ w => (φ.truth w).not
  | .disj φ ψ => λ w => φ.truth w || ψ.truth w
  | .impl φ ψ => λ w => (φ.truth w).not || ψ.truth w
  | .presup φ _ψ => φ.truth  -- presupposition doesn't affect truth


-- ============================================================
-- Felicity Conditions (The F Operator)
-- ============================================================

/--
The F operator: recursive presuppositional felicity.

This is the core of PIP's analysis of intensional anaphora.
F determines whether a PIP expression is felicitous (well-defined)
relative to a world w. Every failure of F traces to a presupposition
violation.
-/
def PIPExpr.felicitous : PIPExpr W → (W → Bool)
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


-- ============================================================
-- Derived Properties (Paper items 41–42, 44–45c)
-- ============================================================

/-- F(¬φ) iff Fφ (paper item 45c) -/
theorem felicitous_neg (φ : PIPExpr W) (w : W) :
    (PIPExpr.neg φ).felicitous w = φ.felicitous w := rfl

/-- F(φ|ψ) iff Fφ ∧ ψ(w) (paper item 41) -/
theorem felicitous_presup (φ : PIPExpr W) (ψ : W → Bool) (w : W) :
    (PIPExpr.presup φ ψ).felicitous w = (φ.felicitous w && ψ w) := rfl

/-- Presupposition truth-independence: φ|ψ is true iff φ is true -/
theorem presup_truth_independent (φ : PIPExpr W) (ψ : W → Bool) (w : W) :
    (PIPExpr.presup φ ψ).truth w = φ.truth w := rfl

/-- Conjunction felicity is asymmetric (paper item 42, @cite{karttunen-1973}):
    the first conjunct can satisfy presuppositions of the second. -/
theorem felicitous_conj (φ ψ : PIPExpr W) (w : W) :
    (PIPExpr.conj φ ψ).felicitous w =
    (φ.felicitous w && ((φ.truth w).not || ψ.felicitous w)) := rfl

/-- If the first conjunct is true and both are felicitous,
    the conjunction is felicitous. -/
theorem felicitous_conj_of_both (φ ψ : PIPExpr W) (w : W)
    (hFφ : φ.felicitous w = true)
    (hFψ : ψ.felicitous w = true) :
    (PIPExpr.conj φ ψ).felicitous w = true := by
  unfold PIPExpr.felicitous
  rw [hFφ, hFψ]; simp

/-- If the first conjunct is false, its felicity suffices for the conjunction. -/
theorem felicitous_conj_of_false_first (φ ψ : PIPExpr W) (w : W)
    (hFφ : φ.felicitous w = true)
    (hTφ : φ.truth w = false) :
    (PIPExpr.conj φ ψ).felicitous w = true := by
  rw [felicitous_conj, hFφ, hTφ]; simp


-- ============================================================
-- Discourse Felicity
-- ============================================================

/--
A discourse (conjunction of sentences) is felicitous when the
felicity conditions are met at every world in the context set.

This captures the paper's item 40: F(Σw(φ₁ ∧ ... ∧ φₙ))
-/
def discourseFelicitous (φ : PIPExpr W) (contextSet : W → Bool) : Prop :=
  ∀ w, contextSet w = true → φ.felicitous w = true

/--
Incremental felicity: adding sentence ψ to a felicitous discourse φ
requires that ψ's presuppositions are met whenever φ is true.

This captures the paper's item 51: ∀wxy(γ → Fφ)
-/
def incrementallyFelicitous (γ ψ : PIPExpr W) : Prop :=
  ∀ w, γ.truth w = true → ψ.felicitous w = true


-- ============================================================
-- Intensional Anaphora: Might vs Must
-- ============================================================

/--
The existential presupposition of pronouns.

A pronoun presupposes that its denotation is non-empty (and singular
for singular pronouns). In PIP, this is modeled as a presupposition
on the summation term: SINGLE(Σxφ).
-/
def singlePresup (denotation : W → Bool) : PIPExpr W :=
  .presup (.pred (λ _ => true)) denotation

/--
Might blocks anaphora: might(φ) does not guarantee that the
antecedent description is non-empty at every world in the context set.

If might(φ) is true at w, there exists an accessible w' where φ holds,
but φ may be false at w itself. A pronoun referring to an entity
introduced by φ will have an empty denotation at w, causing
presupposition failure.
-/
theorem might_blocks_anaphora
    (φ_accessible : W → Bool)     -- φ holds at some accessible worlds
    (pronoun_presup : W → Bool)   -- pronoun presupposes entity exists
    (w : W)
    (h_might : φ_accessible w = false)   -- φ doesn't hold at w itself
    (h_presup_needs : pronoun_presup w = φ_accessible w) :
    (singlePresup pronoun_presup).felicitous w = false := by
  unfold singlePresup
  show (true && pronoun_presup w) = false
  rw [h_presup_needs, h_might]; rfl

/--
Must allows anaphora: if must(φ) is true at w (with a realistic
modal base), then φ holds at w (since w is accessible from itself).
The pronoun's presupposition is satisfied.
-/
theorem must_allows_anaphora
    (φ_everywhere : W → Bool)     -- φ holds at all accessible worlds
    (pronoun_presup : W → Bool)   -- pronoun presupposes entity exists
    (w : W)
    (h_must_realistic : φ_everywhere w = true)  -- realistic: w is accessible from w
    (h_presup_follows : pronoun_presup w = φ_everywhere w) :
    (singlePresup pronoun_presup).felicitous w = true := by
  unfold singlePresup
  show (true && pronoun_presup w) = true
  rw [h_presup_follows, h_must_realistic]; rfl


end Semantics.PIP.Felicity
