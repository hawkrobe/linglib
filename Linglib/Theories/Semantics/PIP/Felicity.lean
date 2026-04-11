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
quantifiers (`∃x`, `∀x`), modals (`□`, `◇`), and label definitions.
It defines its own `truth` and `felicitous` functions covering all
constructors, including the quantifier felicity clauses (items 35, 39d).
The propositional `PIPExpr W` here is the restriction to `D = Empty`.

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


-- ============================================================
-- Full PIPExprF Felicity: Quantifier/Modal Projection (§2.4.4)
-- ============================================================

/-!
### Quantifier and Modal Felicity Projection

@cite{abney-keshet-2025}

The full `PIPExprF` type (Expr.lean) extends the propositional fragment
with quantifiers and modals. Its `felicitous` function implements
the paper's key design: **felicity projects universally** through
both quantifiers and modals, while truth projects existentially or
universally as usual. This asymmetry is PIP's mechanism for
presupposition projection.

The felicity clauses (in `PIPExprF.felicitous`):
- F(∃xφ) = ∀x.Fφ — universal over witnesses (item 39d)
- F(∀xφ) = ∀x.Fφ — (item 35)
- F(□φ) = ∀w'.Fφ — universal over accessible worlds
- F(◇φ) = ∀w'.Fφ — ALSO universal (truth differs: existential)

This section derives:
1. **Prop-level iff characterizations** for each clause
2. **Factored presupposition projection** — the strongest form: a
   presupposition under a universally-felicitous operator factors out
   of the universal check. This is an instance of `forall_and_right`
   (quantifiers, uniform ψ, requires `Nonempty D`) or `forall_and`
   (modals, world-varying ψ, unconditional).
3. **One-directional extraction** as corollaries
-/

section FullFelicity

open Core.Proposition (FiniteWorlds)
open Core.ModalLogic (AccessRel)

variable {W D : Type*} [FiniteDomain D] [FiniteWorlds W]


-- ======== Prop-level iff characterizations ========

/-- F(∃xφ) iff ∀d, F(φ(d)) — existential felicity is universal
    over the domain (item 39d). -/
theorem existsF_felicitous_iff (body : D → PIPExprF W D) (w : W) :
    (PIPExprF.exists_ body).felicitous w = true ↔
    ∀ d, (body d).felicitous w = true := by
  simp only [PIPExprF.felicitous]
  constructor
  · intro h d; exact List.all_eq_true.mp h d (FiniteDomain.complete d)
  · intro h; exact List.all_eq_true.mpr (λ d _ => h d)

/-- F(∀xφ) iff ∀d, F(φ(d)) (item 35). -/
theorem forallF_felicitous_iff (body : D → PIPExprF W D) (w : W) :
    (PIPExprF.forall_ body).felicitous w = true ↔
    ∀ d, (body d).felicitous w = true := by
  simp only [PIPExprF.felicitous]
  constructor
  · intro h d; exact List.all_eq_true.mp h d (FiniteDomain.complete d)
  · intro h; exact List.all_eq_true.mpr (λ d _ => h d)

/-- ∃ and ∀ have identical felicity clauses — both project universally.
    The difference is only in truth conditions (∃ vs ∀). -/
theorem existsF_forallF_felicity_agree (body : D → PIPExprF W D) (w : W) :
    (PIPExprF.exists_ body).felicitous w =
    (PIPExprF.forall_ body).felicitous w := rfl

/-- F(□_R φ) iff φ is felicitous at every R-accessible world. -/
theorem mustF_felicitous_iff (R : AccessRel W) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.must R φ).felicitous w = true ↔
    ∀ w', R w w' = true → φ.felicitous w' = true := by
  simp only [PIPExprF.felicitous]
  constructor
  · intro h w' hw'
    exact List.all_eq_true.mp h w'
      (List.mem_filter.mpr ⟨FiniteWorlds.complete w', hw'⟩)
  · intro h
    exact List.all_eq_true.mpr (λ w' hw' => h w' (List.mem_filter.mp hw').2)

/-- F(◇_R φ) iff φ is felicitous at every R-accessible world.
    Truth is existential for ◇ but felicity is universal for both. -/
theorem mightF_felicitous_iff (R : AccessRel W) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.might R φ).felicitous w = true ↔
    ∀ w', R w w' = true → φ.felicitous w' = true := by
  simp only [PIPExprF.felicitous]
  constructor
  · intro h w' hw'
    exact List.all_eq_true.mp h w'
      (List.mem_filter.mpr ⟨FiniteWorlds.complete w', hw'⟩)
  · intro h
    exact List.all_eq_true.mpr (λ w' hw' => h w' (List.mem_filter.mp hw').2)

/-- □ and ◇ have identical felicity clauses — both project universally.
    The asymmetry between must and might is in truth, not felicity. -/
theorem mustF_mightF_felicity_agree (R : AccessRel W) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.must R φ).felicitous w =
    (PIPExprF.might R φ).felicitous w := rfl


-- ======== Factored presupposition projection (strongest form) ========

/--
Factored projection through ∃: a uniform presupposition ψ factors out
of the universal felicity check.

  F(∃x(φ(x)|ψ)) ↔ (∀d, F(φ(d))) ∧ ψ

This is the strongest form of quantifier presupposition projection.
`Nonempty D` is required: if D is empty, the LHS is vacuously true
regardless of ψ (no witnesses to check), so the → direction fails.

Mathematically, this is `forall_and_right` (Mathlib): the presupposition
ψ doesn't vary with d, so it factors out of `∀d, (F(φ(d)) ∧ ψ)`.
-/
theorem existsF_presup_factored [Nonempty D]
    (φ : D → PIPExprF W D) (ψ : W → Bool) (w : W) :
    (PIPExprF.exists_ (λ d => PIPExprF.presup (φ d) ψ)).felicitous w = true ↔
    (∀ d, (φ d).felicitous w = true) ∧ ψ w = true := by
  rw [existsF_felicitous_iff]
  simp only [PIPExprF.felicitous, Bool.and_eq_true]
  exact forall_and_right _ _

/-- Factored projection through ∀ — identical to ∃ since both have
    the same felicity clause. -/
theorem forallF_presup_factored [Nonempty D]
    (φ : D → PIPExprF W D) (ψ : W → Bool) (w : W) :
    (PIPExprF.forall_ (λ d => PIPExprF.presup (φ d) ψ)).felicitous w = true ↔
    (∀ d, (φ d).felicitous w = true) ∧ ψ w = true := by
  rw [forallF_felicitous_iff]
  simp only [PIPExprF.felicitous, Bool.and_eq_true]
  exact forall_and_right _ _

/--
Factored projection through □: presupposition ψ and body felicity
separate into independent universal checks over accessible worlds.

  F(□(φ|ψ)) ↔ (∀w', R w w' → F(φ)(w')) ∧ (∀w', R w w' → ψ(w'))

No `Nonempty` hypothesis needed: ψ varies with w', so this is a
direct instance of `∀x, (P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x)`.
-/
theorem mustF_presup_factored
    (R : AccessRel W) (φ : PIPExprF W D) (ψ : W → Bool) (w : W) :
    (PIPExprF.must R (PIPExprF.presup φ ψ)).felicitous w = true ↔
    (∀ w', R w w' = true → φ.felicitous w' = true) ∧
    (∀ w', R w w' = true → ψ w' = true) := by
  rw [mustF_felicitous_iff]
  simp only [PIPExprF.felicitous, Bool.and_eq_true]
  exact ⟨fun h => ⟨fun w' hw' => (h w' hw').1, fun w' hw' => (h w' hw').2⟩,
         fun ⟨h1, h2⟩ w' hw' => ⟨h1 w' hw', h2 w' hw'⟩⟩

/-- Factored projection through ◇ — identical structure to □. -/
theorem mightF_presup_factored
    (R : AccessRel W) (φ : PIPExprF W D) (ψ : W → Bool) (w : W) :
    (PIPExprF.might R (PIPExprF.presup φ ψ)).felicitous w = true ↔
    (∀ w', R w w' = true → φ.felicitous w' = true) ∧
    (∀ w', R w w' = true → ψ w' = true) := by
  rw [mightF_felicitous_iff]
  simp only [PIPExprF.felicitous, Bool.and_eq_true]
  exact ⟨fun h => ⟨fun w' hw' => (h w' hw').1, fun w' hw' => (h w' hw').2⟩,
         fun ⟨h1, h2⟩ w' hw' => ⟨h1 w' hw', h2 w' hw'⟩⟩


-- ======== Extraction corollaries ========

/-- Presupposition extraction through ∃: if ∃x(φ(x)|ψ) is felicitous,
    then ψ holds. Follows from the factored form by projecting `.2`. -/
theorem existsF_presup_projection
    (φ : D → PIPExprF W D) (ψ : W → Bool) (w : W) (d : D)
    (hF : (PIPExprF.exists_ (λ d => PIPExprF.presup (φ d) ψ)).felicitous w = true) :
    ψ w = true :=
  haveI : Nonempty D := ⟨d⟩
  (existsF_presup_factored φ ψ w).mp hF |>.2

/-- Presupposition extraction through ∀. -/
theorem forallF_presup_projection
    (φ : D → PIPExprF W D) (ψ : W → Bool) (w : W) (d : D)
    (hF : (PIPExprF.forall_ (λ d => PIPExprF.presup (φ d) ψ)).felicitous w = true) :
    ψ w = true :=
  haveI : Nonempty D := ⟨d⟩
  (forallF_presup_factored φ ψ w).mp hF |>.2

/-- Presupposition extraction through □ at an accessible world. -/
theorem mustF_presup_at_accessible
    (R : AccessRel W) (φ : PIPExprF W D) (ψ : W → Bool) (w w' : W)
    (hR : R w w' = true)
    (hF : (PIPExprF.must R (PIPExprF.presup φ ψ)).felicitous w = true) :
    ψ w' = true :=
  (mustF_presup_factored R φ ψ w).mp hF |>.2 w' hR

/-- Presupposition extraction through ◇ at an accessible world. -/
theorem mightF_presup_at_accessible
    (R : AccessRel W) (φ : PIPExprF W D) (ψ : W → Bool) (w w' : W)
    (hR : R w w' = true)
    (hF : (PIPExprF.might R (PIPExprF.presup φ ψ)).felicitous w = true) :
    ψ w' = true :=
  (mightF_presup_factored R φ ψ w).mp hF |>.2 w' hR


-- ======== Sigma body felicity (item 39f) ========

/-- Sigma body felicity: for Σxφ to appear felicitously in a discourse,
    φ must be felicitous for every witness d. This is item (39f) in the
    common case with no additional local variables. Since `sigmaEval`
    (Composition.lean) takes the same body type `D → PIPExprF W D` as
    `∃`, sigma felicity reduces to existential felicity. -/
theorem sigma_body_felicitous_iff (body : D → PIPExprF W D) (w : W) :
    (∀ d, (body d).felicitous w = true) ↔
    (PIPExprF.exists_ body).felicitous w = true :=
  (existsF_felicitous_iff body w).symm

end FullFelicity


end Semantics.PIP.Felicity
