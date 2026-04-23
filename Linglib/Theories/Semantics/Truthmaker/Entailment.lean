import Linglib.Theories.Semantics.Truthmaker.Inexact
import Linglib.Theories.Semantics.Truthmaker.Closure

/-! # Analytic Entailment and Consequence Relations @cite{jago-2026}

Truthmaker semantics distinguishes several inequivalent notions of
consequence (@cite{jago-2026}):

- **Exact entailment** `p ⊨ₑ q`: every exact verifier of `p` also
  exactly verifies `q`. Hyperintensional — sensitive to subject-matter.
- **Inexact entailment** `p ⊨ᵢ q`: every inexact verifier of `p` also
  inexactly verifies `q`. Coarser than exact entailment. On basic
  models @cite{jago-2026} reports a coincidence with **FDE**
  (@cite{vanfraassen-1969}); FDE is not formalized in linglib, so
  this bridge is documented externally rather than proved here.
- **Analytic / Angellic entailment (AC)** `p ≼ q`: corresponds to
  *content containment* — `p`'s content contains `q`'s content. This is
  the system of @cite{jago-2026} (Fine 2016 *Angellic content*) and is
  the natural truthmaker home for the law of conjunction elimination
  without disjunction introduction (`p ∧ q ⊢ p` but ⊬ `p ⊢ p ∨ q`).

This file:

- defines analytic entailment via the bilateral conjunctive parthood
  `IsContentPart` (Up + Down) on `TMProp`;
- proves the basic chain `(p ⊨ₑ q ∧ q ⊨ₑ p) → (p ≼ q) → (p ⊨ᵢ q)`;
- exhibits the **conjunction-elimination** / **disjunction-introduction**
  asymmetry that distinguishes truthmaker logic from
  classical/intuitionistic/relevant.

## Cross-framework convergence

`AlternativeSensitive.IsTruthmaker p S` (`Theories/Semantics/Conditionals/`)
is the **world-extensional** truthmaker of @cite{santorio-2018}. Modulo
the Bool-vs-Prop adapter, it is exactly `ExactEntails` here:
`IsTruthmaker p S = (p · = true) ⊨ₑ (S · = true)`. It does **not**
correspond to `IsContentPart` (= `AnalyticEntails`); the Up clause and
mereological parthood are exactly what the world-extensional notion drops.

`Theories/Semantics/Attitudes/Doxastic.lean`'s Hintikka `boxAt` is
∀-over-accessible-worlds; truthmaker `attHolds` (`Basic.lean`) is
∃-verifier-part-of-info-state. The empirical heart of
@cite{bondarenko-elliott-2026} is exactly this divergence: `attHolds`
distinguishes hyperintensional content (witness: the headline theorem
`subjectMatter_distinguishes_classically_equivalent` in `Basic.lean`),
which `boxAt` cannot.

-/

namespace Semantics.Truthmaker


-- ════════════════════════════════════════════════════
-- § 1. Analytic Entailment (AC)
-- ════════════════════════════════════════════════════

section Analytic
variable {S : Type*} [Preorder S]

/-- **Analytic entailment** (AC, @cite{jago-2026} after Fine 2016):
    `p ≼ q` iff `q` is a content part of `p` — the Down clause says
    every verifier of `p` has a part verifying `q`, and the Up clause
    says every verifier of `q` is part of some verifier of `p`. This is
    `IsContentPart q p` (Up + Down). -/
def AnalyticEntails (p q : TMProp S) : Prop :=
  IsContentPart q p

/-- Notation: `p ≼ q` for analytic entailment. -/
scoped infix:50 " ≼ " => AnalyticEntails

namespace AnalyticEntails

@[refl] theorem refl (p : TMProp S) : p ≼ p := Mereology.IsContentPart.refl p

theorem trans {p q r : TMProp S} (hpq : p ≼ q) (hqr : q ≼ r) : p ≼ r :=
  -- hpq : q is content part of p; hqr : r is content part of q.
  -- Want: r is content part of p. Compose: r ⊑ q ⊑ p (both clauses).
  Mereology.IsContentPart.trans hqr hpq

end AnalyticEntails

end Analytic

-- ════════════════════════════════════════════════════
-- § 2. Bridges between consequence relations
-- ════════════════════════════════════════════════════

section Bridges
variable {S : Type*} [Preorder S]

/-- **Inexact entailment from analytic entailment**: `p ≼ q → p ⊨ᵢ q`.

    From the **Down** clause of `IsContentPart q p` (= `p ≼ q`): every
    `p`-verifier has a `q`-part. So an inexact `p`-verifier `s`
    (with some `u ≤ s` such that `p u`) yields a `q`-part `t ≤ u ≤ s`,
    witnessing the inexact verification of `q`. -/
theorem InexactEntails.of_analytic {p q : TMProp S} (h : p ≼ q) :
    p ⊨ᵢ q := by
  intro s ⟨u, hule, hp⟩
  obtain ⟨t, hqt, htle⟩ := h.1 u hp
  exact ⟨t, le_trans htle hule, hqt⟩

/-- Mutual exact entailment lifts to analytic entailment. The Up clause
    needs the converse direction `q ⊨ₑ p` to find an extension witness
    inside `p` for each `q`-verifier; with both directions the relation
    becomes essentially propositional equality on verifier-sets, which
    trivially satisfies both clauses with self as witness. -/
theorem AnalyticEntails.of_exact_of_subset {p q : TMProp S}
    (hpq : p ⊨ₑ q) (hqp : q ⊨ₑ p) : p ≼ q :=
  ⟨fun s hp => ⟨s, hpq s hp, le_refl s⟩,
   fun s hq => ⟨s, hqp s hq, le_refl s⟩⟩

end Bridges

-- ════════════════════════════════════════════════════
-- § 3. Conjunction Elimination ≠ Disjunction Introduction
-- ════════════════════════════════════════════════════

section ConjDisj
variable {S : Type*} [SemilatticeSup S]

/-- **Conjunction elimination** holds at the `IsSubsumedBy` (Down) level
    unconditionally: `p ∧ q` is subsumed by `p`. (Re-export of
    `IsSubsumedBy.tmAnd_left` for clarity in the entailment context.) -/
theorem isSubsumedBy_tmAnd_left_AC (p q : TMProp S) :
    IsSubsumedBy p (tmAnd p q) :=
  IsSubsumedBy.tmAnd_left p q

end ConjDisj

/-- **Disjunction introduction is NOT a content-part relation**:
    `p` does not in general subsume `p ∨ q`. A verifier of `p ∨ q` that
    only verifies `q` need not have a part verifying `p`.

    This is the @cite{jago-2026} headline distinction: classical,
    intuitionistic, and relevant logics all collapse `p ∨ (p ∧ q) ≡ p`
    in some directions, conflating containment-respecting and
    containment-violating consequence. Truthmaker semantics keeps the
    asymmetry — enabling a logic of containment that supports
    conjunction elimination without supporting disjunction introduction.

    Witness: `S = Bool` with `p = (· = true)` and `q = (· = false)`.
    `false` verifies `tmOr p q` (via the right disjunct), but the only
    `p`-state is `true`, and `true ≰ false` in the Bool ordering.

    NB: this differs from `isSubsumedBy_or_not_general` in `Basic.lean`
    (which tested whether `q` is subsumed by `tmOr p q`); here we test
    the *introduction* direction. -/
theorem not_isSubsumedBy_tmOr_intro_general :
    ¬ (∀ (S : Type) (_ : SemilatticeSup S) (p q : TMProp S),
       IsSubsumedBy p (tmOr p q)) := by
  intro h
  have := h Bool inferInstance (· = true) (· = false)
  obtain ⟨t, ht, hle⟩ := this false (Or.inr rfl)
  -- ht : t = true, hle : t ≤ false. Subst and contradict.
  cases ht
  exact absurd hle (by decide)

end Semantics.Truthmaker
