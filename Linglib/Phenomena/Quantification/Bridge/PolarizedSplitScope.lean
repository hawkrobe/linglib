import Linglib.Theories.Semantics.Lexical.Determiner.PolarizedIndividuals

/-!
# Split Scope via Polarized Individuals @cite{elliott-2026}

Bridge file connecting the polarized individual decomposition of
determiners (`Theories/Semantics/Lexical/Determiner/PolarizedIndividuals`)
to the empirical phenomenon of split scope.

## Split Scope

Split scope arises when a quantifier's restrictor and scope are
interpreted at different positions in the semantic derivation. The
classic case is negative quantifiers under modals:

  (1) You need to read no book.
      a. Surface: ¬∃x[book(x) ∧ need(read(x))]     — "no" takes wide scope
      b. Split:   need(¬∃x[book(x) ∧ read(x)])      — neg above, ∃ below

Reading (b) is the "split" reading: negation scopes above the modal
while the existential restrictor scopes below it.

## Lattice-Theoretic Analysis

Elliott (2026) derives split scope from the polarized individual
decomposition: `no` = `(⋁_e (e,+))ᶜ`. Since complement distributes
over scope position changes, the negative and existential components
can end up at different heights.

The key algebraic fact is `pos_sup_neg`:
`(e,+) ⊔ (e,-) = λR S. R(e)`
— the join of complementary polarities yields a quantifier that
ignores scope entirely (it only checks the restrictor).

## References

- Elliott, P. (2026). Determiners as Polarized Individuals.
- Rullmann, H. (1995). Maximality in the Semantics of Wh-Constructions.
- Penka, D. (2011). Negative Indefinites.
-/

namespace Phenomena.Quantification.Bridge.PolarizedSplitScope

open Core.Quantification
open Semantics.Lexical.Determiner.Polarized

variable {α : Type*}

-- ============================================================================
-- §1 — Split Scope: Complementary Polarities Cancel Scope
-- ============================================================================

/-- The fundamental split-scope fact: joining complementary polarities
    yields a GQ that depends only on the restrictor, not the scope.
    This means scope position is irrelevant — the quantifier "splits". -/
theorem split_scope_restrictor_only (e : α) (R S₁ S₂ : α → Bool) :
    (PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false)).1 R S₁ =
    (PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false)).1 R S₂ := by
  simp [split_scope]

/-- Corollary: split scope means the result equals `R(e)` regardless of
    what scope predicate is supplied. -/
theorem split_scope_eq_restrictor (e : α) (R S : α → Bool) :
    (PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false)).1 R S = R e := by
  simp [split_scope]

-- ============================================================================
-- §2 — Concrete Illustration: Split Negation
-- ============================================================================

/-- A negative quantifier `no(R,S) = ¬∃e. R(e) ∧ S(e)` decomposes as
    the complement of the join of positive polarized individuals.
    When scope splits, the complement applies at one position while
    the existential restrictor applies at another. -/
theorem no_from_complement_of_some (entities : List α) (R S : α → Bool) :
    Bool.not (entities.any (λ e => R e && S e)) =
    Bool.not (entities.any (λ e => PolInd.toGQ (e, true) R S)) := by
  congr 1; congr 1; ext e; simp

-- ============================================================================
-- §3 — Duality: Every from Not-Some-Not
-- ============================================================================

/-- `every` arises from the dual of `some`: outer + inner negation.
    With polarized individuals: `every(R,S) = ¬(⋁_e (e,-))(R,S)`,
    i.e., the complement of the join of negative polarized individuals.
    This decomposition parallels `no` but with reversed polarity. -/
theorem every_from_neg_polInd (entities : List α) (R S : α → Bool) :
    Bool.not (entities.any (λ e => PolInd.toGQ (e, false) R S)) =
    entities.all (λ e => Bool.not (R e) || S e) := by
  rw [← dual_some_eq_every]
  congr 1; congr 1; ext e; simp

end Phenomena.Quantification.Bridge.PolarizedSplitScope
