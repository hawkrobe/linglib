import Linglib.Core.Logic.PolarizedIndividuals

/-!
# Determiners via Polarized Individuals @cite{elliott-2026}

Connects standard quantifier denotations to the polarized individual
decomposition from `Core.Logic.PolarizedIndividuals`.

The four corners of the square of opposition arise from entity-polarity
pairs via the `ConsGQ` Boolean algebra:

- `some  = ⋁_e (e, +)`        — existential: at least one positive witness
- `every = (⋁_e (e, -))ᶜ`     — universal: no negative witness
- `no    = (⋁_e (e, +))ᶜ`     — negative universal: no positive witness
- `not_all = ⋁_e (e, -)`      — negative existential: at least one negative

The key compositional fact for split scope (PR 4) is `pos_sup_neg`:
`(e,+) ⊔ (e,-) = λR S. R(e)`, already proved in
`Core.Logic.PolarizedIndividuals`.

## References

- Elliott, P. (2026). Determiners as Polarized Individuals.
- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
-/

namespace Semantics.Lexical.Determiner.Polarized

open Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §1 — Quantifiers as PolInd Joins (Concrete, Finite Domain)
-- ============================================================================

/-- On a concrete list of entities, `some(R,S) = ⋁_e R(e) ∧ S(e)`,
    which is the join of positive polarized individuals. -/
theorem some_as_polInd_join (entities : List α) (R S : α → Bool) :
    entities.any (λ e => R e && S e) =
    entities.any (λ e => PolInd.toGQ (e, true) R S) := by
  congr 1; ext e; simp

/-- On a concrete list of entities, `no(R,S) = ⋀_e ¬(R(e) ∧ S(e))`,
    which is the meet of complements of positive polarized individuals. -/
theorem no_as_polInd_neg (entities : List α) (R S : α → Bool) :
    entities.all (λ e => !R e || !S e) =
    entities.all (λ e => !PolInd.toGQ (e, true) R S) := by
  congr 1; ext e; simp

/-- On a concrete list, `every(R,S) = ⋀_e ¬(R(e) ∧ ¬S(e))`,
    which is the meet of complements of negative polarized individuals. -/
theorem every_as_polInd_neg (entities : List α) (R S : α → Bool) :
    entities.all (λ e => !R e || S e) =
    entities.all (λ e => !PolInd.toGQ (e, false) R S) := by
  congr 1; ext e; simp [Bool.not_not]

-- ============================================================================
-- §2 — Inner Negation Swaps Polarity
-- ============================================================================

/-- Inner negation (negating the scope) swaps the polarity of a
    polarized individual: `⟦(e,+)⟧(R, ¬S) = ⟦(e,-)⟧(R, S)`. -/
theorem inner_neg_swaps_polarity (e : α) (R S : α → Bool) :
    PolInd.toGQ (e, true) R (λ x => !S x) =
    PolInd.toGQ (e, false) R S := by
  simp

/-- Inner negation on a quantifier built from positive PolInds yields
    the corresponding negative-PolInd quantifier. -/
theorem inner_neg_pos_list_eq_neg_list (entities : List α) (R S : α → Bool) :
    entities.any (λ e => PolInd.toGQ (e, true) R (λ x => !S x)) =
    entities.any (λ e => PolInd.toGQ (e, false) R S) := by
  congr 1; ext e; exact inner_neg_swaps_polarity e R S

-- ============================================================================
-- §3 — Complement and the Duality Square
-- ============================================================================

/-- Outer negation (negating the result) + inner negation (negating the
    scope) = dual. Applied to `some`, this gives `every`:
    `¬some(R, ¬S) = every(R, S)`. -/
private theorem not_any_eq_all_not {β : Type*} :
    ∀ (l : List β) (f g : β → Bool),
    (∀ x, g x = Bool.not (f x)) → Bool.not (l.any f) = l.all g
  | [], _, _, _ => rfl
  | a :: t, f, g, h => by
    show Bool.not (f a || t.any f) = (g a && t.all g)
    rw [Bool.not_or, h a, not_any_eq_all_not t f g h]

theorem dual_some_eq_every (entities : List α) (R S : α → Bool) :
    Bool.not (entities.any (λ e => R e && Bool.not (S e))) =
    entities.all (λ e => Bool.not (R e) || S e) :=
  not_any_eq_all_not _ _ _ (λ e => by cases R e <;> cases S e <;> rfl)

/-- Outer negation of `some` = `no`: `¬(∃e. R(e) ∧ S(e)) = ∀e. R(e) → ¬S(e)`. -/
theorem outer_neg_some_eq_no (entities : List α) (R S : α → Bool) :
    Bool.not (entities.any (λ e => R e && S e)) =
    entities.all (λ e => Bool.not (R e) || Bool.not (S e)) :=
  not_any_eq_all_not _ _ _ (λ e => by cases R e <;> cases S e <;> rfl)

-- ============================================================================
-- §4 — Split Scope via PolInd Complementarity
-- ============================================================================

/-- The split scope reading: `(e,+) ⊔ (e,-) = λR S. R(e)`.
    Re-exported from `Core.Logic.PolarizedIndividuals` for convenience.
    This is the lattice-theoretic content of split scope: scope is
    "split" between the positive and negative polarities, yielding a
    quantifier that ignores scope entirely. -/
theorem split_scope (e : α) :
    PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false) =
    (⟨λ R _ => R e, λ R _ => by simp⟩ : ConsGQ α) :=
  PolInd.pos_sup_neg e

end Semantics.Lexical.Determiner.Polarized
