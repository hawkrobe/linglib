import Linglib.Theories.Semantics.Exhaustification.Combinators

/-!
# Relevance-Sensitive Exhaustification (Magri 2009)
@cite{magri-2009}

@cite{magri-2009} parameterizes EXH by a contextual relevance relation
`R` on alternatives. Only alternatives that are *both* innocently
excludable and relevant get negated; irrelevant alternatives are silently
dropped.

## Design

Magri's operator is a one-line specialization of the post-exclusion
combinator `Excluder.restrict` defined in `Combinators.lean`:
`magri R := innocent.restrict R`. The combinator algebra (idempotence,
identity, monotonicity, the Fox–Katzir asymmetry theorem
`restrict_preserves_no_implicature`) lives in `Combinators.lean` so it
can be reused by other base excluders. This file holds only the
Magri-specific naming and corollaries.

This factoring is faithful to @cite{magri-2009} eq. (42), which writes
relevance as a side filter on the I-E set, and matches the way
@cite{fox-katzir-2011} treats the contextual constraint `C` as orthogonal
to the choice-of-alternatives problem solved by the structural source.
-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Magri 2009's relevance-sensitive operator: innocent exclusion filtered
    by a contextual relevance predicate on alternatives.

    @cite{magri-2009} eq. (42): `EXH_R(A)(p)(w) = p(w) ∧ ∀q ∈ I-E(p,A).
    (¬R(q) ∨ ¬q(w))`. Irrelevant alternatives drop out of the conjunction. -/
def magri (R : Finset W → Bool) : Excluder W := innocent.restrict R

/-- When every alternative is relevant, Magri's operator agrees with
    Fox's innocent exclusion. -/
theorem magri_const_true_eq_innocent :
    (magri (fun _ : Finset W => true) : Excluder W) = innocent :=
  Excluder.restrict_const_true _

/-- Relevance can only weaken `innocent.exh` (more worlds survive).
    Direct corollary of `Excluder.exh_subset_restrict_exh`. -/
theorem innocent_exh_subset_magri_exh (R : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    innocent.exh ALT φ ⊆ (magri R).exh ALT φ :=
  Excluder.exh_subset_restrict_exh _ _ _ _

end Exhaustification
