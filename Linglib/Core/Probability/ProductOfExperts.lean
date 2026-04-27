import Linglib.Core.Probability.PMFPosterior

/-!
# Product of Experts on `PMF`
@cite{hinton-2002} @cite{erk-herbelot-2024}

Combine two PMFs over the same type by pointwise multiplication followed
by renormalisation. Symmetric in the two factors. Used in product-of-experts
neural-network models (@cite{hinton-2002}) and in distributional semantics
when fusing concept-cue and context-cue distributions
(@cite{erk-herbelot-2024} fn 10).

PoE is **not** a posterior — there is no observation, no kernel, no
direction. It is the symmetric pointwise product of two PMFs over a shared
type, which is why this construction lives in its own file rather than in
`PMFPosterior.lean`.

The construction factors through `PMF.reweight` (defined in
`PMFPosterior.lean`): `productOfExperts p q = p.reweight q`.

## Main definitions

* `PMF.productOfExperts p q h_pos` — `(p × q) / Z` where `Z = ∑' a, p a * q a`.

## Main theorems

* `productOfExperts_apply` — explicit formula.
* `productOfExperts_comm` — symmetry in the two factors.
* `mem_support_productOfExperts_iff` — support is the intersection of the
  factor supports (the disjoint-supports caveat of @cite{erk-herbelot-2024} fn 10).
-/

set_option autoImplicit false

open scoped ENNReal

namespace PMF

variable {α : Type*}

/-- Product of Experts: combine two PMFs over the same type by multiplying
mass at each point and renormalising. Symmetric in `p`, `q`. The crucial
precondition (paper @cite{erk-herbelot-2024} fn 10): at least one point
must have non-zero mass under both factors. -/
noncomputable def productOfExperts (p q : PMF α)
    (h_pos : (∑' a, p a * q a) ≠ 0) : PMF α :=
  p.reweight (fun a => q a) h_pos
    (by
      apply ne_of_lt
      calc (∑' a, p a * q a)
          ≤ ∑' a, p a := ENNReal.tsum_le_tsum (fun a => by
            calc p a * q a ≤ p a * 1 := mul_le_mul_right (PMF.coe_le_one _ _) _
              _ = p a := mul_one _)
        _ = 1 := PMF.tsum_coe p
        _ < ∞ := ENNReal.one_lt_top)

-- Not `@[simp]`: introduces `(∑' x, ...)⁻¹`; use explicitly via `rw`.
theorem productOfExperts_apply (p q : PMF α) (h_pos : (∑' a, p a * q a) ≠ 0) (a : α) :
    p.productOfExperts q h_pos a = p a * q a * (∑' x, p x * q x)⁻¹ :=
  reweight_apply _ _ _ _ _

/-- PoE is commutative in the two factors (modulo the positivity hypothesis,
which is itself symmetric). -/
theorem productOfExperts_comm (p q : PMF α) (h : (∑' a, p a * q a) ≠ 0) :
    p.productOfExperts q h = q.productOfExperts p (by simpa [mul_comm] using h) := by
  ext a
  simp only [productOfExperts_apply, mul_comm (p a) (q a)]
  congr 1
  exact congr_arg _ (tsum_congr fun a => mul_comm _ _)

/-- PoE support: points with non-zero mass under both factors. The formal
content of @cite{erk-herbelot-2024} fn 10's caveat about disjoint supports. -/
theorem mem_support_productOfExperts_iff (p q : PMF α)
    (h : (∑' a, p a * q a) ≠ 0) (a : α) :
    a ∈ (p.productOfExperts q h).support ↔ p a ≠ 0 ∧ q a ≠ 0 :=
  mem_support_reweight_iff _ _ _ _ _

end PMF
