import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Epistemic threshold semantics

Threshold semantics for epistemic vocabulary over agent credence, the
probabilistic tradition of [lassiter-goodman-2017]: an attitude verb,
modal verb, or modal adjective holds of a proposition iff the agent's
credence in it clears a lexical threshold — `meetsThreshold`, with
`failsThreshold` the reversed-polarity form (*uncertain*, *unlikely*).
The pattern is the positive form of a gradable predicate on the
credence scale, whose boundedness makes endpoint standards like
*certain* available on the [kennedy-2007] licensing story; the
[klein-1980] reduction of the comparative to the positive form holds
on this scale (`lt_iff_separating_threshold`).

`isProbabilistic` — monotonicity of credence in entailment — is what
separates probabilistic credence from ordinal confidence orderings:
it validates conjunction elimination (`prob_conjunction_elim`),
which [cariani-santorio-wellwood-2024]'s non-probabilistic confidence
ordering deliberately does not (the divergence witness lives in
`Studies/CarianiSantorioWellwood2024.lean`). The fitted threshold
lexicon of Ying et al.'s Language-augmented Bayesian Theory of Mind
([ying-zhi-xuan-wong-mansinghka-tenenbaum-2025], their Table 1) lives
in `Studies/YingEtAl2025.lean`.
-/

namespace EpistemicThreshold

variable {E W : Type*}

/-- Agent `a`'s credence in `φ` meets the threshold `θ` — the
    positive-form condition underlying *believes*, *certain*, *must*,
    *likely*, *might*. -/
def meetsThreshold (cr : E → Set W → ℚ) (θ : ℚ) (a : E) (φ : Set W) : Prop :=
  θ ≤ cr a φ

/-- Agent `a`'s credence in `φ` is strictly below the threshold `θ` —
    the reversed-polarity condition of *uncertain* and *unlikely*. -/
def failsThreshold (cr : E → Set W → ℚ) (θ : ℚ) (a : E) (φ : Set W) : Prop :=
  cr a φ < θ

/-- For any credence and threshold, exactly one of `meetsThreshold`
    and `failsThreshold` holds. -/
theorem threshold_exhaustive (cr : E → Set W → ℚ) (θ : ℚ) (a : E) (φ : Set W) :
    meetsThreshold cr θ a φ ∨ failsThreshold cr θ a φ :=
  le_or_gt θ (cr a φ)

/-! ### Probabilistic credence -/

/-- A credence function is probabilistic when it is monotone in
    entailment: `φ ⊆ ψ` implies `cr a φ ≤ cr a ψ`. This is the axiom
    that separates probabilistic credence from ordinal confidence
    orderings, which impose no such constraint and so admit
    conjunction fallacies. -/
def IsProbabilistic (cr : E → Set W → ℚ) : Prop :=
  ∀ a : E, Monotone (cr a)

/-- Probabilistic credence never ranks a conjunction above a
    conjunct. -/
theorem IsProbabilistic.conj_elim {cr : E → Set W → ℚ}
    (h : IsProbabilistic cr) (a : E) (φ ψ : Set W) :
    cr a (φ ∩ ψ) ≤ cr a φ :=
  h a Set.inter_subset_left

/-- Probabilistic credence validates conjunction elimination at every
    threshold: believing `φ ∧ ψ` entails believing `φ`. -/
theorem prob_conjunction_elim {cr : E → Set W → ℚ}
    (h : IsProbabilistic cr) (θ : ℚ) (a : E) (φ ψ : Set W)
    (hm : meetsThreshold cr θ a (φ ∩ ψ)) : meetsThreshold cr θ a φ :=
  le_trans hm (h.conj_elim a φ ψ)

/-! ### The Klein reduction -/

/-- The comparative reduces to the positive form ([klein-1980],
    extended from adjectives to the credence scale): `φ` is more
    credent than `ψ` iff some threshold separates them. The witness is
    `θ = cr a φ` itself. -/
theorem lt_iff_separating_threshold (cr : E → Set W → ℚ) (a : E) (φ ψ : Set W) :
    cr a ψ < cr a φ ↔ ∃ θ, meetsThreshold cr θ a φ ∧ ¬ meetsThreshold cr θ a ψ :=
  ⟨fun h => ⟨cr a φ, le_refl _, not_le.mpr h⟩,
   fun ⟨_, hφ, hψ⟩ => lt_of_lt_of_le (not_le.mp hψ) hφ⟩

end EpistemicThreshold
