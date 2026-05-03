import Linglib.Core.Computability.CFGTree
import Linglib.Core.Computability.WeightedCFG
import Linglib.Core.Probability.PolyaUrn
import Linglib.Theories.Morphology.FragmentGrammars.MultinomialPCFG
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Dirichlet–multinomial PCFG (DMPCFG)

@cite{odonnell-2015}

The "full-parsing" model of @cite{odonnell-2015} §2.4.1 / §3.1.4: a
PCFG with a Dirichlet prior on the per-LHS rule-weight vector.
Marginalizing out the rule weights yields the closed-form corpus
probability of eq 3.9 — the Dirichlet–multinomial likelihood.

```
P(D | M) = ∏_{A ∈ V}
  [ Γ(Σ_i π_i^A) / Γ(Σ_i π_i^A + Σ_i x_i^A)
    · ∏_i Γ(π_i^A + x_i^A) / Γ(π_i^A) ]
```

where `π_i^A` are the Dirichlet hyperparameters (pseudo-counts) for
the `i`-th rule with LHS `A`, and `x_i^A` is the count of that rule
across the corpus `D`.

## Why DMPCFG does not factorize

The crucial difference from a multinomial PCFG (`MultinomialPCFG`)
is that *the same rule's count enters the same Pólya term across all
derivations in the corpus*. Two derivations using rule `r` are
correlated through the shared `x_r` in the closed form. As a result,
`P(D | M) ≠ ∏_d P(d | M)` — DMPCFG derivations are *exchangeable but
not independent*. The corpus probability is a corpus-level function;
there is no clean per-derivation factorization to expose.

## Connection to `PolyaUrn`

The per-LHS factor `lhsFactor M D A` IS the closed-form Pólya-urn
*per-sequence likelihood* over rules with LHS `A`, using `M.pseudo`
restricted to those rules. The Type-polymorphic `PolyaUrn α` from
`Linglib.Core.Probability.PolyaUrn` is constructed per-LHS via
`lhsUrn`; positivity of `corpusProb` is derived structurally from
`PolyaUrn.seqProb_pos`. (We use `seqProb`, not the count-vector PMF
`polyaUrnPMFReal`, because a corpus IS a specific labeled sequence
of derivations, not a draw from the unlabeled-count distribution.)

## Main definitions

- `DMPCFG G` — per-rule Dirichlet pseudo-counts.
- Rule application counts (`CFGTree.ruleCount`,
  `CFGTree.corpusRuleCount`) are CFGTree-level operations in
  `Core/Computability/CFGTree.lean`; opened into this namespace.
- `DMPCFG.lhsUrn` — per-LHS `PolyaUrn` over the subtype of rules
  with that LHS.
- `DMPCFG.lhsCounts` — per-LHS corpus counts as a function on the
  subtype.
- `DMPCFG.lhsFactor` — per-LHS Pólya per-sequence likelihood
  (delegates to `PolyaUrn.seqProb`).
- `DMPCFG.corpusProb` — eq 3.9 closed-form corpus probability.

## References

- @cite{odonnell-2015} §2.4.1, §3.1.4 (eq 3.7–3.9).
-/

namespace Morphology.FragmentGrammars

open Real

/--
A Dirichlet–multinomial PCFG over `G`: per-rule pseudo-counts that
parametrize a Dirichlet prior on the per-LHS rule-weight vector.

Per @cite{odonnell-2015} §2.4.1 the conditional distribution over
weights given a corpus is again Dirichlet (conjugacy). The "MAP
weights" (CL convention) are taken to be the Dirichlet posterior
**mean** `(π + x) / Σ(π + x)`, proportional to corpus rule frequencies.

*Terminology note*: in strict Bayesian usage MAP = mode of posterior
over θ, with formula `(π - 1) / Σ(π - 1)` requiring `π > 1` everywhere.
For the symmetric Dirichlet priors typical in CL (α ≤ 1) the strict
mode is at the simplex boundary, so practitioners use the posterior
mean (= posterior predictive probability) and call it "MAP" loosely.
@cite{odonnell-2015} follows this convention; we do too. The strict
mode is also formalized as `posteriorMode`; see that section for the
ordering-equivalence theorem (`mapWeight_lt_iff_posteriorMode_lt`)
that shows the loose convention is harmless for ordering claims.
-/
@[ext]
structure DMPCFG {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] where
  /-- Per-rule pseudo-count (Dirichlet hyperparameter). -/
  pseudo : ContextFreeRule T G.NT → ℝ
  /-- Pseudo-counts are strictly positive on grammar rules. -/
  pseudo_pos : ∀ r ∈ G.rules, 0 < pseudo r

namespace DMPCFG

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

open CFGTree (corpusRuleCount corpusRuleCount_zero corpusRuleCount_add)

variable (M : DMPCFG G)

/--
Per-LHS Pólya urn over the subtype of rules with LHS `a`,
parameterized by `M.pseudo` restricted to those rules.
-/
noncomputable def lhsUrn (a : G.NT) :
    ProbabilityTheory.PolyaUrn (G.RulesWithLHS a) where
  pseudo := fun ⟨r, _⟩ => M.pseudo r
  pseudo_pos := fun ⟨r, hr⟩ => M.pseudo_pos r (Finset.mem_filter.mp hr).1

/-- Per-LHS corpus rule-count vector as a function on the subtype. -/
def lhsCounts (a : G.NT) (D : Multiset (CFGTree T G.NT)) :
    G.RulesWithLHS a → ℕ :=
  fun ⟨r, _⟩ => corpusRuleCount r D

/--
Per-LHS factor in the eq 3.9 product: the Pólya partition probability
of the corpus rule-counts under the per-LHS pseudo-counts.

```
  Γ(Σ π_i^A) / Γ(Σ π_i^A + Σ x_i^A)  ·  ∏_i Γ(π_i^A + x_i^A) / Γ(π_i^A) .
```
-/
noncomputable def lhsFactor (a : G.NT) (D : Multiset (CFGTree T G.NT)) : ℝ :=
  (M.lhsUrn a).seqProb (lhsCounts a D)

/--
DMPCFG corpus probability — eq 3.9 of @cite{odonnell-2015}. Product
over LHSs that appear in the grammar of the per-LHS Pólya factor.
LHSs with no rules in `G` contribute trivially (empty image term)
so the product is over `G.rules.image (·.input)`.
-/
noncomputable def corpusProb (D : Multiset (CFGTree T G.NT)) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), M.lhsFactor a D

omit [DecidableEq T] in
/-- For LHSs that have at least one rule, the subtype is nonempty. -/
theorem nonempty_rulesWithLHS_of_mem_image {a : G.NT}
    (ha : a ∈ G.rules.image (·.input)) :
    Nonempty (G.RulesWithLHS a) := by
  obtain ⟨r0, hr0_mem, hr0_input⟩ := Finset.mem_image.mp ha
  exact ⟨r0, Finset.mem_filter.mpr ⟨hr0_mem, hr0_input⟩⟩

/-- The per-LHS factor is strictly positive when the LHS has rules.
    Direct corollary of `PolyaUrn.seqProb_pos`. -/
theorem lhsFactor_pos {a : G.NT} (ha : a ∈ G.rules.image (·.input))
    (D : Multiset (CFGTree T G.NT)) : 0 < M.lhsFactor a D := by
  haveI := nonempty_rulesWithLHS_of_mem_image ha
  exact (M.lhsUrn a).seqProb_pos _

/-- DMPCFG corpus probabilities are nonnegative (in fact, positive). -/
theorem corpusProb_nonneg (D : Multiset (CFGTree T G.NT)) :
    0 ≤ M.corpusProb D := by
  unfold corpusProb
  apply Finset.prod_nonneg
  intro a ha
  exact (M.lhsFactor_pos ha D).le

/-- Per-LHS counts vanish on the empty corpus. -/
@[simp]
theorem lhsCounts_zero (a : G.NT) :
    lhsCounts (G := G) a (0 : Multiset (CFGTree T G.NT)) = fun _ => 0 := by
  funext ⟨r, _⟩
  simp [lhsCounts]

/-- The empty corpus has probability 1 under any DMPCFG: each
    per-LHS Pólya factor is `seqProb` on the all-zero count
    vector, which equals 1 by `PolyaUrn.seqProb_zero`. -/
@[simp]
theorem corpusProb_zero : M.corpusProb (0 : Multiset (CFGTree T G.NT)) = 1 := by
  unfold corpusProb
  apply Finset.prod_eq_one
  intro a ha
  haveI := nonempty_rulesWithLHS_of_mem_image ha
  show M.lhsFactor a 0 = 1
  unfold lhsFactor
  rw [lhsCounts_zero]
  exact (M.lhsUrn a).seqProb_zero

/-! ## Posterior MAP weights

Per @cite{odonnell-2015} §2.4 (Dirichlet–multinomial conjugacy),
the posterior over rule weights given a corpus is again Dirichlet,
so per-rule posterior expected value (the MAP weight in the
symmetric prior limit) is
`(π_r + x_r) / Σ_{r' with same LHS} (π_{r'} + x_{r'})`.
This is the productivity score @cite{odonnell-2015} Ch 7 (p. 268)
identifies as DMPCFG's failure mode: when corpus counts dominate
pseudo-counts, frequency wins over the prior. -/

/--
Per-rule MAP weight: posterior expected value of the rule's
Dirichlet weight given the corpus rule-counts. Equals
`(pseudo r + count r D) / Σ_{r' with same LHS} (pseudo r' + count r' D)`.
Returns 0 by convention when the LHS has no rules in `G` (vacuous;
in practice `r ∈ G.rules` makes the denominator positive — see
`mapWeight_denom_pos`).
-/
noncomputable def mapWeight (r : ContextFreeRule T G.NT)
    (D : Multiset (CFGTree T G.NT)) : ℝ :=
  (M.pseudo r + (corpusRuleCount r D : ℝ)) /
    ∑ r' ∈ G.rules.filter (·.input = r.input),
      (M.pseudo r' + (corpusRuleCount r' D : ℝ))

/-- The denominator of `mapWeight` is positive whenever the LHS
    has at least one rule in `G`. Each summand `pseudo r' + count r' D`
    is at least `pseudo r' > 0` by `pseudo_pos`.

    Takes the per-LHS nonemptiness as a `Nonempty` typeclass
    argument rather than an explicit existential — mathlib idiom
    for "this construction needs the bucket to be inhabited."
    Consumers either declare `instance : Nonempty (RulesWithLHS …) := ⟨⟨r, _⟩⟩`
    once for their grammar+LHS pair, or `haveI` the witness locally. -/
theorem mapWeight_denom_pos {a : G.NT}
    [hne : Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    0 < ∑ r' ∈ G.rules.filter (·.input = a),
        (M.pseudo r' + (corpusRuleCount r' D : ℝ)) := by
  obtain ⟨⟨r₀, hr₀_in⟩⟩ := hne
  apply Finset.sum_pos'
  · intro r' hr'
    have h1 : 0 < M.pseudo r' := M.pseudo_pos r' (Finset.mem_filter.mp hr').1
    have h2 : 0 ≤ (corpusRuleCount r' D : ℝ) := Nat.cast_nonneg _
    linarith
  · refine ⟨r₀, hr₀_in, ?_⟩
    have h1 : 0 < M.pseudo r₀ := M.pseudo_pos r₀ (Finset.mem_filter.mp hr₀_in).1
    have h2 : 0 ≤ (corpusRuleCount r₀ D : ℝ) := Nat.cast_nonneg _
    linarith

/-- `mapWeight` is strictly positive for any rule in `G`. The
    numerator is positive (`pseudo_pos` + nonneg cast) and the
    denominator is positive (witness: `r` itself is in its own LHS
    bucket). The `Nonempty` instance for `RulesWithLHS r.input` is
    synthesised internally from `hr`. -/
theorem mapWeight_pos {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (CFGTree T G.NT)) : 0 < M.mapWeight r D := by
  unfold mapWeight
  apply div_pos
  · have h1 : 0 < M.pseudo r := M.pseudo_pos r hr
    have h2 : 0 ≤ (corpusRuleCount r D : ℝ) := Nat.cast_nonneg _
    linarith
  · haveI : Nonempty (G.RulesWithLHS r.input) :=
      ⟨⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩⟩
    exact M.mapWeight_denom_pos D

/-- Corollary: `mapWeight` is nonnegative for rules in `G`. -/
theorem mapWeight_nonneg {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (CFGTree T G.NT)) : 0 ≤ M.mapWeight r D :=
  (M.mapWeight_pos hr D).le

/-- Empty-corpus reduction: `mapWeight` collapses to the prior
    expected value `pseudo r / Σ_{r' with same LHS} pseudo r'`.
    The Dirichlet posterior with no data IS the prior. -/
@[simp]
theorem mapWeight_zero (r : ContextFreeRule T G.NT) :
    M.mapWeight r (0 : Multiset (CFGTree T G.NT)) =
      M.pseudo r / ∑ r' ∈ G.rules.filter (·.input = r.input), M.pseudo r' := by
  unfold mapWeight
  simp [corpusRuleCount_zero]

/-- Same-LHS comparison (iff form): with a shared LHS, `mapWeight`
    ordering is *equivalent* to `pseudo + count` ordering. The shared
    denominator cancels. This is the technical core of the
    @cite{odonnell-2015} Ch 7 DMPCFG critique: when corpus counts
    overcome pseudo-count differences, the more-frequent rule wins
    regardless of prior. -/
theorem mapWeight_lt_mapWeight_iff_of_same_lhs
    {r r' : ContextFreeRule T G.NT} (hr'_in : r' ∈ G.rules)
    (h_lhs : r.input = r'.input)
    {D : Multiset (CFGTree T G.NT)} :
    M.mapWeight r D < M.mapWeight r' D ↔
      M.pseudo r + (corpusRuleCount r D : ℝ) <
        M.pseudo r' + (corpusRuleCount r' D : ℝ) := by
  unfold mapWeight
  have h_denom_eq : G.rules.filter (·.input = r.input) =
                    G.rules.filter (·.input = r'.input) := by rw [h_lhs]
  rw [h_denom_eq]
  haveI : Nonempty (G.RulesWithLHS r'.input) :=
    ⟨⟨r', Finset.mem_filter.mpr ⟨hr'_in, rfl⟩⟩⟩
  exact div_lt_div_iff_of_pos_right (M.mapWeight_denom_pos D)

/-- Directional form of `mapWeight_lt_mapWeight_iff_of_same_lhs` for
    `apply`-style proofs. -/
theorem mapWeight_lt_mapWeight_of_same_lhs
    {r r' : ContextFreeRule T G.NT} (hr'_in : r' ∈ G.rules)
    (h_lhs : r.input = r'.input)
    {D : Multiset (CFGTree T G.NT)}
    (h_num : M.pseudo r + (corpusRuleCount r D : ℝ) <
             M.pseudo r' + (corpusRuleCount r' D : ℝ)) :
    M.mapWeight r D < M.mapWeight r' D :=
  (M.mapWeight_lt_mapWeight_iff_of_same_lhs hr'_in h_lhs).mpr h_num

/-- The probability axiom: `mapWeight` over rules sharing an LHS
    sums to 1. Each summand has the same denominator (the LHS-sum),
    and the numerators sum to that same denominator, so the ratio
    sums to 1. This is what justifies calling `mapWeight` a *weight*
    rather than just a number — it is the per-LHS Dirichlet
    posterior mass function. -/
theorem mapWeight_sum_eq_one_of_lhs {a : G.NT}
    [Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    ∑ r ∈ G.rules.filter (·.input = a), M.mapWeight r D = 1 := by
  have hdenom_pos := M.mapWeight_denom_pos (a := a) D
  have h_rewrite : ∀ r ∈ G.rules.filter (·.input = a),
      M.mapWeight r D =
        (M.pseudo r + (corpusRuleCount r D : ℝ)) /
        ∑ r' ∈ G.rules.filter (·.input = a),
          (M.pseudo r' + (corpusRuleCount r' D : ℝ)) := by
    intro r hr
    have hra : r.input = a := (Finset.mem_filter.mp hr).2
    show M.mapWeight r D = _
    unfold mapWeight
    rw [hra]
  rw [Finset.sum_congr rfl h_rewrite, ← Finset.sum_div]
  exact div_self hdenom_pos.ne'

/-! ## PMF lift

The per-LHS `mapWeight`s sum to 1 (`mapWeight_sum_eq_one_of_lhs`),
so they form a probability mass function on the rules sharing that
LHS. `mapWeightPMF` packages this as mathlib's `PMF`, connecting
DMPCFG to the standard probability infrastructure: the resulting
object inherits `support`, `bind`, `map`, etc. from `PMF`, and
sum-to-1 is now a structural property (a field of `PMF`) rather
than a follow-up theorem. -/

/-- The per-LHS Dirichlet posterior MAP weights as a probability
    mass function on the rules sharing that LHS.

    Built via `PMF.ofFintype` over the subtype `RulesWithLHS a`,
    using `mapWeight_sum_eq_one_of_lhs` for the normalisation
    obligation. The PMF's value at `⟨r, hr⟩` is
    `ENNReal.ofReal (M.mapWeight r D)` — see `mapWeightPMF_apply`. -/
noncomputable def mapWeightPMF {a : G.NT}
    [Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    PMF (G.RulesWithLHS a) :=
  PMF.ofFintype
    (fun x => ENNReal.ofReal (M.mapWeight x.1 D))
    (by
      -- Reduce the subtype-Fintype sum to a Finset sum over the LHS bucket
      rw [show (∑ x : G.RulesWithLHS a,
                  ENNReal.ofReal (M.mapWeight x.1 D)) =
              ∑ r ∈ G.rules.filter (·.input = a),
                ENNReal.ofReal (M.mapWeight r D) from
            Finset.sum_attach _ (fun r => ENNReal.ofReal (M.mapWeight r D))]
      -- Push ofReal through the sum (each summand is nonneg)
      rw [← ENNReal.ofReal_sum_of_nonneg
            (fun r hr => M.mapWeight_nonneg (Finset.mem_filter.mp hr).1 D)]
      -- Sum equals 1; ofReal 1 = 1
      rw [M.mapWeight_sum_eq_one_of_lhs D, ENNReal.ofReal_one])

/-- The PMF value at a rule equals the `mapWeight` value, lifted
    to `ℝ≥0∞`. Bridges `mapWeightPMF` (the structural object) to
    `mapWeight` (the numeric accessor). Holds by `rfl` via
    `PMF.ofFintype_apply`. -/
@[simp]
theorem mapWeightPMF_apply {a : G.NT}
    [Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) (r : G.RulesWithLHS a) :
    M.mapWeightPMF D r = ENNReal.ofReal (M.mapWeight r.1 D) := rfl

/-- PMF comparison lemma: at a shared LHS, the per-LHS posterior
    PMF ordering reduces to `pseudo + count` ordering. Bundles
    `mapWeightPMF_apply` + `mapWeight_lt_mapWeight_iff_of_same_lhs`
    + `ENNReal.ofReal_lt_ofReal_iff` so consumers can rewrite
    straight from PMF mass to numerator arithmetic. The shared LHS
    and `r₂.1 ∈ G.rules` premises both come for free from the
    subtype proofs `r₁.2`, `r₂.2`. -/
theorem mapWeightPMF_lt_iff {a : G.NT}
    [Nonempty (G.RulesWithLHS a)]
    (r₁ r₂ : G.RulesWithLHS a)
    (D : Multiset (CFGTree T G.NT)) :
    M.mapWeightPMF D r₁ < M.mapWeightPMF D r₂ ↔
      M.pseudo r₁.1 + (corpusRuleCount r₁.1 D : ℝ) <
        M.pseudo r₂.1 + (corpusRuleCount r₂.1 D : ℝ) := by
  rw [mapWeightPMF_apply, mapWeightPMF_apply]
  have hr₂_in : r₂.1 ∈ G.rules := (Finset.mem_filter.mp r₂.2).1
  have hr₂_pos : 0 < M.mapWeight r₂.1 D := M.mapWeight_pos hr₂_in D
  have h_lhs : r₁.1.input = r₂.1.input := by
    rw [(Finset.mem_filter.mp r₁.2).2, (Finset.mem_filter.mp r₂.2).2]
  rw [ENNReal.ofReal_lt_ofReal_iff hr₂_pos]
  exact M.mapWeight_lt_mapWeight_iff_of_same_lhs hr₂_in h_lhs

/-! ## Strict Bayesian mode (the actual MAP)

`mapWeight` computes the Dirichlet posterior **mean**, which is what
@cite{odonnell-2015} and CL practice generally call "MAP" (a loose
convention). The strict Bayesian MAP — the single most likely value
of the rule-weight vector under the posterior — is the **mode** of
`Dir(pseudo + count)`, with closed form `(π_i - 1) / Σ(π_j - 1)`.

The mode is well-defined only when `pseudo + count > 1` for every
rule in the LHS bucket. Otherwise the posterior density goes to ∞ at
a simplex vertex (when some `π_i + x_i < 1`) or has flat edges
(equality case). For symmetric Dirichlet priors with concentration
α ≤ 1 (the CL norm), the strict mode lives at the boundary; this is
exactly why CL uses the mean instead.

When both estimators are defined, **they agree on orderings**: rule
with higher `pseudo + count` has higher mean *and* higher mode. So
the productivity-ordering theorems we prove for `mapWeight` apply to
`posteriorMode` automatically (under its precondition). The mode adds
genuinely new content the mean can't express: vertex behavior,
asymptotic agreement (mode → mean as `pseudo + count → ∞`), and
boundary collapse. -/

/-- The Dirichlet posterior **mode** of the rule weight: the single
    most likely value of θ_r under `Dir(pseudo + count)`. Closed form
    `(π_i - 1) / Σ(π_j - 1)`, valid in the simplex interior when
    `pseudo r' + count r' D > 1` for every `r'` in the LHS bucket
    (otherwise the mode is at the boundary; see `posteriorMode_well_defined`).

    Returns `0/0 = 0` (Lean convention) outside the well-defined
    regime; theorems carry the well-definedness hypothesis. -/
noncomputable def posteriorMode (M : DMPCFG G)
    (r : ContextFreeRule T G.NT) (D : Multiset (CFGTree T G.NT)) : ℝ :=
  (M.pseudo r + (corpusRuleCount r D : ℝ) - 1) /
    ∑ r' ∈ G.rules.filter (·.input = r.input),
      (M.pseudo r' + (corpusRuleCount r' D : ℝ) - 1)

/-- The mode-well-definedness condition: every entry of the LHS
    bucket exceeds 1 in the posterior. Equivalent to "the Dirichlet
    posterior has its mode strictly in the simplex interior." -/
def PosteriorModeWellDefined (M : DMPCFG G) (a : G.NT)
    (D : Multiset (CFGTree T G.NT)) : Prop :=
  ∀ r ∈ G.rules.filter (·.input = a), 1 < M.pseudo r + (corpusRuleCount r D : ℝ)

/-- The mode denominator is positive when the well-definedness
    condition holds. Each summand exceeds 0 by hypothesis. -/
theorem posteriorMode_denom_pos {a : G.NT}
    [hne : Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT))
    (h : M.PosteriorModeWellDefined a D) :
    0 < ∑ r' ∈ G.rules.filter (·.input = a),
        (M.pseudo r' + (corpusRuleCount r' D : ℝ) - 1) := by
  obtain ⟨⟨r₀, hr₀_in⟩⟩ := hne
  apply Finset.sum_pos'
  · intro r' hr'
    have := h r' hr'
    linarith
  · refine ⟨r₀, hr₀_in, ?_⟩
    have := h r₀ hr₀_in
    linarith

/-- `posteriorMode` is strictly positive on rules in `G` when the
    well-definedness condition holds. The numerator and denominator
    are both positive. -/
theorem posteriorMode_pos {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (CFGTree T G.NT))
    (h : M.PosteriorModeWellDefined r.input D) :
    0 < M.posteriorMode r D := by
  unfold posteriorMode
  apply div_pos
  · have := h r (Finset.mem_filter.mpr ⟨hr, rfl⟩)
    linarith
  · haveI : Nonempty (G.RulesWithLHS r.input) :=
      ⟨⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩⟩
    exact M.posteriorMode_denom_pos D h

/-- **Same-LHS comparison (mode version).** Mode ordering matches
    `pseudo + count` ordering, just like `mapWeight`. The shared
    denominator cancels. This is the key fact that makes CL's "MAP =
    mean" loose convention harmless for *ordering* claims: both
    estimators give the same productivity ranking. -/
theorem posteriorMode_lt_iff_of_same_lhs
    {r r' : ContextFreeRule T G.NT} (hr'_in : r' ∈ G.rules)
    (h_lhs : r.input = r'.input)
    {D : Multiset (CFGTree T G.NT)}
    (h_wd : M.PosteriorModeWellDefined r'.input D) :
    M.posteriorMode r D < M.posteriorMode r' D ↔
      M.pseudo r + (corpusRuleCount r D : ℝ) <
        M.pseudo r' + (corpusRuleCount r' D : ℝ) := by
  unfold posteriorMode
  have h_denom_eq : G.rules.filter (·.input = r.input) =
                    G.rules.filter (·.input = r'.input) := by rw [h_lhs]
  rw [h_denom_eq]
  haveI : Nonempty (G.RulesWithLHS r'.input) :=
    ⟨⟨r', Finset.mem_filter.mpr ⟨hr'_in, rfl⟩⟩⟩
  rw [div_lt_div_iff_of_pos_right (M.posteriorMode_denom_pos D h_wd)]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Mean-mode ordering equivalence.** Whenever both `mapWeight`
    and `posteriorMode` are well-defined for the same comparison,
    they agree on ordering of two rules sharing an LHS. This is the
    formal Lean witness of "the mean-vs-mode distinction is moot for
    productivity-ranking claims." -/
theorem mapWeight_lt_iff_posteriorMode_lt {r r' : ContextFreeRule T G.NT}
    (hr'_in : r' ∈ G.rules) (h_lhs : r.input = r'.input)
    {D : Multiset (CFGTree T G.NT)}
    (h_wd : M.PosteriorModeWellDefined r'.input D) :
    M.mapWeight r D < M.mapWeight r' D ↔
      M.posteriorMode r D < M.posteriorMode r' D := by
  rw [M.mapWeight_lt_mapWeight_iff_of_same_lhs hr'_in h_lhs,
      M.posteriorMode_lt_iff_of_same_lhs hr'_in h_lhs h_wd]

/-! ## Bridge: DMPCFG → MultinomialPCFG via posterior MAP

A DMPCFG is a *prior over* multinomial PCFGs (Dirichlet hyperparameters
parameterize a distribution over per-LHS rule-weight vectors). The
posterior given a corpus is again Dirichlet (conjugacy); the posterior
MAP weights are a single multinomial PCFG.

This is the bridge: collapse a DMPCFG, conditioned on a corpus, into
its MAP point estimate. At the empty corpus (`D = 0`), the result is
the prior mean — see `posteriorMAP_zero`.

`DMPCFG` does **not** `extends MultinomialPCFG`: a prior is a different
kind of object than a point in weight space. The two relate via this
*function*, not via inheritance. -/

/-- The Dirichlet posterior MAP collapse: given a corpus `D`, package
    DMPCFG's per-LHS posterior MAP weights as a `MultinomialPCFG`.
    Per-LHS PMFs come straight from `mapWeightPMF`; sum-to-1 is
    structural via `PMF`.

    Requires `[∀ a, Nonempty (G.RulesWithLHS a)]` (carried by
    `MultinomialPCFG` itself): the construction can't deliver a
    multinomial PCFG over a grammar with empty LHS buckets. -/
noncomputable def posteriorMAP [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) : MultinomialPCFG G :=
  ⟨fun a => M.mapWeightPMF (a := a) D⟩

/-- The posterior MAP `MultinomialPCFG`'s per-LHS PMF unfolds to
    DMPCFG's `mapWeightPMF`. Holds by `rfl`. **Not `@[simp]`** —
    Lean unfolds eagerly anyway (consumers like ODonnell2015's
    bridge demo use direct application without `rw`), and tagging
    `simp` risks loops in unfamiliar simp contexts. -/
theorem posteriorMAP_rulePMF [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) (a : G.NT) :
    (M.posteriorMAP D).rulePMF a = M.mapWeightPMF D := rfl

/-! ## Conjugacy decomposition: posterior + mode

The `posteriorMAP` collapses two distinct Bayesian operations:

1. `DMPCFG.posterior : DMPCFG G → Multiset _ → DMPCFG G` —
   Dirichlet-conjugate update: bump pseudo-counts by the corpus rule
   counts. The posterior of a Dirichlet given multinomial data is again
   a Dirichlet (conjugacy), so this stays inside the DMPCFG type.
2. `DMPCFG.mode : DMPCFG G → MultinomialPCFG G` — the Dirichlet-mode
   projection (= `posteriorMAP` at the empty corpus).

The decomposition `posteriorMAP = mode ∘ posterior` is captured by
`posteriorMAP_eq_mode_posterior`. Naming the two primitives separately
makes the Bayesian structure visible in code and exposes incrementality
of the update (`posterior_add`) as a stand-alone theorem rather than
an unspoken consequence. -/

/-- The Dirichlet-conjugate posterior update: given a corpus, bump
    each rule's Dirichlet pseudo-count by that rule's corpus count.
    Stays inside the `DMPCFG` type — that's the point of conjugacy. -/
noncomputable def posterior (D : Multiset (CFGTree T G.NT)) : DMPCFG G where
  pseudo r := M.pseudo r + (corpusRuleCount r D : ℝ)
  pseudo_pos r hr := by
    have h1 : 0 < M.pseudo r := M.pseudo_pos r hr
    have h2 : 0 ≤ (corpusRuleCount r D : ℝ) := Nat.cast_nonneg _
    linarith

/-- Posterior at the empty corpus is the prior: no data, no update. -/
@[simp]
theorem posterior_zero : M.posterior 0 = M := by
  ext r
  show M.pseudo r + ((corpusRuleCount r 0 : ℕ) : ℝ) = M.pseudo r
  rw [corpusRuleCount_zero]
  simp

/-- **Incrementality.** Updating with `D₁ + D₂` equals updating
    sequentially with `D₁` then `D₂`. Bayesian update is associative
    over disjoint data — the actual content of "the prior commutes
    with corpus aggregation." Follows from `corpusRuleCount_add`. -/
theorem posterior_add (D₁ D₂ : Multiset (CFGTree T G.NT)) :
    M.posterior (D₁ + D₂) = (M.posterior D₁).posterior D₂ := by
  ext r
  show M.pseudo r + ((corpusRuleCount r (D₁ + D₂) : ℕ) : ℝ) =
       (M.posterior D₁).pseudo r + ((corpusRuleCount r D₂ : ℕ) : ℝ)
  rw [corpusRuleCount_add]
  show M.pseudo r + ((corpusRuleCount r D₁ + corpusRuleCount r D₂ : ℕ) : ℝ) =
       (M.pseudo r + ((corpusRuleCount r D₁ : ℕ) : ℝ)) +
         ((corpusRuleCount r D₂ : ℕ) : ℝ)
  push_cast
  ring

/-- **Mode** of the Dirichlet prior in `MultinomialPCFG`-space:
    the per-LHS-normalized pseudo-counts as a `MultinomialPCFG`.
    Equivalently: `posteriorMAP` at the empty corpus (no data). -/
noncomputable def mode [∀ a : G.NT, Nonempty (G.RulesWithLHS a)] :
    MultinomialPCFG G :=
  M.posteriorMAP 0

/-- **The conjugacy decomposition.** `posteriorMAP` factors as
    `mode ∘ posterior`: first update the prior with data (Dirichlet
    conjugacy), then take the mode (Dirichlet-to-MultinomialPCFG
    projection). The Bayesian-MAP estimator stops being a primitive
    and becomes a derived composition. -/
theorem posteriorMAP_eq_mode_posterior [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    M.posteriorMAP D = (M.posterior D).mode := by
  show M.posteriorMAP D = (M.posterior D).posteriorMAP 0
  apply MultinomialPCFG.ext
  funext a
  show M.mapWeightPMF (a := a) D = (M.posterior D).mapWeightPMF (a := a) 0
  ext x
  rw [DMPCFG.mapWeightPMF_apply, DMPCFG.mapWeightPMF_apply]
  congr 1
  show M.mapWeight x.1 D = (M.posterior D).mapWeight x.1 0
  unfold mapWeight
  show (M.pseudo x.1 + ((corpusRuleCount x.1 D : ℕ) : ℝ)) /
        ∑ r' ∈ G.rules.filter (·.input = x.1.input),
          (M.pseudo r' + ((corpusRuleCount r' D : ℕ) : ℝ))
       = ((M.posterior D).pseudo x.1 + ((corpusRuleCount x.1 0 : ℕ) : ℝ)) /
        ∑ r' ∈ G.rules.filter (·.input = x.1.input),
          ((M.posterior D).pseudo r' + ((corpusRuleCount r' 0 : ℕ) : ℝ))
  simp [DMPCFG.posterior, corpusRuleCount_zero]

end DMPCFG

end Morphology.FragmentGrammars
