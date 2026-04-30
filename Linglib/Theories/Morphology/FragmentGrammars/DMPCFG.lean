import Linglib.Core.Computability.CFGTree
import Linglib.Core.Probability.PolyaUrn
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
- `DMPCFG.derivRuleCount` — count of rule applications in one
  derivation tree.
- `DMPCFG.corpusRuleCount` — count of rule applications across a
  corpus.
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
weights given a corpus is again Dirichlet (conjugacy), so the
posterior MAP weights are proportional to corpus rule frequencies.
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

mutual
/-- Number of times rule `r` is applied at internal nodes of the
    derivation tree `t`. -/
def derivRuleCount (r : ContextFreeRule T G.NT) :
    CFGTree T G.NT → ℕ
  | .leaf _ => 0
  | .node nt cs =>
      (if r = ⟨nt, cs.map CFGTree.rootSymbol⟩ then 1 else 0) +
      derivRuleCountList r cs

/-- List version of `derivRuleCount`. -/
def derivRuleCountList (r : ContextFreeRule T G.NT) :
    List (CFGTree T G.NT) → ℕ
  | [] => 0
  | t :: ts => derivRuleCount r t + derivRuleCountList r ts
end

/-- Total number of times rule `r` is used across the corpus `D`. -/
def corpusRuleCount (r : ContextFreeRule T G.NT)
    (D : Multiset (CFGTree T G.NT)) : ℕ :=
  (D.map (derivRuleCount r)).sum

variable (M : DMPCFG G)

/-- The subtype of rules with LHS `a` (as a sort, for indexing). -/
abbrev RulesWithLHS (a : G.NT) : Type :=
  { r : ContextFreeRule T G.NT // r ∈ G.rules.filter (·.input = a) }

/--
Per-LHS Pólya urn over the subtype of rules with LHS `a`,
parameterized by `M.pseudo` restricted to those rules.
-/
noncomputable def lhsUrn (a : G.NT) :
    ProbabilityTheory.PolyaUrn (RulesWithLHS (G := G) a) where
  pseudo := fun ⟨r, _⟩ => M.pseudo r
  pseudo_pos := fun ⟨r, hr⟩ => M.pseudo_pos r (Finset.mem_filter.mp hr).1

/-- Per-LHS corpus rule-count vector as a function on the subtype. -/
def lhsCounts (a : G.NT) (D : Multiset (CFGTree T G.NT)) :
    RulesWithLHS (G := G) a → ℕ :=
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
    Nonempty (RulesWithLHS (G := G) a) := by
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

/-- Corpus rule-counts vanish on the empty corpus. -/
@[simp]
theorem corpusRuleCount_zero (r : ContextFreeRule T G.NT) :
    corpusRuleCount r (0 : Multiset (CFGTree T G.NT)) = 0 := by
  simp [corpusRuleCount]

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
    [hne : Nonempty (RulesWithLHS (G := G) a)]
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
  · haveI : Nonempty (RulesWithLHS (G := G) r.input) :=
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
  haveI : Nonempty (RulesWithLHS (G := G) r'.input) :=
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
    [Nonempty (RulesWithLHS (G := G) a)]
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
    [Nonempty (RulesWithLHS (G := G) a)]
    (D : Multiset (CFGTree T G.NT)) :
    PMF (RulesWithLHS (G := G) a) :=
  PMF.ofFintype
    (fun x => ENNReal.ofReal (M.mapWeight x.1 D))
    (by
      -- Reduce the subtype-Fintype sum to a Finset sum over the LHS bucket
      rw [show (∑ x : RulesWithLHS (G := G) a,
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
    [Nonempty (RulesWithLHS (G := G) a)]
    (D : Multiset (CFGTree T G.NT)) (r : RulesWithLHS (G := G) a) :
    M.mapWeightPMF D r = ENNReal.ofReal (M.mapWeight r.1 D) := rfl

/-- PMF comparison lemma: at a shared LHS, the per-LHS posterior
    PMF ordering reduces to `pseudo + count` ordering. Bundles
    `mapWeightPMF_apply` + `mapWeight_lt_mapWeight_iff_of_same_lhs`
    + `ENNReal.ofReal_lt_ofReal_iff` so consumers can rewrite
    straight from PMF mass to numerator arithmetic. The shared LHS
    and `r₂.1 ∈ G.rules` premises both come for free from the
    subtype proofs `r₁.2`, `r₂.2`. -/
theorem mapWeightPMF_lt_iff {a : G.NT}
    [Nonempty (RulesWithLHS (G := G) a)]
    (r₁ r₂ : RulesWithLHS (G := G) a)
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

end DMPCFG

end Morphology.FragmentGrammars
