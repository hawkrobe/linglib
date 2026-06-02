import Linglib.Morphology.FragmentGrammars.AdaptorGrammar

/-!
# Fragment grammars (FG) — the central proposal

[odonnell-2015]

The "inference-based" model of [odonnell-2015] §2.4.4 / §3.1.8,
and the central theoretical proposal of the book. A `FragmentGrammar`
extends an `AdaptorGrammar` by adding a *per-rule-RHS-position
beta-binomial halt prior*: at each nonterminal slot in each rule's
right-hand side, a Beta-distributed weight `ν` controls the
probability of recursing (productively expanding the slot) vs.
halting (storing the slot as an open NT in a memoized fragment).

This generalizes both DMPCFG (`ν → 1` everywhere: always recurse,
fragments are depth-one) and MAG (`ν` decided once per nonterminal,
not per slot: fragments are full subtrees). FG learns a separate
recursion probability per (rule, position), letting fragments be
arbitrary partial trees with selective open NT slots — the
distinguishing feature of the book's account of productivity-and-
reuse.

Per [odonnell-2015] §3.1.8 the corpus probability factorizes as

```
fg(X, Y, Z; F) = ∏_{A ∈ V} [DMPCFG-factor on X^A] · [PYP-factor on Y^A]
              · ∏_{r ∈ R_G} ∏_{B ∈ rhs(r)}
                  B(ψ_B + z_{r,B}^↻, ψ'_B + z_{r,B}^⊥) /
                  B(ψ_B, ψ'_B)
```

where `Z = z_{r,B}^{↻/⊥}` is the corpus-aggregate count of recurse/
halt decisions at each (rule, RHS-position) pair, and `B(·,·)` is
the Beta function (here written as a ratio of Γ-products to avoid
a dependency on `Mathlib.Probability.Distributions.Beta`).

## Why corpus probability is `(D, Y, Z) → ℝ`

`Z` is latent — the recurse/halt assignment per fragment is part of
the MAP analysis, not the observed corpus. Same situation as `Y` in
`AdaptorGrammar`. Marginalizing over `(Y, Z)` is the MH inference
target distribution of [odonnell-2015] §3.2 — out of scope
per the Processing-scope rule.

## What we inherit from `AdaptorGrammar`

`FragmentGrammar G extends AdaptorGrammar G`, so the entire DMPCFG
+ PYP infrastructure is inherited: `pseudo`, `pseudo_pos`, `lhsUrn`,
`lhsCounts`, `lhsFactor`, `pyp`, `pypFactor`,
`corpusProbGivenTables`, all the positivity proofs. FG only adds
the beta-binomial halt prior and the per-(rule, position) factor.

## Main definitions

- `FragmentGrammar G` — extends `AdaptorGrammar G` with per-(rule,
  RHS-position) beta-binomial pseudo-counts (`haltPriorRecurse`,
  `haltPriorHalt`).
- `FragmentGrammar.HaltCounts` — abbrev for the latent recurse/halt
  count assignment.
- `FragmentGrammar.fgFactor` — per-(rule, position) beta-binomial
  factor.
- `FragmentGrammar.corpusProbGivenStorage` — eq from §3.1.8,
  conditional on table assignment `Y` and halt counts `Z`.

## §2.3.7 vs §3.1.8 — sampler vs distribution

This file is the **distribution** side: `corpusProbGivenStorage` is the
density `fg(F; F)` of [odonnell-2015] §3.1.8 (p. 94). The
**sampler** that draws from this density is in the sibling file
`FragmentLambda.lean`, scaffolding [odonnell-2015] §2.3.7's
Church macro `(fragment-lambda args body)` (Figure 2.21, p. 71). The
two are linked by the soundness contract
`fragmentLambdaDepth_marginalises_to_fg`, which equates the sampler's
output marginal with the §3.1.8 density.

Per [odonnell-2015] §3.1.8 (p. 92) the substrate here implements
the actual model used in the rest of the book — biased halt coin
`BINOMIAL(ν)` with `ν` itself drawn from a Beta prior — not the
fair-coin presentation of §2.3.6. The §2.3.7 fair-coin macro is
recovered as the `haltPriorRecurse = haltPriorHalt = 1` special case
(Beta(1,1) = Uniform).

## References

- [odonnell-2015] §2.4.4, §3.1.8.
-/

namespace Morphology.FragmentGrammars

open Real

/--
A *fragment grammar* over `G`: an adaptor grammar augmented with a
per-(rule, RHS-position) beta-binomial halt prior. At each
nonterminal slot in each rule's right-hand side, the weight `ν` of
recursing-vs-halting is Beta-distributed with pseudo-counts
`(haltPriorRecurse r i, haltPriorHalt r i)`.

Allowing per-slot halt decisions (rather than per-nonterminal as in
MAG) lets fragments be arbitrary partial trees — the central
theoretical commitment of [odonnell-2015].
-/
@[ext]
structure FragmentGrammar {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] extends AdaptorGrammar G where
  /-- Beta pseudo-count for "recurse" outcome at (rule, RHS position). -/
  haltPriorRecurse : ContextFreeRule T G.NT → ℕ → ℝ
  /-- Beta pseudo-count for "halt" outcome at (rule, RHS position). -/
  haltPriorHalt : ContextFreeRule T G.NT → ℕ → ℝ
  /-- Recurse pseudo-counts are strictly positive. -/
  haltPriorRecurse_pos : ∀ r i, 0 < haltPriorRecurse r i
  /-- Halt pseudo-counts are strictly positive. -/
  haltPriorHalt_pos : ∀ r i, 0 < haltPriorHalt r i

namespace FragmentGrammar

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/--
A *halt-count assignment* gives, for each rule `r` and each
RHS-position `i`, the corpus-aggregate counts of "recurse" and
"halt" decisions at that slot. This is the latent variable `Z` in
[odonnell-2015] §3.1.8.

Consistency between `Z`, `Y` (table assignment), and the observed
corpus `D` is the responsibility of the caller (or of the MAP
inference step we do not formalize).
-/
abbrev HaltCounts (G : ContextFreeGrammar T) : Type :=
  ContextFreeRule T G.NT → ℕ → ℕ × ℕ

variable (M : FragmentGrammar G)

/--
Per-(rule, position) beta-binomial factor in the eq from §3.1.8.
For pseudo-counts `α = haltPriorRecurse r i`, `β = haltPriorHalt r i`,
and observed counts `(zr, zh) = Z r i`,

```
B(α + zr, β + zh) / B(α, β)
  = Γ(α+zr)·Γ(β+zh)·Γ(α+β) / (Γ(α+β+zr+zh)·Γ(α)·Γ(β)) .
```

Inlined via `Real.Gamma` rather than mathlib's
`ProbabilityTheory.beta` to avoid pulling in
`Mathlib.Probability.Distributions.Beta`.
-/
noncomputable def fgFactor (r : ContextFreeRule T G.NT) (i : ℕ)
    (z : ℕ × ℕ) : ℝ :=
  Gamma (M.haltPriorRecurse r i + z.1) *
  Gamma (M.haltPriorHalt r i + z.2) *
  Gamma (M.haltPriorRecurse r i + M.haltPriorHalt r i) /
  (Gamma (M.haltPriorRecurse r i + M.haltPriorHalt r i +
          (z.1 : ℝ) + (z.2 : ℝ)) *
   Gamma (M.haltPriorRecurse r i) *
   Gamma (M.haltPriorHalt r i))

/--
FG corpus probability conditional on a table assignment `Y` and a
halt-count assignment `Z`. Per [odonnell-2015] §3.1.8:

```
fg(X, Y, Z; F) = ag(X, Y; A) · ∏_r ∏_i fgFactor r i (Z r i)
```

The AG part is inherited from `AdaptorGrammar.corpusProbGivenTables`
(via `extends`); FG adds only the per-(rule, position) Beta-
binomial factors.
-/
noncomputable def corpusProbGivenStorage
    (D : Multiset (CFGTree T G.NT))
    (Y : AdaptorGrammar.TableAssignment G)
    (Z : HaltCounts G) : ℝ :=
  M.toAdaptorGrammar.corpusProbGivenTables D Y *
  ∏ r ∈ G.rules, ∏ i ∈ Finset.range r.output.length,
    M.fgFactor r i (Z r i)

/-- The per-(rule, position) factor is strictly positive. -/
theorem fgFactor_pos (r : ContextFreeRule T G.NT) (i : ℕ) (z : ℕ × ℕ) :
    0 < M.fgFactor r i z := by
  have h_α_pos : 0 < M.haltPriorRecurse r i := M.haltPriorRecurse_pos r i
  have h_β_pos : 0 < M.haltPriorHalt r i := M.haltPriorHalt_pos r i
  have h_zr_nn : (0 : ℝ) ≤ (z.1 : ℝ) := Nat.cast_nonneg _
  have h_zh_nn : (0 : ℝ) ≤ (z.2 : ℝ) := Nat.cast_nonneg _
  have h_α_zr_pos : 0 < M.haltPriorRecurse r i + (z.1 : ℝ) := by linarith
  have h_β_zh_pos : 0 < M.haltPriorHalt r i + (z.2 : ℝ) := by linarith
  have h_αβ_pos : 0 < M.haltPriorRecurse r i + M.haltPriorHalt r i := by linarith
  have h_αβ_z_pos :
      0 < M.haltPriorRecurse r i + M.haltPriorHalt r i +
          (z.1 : ℝ) + (z.2 : ℝ) := by linarith
  unfold fgFactor
  refine div_pos ?_ ?_
  · refine mul_pos (mul_pos ?_ ?_) ?_
    · exact Gamma_pos_of_pos h_α_zr_pos
    · exact Gamma_pos_of_pos h_β_zh_pos
    · exact Gamma_pos_of_pos h_αβ_pos
  · refine mul_pos (mul_pos ?_ ?_) ?_
    · exact Gamma_pos_of_pos h_αβ_z_pos
    · exact Gamma_pos_of_pos h_α_pos
    · exact Gamma_pos_of_pos h_β_pos

/-- FG corpus probability is nonnegative on any storage assignment. -/
theorem corpusProbGivenStorage_nonneg
    (D : Multiset (CFGTree T G.NT))
    (Y : AdaptorGrammar.TableAssignment G)
    (Z : HaltCounts G) : 0 ≤ M.corpusProbGivenStorage D Y Z := by
  unfold corpusProbGivenStorage
  refine mul_nonneg ?_ ?_
  · exact M.toAdaptorGrammar.corpusProbGivenTables_nonneg D Y
  · apply Finset.prod_nonneg
    intro r _
    apply Finset.prod_nonneg
    intro i _
    exact (M.fgFactor_pos r i (Z r i)).le

/-- The "empty" halt-count assignment: zero recurse-decisions and
    zero halt-decisions at every (rule, position) pair. The
    corresponding `fgFactor` evaluates to `1` because the Beta-
    binomial ratio is `B(α, β) / B(α, β) = 1`. -/
def emptyHaltCounts (G : ContextFreeGrammar T) : HaltCounts G :=
  fun _ _ => (0, 0)

/-- The per-(rule, position) factor at zero counts is `1`: the
    Beta-binomial ratio degenerates to `B(α, β) / B(α, β)`. -/
@[simp]
theorem fgFactor_zero (r : ContextFreeRule T G.NT) (i : ℕ) :
    M.fgFactor r i (0, 0) = 1 := by
  unfold fgFactor
  have h_Γα : 0 < Gamma (M.haltPriorRecurse r i) :=
    Gamma_pos_of_pos (M.haltPriorRecurse_pos r i)
  have h_Γβ : 0 < Gamma (M.haltPriorHalt r i) :=
    Gamma_pos_of_pos (M.haltPriorHalt_pos r i)
  have h_Γαβ : 0 < Gamma (M.haltPriorRecurse r i + M.haltPriorHalt r i) :=
    Gamma_pos_of_pos (by
      linarith [M.haltPriorRecurse_pos r i, M.haltPriorHalt_pos r i])
  simp only [Nat.cast_zero, add_zero]
  field_simp

/-- FG corpus probability is `1` on the empty corpus paired with
    the empty table assignment and empty halt-count assignment.
    Each `fgFactor` is `1`, the AG factor is `1`, so the overall
    product is `1`. -/
@[simp]
theorem corpusProbGivenStorage_empty :
    M.corpusProbGivenStorage (0 : Multiset (CFGTree T G.NT))
      (AdaptorGrammar.emptyTables G) (emptyHaltCounts G) = 1 := by
  unfold corpusProbGivenStorage
  rw [show M.toAdaptorGrammar.corpusProbGivenTables 0 (AdaptorGrammar.emptyTables G) = 1
      from M.toAdaptorGrammar.corpusProbGivenTables_empty]
  rw [one_mul]
  apply Finset.prod_eq_one
  intro r _
  apply Finset.prod_eq_one
  intro i _
  show M.fgFactor r i ((emptyHaltCounts G) r i) = 1
  unfold emptyHaltCounts
  exact M.fgFactor_zero r i

/-! ## Bridge: FragmentGrammar → MultinomialPCFG via posterior MAP

FG = AG + per-(rule, RHS-position) beta-binomial halt prior. Like
PYP in AG, the halt-prior factor is multiplicative in
`corpusProbGivenStorage` and does not enter per-LHS rule-weight
inference. So FG's posterior MAP rule weights factor through AG
which factors through DMPCFG.

The "tower equality" `FG.posteriorMAP D = AG.posteriorMAP D =
DMPCFG.posteriorMAP D` is structural — every layer above DMPCFG in
the prior tower is purely additive on rule-weight inference. This
is the architectural payoff: the family-of-priors structure
(`extends` chain) is genuinely "richer hyperparameter sets," not
"different rule-weight semantics." -/

/-- The Dirichlet posterior MAP collapse for FG. Same one-liner as
    AG, factoring transitively through `extends`: FG → AG → DMPCFG.
    The beta-binomial halt prior contributes a multiplicative factor
    to corpus probability but does not alter rule-weight inference. -/
noncomputable def posteriorMAP [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) : MultinomialPCFG G :=
  M.toAdaptorGrammar.posteriorMAP D

/-- **Coherence (one step).** FG's posterior-MAP agrees with AG's
    posterior-MAP. Holds by `rfl` — FG only adds halt priors on top
    of AG; rule-weight inference is unchanged. -/
theorem posteriorMAP_eq_toAdaptorGrammar
    [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    M.posteriorMAP D = M.toAdaptorGrammar.posteriorMAP D := rfl

/-- **Coherence (two steps).** FG's posterior-MAP agrees with the
    underlying DMPCFG's posterior-MAP. The "prior tower" of length
    three collapses to a single canonical MultinomialPCFG by `rfl`. -/
theorem posteriorMAP_eq_toDMPCFG
    [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    M.posteriorMAP D = M.toAdaptorGrammar.toDMPCFG.posteriorMAP D := rfl

/-! ## Conjugacy decomposition (mirror of AG / DMPCFG)

FG's posterior delegates through AG which delegates through DMPCFG.
Halt-prior pseudo-counts are unchanged by corpus updates (the
beta-binomial layer doesn't see corpus rule counts). Mode delegates
to the underlying DMPCFG. The decomposition holds by `rfl` at all
three layers, witnessing the rfl-tower discovery (the prior tower's
extends-chain is structurally orthogonal to rule-weight inference). -/

/-- FG's posterior update: bump the underlying AG/DMPCFG, leave
    halt-prior pseudo-counts unchanged. -/
noncomputable def posterior (D : Multiset (CFGTree T G.NT)) : FragmentGrammar G :=
  { M with toAdaptorGrammar := M.toAdaptorGrammar.posterior D }

/-- FG's mode in `MultinomialPCFG`-space: delegates through AG to
    DMPCFG. Halt-prior pseudo-counts contribute no rule-weight mass. -/
noncomputable def mode [∀ a : G.NT, Nonempty (G.RulesWithLHS a)] :
    MultinomialPCFG G :=
  M.toAdaptorGrammar.mode

/-- Empty corpus = identity update (delegated to `AG.posterior_zero`). -/
@[simp]
theorem posterior_zero : M.posterior 0 = M := by
  ext1 <;> simp [posterior, AdaptorGrammar.posterior_zero]

/-- Incrementality at the FG layer. -/
theorem posterior_add (D₁ D₂ : Multiset (CFGTree T G.NT)) :
    M.posterior (D₁ + D₂) = (M.posterior D₁).posterior D₂ := by
  ext1 <;> simp [posterior, AdaptorGrammar.posterior_add]

/-- **The conjugacy decomposition at FG layer.** `posteriorMAP =
    mode ∘ posterior`, holding by `rfl` because all FG operations
    delegate through DMPCFG. -/
theorem posteriorMAP_eq_mode_posterior [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    M.posteriorMAP D = (M.posterior D).mode :=
  M.toAdaptorGrammar.toDMPCFG.posteriorMAP_eq_mode_posterior D

end FragmentGrammar

end Morphology.FragmentGrammars
