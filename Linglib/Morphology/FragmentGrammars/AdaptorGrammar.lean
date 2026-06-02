import Linglib.Morphology.FragmentGrammars.DMPCFG
import Linglib.Core.Probability.PitmanYor
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Adaptor grammars (Maximum a posteriori variant: MAG)

[odonnell-2015]

The "full-listing" model of [odonnell-2015] §2.4.2 / §3.1.7: a
Dirichlet–multinomial PCFG (rule weights with conjugate Dirichlet
prior) augmented with a per-LHS Pitman–Yor process for memoizing
subtree expansions. Each nonterminal `A` carries a PYP "restaurant"
whose tables hold previously-computed subderivations rooted at `A`;
new derivations either reuse a stored subtree (with probability
proportional to its current table occupancy) or productively compute
a fresh subtree from the underlying CFG.

Per [odonnell-2015] §3.1.7 the corpus probability factorizes
per-LHS as

```
ag(X, Y; A) = ∏_{A ∈ V} [DMPCFG-factor for A on X^A]
                       · [PYP-factor for A on Y^A]
```

where `X^A` is the rule-count vector for LHS `A` (the same data
DMPCFG consumes) and `Y^A` is the table-occupancy assignment for
`A`'s restaurant — formally a *set partition* of `[N^A]` (the `N^A`
uses of NT `A` in the corpus, partitioned by which table each use
sat at).

## Why a set partition (not a multiset)?

[odonnell-2015] writes `Y^A = ȳ^A` as a "count vector of reused
derivations stored on each table". Tables in O'Donnell's PYP are
*labeled* (table 1, 2, ...) — each table stores a specific
subderivation, and different tables store different ones (line 91-92
of the book). The natural mathematical object is therefore "for each
NT-A use in the corpus, which table did it go to?", i.e. a customer-
to-table assignment function. Each set partition of `[N^A]` corresponds
to exactly one labeled assignment under any canonical labeling
convention.

The EPPF formula `[θ + α]_{K-1, α} · ∏ [1 - α]_{n_i - 1, 1} /
[θ + 1]_{N - 1, 1}` ([pitman-2006] Thm 3.2 / [odonnell-2015]
eq from §3.1.7) is precisely the probability of one such specific set
partition. By the EPPF's symmetry it depends only on the multiset of
block sizes — but the underlying random variable is the set partition
itself.

We model `TableAssignment` as `G.NT → Σ n, OrderedFinpartition n` using
mathlib's `OrderedFinpartition n` (the structure mathlib uses for
Faà di Bruno; it represents a set partition of `Fin n` with a canonical
labeling by greatest element). The choice of `OrderedFinpartition` over
`Finpartition` is for the proof of `sum_partitionProb_ord_eq_one`:
mathlib's `OrderedFinpartition.extendEquiv` gives the seating-plan
bijection
`(c : OrderedFinpartition n) × Option (Fin c.length) ≃ OrderedFinpartition (n+1)`
out of the box, exactly matching Pitman's (α, θ) seating-plan
recursion. `Finpartition` lacks this bijection lemma. Either type
admits the same number of objects (one per set partition of `[n]`)
and `partitionProb` only depends on the block-size multiset, so the
choice is purely about which lemmas come for free. `pypFactor`
extracts the block-size multiset (via `OrderedFinpartition.toNatPartition`)
to evaluate the EPPF.

## Why corpus probability is `(D, Y) → ℝ`, not `D → ℝ`

`Y^A` is *latent* — it is part of the MAP analysis, not part of the
observed corpus. To reduce to `D → ℝ` we would have to marginalize
over all possible `Y`, which is exactly the MH inference target
distribution of [odonnell-2015] §3.2.1 — out of scope per the
"Processing scope" rule (we formalize target distributions, not
inference algorithms). The honest signature is `(D, Y) → ℝ`: the
closed-form probability *given* a particular table assignment.

The mathlib analog is `MeasureTheory.Kernel`: AG defines a kernel
from corpora to table assignments, and the marginal distribution on
corpora is `kernel.bind` against the prior — a perfectly
well-defined object that we do not compute.

## What we inherit from `DMPCFG`

`AdaptorGrammar G extends DMPCFG G`, so `pseudo`, `pseudo_pos`,
`lhsUrn`, `lhsCounts`, `lhsFactor`, `lhsFactor_pos` are all
inherited. AG adds only the per-LHS Pitman–Yor process and the PYP
factor.

## Main definitions

- `AdaptorGrammar G` — extends `DMPCFG G` with per-LHS Pitman–Yor.
- `AdaptorGrammar.TableAssignment` — abbrev for the latent table
  data: per LHS, a set partition of `[N^A]`.
- `AdaptorGrammar.pypFactor` — per-LHS Pitman–Yor partition
  probability (EPPF evaluated on the block-size multiset).
- `AdaptorGrammar.corpusProbGivenTables` — eq from §3.1.7, conditional
  on a table assignment.

## References

- [odonnell-2015] §2.4.2, §3.1.7.
- [pitman-2006] §3.2 (EPPF and the (α, θ) seating plan).
-/

namespace Morphology.FragmentGrammars

open ProbabilityTheory

/--
An adaptor grammar over `G`: a Dirichlet–multinomial PCFG plus a
per-LHS Pitman–Yor process for memoization. Each nonterminal's PYP
restaurant stores subderivations rooted at that nonterminal; new
derivations may reuse stored subtrees or productively compute fresh
ones.
-/
@[ext]
structure AdaptorGrammar {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] extends DMPCFG G where
  /-- Per-LHS Pitman–Yor process for memoizing subtree expansions. -/
  pyp : G.NT → PitmanYor

namespace AdaptorGrammar

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/--
A *table assignment* gives, for each nonterminal `A`, a set partition
of `[N^A]` (the uses of `A` in the corpus) into tables. Two uses are
in the same block iff they sat at the same table. This is the latent
variable `Y` in [odonnell-2015] eq from §3.1.7; see the module
docstring for why a set partition (not a multiset of sizes) is the
right type.

Bundled as `Σ n, OrderedFinpartition n` per LHS so the total number of
customers `n` is exposed but not constrained to match `corpusSumLHS`
automatically — consistency between `Y` and the observed corpus `D` is
the responsibility of the caller (or of a MAP-inference step we do
not formalize). `OrderedFinpartition` is mathlib's canonically-ordered
set-partition type (parts ordered by greatest element); the ordering
is irrelevant for `pypFactor` (which depends only on block-size
multiset) but unlocks `extendEquiv` for the sum-to-1 proof.
-/
abbrev TableAssignment (G : ContextFreeGrammar T) : Type :=
  G.NT → Σ n, OrderedFinpartition n

variable (M : AdaptorGrammar G)

/--
Per-LHS Pitman–Yor factor for the eq from §3.1.7 product: the
Pitman–Yor EPPF evaluated on the block-size multiset of the table
assignment under `M.pyp a`. Pitman's EPPF gives the prob of one
specific set partition with these block sizes
([pitman-2006] Thm 3.2).
-/
noncomputable def pypFactor (a : G.NT) (Y : TableAssignment G) : ℝ :=
  (M.pyp a).partitionProb (Y a).snd.toNatPartition

/--
AG corpus probability conditional on a table assignment `Y`. Per
[odonnell-2015] §3.1.7:

```
ag(X, Y; A) = ∏_{A ∈ V} [DMPCFG-factor on X^A] · [PYP-factor on Y^A]
```

Inherits the DMPCFG part from `DMPCFG.lhsFactor` (via `extends`);
adds the PYP factor per LHS.
-/
noncomputable def corpusProbGivenTables (D : Multiset (CFGTree T G.NT))
    (Y : TableAssignment G) : ℝ :=
  ∏ a ∈ G.rules.image (·.input),
    M.toDMPCFG.lhsFactor a D * M.pypFactor a Y

/-- AG corpus probability is nonnegative on any table assignment.
    Each per-LHS factor is `[DMPCFG-positive] · [PYP-nonneg]`. -/
theorem corpusProbGivenTables_nonneg (D : Multiset (CFGTree T G.NT))
    (Y : TableAssignment G) : 0 ≤ M.corpusProbGivenTables D Y := by
  unfold corpusProbGivenTables
  apply Finset.prod_nonneg
  intro a ha
  exact mul_nonneg (M.toDMPCFG.lhsFactor_pos ha D).le
    ((M.pyp a).partitionProb_nonneg (Y a).snd.toNatPartition)
    -- ↑ `PitmanYor.partitionProb_nonneg` (different file from `PolyaUrn`)

/-- The "empty" table assignment: every nonterminal gets the
    unique `OrderedFinpartition 0` (the empty partition, supplied
    by mathlib's `Unique` instance). The corresponding PYP factor
    evaluates to 1, so this is the natural Y to use when stating the
    empty-corpus probability. -/
def emptyTables (G : ContextFreeGrammar T) : TableAssignment G :=
  fun _ => ⟨0, default⟩

/-- AG corpus probability is `1` on the empty corpus paired with
    the empty table assignment: each per-LHS factor is
    `DMPCFG.lhsFactor a 0 · PitmanYor.partitionProb (empty) = 1 · 1`. -/
@[simp]
theorem corpusProbGivenTables_empty :
    M.corpusProbGivenTables (0 : Multiset (CFGTree T G.NT)) (emptyTables G) = 1 := by
  unfold corpusProbGivenTables
  apply Finset.prod_eq_one
  intro a ha
  haveI := DMPCFG.nonempty_rulesWithLHS_of_mem_image ha
  show M.toDMPCFG.lhsFactor a 0 * M.pypFactor a (emptyTables G) = 1
  have h_dm : M.toDMPCFG.lhsFactor a 0 = 1 := by
    unfold DMPCFG.lhsFactor
    rw [DMPCFG.lhsCounts_zero]
    exact (M.toDMPCFG.lhsUrn a).seqProb_zero
  have h_py : M.pypFactor a (emptyTables G) = 1 := by
    -- emptyTables a = ⟨0, default⟩ with default : OrderedFinpartition 0
    -- has length 0, partSize empty, so toNatPartition is the unique
    -- Nat.Partition 0, and partitionProb evaluates to 1.
    show (M.pyp a).partitionProb
        (OrderedFinpartition.toNatPartition (default : OrderedFinpartition 0)) = 1
    rw [Subsingleton.elim
        (OrderedFinpartition.toNatPartition (default : OrderedFinpartition 0))
        (default : Nat.Partition 0)]
    simp [PitmanYor.partitionProb, default, Nat.Partition.indiscrete]
  rw [h_dm, h_py, mul_one]

/-! ## Bridge: AdaptorGrammar → MultinomialPCFG via posterior MAP

An AG is a *prior over* multinomial PCFGs: the per-LHS rule weights
have a Dirichlet prior (inherited from the underlying DMPCFG via
`extends`), augmented with PYP table state. The PYP component is a
multiplicative factor in `corpusProbGivenTables` that does not enter
the per-LHS rule-weight inference — DMPCFG's `lhsFactor a D` consumes
the same corpus rule counts whether or not stored fragments are
reused (under this Lean formalization; see the AG module docstring
for the simplification relative to [odonnell-2015] §3.1.7).

Consequence: the posterior MAP rule weights of an AG are exactly the
posterior MAP rule weights of its underlying DMPCFG. The bridge is a
one-liner. The PYP layer is "purely additive" on the prior tower:
it multiplies corpus probability without disturbing rule-weight
estimation. -/

/-- The Dirichlet posterior MAP collapse for AG: package per-LHS
    posterior MAP weights (inherited from the underlying DMPCFG) as a
    `MultinomialPCFG`. The PYP component does not contribute — see the
    section docstring above. -/
noncomputable def posteriorMAP [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) : MultinomialPCFG G :=
  M.toDMPCFG.posteriorMAP D

/-- **Coherence.** AG's posterior-MAP MultinomialPCFG agrees with
    the underlying DMPCFG's posterior-MAP MultinomialPCFG. Holds by
    `rfl` — AG's rule-weight inference IS DMPCFG's rule-weight
    inference. The "prior tower" claim made formal at this layer. -/
theorem posteriorMAP_eq_toDMPCFG [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    M.posteriorMAP D = M.toDMPCFG.posteriorMAP D := rfl

/-! ## Conjugacy decomposition (mirror of DMPCFG)

AG inherits Dirichlet conjugacy on its DMPCFG component: the posterior
of an AG given a corpus is again an AG, with the DMPCFG component
updated and the PYP component unchanged. The mode projection (= mean,
in CL convention) delegates to `DMPCFG.mode`. The decomposition
`posteriorMAP = mode ∘ posterior` therefore holds by `rfl` at the AG
layer too. -/

/-- AG's posterior update: bump the underlying DMPCFG's pseudo-counts
    by the corpus rule counts (Dirichlet conjugacy on the DMPCFG
    component), leave PYP table state unchanged. -/
noncomputable def posterior (D : Multiset (CFGTree T G.NT)) : AdaptorGrammar G :=
  { M with toDMPCFG := M.toDMPCFG.posterior D }

/-- AG's mode in `MultinomialPCFG`-space: the mode of the underlying
    DMPCFG. The PYP component does not contribute to rule-weight
    inference. -/
noncomputable def mode [∀ a : G.NT, Nonempty (G.RulesWithLHS a)] :
    MultinomialPCFG G :=
  M.toDMPCFG.mode

/-- Empty corpus = identity update (delegated to `DMPCFG.posterior_zero`). -/
@[simp]
theorem posterior_zero : M.posterior 0 = M := by
  ext1 <;> simp [posterior, DMPCFG.posterior_zero]

/-- Incrementality at the AG layer (delegated to `DMPCFG.posterior_add`). -/
theorem posterior_add (D₁ D₂ : Multiset (CFGTree T G.NT)) :
    M.posterior (D₁ + D₂) = (M.posterior D₁).posterior D₂ := by
  ext1 <;> simp [posterior, DMPCFG.posterior_add]

/-- **The conjugacy decomposition at AG layer.** `posteriorMAP =
    mode ∘ posterior`, holding by `rfl` because both AG operations
    delegate through DMPCFG's. -/
theorem posteriorMAP_eq_mode_posterior [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]
    (D : Multiset (CFGTree T G.NT)) :
    M.posteriorMAP D = (M.posterior D).mode :=
  M.toDMPCFG.posteriorMAP_eq_mode_posterior D

end AdaptorGrammar

end Morphology.FragmentGrammars
