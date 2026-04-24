import Linglib.Theories.Morphology.FragmentGrammars.DMPCFG
import Linglib.Core.Probability.PitmanYor

/-!
# Adaptor grammars (Maximum a posteriori variant: MAG)

@cite{odonnell-2015}

The "full-listing" model of @cite{odonnell-2015} §2.4.2 / §3.1.7: a
Dirichlet–multinomial PCFG (rule weights with conjugate Dirichlet
prior) augmented with a per-LHS Pitman–Yor process for memoizing
subtree expansions. Each nonterminal `A` carries a PYP "restaurant"
whose tables hold previously-computed subderivations rooted at `A`;
new derivations either reuse a stored subtree (with probability
proportional to its current table occupancy) or productively compute
a fresh subtree from the underlying CFG.

Per @cite{odonnell-2015} §3.1.7 the corpus probability factorizes
per-LHS as

```
ag(X, Y; A) = ∏_{A ∈ V} [DMPCFG-factor for A on X^A]
                       · [PYP-factor for A on Y^A]
```

where `X^A` is the rule-count vector for LHS `A` (the same data
DMPCFG consumes) and `Y^A` is the table-occupancy partition for
`A`'s restaurant — i.e. the multiset of "how many customers sat at
each table" once the corpus is fully decomposed.

## Why corpus probability is `(D, Y) → ℝ`, not `D → ℝ`

`Y^A` is *latent* — it is part of the MAP analysis, not part of the
observed corpus. To reduce to `D → ℝ` we would have to marginalize
over all possible `Y`, which is exactly the MH inference target
distribution of @cite{odonnell-2015} §3.2.1 — out of scope per the
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
  data: per LHS, a partition (multiset of positive table sizes).
- `AdaptorGrammar.pypFactor` — per-LHS Pitman–Yor partition
  probability.
- `AdaptorGrammar.corpusProbGivenTables` — eq from §3.1.7, conditional
  on a table assignment.

## References

- @cite{odonnell-2015} §2.4.2, §3.1.7.
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
A *table assignment* gives, for each nonterminal `A`, the
multiset-of-positive-counts of customer occupancies at the tables
of `A`'s Pitman–Yor restaurant. This is the latent variable `Y` in
@cite{odonnell-2015} eq from §3.1.7.

Bundled as `Σ n, Nat.Partition n` per LHS so the total number of
customers `n` (sum of table sizes) is exposed but not constrained
to match `corpusSumLHS` automatically — consistency between `Y` and
the observed corpus `D` is the responsibility of the caller (or of a
MAP-inference step we do not formalize).
-/
abbrev TableAssignment (G : ContextFreeGrammar T) : Type :=
  G.NT → Σ n, Nat.Partition n

variable (M : AdaptorGrammar G)

/--
Per-LHS Pitman–Yor factor for the eq from §3.1.7 product: the
Pitman–Yor partition probability of the table-occupancy partition
under `M.pyp a`.
-/
noncomputable def pypFactor (a : G.NT) (Y : TableAssignment G) : ℝ :=
  (M.pyp a).partitionProb (Y a).snd

/--
AG corpus probability conditional on a table assignment `Y`. Per
@cite{odonnell-2015} §3.1.7:

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
    ((M.pyp a).partitionProb_nonneg (Y a).snd)
    -- ↑ `PitmanYor.partitionProb_nonneg` (different file from `PolyaUrn`)

/-- The "empty" table assignment: every nonterminal gets the
    `Nat.Partition 0` consisting of no tables. The corresponding
    PYP factor evaluates to 1, so this is the natural Y to use
    when stating the empty-corpus probability. -/
def emptyTables (G : ContextFreeGrammar T) : TableAssignment G :=
  fun _ => ⟨0, { parts := 0,
                  parts_pos := fun {i} h => absurd h (Multiset.notMem_zero i),
                  parts_sum := rfl }⟩

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
    unfold pypFactor emptyTables
    -- The empty Nat.Partition 0 has parts.card = 0 and total = 0,
    -- so all stepPochhammer m-values are 0, products are empty = 1
    simp [PitmanYor.partitionProb]
  rw [h_dm, h_py, mul_one]

end AdaptorGrammar

end Morphology.FragmentGrammars
