import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Linglib.Theories.Morphology.FragmentGrammars.FragmentGrammar

/-!
# Operational fragment-lambda: a stochastic-lazy unfold sampler

@cite{odonnell-2015}

This file gives an **operational** counterpart to the substrate in
`FragmentGrammar.lean`. Where `FragmentGrammar` formalises the *joint
density* `fg(F; F)` of @cite{odonnell-2015} §3.1.8 (p. 94) — the
probability of a corpus given a table assignment and halt counts —
this file formalises the *sampler* that draws from that density.

The architecture follows the macro-expansion of @cite{odonnell-2015}
§2.3.7 Figure 2.21:

```
(fragment-lambda args body)
  ↦  (PYmem a b (lambda args (if (delay? args) (delay body) body)))
```

mapping each Church construct to a Lean component:

- `(PYmem a b _)` ⤳ `pypDraw` over `PYPState` with `PYM := StateT _ PMF`
  (Pitman-Yor stochastic memoisation per §2.3.3.2 / §3.1.6).
- `(if (delay? args) (delay body) body)` ⤳ `PMF.bernoulli` halt-coin per
  §3.1.8 (p. 92): "this decision is made by flipping a biased coin —
  a binomial distribution with parameter ν not necessarily equal to 0.5".
- The `(delay body)` thunks ⤳ `LazyTree.fragment` constructor: a
  partial derivation tree whose leaves include unforced non-terminals.

## Why operational and not just §3.1.8 distribution

The substrate `FragmentGrammar.corpusProbGivenStorage` is the *target*
distribution. The sampler in this file is what makes the model
*operational* — it lets a downstream consumer simulate fragment-grammar
draws, not merely score corpora. The bridge is the soundness contract
`fragmentLambdaDepth_marginalises_to_fg` (statement only; proof
deferred — see TODO).

## What is intentionally `sorry` / out of scope

The file is a **scaffold**: types and operation shapes are present at
mathlib quality, but several pieces are deferred:

1. **`pypDraw` weighted choice** — the K+1-way choice between existing
   tables and a fresh one needs ENNReal arithmetic and a `PMF.ofFinset`-
   style construction; the architecture is in the docstring, the proof
   is `sorry`.
2. **`fragmentLambdaDepth` child threading** — recursive expansion of
   non-terminal children needs careful state-passing through `mapM`;
   sketch in the function, `sorry`-marked.
3. **Soundness theorem proof** — equating the depth-∞ limit of sample
   marginals with `corpusProbGivenStorage` requires probabilistic-
   fixed-point machinery (an order-theoretic Knaster-Tarski for
   ω-CPPOs of PMFs) absent from mathlib. The theorem statement is the
   contract; the `sorry` is honestly deferred infrastructure.
4. **Universal version** — a polymorphic
   `fragmentLambda : (α → Free F β) → α → Free (PYP ⊕ Halt ⊕ F) β`
   over arbitrary generative effects `F` would require `Free` monad
   infrastructure absent from mathlib (cf. Heunen–Kammar–Staton–Yang
   LICS 2017 quasi-Borel spaces for the categorical-PPL framing). Not
   in scope here.
5. **Inference (§3.2 Metropolis–Hastings)** — a separate file's worth.

## Hyperparameters used in @cite{odonnell-2015}

§3.5.5 (p. 102) reports the simulations in the book use `a = 0.5`,
`b = 100` for all PYP restaurants; `ψ_B = 50` for all RHS NTs in the
beta-binomial; `π_i = 1` for all DM-PCFG rules. These are
configuration choices, not theorems — not encoded here as defaults.

## References

- @cite{odonnell-2015} §2.3.7 (Figure 2.21, p. 71 — fragment-lambda
  Church macro), §3.1.8 (p. 92-94 — the actual halt-prior model),
  §3.5.5 (p. 102 — hyperparameters).
- Stochastic memoisation as a Church language primitive is from
  Goodman, Mansinghka, Roy, Bonawitz, Tenenbaum (UAI 2008) — the
  Church paper. Memoisation as an AI/learning technique originates
  with Michie 1968 (*Nature* 218: 19–22, "Memo functions and machine
  learning"); @cite{odonnell-2015} §2.3.3 cites both.
-/

namespace Morphology.FragmentGrammars.Operational

/-! ## Pitman–Yor memoisation state -/

/-- A Pitman–Yor memoisation slot for one input value. We track:
- `dishes` — the value sampled at the i-th distinct table
- `customerCounts` — how many customers have sat at each table

The lists are kept length-equal by the public API (`empty`, `seatCustomer`,
`addTable`); we don't enforce this as a structural invariant. Per
@cite{odonnell-2015} footnote 14 (p. 60), multiple tables may share a dish,
which is why we keep `dishes` as a list rather than a set or finmap. -/
structure PYPSlot (D : Type) where
  dishes : List D
  customerCounts : List ℕ
  deriving Inhabited

namespace PYPSlot

variable {D : Type}

@[simp] def empty : PYPSlot D := ⟨[], []⟩

/-- Total customers seated at this slot (`N` in the book's notation). -/
@[simp] def numCustomers (s : PYPSlot D) : ℕ := s.customerCounts.sum

/-- Number of occupied tables at this slot (`K` in the book's notation). -/
@[simp] def numTables (s : PYPSlot D) : ℕ := s.dishes.length

/-- Seat one more customer at the existing table indexed by `i`.
Out-of-range indices leave the slot unchanged (the public API never
constructs them). -/
def seatCustomer (s : PYPSlot D) (i : ℕ) : PYPSlot D :=
  { s with customerCounts := s.customerCounts.modify i (· + 1) }

/-- Open a fresh table with dish `v` and one initial customer. -/
def addTable (s : PYPSlot D) (v : D) : PYPSlot D :=
  ⟨s.dishes ++ [v], s.customerCounts ++ [1]⟩

end PYPSlot

/-- Pitman–Yor hyperparameters: discount `a ∈ [0, 1)` and concentration
`b ≥ -a`. @cite{odonnell-2015} §3.5.5 (p. 102) sets `a = 0.5`, `b = 100`. -/
structure PYPHyper where
  discount : ℝ
  concentration : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1
  concentration_ge : -discount ≤ concentration

/-- Global Pitman–Yor memoisation state: per-input slot states (one
"restaurant" per input value) plus shared hyperparameters. -/
structure PYPState (α D : Type) where
  slots : α → PYPSlot D
  hyper : PYPHyper

namespace PYPState

variable {α D : Type}

/-- Empty memoisation state (no customers anywhere). -/
def empty (h : PYPHyper) : PYPState α D :=
  ⟨fun _ => PYPSlot.empty, h⟩

/-- Update the slot at input `x`, leaving all others unchanged. -/
def updateSlot [DecidableEq α] (st : PYPState α D) (x : α) (s : PYPSlot D) :
    PYPState α D :=
  { st with slots := fun y => if y = x then s else st.slots y }

end PYPState

/-! ## The PYP-memoised stochastic monad

`PYM α D γ` is the type of `γ`-valued stochastic computations whose state
is a Pitman–Yor memoisation table over inputs `α` storing dishes of type `D`.
This is the monad-stack equivalent of the `(PYmem a b _)` wrapper in
@cite{odonnell-2015} Figure 2.21. -/

abbrev PYM (α D γ : Type) := StateT (PYPState α D) PMF γ

namespace PYM

variable {α D γ : Type}

/-- Lift a state-free PMF sample into PYM. -/
noncomputable def liftBase (p : PMF γ) : PYM α D γ :=
  fun st => p.bind (fun v => PMF.pure (v, st))

end PYM

/-! ## Pitman–Yor draw

Per @cite{odonnell-2015} §2.3.3.2 (p. 59) and §3.1.6 (p. 89), the
(N+1)-th customer at a slot sits at:

- existing table `i` (1 ≤ i ≤ K) with weight `(yᵢ − a) / (N + b)`
- a fresh new table with weight `(K·a + b) / (N + b)`

where `yᵢ` is the count at table `i`, `N = Σyᵢ`, `K` = number of tables,
`a` = `hyper.discount`, `b` = `hyper.concentration`. -/

/-- Sample from the PYP at slot `x` with base distribution `base`.

Either reuse the dish at an existing table (with the §3.1.6 weights), or
sample a fresh dish from `base` and seat the new customer at a new table.
Both branches update the memo state appropriately.

**Status: scaffold (`sorry`).** The architecture is fixed; the K+1-way
weighted choice and the ENNReal arithmetic for the table weights are
deferred. A faithful implementation requires:

1. Building `weights : Fin (K+1) → ℝ≥0∞` for the existing-table and
   new-table branches.
2. A `PMF.ofFn` / `PMF.ofFinset`-style construction normalising the
   weights and yielding a `PMF (Fin (K+1))`.
3. Branching on the choice: existing-table updates `seatCustomer`; new-
   table samples from `base` and updates `addTable`.

The base distribution is `PYM`-typed (state-passing) rather than the
usual `PMF`-typed because in fragment-lambda the recursive children of
a fresh sample themselves invoke the memo (via `mem{L^B}` for B≠A in
the §3.1.8 equations). The slots for distinct inputs are independent,
so this state-threading is well-defined; a per-restaurant `PMF` base
would suffice if the children's states were marginalised first.
-/
noncomputable def pypDraw {α D : Type} [DecidableEq α]
    (_base : α → PYM α D D) (_x : α) : PYM α D D := by
  -- TODO: see docstring for the architecture sketch.
  sorry

/-! ## Lazy partial derivation trees -/

/-- A partial derivation tree under fragment-grammar generation:

- `terminal t` — a fully-evaluated terminal symbol (the result of `unfold`
  reaching a terminal in @cite{odonnell-2015} Figure 2.7, p. 52)
- `fragment x` — a non-terminal stored as a fragment-leaf: the type-level
  representation of the `(delay body)` thunks of Figure 2.21 (p. 71). When
  the body of `fragment-lambda` flips heads on the halt coin, the result
  at this position is `fragment x` rather than further recursion.
- `branch x children` — a non-terminal that has been productively
  expanded; corresponds to the `unfold` recursion firing.

The "complete" tree (no fragment-leaves anywhere) is the result of
forcing all delayed thunks until termination. -/
inductive LazyTree (α β : Type) where
  | terminal : β → LazyTree α β
  | fragment : α → LazyTree α β
  | branch   : α → List (LazyTree α β) → LazyTree α β
  deriving Inhabited

namespace LazyTree

variable {α β : Type}

/-- The fragment-leaf frontier: the non-terminals stored as halted
sub-derivations (the "open slots" of a fragment, in @cite{odonnell-2015}
§3.1.8's terminology). -/
def fragmentLeaves : LazyTree α β → List α
  | .terminal _      => []
  | .fragment x      => [x]
  | .branch _ kids   => kids.flatMap fragmentLeaves

/-- The terminal yield: the in-order sequence of terminal symbols
reachable without forcing any fragment-leaf. -/
def yield : LazyTree α β → List β
  | .terminal t      => [t]
  | .fragment _      => []
  | .branch _ kids   => kids.flatMap yield

end LazyTree

/-! ## fragmentLambda — depth-bounded operational unfold

The depth bound is a structural-recursion device. The mathematically-
intended object is the depth-∞ limit, which terminates almost surely
when the recurse probability is bounded away from 1 (geometric depth).
Formalising the limit requires probabilistic-fixed-point machinery not
yet in mathlib; the bounded version is genuine and ships now. -/

variable {α β : Type} [DecidableEq α]

/-- Depth-bounded operational fragment-lambda. At each call to non-
terminal `x`:

1. **Memoisation step** (`pypDraw`): consult the PYP memo at slot `x`.
   With PYP-probability a previously-stored partial subtree at `x` is
   returned (representing reuse); otherwise we generate fresh below.
2. **Halt-or-recurse step** (when generating fresh): flip the biased
   coin (§3.1.8 BINOMIAL(ν)). With probability `1 − recurseProb x`,
   halt and return `LazyTree.fragment x`. Otherwise sample a RHS via
   `recurse x` and recursively expand each non-terminal child via
   `fragmentLambdaDepth` at the next-smaller depth; map each terminal
   to `LazyTree.terminal`.

Depth `0` always halts and returns `fragment`.

The §2.3.7 Church macro corresponds to `recurseProb x = 1/2` for all
`x` (fair coin, `BINOMIAL(0.5)`); the §3.1.8 model used in the book
allows arbitrary biased `recurseProb` and places a Beta prior on it
for inference.

**Status: scaffold (`sorry` in `sampleFresh`).** The recursive child
expansion needs careful state-threading; the type signature is fixed.
-/
noncomputable def fragmentLambdaDepth
    (recurse : α → PMF (List (α ⊕ β)))
    (recurseProb : α → ENNReal)
    (recurseProb_le : ∀ x, recurseProb x ≤ 1) :
    ℕ → α → PYM α (LazyTree α β) (LazyTree α β)
  | 0,     x => pure (.fragment x)
  | _ + 1, x => pypDraw (sampleFresh) x
where
  /-- The fresh-generation branch: flip the halt coin, then either
  halt-with-fragment or sample-and-recurse. -/
  sampleFresh : α → PYM α (LazyTree α β) (LazyTree α β) := by
    -- TODO: full body. Sketch:
    --   intro x
    --   let coin ← PYM.liftBase (PMF.bernoulli (recurseProb x) (recurseProb_le x))
    --   if coin then
    --     let rhs ← PYM.liftBase (recurse x)
    --     let kids ← rhs.mapM (fun
    --       | .inl nt   => fragmentLambdaDepth recurse recurseProb recurseProb_le n nt
    --       | .inr term => pure (.terminal term))
    --     pure (.branch x kids)
    --   else
    --     pure (.fragment x)
    -- Blocker: the recursive call's depth needs a `Decreasing_by` argument
    -- or to be lifted out of the `where` clause. Will be cleaned up in the
    -- next pass on this scaffold.
    sorry

/-! ## Soundness contract -/

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/-- Extract corpus-counts triple `(D, Y, Z)` from a completed sample.
Maps a `LazyTree` (with PYP final state) into the input shape that
`FragmentGrammar.corpusProbGivenStorage` expects:

- `D : Multiset (CFGTree T G.NT)` — the underlying derivation trees
- `Y : AdaptorGrammar.TableAssignment G` — table-level reuse counts
- `Z : FragmentGrammar.HaltCounts G` — recurse/halt counts per (rule, position)

**Status: deferred (`sorry`).** The extraction is mechanical given a
`LazyTree → CFGTree` projection that forces fragment-leaves (provided
by some completion strategy) and a state-walker that reads off table
and halt counts. It is the bridge from the operational sample shape
to the densimetric input shape; without it the soundness theorem
cannot even be stated cleanly. -/
noncomputable def samplesToCorpusCounts
    (_tree : LazyTree G.NT T) (_finalState : PYPState G.NT (LazyTree G.NT T)) :
    Multiset (CFGTree T G.NT) × AdaptorGrammar.TableAssignment G ×
    FragmentGrammar.HaltCounts G := by
  sorry

/-- **Soundness contract for the operational fragment-lambda.**

For any fragment grammar `M` with substrate `G`, recursion procedure
`recurse`, halt prior `recurseProb`, depth `n`, and starting non-terminal
`start`: the depth-`n` truncated probability mass that the sampler
assigns to a sample `(tree, finalState)` equals
`ENNReal.ofReal (M.corpusProbGivenStorage D Y Z)`, where `(D, Y, Z) =
samplesToCorpusCounts tree finalState`.

This says: the operational sampler distributes its outputs according to
the §3.1.8 fragment-grammar density of @cite{odonnell-2015}.

**Proof strategy** (for the deferred `sorry`):

1. Show the depth-`n` truncated distribution converges to a limit as
   `n → ∞`. Almost-sure halting from `recurseProb x < 1` for all `x`
   gives geometric-tail bounds; pass to the limit via dominated
   convergence on `PMF`.
2. Identify the limit's pmf with the §3.1.8 product formula by induction
   on the sample tree, matching each PYP draw with its table-count
   contribution to `M.toAdaptorGrammar.corpusProbGivenTables` and each
   biased-coin flip with its beta-binomial-ratio contribution to
   `M.fgFactor`.

Step 1 requires probabilistic-fixed-point machinery for monotone
PMF-valued recursions (Knaster–Tarski / Kleene fixed point on
ω-CPPOs of sub-probability measures) that mathlib does not yet have.
Step 2 is mechanical induction once Step 1 is in place.

The theorem statement IS the deliverable: it makes precise what
"FragmentLambda implements §3.1.8" means, and what would have to be
proved to discharge the implementation-correctness obligation.
-/
theorem fragmentLambdaDepth_marginalises_to_fg
    (M : FragmentGrammar G)
    (recurse : G.NT → PMF (List (G.NT ⊕ T)))
    (recurseProb : G.NT → ENNReal) (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    -- TODO: in a faithful version this is `G.NT → PYPHyper` (per-NT
    -- restaurants per @cite{odonnell-2015} §3.1.7 `pyp : G.NT → PitmanYor`).
    -- The scaffold uses a single global hyper for clarity.
    (hyper : PYPHyper)
    (start : G.NT) (n : ℕ)
    (tree : LazyTree G.NT T) (finalState : PYPState G.NT (LazyTree G.NT T)) :
    (fragmentLambdaDepth recurse recurseProb recurseProb_le n start
        (PYPState.empty hyper)) (tree, finalState)
      = ENNReal.ofReal (M.corpusProbGivenStorage
          (samplesToCorpusCounts tree finalState).1
          (samplesToCorpusCounts tree finalState).2.1
          (samplesToCorpusCounts tree finalState).2.2) := by
  sorry

end Morphology.FragmentGrammars.Operational
