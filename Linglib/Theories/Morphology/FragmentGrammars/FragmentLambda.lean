import Linglib.Theories.Morphology.FragmentGrammars.FragmentGrammar

/-!
# fragment-lambda: the book's universal construction (CFG instance)

@cite{odonnell-2015}

Per @cite{odonnell-2015} §2.3.7 (p. 71-72), `fragment-lambda` is a
higher-order program transformation that takes any generative
procedure and returns a memoized, stochastically-lazy version: each
recursive call may either expand productively or halt-and-store as
a fragment, with PYP-table dynamics governing memoization. Applied
to the CFG-`unfold` procedure (which samples derivations from a
multinomial PCFG), `fragment-lambda(unfold)` yields the
fragment-grammar model.

This file gives the **CFG-instantiated** version of
`fragment-lambda`: a constructor taking an `AdaptorGrammar` (the
DMPCFG + PYP substrate already encoding everything below the
halt-prior layer) plus a beta-binomial halt prior, returning a
`FragmentGrammar`. The decomposition theorem
`corpusProbGivenStorage_eq_AG_times_haltFactor` makes the book's
central identity explicit: **FG IS AG augmented by exactly the
halt-prior factor**, in the precise sense the book's
fragment-lambda construction captures.

## Why concrete-on-CFG and not the abstract universal version

The abstract `fragment-lambda` is naturally a free-monad-based
program transformation `(α → M β) → (α → PYMemT α M β)` over an
arbitrary generative monad `M`. Implementing it requires
substantial substrate that mathlib does not yet have:

- **Free monads** (`Mathlib.Control.Free`) — absent. The natural
  formulation uses a `Free F α` over a "Generate + Memoize + Halt"
  signature functor; mathlib has neither `Free` nor cofree
  comonads.
- **Stochastic memoization as a monad effect** — no formal
  treatment exists in any proof assistant we are aware of.
  Standard memoization (Michie 1968) is deterministic; PYP-style
  stochastic memoization (Goodman et al. 2008 "Church") is a
  Bayesian-non-parametric extension where the memo table itself is
  a draw from a stochastic process.
- **Probabilistic lazy evaluation** — known to differ semantically
  from probabilistic eager evaluation under randomness; no formal
  treatment.
- **Probabilistic fixed points** — needed for unbounded recursion
  with almost-sure termination; mathlib has Borel-Cantelli but no
  general probabilistic-recursion framework.

A deep formalization of fragment-lambda is **a real research
project** with publishable byproducts: a contribution to mathlib
of free-monad infrastructure, an original formalization of
stochastic memoization, and possibly a categorical formulation in
the style of Heunen-Kammar-Staton-Yang (LICS 2017,
quasi-Borel spaces). It is not in scope here.

Per "don't speculatively factor": we instantiate to the CFG case
until a second consumer (fragmentized TAG, fragmentized minimalist
grammars, fragmentized image-recognition theories per
@cite{odonnell-2015} p. 73) needs the abstract version. The
concrete version below captures the linguistic content of the
book's central theoretical move; the abstract version captures the
universal type-theoretic content.

## Main definitions

- `fragmentLambda M halt` — CFG-instantiated constructor: takes an
  `AdaptorGrammar G` plus per-(rule, position) beta-binomial
  pseudo-counts and returns the corresponding `FragmentGrammar G`.
- `FragmentGrammar.eq_fragmentLambda` — every `FragmentGrammar`
  factors through `fragmentLambda` applied to its underlying AG.
- `FragmentGrammar.corpusProbGivenStorage_eq_AG_times_haltFactor`
  — the corpus probability decomposes as
  `[AG corpus prob] × [Π halt-prior factor]`, making explicit that
  fragment-lambda augments AG by exactly the halt-prior layer.

## References

- @cite{odonnell-2015} §2.3.5 (stochastic-lazy `unfold`), §2.3.6
  (fragment grammars), §2.3.7 (`fragment-lambda` and the
  generalization to arbitrary procedures).
-/

namespace Morphology.FragmentGrammars

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/--
The CFG-instantiated fragment-lambda construction. Given an adaptor
grammar `M` and a per-(rule, position) beta-binomial halt prior,
produce the corresponding `FragmentGrammar`.

This is the linguistic-content version of @cite{odonnell-2015}
§2.3.7's `fragment-lambda`: applying `fragment-lambda` to the
recursive `unfold` procedure of an adaptor grammar yields a
fragment grammar. The recursion-and-memoization machinery that
makes `fragment-lambda` work in Church is structurally encoded in
`AdaptorGrammar` + `FragmentGrammar`'s `extends` chain; the present
constructor names the final halt-prior step.

Universality (over arbitrary generative monads `M`, not just
CFG-`unfold`) is deferred — see module docstring for the
type-theoretic substrate that would be required.
-/
def fragmentLambda (M : AdaptorGrammar G)
    (haltRecurse haltHalt : ContextFreeRule T G.NT → ℕ → ℝ)
    (haltRecurse_pos : ∀ r i, 0 < haltRecurse r i)
    (haltHalt_pos : ∀ r i, 0 < haltHalt r i) :
    FragmentGrammar G where
  toAdaptorGrammar := M
  haltPriorRecurse := haltRecurse
  haltPriorHalt := haltHalt
  haltPriorRecurse_pos := haltRecurse_pos
  haltPriorHalt_pos := haltHalt_pos

/--
Every `FragmentGrammar` factors uniquely through
`fragmentLambda` applied to its underlying `AdaptorGrammar` and its
own halt-prior fields. The book's central identity: **a fragment
grammar IS an adaptor grammar with a halt prior layered on top**,
and `fragmentLambda` is the operation that performs that layering.
-/
theorem FragmentGrammar.eq_fragmentLambda (M : FragmentGrammar G) :
    M = fragmentLambda M.toAdaptorGrammar
        M.haltPriorRecurse M.haltPriorHalt
        M.haltPriorRecurse_pos M.haltPriorHalt_pos := rfl

/--
**The book's decomposition identity** for the corpus probability of
a fragment grammar:

```
FG.corpusProbGivenStorage D Y Z
  = AG.corpusProbGivenTables D Y · ∏_{r,i} fgFactor r i (Z r i)
```

The first factor is the adaptor-grammar corpus probability (the
DMPCFG-Pólya part times the per-LHS Pitman–Yor part); the second
factor is the per-(rule, position) beta-binomial halt-prior product
that fragment-lambda contributes. This is the precise mathematical
content of the claim that `FG = fragmentLambda(AG)`: the only
thing fragment-lambda adds to the AG corpus probability is the
halt-prior factor.
-/
theorem FragmentGrammar.corpusProbGivenStorage_eq_AG_times_haltFactor
    (M : FragmentGrammar G) (D : Multiset (CFGTree T G.NT))
    (Y : AdaptorGrammar.TableAssignment G) (Z : FragmentGrammar.HaltCounts G) :
    M.corpusProbGivenStorage D Y Z =
    M.toAdaptorGrammar.corpusProbGivenTables D Y *
    ∏ r ∈ G.rules, ∏ i ∈ Finset.range r.output.length,
      M.fgFactor r i (Z r i) := rfl

end Morphology.FragmentGrammars
