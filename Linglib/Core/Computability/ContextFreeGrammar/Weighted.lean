import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Algebra.Order.Group.Defs

/-!
# Weighted context-free grammars

Substrate for any analysis that attaches a weight to each rule of a
`ContextFreeGrammar`. A `WeightedCFG G W` carries a per-rule value in
some ordered type `W` with a zero element, plus a nonnegativity
constraint. **No normalization is bundled** — that's the job of
specializations (e.g. `PCFG`, where the W is `ℝ≥0∞` and per-LHS sums
to 1, and `DirichletPCFG`, whose pseudo-counts are not normalized).

This file also defines the per-LHS rule subtype `G.RulesWithLHS a`,
which is the natural index for any per-LHS analysis (PMFs, Pólya
urns, posterior-weight comparisons), shared by `PCFG`, `DirichletPCFG`,
and any future weighted-CFG consumer.

## Main definitions

- `ContextFreeGrammar.RulesWithLHS G a` — subtype of grammar rules
  whose left-hand side equals `a`.
- `Symbol.IsNonterminal` — the predicate picking out nonterminal symbols.
- `ContextFreeRule.NonterminalPos r` — subtype of right-hand-side positions
  of `r` holding a nonterminal, the index for any per-slot analysis.
- `WeightedCFG G W` — per-rule weight in `W`, nonnegative, no
  normalization constraint.
-/

namespace ContextFreeGrammar

variable {T : Type*} (G : ContextFreeGrammar T) [DecidableEq G.NT]

/-- The subtype of grammar rules whose left-hand side equals `a`.
    The natural index for per-LHS analyses (PMFs, Pólya urns,
    productivity comparisons): a value of type `G.RulesWithLHS a` is
    a rule paired with a proof that its `input` is `a` and that it
    sits in `G.rules`. -/
abbrev RulesWithLHS (a : G.NT) :=
  { r : ContextFreeRule T G.NT // r ∈ G.rules.filter (·.input = a) }

end ContextFreeGrammar

namespace Symbol

variable {T N : Type*}

/-- `s.IsNonterminal` holds when the symbol `s` is a nonterminal. -/
def IsNonterminal : Symbol T N → Prop
  | terminal _ => False
  | nonterminal _ => True

instance : DecidablePred (IsNonterminal : Symbol T N → Prop)
  | terminal _ => isFalse id
  | nonterminal _ => isTrue trivial

@[simp] theorem isNonterminal_nonterminal (n : N) :
    (nonterminal n : Symbol T N).IsNonterminal := trivial

@[simp] theorem not_isNonterminal_terminal (t : T) :
    ¬ (terminal t : Symbol T N).IsNonterminal := id

end Symbol

namespace ContextFreeRule

/-- The positions on the right-hand side of `r` that hold a nonterminal: the slots at which a
derivation from `r` branches, and the index for any analysis carried out per slot. -/
abbrev NonterminalPos {T N : Type*} (r : ContextFreeRule T N) : Type :=
  {i : Fin r.output.length // r.output[i].IsNonterminal}

end ContextFreeRule

/--
A *weighted CFG* over `G` with weights in `W`: per-rule weight
function and a nonnegativity constraint, but no normalization.

Specializations layer normalization on top:
- `PCFG G` (= `WeightedCFG G ℝ≥0∞` with per-LHS sum-to-1 exposed as a
  per-LHS `PMF`).
- `DirichletPCFG G` carries `pseudo : Rule → ℝ` with the stronger
  constraint `0 < pseudo r` for `r ∈ G.rules` (Dirichlet
  hyperparameters); the normalized object it induces is the posterior
  predictive `DirichletPCFG.predictivePCFG`.

The W-polymorphism mirrors mathlib's `Module R M`, `Polynomial R`,
etc.: the substrate doesn't fix the value type, leaving consumers to
choose `ℝ`, `ℝ≥0∞`, `NNReal`, or anything with the required structure.
-/
@[ext]
structure WeightedCFG {T : Type*} (G : ContextFreeGrammar T)
    (W : Type*) [Zero W] [LE W] where
  /-- Per-rule weight. -/
  weight : ContextFreeRule T G.NT → W
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ r, 0 ≤ weight r
