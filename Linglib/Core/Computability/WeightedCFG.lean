import Linglib.Core.Computability.CFGTree

/-!
# Weighted context-free grammars

Substrate for any analysis that attaches a weight to each rule of a
`ContextFreeGrammar`. A `WeightedCFG G W` carries a per-rule value in
some ordered type `W` with a zero element, plus a nonnegativity
constraint. **No normalization is bundled** — that's the job of
specializations (e.g. multinomial PCFG, where the W is `ℝ≥0∞` and
per-LHS sums to 1).

Anchored on the multinomial-PCFG file's previous docstring promise:
"the unbundled 'weighted CFG' is genuinely useful for theories where
weights are not yet normalized (e.g. `DMPCFG`'s pre-Dirichlet
hyperparameters), and will be introduced when the first such consumer
arrives." DMPCFG arrived; this is that file.

This file also defines the per-LHS rule subtype `G.RulesWithLHS a`,
which is the natural index for any per-LHS analysis (PMFs, Pólya
urns, MAP-weight comparisons). Previously declared inside `DMPCFG`'s
namespace; promoted here so that `MultinomialPCFG`, `DMPCFG`, and any
future weighted-CFG consumer share one definition.

## Main definitions

- `ContextFreeGrammar.RulesWithLHS G a` — subtype of grammar rules
  whose left-hand side equals `a`.
- `WeightedCFG G W` — per-rule weight in `W`, nonnegative, no
  normalization constraint.
-/

namespace ContextFreeGrammar

variable {T : Type} (G : ContextFreeGrammar T) [DecidableEq G.NT]

/-- The subtype of grammar rules whose left-hand side equals `a`.
    The natural index for per-LHS analyses (PMFs, Pólya urns,
    productivity comparisons): a value of type `G.RulesWithLHS a` is
    a rule paired with a proof that its `input` is `a` and that it
    sits in `G.rules`. -/
abbrev RulesWithLHS (a : G.NT) : Type :=
  { r : ContextFreeRule T G.NT // r ∈ G.rules.filter (·.input = a) }

end ContextFreeGrammar

/--
A *weighted CFG* over `G` with weights in `W`: per-rule weight
function and a nonnegativity constraint, but no normalization.

Specializations layer normalization on top:
- `MultinomialPCFG G` (= `WeightedCFG G ℝ≥0∞` with per-LHS sum-to-1
  exposed as a per-LHS `PMF`).
- `DMPCFG` carries `pseudo : Rule → ℝ` with the stronger constraint
  `0 < pseudo r` for `r ∈ G.rules` (Dirichlet hyperparameters); the
  normalized object DMPCFG induces is the posterior MAP, available
  via `DMPCFG.posteriorMAP : DMPCFG G → Multiset _ → MultinomialPCFG G`.

The W-polymorphism mirrors mathlib's `Module R M`, `Polynomial R`,
etc.: the substrate doesn't fix the value type, leaving consumers to
choose `ℝ`, `ℝ≥0∞`, `NNReal`, or anything with the required structure.
-/
@[ext]
structure WeightedCFG {T : Type} (G : ContextFreeGrammar T)
    (W : Type) [Zero W] [LE W] where
  /-- Per-rule weight. -/
  weight : ContextFreeRule T G.NT → W
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ r, 0 ≤ weight r
