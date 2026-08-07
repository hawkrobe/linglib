import Linglib.Syntax.DependencyGrammar.Length
import Linglib.Morphology.Word.Basic

/-!
# Hahn, Degen & Futrell 2021: memory-surprisal trade-off
[hahn-degen-futrell-2021]

The Efficient Trade-off Hypothesis: natural word orders optimize the
trade-off between memory investment and surprisal. Study 2 measures 54
Universal Dependencies languages against grammar-preserving random
baselines: 50 have significantly more efficient trade-offs, and the four
exceptions (Latvian, North Sami, Polish, Slovak) all have high branching
direction entropy — word-order freedom correlates negatively with
optimization strength (Spearman ρ ≈ −.58). Those measured results live
in the paper and its data release, not here; the trade-off theory itself
(the marginal-rate theorem and information locality) is formalized in
`Processing/Memory/SurprisalTradeoff.lean`.

This file holds the study's structural argument as a stimulus contrast:
information locality generalizes dependency length minimization, and
consistent head direction yields strictly shorter dependencies than
mixed direction on the same chain — the mechanism behind the
low-entropy-implies-efficient half of the paper's Figure 13 pattern.
-/

namespace HahnDegenFutrell2021

open DependencyGrammar
open Morphology (Word)

/-- A three-link chain linearized with consistent head direction:
    `A → B → C → D` in surface order `A B C D`. -/
private def harmonicChain : Graph 4 :=
  .ofArcs
    [Word.mk' "A" .X, Word.mk' "B" .X, Word.mk' "C" .X, Word.mk' "D" .X]
    0 [(0, 1, .dep), (1, 2, .dep), (2, 3, .dep)]

/-- The same chain with mixed head direction: surface order `A C D B`,
    arcs `A → B`, `B → C`, `C → D`. -/
private def disharmonicChain : Graph 4 :=
  .ofArcs
    [Word.mk' "A" .X, Word.mk' "C" .X, Word.mk' "D" .X, Word.mk' "B" .X]
    0 [(0, 3, .dep), (3, 1, .dep), (1, 2, .dep)]

/-- Consistent head direction gives strictly shorter total dependency
    length than mixed direction on the same chain. -/
theorem harmonic_dlm_holds :
    harmonicChain.totalLength < disharmonicChain.totalLength := by decide

end HahnDegenFutrell2021
