import Linglib.Phonology.Prosody.Tree
import Linglib.Core.Optimization.Evaluation

/-!
# Bennett 2018: recursion of the prosodic word in Kaqchikel
[bennett-2018]

Bennett, R. (2018). Recursive prosodic words in Kaqchikel (Mayan).
*Glossa: a journal of general linguistics* 3(1): 67, 1–33.

Kaqchikel splits prefixes into **low-attaching** (parsed inside the stem's ω,
`[ω LowPref-Stem]`) and **high-attaching** (parsed outside it). Two diagnostics
converge on this cut: initial glottal-stop insertion (`/V…/ → [ʔV…]`, bled by
low prefixes but co-occurring with high ones) and degemination (triggered across
a low-prefix juncture but not a high-prefix one). Bennett argues the
high-attaching structure is **recursive**, `[ω HighPref [ω Stem]]`: the stem
keeps its own ω, and the prefix adjoins to a dominating ω. A non-recursive
analysis must invent an *ad hoc* Clitic/Composite Group, and derivational or
transderivational alternatives fail on morphological grounds. The conclusion:
ω-recursion is indispensable.

Formally this is one ranking fact: a `Match(X⁰, ω)` faithfulness constraint
([ishihara-kalivoda-2022], recasting Selkirk's Match as Max/Dep) outranks
`NoRecursion` ([ito-mester-2003]). The recursive parse violates `NoRecursion`
once but satisfies `Match`; the flat parse satisfies `NoRecursion` but violates
`Match`. With `Match ≫ NoRecursion`, the recursive parse is the optimum — a
prediction the flat `List`-of-weights `Word` could not even state.

The prosodic candidates are `ProsTree`s (`Phonology/Prosody/Tree.lean`); EVAL is
mathlib's lexicographic minimum — `Core.Optimization`'s `argMinSet`, the
computable form of `Order.Minimal` under the profile pullback
`Order.Preimage profile LexLE`. Constraints are plain `ProsTree → ℕ` functions;
the ranking is the order of entries in the profile. No `Constraint`/tableau
wrapper is needed (cf. how mathlib selects optima — `Order.Minimal` + `Order.Lex`,
not a bespoke decorated structure).

## Implementation note

`matchStemViol` here is a stand-in for the full `Match(X⁰, ω)` constraint: it
penalises the stem morpheme not surfacing as its own ω, with the stem supplied
as a parameter (the morpheme under analysis). The general syntax↔prosody Match,
built on `OptimalityTheory.Correspondence`, is future work.
-/

namespace Bennett2018

open Prosody Features.Prosody RootedTree Core.Optimization.Evaluation

/-! ### Candidate prosodifications of a high-prefix + stem -/

/-- A high-attaching prefix syllable (light). -/
def prefσ : ProsTree := .node ⟨.σ, 1⟩ []

/-- The stem syllable (heavy). -/
def stemσ : ProsTree := .node ⟨.σ, 2⟩ []

/-- Flat parse `[ω HighPref Stem]`: no recursion, but the stem has no ω of its own. -/
def flatParse : ProsTree := .node ⟨.ω, 0⟩ [prefσ, stemσ]

/-- Recursive parse `[ω HighPref [ω Stem]]`: the stem keeps its ω; the prefix
    adjoins to a dominating ω ([bennett-2018]). -/
def recParse : ProsTree := .node ⟨.ω, 0⟩ [prefσ, .node ⟨.ω, 0⟩ [stemσ]]

/-! ### `Match(Stem, ω)` (stand-in) -/

mutual
/-- Does some ω-node dominate exactly the stem (i.e. have children `[stem]`)? -/
def hasOmegaOver (stem : ProsTree) : ProsTree → Bool
  | .node a cs => (decide (a.level = .ω) && decide (cs = [stem])) || hasOmegaOverList stem cs
/-- Auxiliary over a list of subtrees. -/
def hasOmegaOverList (stem : ProsTree) : List ProsTree → Bool
  | [] => false
  | t :: ts => hasOmegaOver stem t || hasOmegaOverList stem ts
end

/-- `Match(Stem, ω)` violation: 1 if the stem is not exhaustively matched by an
    ω of its own, else 0. -/
def matchStemViol (stem t : ProsTree) : Nat := if hasOmegaOver stem t then 0 else 1

/-! ### The ranking and the prediction

EVAL is mathlib's lexicographic minimum: the optimum is the `LexLE`-least
candidate under the violation profile. `argMinSet s f r = s.filter (f ·
`r`-below all)` is the computable form of `Order.Minimal` under
`Order.Preimage profile LexLE`. The ranking `Match(X⁰,ω) ≫ NoRecursion` is just
the entry order in the profile. -/

/-- Violation profile, ranked `Match(X⁰,ω) ≫ NoRecursion`: a plain `ℕ`-vector
    of the two constraint functions, compared by `LexLE`. -/
def profile (t : ProsTree) : List Nat := [matchStemViol stemσ t, ProsTree.recursionCount t]

/-- The two candidate prosodifications. -/
def candidates : Finset ProsTree := {recParse, flatParse}

-- The violation contrast: recursion costs `NoRecursion`, the flat parse costs `Match`.
example : profile recParse = [0, 1] := by decide
example : profile flatParse = [1, 0] := by decide

/-- Under `Match(X⁰,ω) ≫ NoRecursion`, the **recursive** parse is the unique
    optimum — Bennett's central result, that ω-recursion is forced. The optimum
    is mathlib's lex-minimum (`argMinSet` = computable `Order.Minimal`). -/
theorem recParse_optimal : argMinSet candidates profile LexLE = {recParse} := by decide

end Bennett2018
