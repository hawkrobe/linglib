import Linglib.Phonology.Prosody.Tree
import Linglib.Phonology.OptimalityTheory.DirectionalTableau

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

The prosodic candidates are `ProsTree`s (`Phonology/Prosody/Tree.lean`) and the
prediction is computed by the existing OT engine (`DirectionalTableau.optima`).

## Implementation note

`matchStemViol` here is a stand-in for the full `Match(X⁰, ω)` constraint: it
penalises the stem morpheme not surfacing as its own ω, with the stem supplied
as a parameter (the morpheme under analysis). The general syntax↔prosody Match,
built on `OptimalityTheory.Correspondence`, is future work.
-/

namespace Bennett2018

open Prosody Features.Prosody RootedTree OptimalityTheory

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

/-! ### The ranking and the prediction -/

/-- `Match(Stem, ω)` — a faithfulness constraint. -/
def matchStem : Constraint ProsTree := .ofCount "Match(Stem,ω)" .faithfulness (matchStemViol stemσ)

/-- `NoRecursion` — a markedness constraint. -/
def noRec : Constraint ProsTree := .ofCount "NoRecursion" .markedness ProsTree.recursionCount

/-- The Kaqchikel high-prefix tableau, ranked `Match ≫ NoRecursion`. -/
def tableau : DirectionalTableau ProsTree where
  candidates := {recParse, flatParse}
  ranking := [matchStem, noRec]
  nonempty := by decide

-- The violation contrast: recursion costs `NoRecursion`, the flat parse costs `Match`.
example : ProsTree.recursionCount recParse = 1 := by decide
example : ProsTree.recursionCount flatParse = 0 := by decide
example : matchStemViol stemσ recParse = 0 := by decide
example : matchStemViol stemσ flatParse = 1 := by decide

/-- Under `Match(X⁰,ω) ≫ NoRecursion`, the **recursive** parse is the optimum —
    Bennett's central result, that ω-recursion is forced. -/
theorem recParse_optimal : tableau.IsOptimal recParse := by decide

/-- The flat (non-recursive) parse is *not* optimal under this ranking. -/
theorem flatParse_not_optimal : ¬ tableau.IsOptimal flatParse := by decide

/-- Equivalently: the optimal set is exactly the recursive parse. -/
theorem optima_eq : tableau.optima = {recParse} := by decide

end Bennett2018
