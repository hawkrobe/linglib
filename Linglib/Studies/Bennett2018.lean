import Linglib.Phonology.Prosody.Word
import Linglib.Phonology.OptimalityTheory.Basic

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

The prosodic candidates are `Tree`s; the constraints are `Constraints.Constraint Tree`
values (`NoRecursion` is the carrier constraint `Prosody.noRec`; `Match` is the local
`matchStem`), and EVAL is the OT engine `OptimalityTheory.Tableau.ofRanking … |>.optimal`
— the same machinery every OT study in the library uses.

## Implementation note

`matchStem` here is a stand-in for the full `Match(X⁰, ω)` constraint: it penalises the
stem morpheme not surfacing as its own ω, with the stem baked in (the morpheme under
analysis). The general syntax↔prosody Match, built on `OptimalityTheory.Correspondence`,
is future work.
-/

namespace Bennett2018

open Prosody RootedTree Constraints OptimalityTheory

/-! ### Candidate prosodifications of a high-prefix + stem -/

/-- A high-attaching prefix syllable (light). -/
def prefσ : Tree := .σ 1

/-- The stem syllable (heavy). -/
def stemσ : Tree := .σ 2

/-- Flat parse `[ω HighPref Stem]`: no recursion, but the stem has no ω of its own. -/
def flatParse : Tree := .om [prefσ, stemσ]

/-- Recursive parse `[ω HighPref [ω Stem]]`: the stem keeps its ω; the prefix
    adjoins to a dominating ω ([bennett-2018]). -/
def recParse : Tree := .om [prefσ, .om [stemσ]]

/-! ### `Match(Stem, ω)` (stand-in) -/

/-- Does some ω-node dominate exactly the stem (i.e. have children `[stem]`)? -/
def hasOmegaOver (stem : Tree) : Tree → Bool := fun t => go t where
  go : Tree → Bool
    | .node a cs => (a.isOm && decide (cs = [stem])) || goList cs
  goList : List Tree → Bool
    | [] => false
    | t :: ts => go t || goList ts

/-- `Match(Stem, ω)` ([ishihara-kalivoda-2022]) as a `Constraint Tree`: 1 if the stem is
    not exhaustively matched by an ω of its own, else 0. -/
def matchStem : Constraint Tree := fun t => if hasOmegaOver stemσ t then 0 else 1

/-! ### The ranking and the prediction

EVAL is the OT tableau engine: `Tableau.ofRanking candidates ranking |>.optimal` selects the
lexicographic optimum under the constraint ranking (priority = list order). The ranking
`Match(X⁰,ω) ≫ NoRecursion` is `[matchStem, noRec]`. -/

-- The violation contrast: recursion costs `NoRecursion`, the flat parse costs `Match`.
example : matchStem recParse = 0 ∧ noRec recParse = 1 := by decide
example : matchStem flatParse = 1 ∧ noRec flatParse = 0 := by decide

/-- Under `Match(X⁰,ω) ≫ NoRecursion`, the **recursive** parse is the unique optimum —
    Bennett's central result, that ω-recursion is forced. -/
theorem recParse_optimal :
    (Tableau.ofRanking [recParse, flatParse] [matchStem, noRec]).optimal = {recParse} := by
  decide

-- The optimum is a legal recursive prosodic word (ω-over-ω is well-formed; No-Recursion,
-- which it violates, is a *violable* OT constraint, not part of `IsWord`).
example : IsWord recParse := by decide

end Bennett2018
