import Linglib.Phonology.Prosody.Word
import Linglib.Phonology.OptimalityTheory.Basic

/-!
# Uchihara & Mendoza Ruiz 2021: minimality, maximality, and the perfect word in Mixtec
[uchihara-mendozaruiz-2021]

Uchihara, H. & Mendoza Ruiz, J. (2021). Minimality, maximality and perfect
prosodic word in Alcozauca Mixtec. *Natural Language & Linguistic Theory* 40,
599–649.

In Alcozauca Mixtec the prosodic word is ideally both minimally *and* maximally
bimoraic: monosyllabic stems lengthen to bimoraic (CVV), and over-long words
truncate to fit the bimoraic template. The paper's reductionist claim is that one
constraint set — `FtBin`, `Parse(μ)`, `AllFeetRight` — derives *both* bounds, so
the ideal word is the **perfect prosodic word**: ω coextensive with a single
well-formed (bimoraic) foot. The typological prediction is that maximality always
entails minimality, not conversely.

We exercise the unified prosodic machinery: candidates are `Prosody.Tree`s, the
constraints are `Constraints.Constraint Tree` values (`FtBin` is the local `ftBin`,
`Parse(μ)` is the carrier constraint `Prosody.parseInto .f`), the word-size notions are
`Prosody.PerfectWord` / `MinimalWord` / `MaximalWord`, and EVAL is the OT engine
`OptimalityTheory.Tableau.ofRanking … |>.optimal`. The *same* ranking `FtBin ≫ Parse`
selects the bimoraic foot for both a too-small input (lengthening) and a too-big one
(truncation); the winner is a `PerfectWord`.
-/

namespace Uchihara2021

open Prosody Features.Prosody RootedTree Constraints OptimalityTheory

/-! ### Constraint ranking -/

/-- `FtBin` ([uchihara-mendozaruiz-2021]) as a `Constraint Tree`: feet whose mora count is
    not 2. (`Parse(μ)` is the carrier constraint `parseInto .f` — unfooted syllables.) -/
def ftBin : Constraint Tree := fun t => ((feet t).filter (fun f => footMorae f != 2)).length

/-! ### Minimality: a monomoraic input lengthens to a bimoraic foot -/

/-- `(taa)` — one heavy syllable footed: the bimoraic perfect word. -/
def bimoraic : Tree := .node .om [.node .ft [.node (.syl .heavy) []]]
/-- `(ta)` — a degenerate monomoraic foot (`FtBin` violation). -/
def degenerate : Tree := .node .om [.node .ft [.node (.syl .light) []]]
/-- `[ta]` — an unfooted light syllable (`Parse` violation). -/
def unfooted : Tree := .node .om [.node (.syl .light) []]

def minCandidates : List Tree := [bimoraic, degenerate, unfooted]

example : ftBin degenerate = 1 := by decide
example : parseInto .f unfooted = 1 := by decide
example : ftBin bimoraic = 0 ∧ parseInto .f bimoraic = 0 := by decide

/-- Minimality: from a monomoraic input the bimoraic foot is the unique optimum
    (lengthening beats both the degenerate foot and the unfooted syllable). -/
theorem minimality_optimum :
    (Tableau.ofRanking minCandidates [ftBin, parseInto .f]).optimal = {bimoraic} := by decide

/-! ### Maximality: a trimoraic input truncates to a bimoraic foot -/

/-- `(taa.ta)` — a trimoraic foot (`FtBin` violation). -/
def trimoraicFoot : Tree :=
  .node .om [.node .ft [.node (.syl .heavy) [], .node (.syl .light) []]]
/-- `(taa).ta` — a bimoraic foot plus an unfooted syllable (`Parse` violation). -/
def footPlusStray : Tree :=
  .node .om [.node .ft [.node (.syl .heavy) []], .node (.syl .light) []]

def maxCandidates : List Tree := [bimoraic, trimoraicFoot, footPlusStray]

example : ftBin trimoraicFoot = 1 := by decide
example : parseInto .f footPlusStray = 1 := by decide

/-- Maximality: from a trimoraic input the bimoraic foot is again the unique
    optimum (truncation beats the trimoraic foot and the foot-plus-stray) — the
    *same* `FtBin ≫ Parse` ranking, hence "maximality from the minimality
    constraints" ([uchihara-mendozaruiz-2021]). -/
theorem maximality_optimum :
    (Tableau.ofRanking maxCandidates [ftBin, parseInto .f]).optimal = {bimoraic} := by decide

/-! ### The winner is the perfect prosodic word -/

/-- The shared optimum is the perfect prosodic word: ω coextensive with one
    well-formed (moraic-trochee) foot. -/
theorem winner_perfect : PerfectWord footMorae bimoraic := by decide

/-- Hence the optimum is both minimal and maximal (Itô & Mester's perfect word =
    minimal ∧ maximal). -/
theorem winner_minimal_and_maximal :
    MinimalWord footMorae bimoraic ∧ MaximalWord footMorae bimoraic :=
  ⟨winner_perfect.minimal, winner_perfect.maximal⟩

end Uchihara2021
