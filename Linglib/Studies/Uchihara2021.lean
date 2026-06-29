import Linglib.Phonology.Prosody.WordSize
import Linglib.Core.Optimization.Evaluation

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

We exercise the unified prosodic machinery: candidates are `Prosody.Tree`s, size
notions come from `Phonology/Prosody/WordSize.lean`, and EVAL is mathlib's
lexicographic minimum (`Core.Optimization`'s `argMinSet`, no OT-engine wrapper).
The *same* profile `FtBin ≫ Parse` selects the bimoraic foot for both a too-small
input (lengthening) and a too-big one (truncation); the winner is a `PerfectWord`.
-/

namespace Uchihara2021

open Prosody Features.Prosody RootedTree Core.Optimization.Evaluation

/-! ### Constraint profile -/

/-- `FtBin` violations over a tree: feet whose mora count is not 2. -/
def ftBinViol (t : Tree) : Nat :=
  ((feet t).filter (fun f => footMorae f != 2)).length

/-- Violation profile, ranked `FtBin ≫ Parse(μ)` (unfooted syllables). -/
def profile (t : Tree) : List Nat := [ftBinViol t, unfootedCount t]

/-! ### Minimality: a monomoraic input lengthens to a bimoraic foot -/

/-- `(taa)` — one heavy syllable footed: the bimoraic perfect word. -/
def bimoraic : Tree := .node .om [.node .ft [.node (.syl .heavy) []]]
/-- `(ta)` — a degenerate monomoraic foot (`FtBin` violation). -/
def degenerate : Tree := .node .om [.node .ft [.node (.syl .light) []]]
/-- `[ta]` — an unfooted light syllable (`Parse` violation). -/
def unfooted : Tree := .node .om [.node (.syl .light) []]

def minCandidates : Finset Tree := {bimoraic, degenerate, unfooted}

example : profile bimoraic = [0, 0] := by decide
example : profile degenerate = [1, 0] := by decide
example : profile unfooted = [0, 1] := by decide

/-- Minimality: from a monomoraic input the bimoraic foot is the unique optimum
    (lengthening beats both the degenerate foot and the unfooted syllable). -/
theorem minimality_optimum : argMinSet minCandidates profile LexLE = {bimoraic} := by decide

/-! ### Maximality: a trimoraic input truncates to a bimoraic foot -/

/-- `(taa.ta)` — a trimoraic foot (`FtBin` violation). -/
def trimoraicFoot : Tree :=
  .node .om [.node .ft [.node (.syl .heavy) [], .node (.syl .light) []]]
/-- `(taa).ta` — a bimoraic foot plus an unfooted syllable (`Parse` violation). -/
def footPlusStray : Tree :=
  .node .om [.node .ft [.node (.syl .heavy) []], .node (.syl .light) []]

def maxCandidates : Finset Tree := {bimoraic, trimoraicFoot, footPlusStray}

example : profile trimoraicFoot = [1, 0] := by decide
example : profile footPlusStray = [0, 1] := by decide

/-- Maximality: from a trimoraic input the bimoraic foot is again the unique
    optimum (truncation beats the trimoraic foot and the foot-plus-stray) — the
    *same* `FtBin ≫ Parse` profile, hence "maximality from the minimality
    constraints" ([uchihara-mendozaruiz-2021]). -/
theorem maximality_optimum : argMinSet maxCandidates profile LexLE = {bimoraic} := by decide

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
