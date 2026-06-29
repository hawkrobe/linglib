import Linglib.Phonology.Prosody.WordSize
import Linglib.Core.Optimization.Evaluation

/-!
# Itô & Mester 2009: the extended prosodic word
[ito-mester-2009]

Itô, J. & Mester, A. (2009). The extended prosodic word. In J. Grijzenhout & B.
Kabak (eds.), *Phonological Domains: Universals and Deviations*. Berlin: De
Gruyter Mouton.

A function-word + lexical-word complex (English *the dinosaurs*, German *ne
Zigarette*) has four conceivable prosodifications, arising from the factorial
interaction of `FtBin`, `Lex-to-ω`, `Parse-into-ω`, and `No-Recursion`:

* **full-ω** `[φ [ω fnc] [ω lex]]` — the function word is its own ω (violates
  `FtBin`: a subminimal ω);
* **amalgamated** `[ω fnc lex]` — fused into one ω (violates `Lex-to-ω`: the
  lexical word has no ω of its own);
* **ω-adjoined** `[ω fnc [ω lex]]` — the function word adjoins, the lexical word
  keeps its ω (violates `No-Recursion`: ω over ω);
* **φ-attached** `[φ fnc [ω lex]]` — attached straight to φ (violates
  `Parse-into-ω`: the function word is in no ω).

With `FtBin`, `Lex-to-ω ≫ Parse-into-ω ≫ No-Recursion`, the **ω-adjoined**
(recursive) structure is the optimum — Itô & Mester's central claim, that English
and German function-word complexes use ω-adjunction, *contra* Selkirk's
φ-attachment. This is a second OT consumer of prosodic-word recursion alongside
`Studies/Bennett2018.lean` (Kaqchikel).

Candidates are `Prosody.Tree`s; EVAL is mathlib's lexicographic minimum
(`Core.Optimization`'s `argMinSet`, no OT-engine wrapper). `No-Recursion` is
`Tree.recursionCount` and `Parse-into-ω` is `parseIntoViol .ω` from the shared
machinery; `FtBin`-at-ω and `Lex-to-ω` are the function-word constraints below.
-/

namespace ItoMester2009

open Prosody Features.Prosody RootedTree Core.Optimization.Evaluation

/-! ### Function-word constraints -/

mutual
/-- `FtBin`-at-ω violations: ω-nodes whose mora count is below a foot (< 2). A
    subminimal function word parsed as its own ω is penalised. -/
def subminimalOmegaViol : Tree → Nat
  | .node a cs =>
      (if decide (a.level = .ω) && decide (moraCount (.node a cs) < 2) then 1 else 0)
        + subminimalOmegaViolList cs
/-- Auxiliary over a list of subtrees. -/
def subminimalOmegaViolList : List Tree → Nat
  | []      => 0
  | t :: ts => subminimalOmegaViol t + subminimalOmegaViolList ts
end

mutual
/-- Is the lexical word `lex` realised as its own ω-node somewhere in the tree? -/
def lexHasOmega (lex : Tree) : Tree → Bool
  | .node a cs =>
      (decide (a.level = .ω) && decide ((.node a cs : Tree) = lex)) || lexHasOmegaList lex cs
/-- Auxiliary over a list of subtrees. -/
def lexHasOmegaList (lex : Tree) : List Tree → Bool
  | []      => false
  | t :: ts => lexHasOmega lex t || lexHasOmegaList lex ts
end

/-- `Lex-to-ω` violation ([ito-mester-2009], after [mccarthy-prince-1993]'s
    `Align(Lex, ω)`): 1 if the lexical word is not aligned with an ω of its own. -/
def lexToOmegaViol (lex t : Tree) : Nat := if lexHasOmega lex t then 0 else 1

/-! ### The four candidate prosodifications of *(fnc lex)* -/

/-- The function word: one light syllable. -/
def fncσ : Tree := .node (.syl .light) []
/-- The lexical word as a well-formed (bimoraic) ω. -/
def lexω : Tree := .node .om [.node .ft [.node (.syl .heavy) []]]

/-- (a) full-ω: `[φ [ω fnc] [ω lex]]`. -/
def fullOmega : Tree := .node .ph [.node .om [fncσ], lexω]
/-- (b) amalgamated: `[ω fnc lex]` (lexical word loses its own ω). -/
def amalgamated : Tree := .node .om [fncσ, .node .ft [.node (.syl .heavy) []]]
/-- (c) ω-adjoined: `[ω fnc [ω lex]]` — recursive. -/
def omegaAdjoined : Tree := .node .om [fncσ, lexω]
/-- (d) φ-attached: `[φ fnc [ω lex]]`. -/
def phiAttached : Tree := .node .ph [fncσ, lexω]

/-- Violation profile, ranked `FtBin, Lex-to-ω ≫ Parse-into-ω ≫ No-Recursion`. -/
def profile (t : Tree) : List Nat :=
  [subminimalOmegaViol t, lexToOmegaViol lexω t, parseIntoViol .ω t, Tree.recursionCount t]

-- Each candidate violates exactly one constraint (the factorial typology).
example : profile fullOmega    = [1, 0, 0, 0] := by decide
example : profile amalgamated  = [0, 1, 0, 0] := by decide
example : profile omegaAdjoined = [0, 0, 0, 1] := by decide
example : profile phiAttached  = [0, 0, 1, 0] := by decide

def candidates : Finset Tree := {fullOmega, amalgamated, omegaAdjoined, phiAttached}

/-- The function-word complex is prosodified by **ω-adjunction** — the recursive
    `[ω fnc [ω lex]]` is the unique optimum, beating φ-attachment because
    `Parse-into-ω ≫ No-Recursion` ([ito-mester-2009], contra Selkirk's φ-attached). -/
theorem omegaAdjunction_optimum :
    argMinSet candidates profile LexLE = {omegaAdjoined} := by decide

/-- The winning structure is recursive: ω dominates ω. -/
theorem winner_is_recursive : Tree.recursionCount omegaAdjoined = 1 := by decide

end ItoMester2009
