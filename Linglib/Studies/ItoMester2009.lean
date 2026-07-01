import Linglib.Phonology.Prosody.Word
import Linglib.Phonology.OptimalityTheory.Basic

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

Candidates are `Prosody.Tree`s; the constraints are `Constraints.Constraint Tree` values
(`No-Recursion` is the carrier constraint `Prosody.noRec`, `Parse-into-ω` is
`Prosody.parseInto (·.isOm)`; `FtBin`-at-ω and `Lex-to-ω` are the function-word constraints
below), and EVAL is the OT engine `OptimalityTheory.Tableau.ofRanking … |>.optimal`.
-/

namespace ItoMester2009

open Prosody RootedTree Constraints OptimalityTheory

/-! ### Function-word constraints -/

/-- `FtBin`-at-ω ([ito-mester-2009]) as a `Constraint Tree`: ω-nodes whose mora count is
    below a foot (< 2) — a subminimal function word parsed as its own ω. -/
def subminimalOmega : Constraint Tree := fun t => go t where
  go : Tree → Nat
    | .node a cs =>
        (if a.isOm && decide (moraCount (.node a cs) < 2) then 1 else 0)
          + goList cs
  goList : List Tree → Nat
    | []      => 0
    | t :: ts => go t + goList ts

/-- Is the lexical word `lex` realised as its own ω-node somewhere in the tree? -/
def lexHasOmega (lex : Tree) : Tree → Bool := fun t => go t where
  go : Tree → Bool
    | .node a cs => (a.isOm && decide ((.node a cs : Tree) = lex)) || goList cs
  goList : List Tree → Bool
    | []      => false
    | t :: ts => go t || goList ts

/-! ### The four candidate prosodifications of *(fnc lex)* -/

/-- The function word: one light syllable. -/
def fncσ : Tree := .σ .light
/-- The lexical word as a well-formed (bimoraic) ω. -/
def lexω : Tree := .om [.ft false [.σ .heavy]]

/-- (a) full-ω: `[φ [ω fnc] [ω lex]]`. -/
def fullOmega : Tree := .ph [.om [fncσ], lexω]
/-- (b) amalgamated: `[ω fnc lex]` (lexical word loses its own ω). -/
def amalgamated : Tree := .om [fncσ, .ft false [.σ .heavy]]
/-- (c) ω-adjoined: `[ω fnc [ω lex]]` — recursive. -/
def omegaAdjoined : Tree := .om [fncσ, lexω]
/-- (d) φ-attached: `[φ fnc [ω lex]]`. -/
def phiAttached : Tree := .ph [fncσ, lexω]

/-- `Lex-to-ω` ([ito-mester-2009], after [mccarthy-prince-1993]'s `Align(Lex, ω)`) as a
    `Constraint Tree`: 1 if the lexical word `lexω` is not aligned with an ω of its own. -/
def lexToOmega : Constraint Tree := fun t => if lexHasOmega lexω t then 0 else 1

/-! ### The ranking and the prediction

EVAL is the OT tableau engine; the ranking is `FtBin, Lex-to-ω ≫ Parse-into-ω ≫
No-Recursion` = `[subminimalOmega, lexToOmega, parseInto (·.isOm), noRec]`. -/

def candidates : List Tree := [fullOmega, amalgamated, omegaAdjoined, phiAttached]

-- Each candidate violates exactly one constraint (the factorial typology).
example : subminimalOmega fullOmega = 1 := by decide
example : lexToOmega amalgamated = 1 := by decide
example : parseInto (·.isOm) phiAttached = 1 := by decide
example : noRec omegaAdjoined = 1 := by decide

/-- The function-word complex is prosodified by **ω-adjunction** — the recursive
    `[ω fnc [ω lex]]` is the unique optimum, beating φ-attachment because
    `Parse-into-ω ≫ No-Recursion` ([ito-mester-2009], contra Selkirk's φ-attached). -/
theorem omegaAdjunction_optimum :
    (Tableau.ofRanking candidates [subminimalOmega, lexToOmega, parseInto (·.isOm), noRec]).optimal
      = {omegaAdjoined} := by decide

/-- The winning structure is recursive: ω dominates ω. -/
theorem winner_is_recursive : noRec omegaAdjoined = 1 := by decide

-- The ω-adjoined optimum is a legal recursive prosodic word: an ω over a stray function
-- word and an embedded ω (the violated No-Recursion is a *violable* constraint, not `IsWord`).
example : IsWord omegaAdjoined := by decide

end ItoMester2009
