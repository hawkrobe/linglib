import Linglib.Theories.Semantics.Alternatives.StructuralAlternatives
import Linglib.Theories.Semantics.Alternatives.Symmetry

/-!
# Fox & Katzir 2011: On the Characterization of Alternatives
@cite{fox-katzir-2011}

Fox, D. & Katzir, R. (2011). On the characterization of alternatives.
Natural Language Semantics, 19(1), 87–107.

## Core Argument

The formal alternatives for Scalar Implicatures (SI) and Association
with Focus (AF) are determined the same way — via @cite{katzir-2007}'s
structural complexity, not via Horn scales (for SI) or Rooth's focus
semantics (for AF).

## Key Formalized Results

1. **Worked example**: some/all symmetry verified computationally
2. **Bridge to Fox 2007**: exh vacuous with symmetric alts, correct without
3. **Bridge to Katzir 2007**: structural F breaks symmetry
4. **Unified F(S,C) (37)**: structural alternatives with contextual extension

The core symmetry infrastructure (`isSymmetric`, `symmetric_complement`,
`both_excluded_inconsistent`, `context_cannot_break_symmetry`) lives in
`Symmetry.lean` — those concepts predate this paper and are used across
the exhaustification literature.

## Connection to Linglib

This file bridges @cite{katzir-2007} (`StructuralAlternatives.lean`)
and @cite{fox-2007} (`Fox2007.lean`):

- Katzir defines F(S) structurally → symmetry is broken in F
- Fox defines `exh` via innocent exclusion → symmetric alts are
  not in I-E (they appear in different maximal consistent exclusions)
- Fox & Katzir prove that contextual restriction C *cannot* break
  symmetry — only F can
-/

namespace Alternatives.FoxKatzir2011

open Alternatives.Symmetry
open Exhaustification.Fox2007 hiding sublists


-- ============================================================
-- SECTION 1: Worked Example — Some/All (§1.1, p. 88)
-- ============================================================

/-!
## The Canonical Symmetric Example

S = "John did some of the homework"
S₁ = "John did all of the homework"
S₂ = "John did some but not all of the homework"

⟦S₁⟧ ∪ ⟦S₂⟧ = ⟦S⟧ and ⟦S₁⟧ ∩ ⟦S₂⟧ = ∅ — the classic partition.
-/

section SomeAll

/-- Three homework worlds: did all, did some (but not all), did none. -/
inductive HWWorld where | all_ | someNotAll | none_
  deriving Repr, DecidableEq, BEq

private def hwDomain : List HWWorld := [.all_, .someNotAll, .none_]

private def didSome : HWWorld → Bool
  | .all_ | .someNotAll => true | .none_ => false
private def didAll : HWWorld → Bool
  | .all_ => true | _ => false
private def didSomeNotAll : HWWorld → Bool
  | .someNotAll => true | _ => false

/-- "All" and "some but not all" are symmetric alternatives of "some":
    they partition "some"'s denotation. -/
theorem some_all_symmetric :
    isSymmetric hwDomain didSome didAll didSomeNotAll = true := by
  native_decide

/-- Symmetric complement verified: some ∧ ¬all = sbna on this domain. -/
theorem some_all_complement :
    hwDomain.all (fun w => (didSome w && !didAll w) == didSomeNotAll w)
      = true := by
  native_decide

/-- Alternatives for "some": {some, all, sbna}. -/
private def someAlts : List (HWWorld → Bool) :=
  [didSome, didAll, didSomeNotAll]

/-- With both symmetric alternatives, neither is innocently excludable:
    MCE₁ excludes all (index 1), MCE₂ excludes sbna (index 2). -/
theorem some_symmetric_neither_ie :
    let ie := ieIndices hwDomain didSome someAlts
    ie.contains 1 = false ∧ ie.contains 2 = false := by
  native_decide

/-- Without the symmetric alternative sbna (i.e., with Horn-scale
    alternatives {some, all}), "all" IS innocently excludable. -/
theorem some_hornscale_all_ie :
    let hornAlts : List (HWWorld → Bool) := [didSome, didAll]
    let ie := ieIndices hwDomain didSome hornAlts
    ie.contains 1 = true := by
  native_decide

/-- The symmetry problem in a nutshell: with the full set
    {some, all, sbna}, exh is vacuous (no SIs). With the restricted
    set {some, all}, exh correctly derives ¬all. -/
theorem symmetry_problem :
    -- Full set: exh is identity (no exclusions)
    (∀ w : HWWorld, exhB hwDomain someAlts didSome w =
      didSome w) ∧
    -- Restricted set: exh derives ¬all
    (∀ w : HWWorld, exhB hwDomain [didSome, didAll] didSome w =
      (didSome w && !didAll w)) := by
  constructor <;> intro w <;> cases w <;> native_decide

end SomeAll


-- ============================================================
-- SECTION 2: F Breaks Symmetry — Bridge to Katzir 2007 (§2–3)
-- ============================================================

/-!
## F Breaks Symmetry

While C cannot break symmetry, the formal alternatives F(S) can.
@cite{katzir-2007}'s structural definition excludes "some but not all"
from F("some") because it requires ConjP/NegP structure not derivable
from the substitution source.

- `all_is_alternative_to_some`: "all" ∈ F("some")
- `symmetry_problem_solved`: "some but not all" ∉ F("some")

These are re-exported from `StructuralAlternatives.lean`.
-/

section FBreaksSymmetry

open StructuralAlternatives

/-- F contains the non-symmetric alternative (all) but excludes the
    symmetric partner (sbna). This is exactly what's needed for exh
    to derive the correct SI ¬all. -/
theorem f_breaks_symmetry :
    allSentence ∈ structuralAlternatives exLexicon someSentence ∧
    someButNotAllSentence ∉ structuralAlternatives exLexicon
      someSentence :=
  ⟨all_is_alternative_to_some, symmetry_problem_solved⟩

end FBreaksSymmetry


-- ============================================================
-- SECTION 3: Unified F for SI and AF (claim 27, p. 94)
-- ============================================================

/-!
## Unified Definition: F_SI = F_AF (claim 27)

Fox & Katzir argue that the formal alternatives for SI and AF should
be defined identically — both via structural complexity (extending
@cite{katzir-2007} to focused constituents).

The standard view (26):
- For SI: F(S) = Horn scales (stipulated)
- For AF: F(S) = Rooth's focus semantics (type-based)

Their proposal (37): both use structural alternatives restricted to
focused constituents:
  F(S, C) = {S' : S' derived from S by replacing focused
             constituents with items ≲_C-comparable}

This preserves focus sensitivity (from Rooth) while allowing symmetry
breaking (from Katzir).

**Simplification**: our `formalAlternatives` does not enforce the focus
restriction (replacements may target any constituent, not only focused
ones). The full definition 37 would require focus-marking on parse tree
nodes. This simplification is conservative: the actual F(S,C) is a
subset of our `formalAlternatives`.
-/

/-- The substitution source for F(S, C) (conditions 34–35):
    Lexicon ∪ sub-constituents of S ∪ salient constituents in C.

    This extends @cite{katzir-2007}'s substitution source (def 41)
    with contextually salient material, enabling examples like
    Matsumoto's "warm"/"a little bit more than warm" (ex. 36). -/
def substitutionSourceFC {W : Type}
    (lexicon : List (StructuralAlternatives.PFTree W))
    (φ : StructuralAlternatives.PFTree W)
    (salient : List (StructuralAlternatives.PFTree W)) :
    List (StructuralAlternatives.PFTree W) :=
  lexicon ++ φ.subtrees ++ salient

/-- Structural alternatives with contextual extension (definition 37).
    F(S, C) = {S' : S' ≲_C S}, where the substitution source includes
    salient constituents from context C.

    When `salient = []`, this reduces to @cite{katzir-2007}'s original
    `structuralAlternatives` (modulo the focus restriction; see above). -/
def formalAlternatives {W : Type}
    (lex : List (StructuralAlternatives.PFTree W))
    (φ : StructuralAlternatives.PFTree W)
    (salient : List (StructuralAlternatives.PFTree W)) :
    Set (StructuralAlternatives.PFTree W) :=
  {ψ | StructuralAlternatives.atMostAsComplex
    (substitutionSourceFC lex φ salient) ψ φ}


end Alternatives.FoxKatzir2011
