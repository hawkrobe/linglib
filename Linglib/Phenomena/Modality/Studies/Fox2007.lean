import Linglib.Theories.Semantics.Exhaustification.Innocent
import Mathlib.Tactic.DeriveFintype

/-!
# Fox 2007: Free Choice via Recursive Exhaustification @cite{fox-2007}

The original grammatical account of free-choice permission. Recursive
application of the covert exhaustivity operator `exh` (Innocent
Exclusion) over the Sauerland alternatives `{◇(p∨q), ◇p, ◇q, ◇(p∧q)}`
derives the FC inference without Innocent Inclusion.

- **Layer 1**: `Exh(◇(p∨q)) = ◇(p∨q) ∧ ¬◇(p∧q)`
  (only `◇(p∧q)` is innocently excludable)
- **Layer 2**: `Exh²(◇(p∨q)) = ◇p ∧ ◇q ∧ ¬◇(p∧q)` — free choice

The five-world model below (`ModalW`) makes each ◇-formula correspond to
which propositional situations are accessible from the evaluation world,
so that the four Sauerland alternatives have non-trivial truth values
and the IE algorithm has something to compute over.
-/

namespace Phenomena.Modality.Studies.Fox2007

open Exhaustification (innocent predToFinset altsFromPreds)

/-- Modal worlds named by which ◇-propositions they make true. -/
inductive ModalW where
  | seesP        -- accessible: {p∧¬q}
  | seesQ        -- accessible: {¬p∧q}
  | seesPQ       -- accessible: {p∧¬q, ¬p∧q}
  | seesBoth     -- accessible: {p∧q}
  | seesNothing  -- accessible: ∅
  deriving Repr, DecidableEq, Fintype

def diamP : ModalW → Bool
  | .seesP | .seesPQ | .seesBoth => true | _ => false
def diamQ : ModalW → Bool
  | .seesQ | .seesPQ | .seesBoth => true | _ => false
def diamPorQ : ModalW → Bool
  | .seesNothing => false | _ => true
def diamPandQ : ModalW → Bool
  | .seesBoth => true | _ => false

/-- Sauerland alternatives under ◇: `{◇(p∨q), ◇p, ◇q, ◇(p∧q)}`. -/
abbrev modalAltsF : Finset (Finset ModalW) :=
  altsFromPreds [diamPorQ, diamP, diamQ, diamPandQ]

abbrev diamPorQF  : Finset ModalW := predToFinset diamPorQ
abbrev diamPF     : Finset ModalW := predToFinset diamP
abbrev diamQF     : Finset ModalW := predToFinset diamQ
abbrev diamPandQF : Finset ModalW := predToFinset diamPandQ

-- ── Layer 1 ──────────────────────────────────────────────────────────────

/-- Layer 1: `Exh(◇(p∨q)) = ◇(p∨q) ∧ ¬◇(p∧q)`. Only `◇(p∧q)` is
    innocently excludable; `◇p` and `◇q` cannot be IE-excluded because
    excluding `◇p` while keeping `◇(p∨q)` forces `◇q`, and conversely. -/
theorem exhDiamPorQ_eq :
    innocent.exh modalAltsF diamPorQF
      = predToFinset (fun w => diamPorQ w && !diamPandQ w) := by
  decide

/-- Exhaustifying `◇p` (relative to the same alternatives) excludes `◇q`. -/
theorem exhDiamP_eq :
    innocent.exh modalAltsF diamPF
      = predToFinset (fun w => diamP w && !diamQ w) := by
  decide

/-- Exhaustifying `◇q` excludes `◇p` (symmetric). -/
theorem exhDiamQ_eq :
    innocent.exh modalAltsF diamQF
      = predToFinset (fun w => diamQ w && !diamP w) := by
  decide

/-- Exhaustifying `◇(p∧q)` is vacuous: it entails every other alternative,
    so nothing is non-weaker. -/
theorem exhDiamPandQ_eq :
    innocent.exh modalAltsF diamPandQF = diamPandQF := by
  decide

-- ── Layer 2 ──────────────────────────────────────────────────────────────

/-- Layer-2 alternatives: `{Exh(φ) : φ ∈ C}` — the exhaustified
    versions of the original Sauerland alternatives. -/
abbrev layer2AltsF : Finset (Finset ModalW) :=
  ({ innocent.exh modalAltsF diamPorQF
   , innocent.exh modalAltsF diamPF
   , innocent.exh modalAltsF diamQF
   , innocent.exh modalAltsF diamPandQF } : Finset (Finset ModalW))

/-- Layer-1 result, used as the prejacent for layer 2. -/
abbrev layer1ResultF : Finset ModalW := innocent.exh modalAltsF diamPorQF

set_option maxRecDepth 2000 in
/-- **Free Choice**: double exhaustification yields `◇p ∧ ◇q ∧ ¬◇(p∧q)`.

    `Exh(C')[Exh(C)(◇(p∨q))]` excludes the layer-2 alternatives
    `Exh(◇p) = ◇p ∧ ¬◇q` and `Exh(◇q) = ◇q ∧ ¬◇p`. Negating both
    (given the layer-1 prejacent `◇(p∨q) ∧ ¬◇(p∧q)`) forces both `◇p`
    and `◇q` to hold. -/
theorem free_choice :
    innocent.exh layer2AltsF layer1ResultF
      = predToFinset (fun w => diamP w && diamQ w && !diamPandQ w) := by
  decide

set_option maxRecDepth 2000 in
/-- FC entails both disjuncts hold: the speaker has permission for each
    disjunct individually. -/
theorem fc_entails_both_disjuncts (w : ModalW)
    (h : w ∈ innocent.exh layer2AltsF layer1ResultF) :
    diamP w ∧ diamQ w := by
  rw [free_choice] at h
  cases w <;> simp_all [predToFinset, diamP, diamQ, diamPandQ]

end Phenomena.Modality.Studies.Fox2007
