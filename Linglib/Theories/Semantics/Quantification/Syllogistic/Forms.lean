import Linglib.Theories.Semantics.Quantification.Syllogistic.Defs
import Linglib.Theories.Semantics.Quantification.Quantifier

/-!
# Syllogistic forms: modern (FOL) reading

The four `syll*` predicates correspond to the A/I/E/O corners of the
Aristotelian square, evaluated over a Venn state with given term predicates
`X, Y : Region → Bool`. This file uses the **modern** (first-order)
reading: no existential import on the universal forms (`syllAll`, `syllNone`).

| Form  | A (universal +) | I (particular +) | E (universal −) | O (particular −) |
|-------|-----------------|------------------|-----------------|------------------|
| Lean  | `syllAll`       | `syllSome`       | `syllNone`      | `syllSomeNot`    |
| GQ    | `every_sem`     | `some_sem`       | `no_sem`        | ¬`every_sem`     |
| FOL   | `∀ X→Y`         | `∃ X∧Y`          | `∀ X→¬Y`        | `∃ X∧¬Y`         |

The grounding theorems `syll*_eq_true_iff` connect each `syll*` to the
corresponding GQ denotation from `Quantifier.lean`, making the relationship
true by construction.

## Existential import lives in study files

Aristotelian readings (existential import on universal forms — e.g.
"All A is B" presupposes `∃A`) are paper-specific stances and live as
study-file wrappers, e.g.
```
def tesslerAll s X Y := syllAll s X Y && decide (∃ r, s r ∧ X r)
```
This matches the codebase convention: substrate stays modern/FOL/mathlib-style;
paper-specific commitments wrap the substrate at the point of use.

The `Aristotelian` Square (with full `SquareRelations`) lives in `Square.lean`
as a sortal restriction to states with non-empty restrictor — see that file
for the full opposition diagram in the Demey–Smessaert sense.
-/

namespace Semantics.Quantification.Syllogistic

open Core.IntensionalLogic (Frame)
open Semantics.Quantification.Quantifier
  (every_sem some_sem no_sem subalternation_a_i)

-- ============================================================================
-- §1. Region Frame
-- ============================================================================

/-- Regions as a Montague model, enabling reuse of `every_sem`/`some_sem`/`no_sem`
    from the GQ theory layer. Index = `Unit` (extensional). `abbrev` so that
    `regionModel.Entity` reduces transparently to `Region` for unification. -/
abbrev regionModel : Frame := { Entity := Region, Index := Unit }

-- ============================================================================
-- §2. Syllogistic Forms (modern reading, no existential import)
-- ============================================================================

/-- "All Xs are Ys" in state s (modern reading): every populated X-region
    also has Y. Vacuously true when no populated X-region exists. -/
def syllAll (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (∀ r : Region, (s r = true ∧ X r = true) → Y r = true)

/-- "Some Xs are Ys": some populated X-region also has Y. -/
def syllSome (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (∃ r : Region, (s r = true ∧ X r = true) ∧ Y r = true)

/-- "Some Xs are not Ys": some populated X-region lacks Y. -/
def syllSomeNot (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (∃ r : Region, (s r = true ∧ X r = true) ∧ ¬(Y r = true))

/-- "No Xs are Ys" (modern reading): no populated X-region has Y.
    Vacuously true when no populated X-region exists. -/
def syllNone (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (∀ r : Region, (s r = true ∧ X r = true) → ¬(Y r = true))

-- ============================================================================
-- §3. Grounding in `every_sem` / `some_sem` / `no_sem`
-- ============================================================================

/-- `syllAll` is exactly `every_sem` over the state-restricted restrictor. -/
theorem syllAll_eq_true_iff (s : VennState) (X Y : Region → Bool) :
    syllAll s X Y = true ↔
      every_sem regionModel (fun r => s r = true ∧ X r = true)
        (fun r => Y r = true) := by
  unfold syllAll every_sem
  simp [decide_eq_true_eq]

/-- `syllSome` is exactly `some_sem` over the state-restricted restrictor. -/
theorem syllSome_eq_true_iff (s : VennState) (X Y : Region → Bool) :
    syllSome s X Y = true ↔
      some_sem regionModel (fun r => s r = true ∧ X r = true)
        (fun r => Y r = true) := by
  unfold syllSome some_sem
  simp [decide_eq_true_eq]

/-- `syllNone` is exactly `no_sem` over the state-restricted restrictor. -/
theorem syllNone_eq_true_iff (s : VennState) (X Y : Region → Bool) :
    syllNone s X Y = true ↔
      no_sem regionModel (fun r => s r = true ∧ X r = true)
        (fun r => Y r = true) := by
  unfold syllNone no_sem
  simp [decide_eq_true_eq]

-- ============================================================================
-- §4. Quantifier and Premise Evaluation
-- ============================================================================

/-- Evaluate a syllogistic quantifier on given terms in a Venn state. -/
def syllQuantEval (q : AristQuant) (s : VennState) (X Y : Region → Bool) : Bool :=
  match q with
  | .all => syllAll s X Y
  | .some => syllSome s X Y
  | .someNot => syllSomeNot s X Y
  | .no => syllNone s X Y

/-- Truth value of premise 1 in state s. -/
def premise1Truth (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order1AB then syllQuantEval syl.q1 s hasA hasB
  else syllQuantEval syl.q1 s hasB hasA

/-- Truth value of premise 2 in state s. -/
def premise2Truth (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order2BC then syllQuantEval syl.q2 s hasB hasC
  else syllQuantEval syl.q2 s hasC hasB

/-- Literal meaning of each conclusion in a Venn state (modern reading).
    NVC ("nothing follows") is true in every state — the vacuous utterance. -/
def concMeaning : Conclusion → VennState → Bool
  | .allAC, s      => syllAll s hasA hasC
  | .allCA, s      => syllAll s hasC hasA
  | .someAC, s     => syllSome s hasA hasC
  | .someCA, s     => syllSome s hasC hasA
  | .someNotAC, s  => syllSomeNot s hasA hasC
  | .someNotCA, s  => syllSomeNot s hasC hasA
  | .noAC, s       => syllNone s hasA hasC
  | .noCA, s       => syllNone s hasC hasA
  | .nvc, _        => true

/-- "Nothing follows" is always true. -/
@[simp] theorem nvc_always_true (s : VennState) :
    concMeaning .nvc s = true := rfl

-- ============================================================================
-- §5. Subalternation A → I (conditional on non-empty restrictor)
-- ============================================================================

/-- Subalternation in the modern reading: "All Xs are Ys" entails "Some Xs
    are Ys" only when at least one X-region is populated. Derived from
    `subalternation_a_i` in `Quantifier.lean`. -/
theorem syllAll_imp_syllSome (s : VennState) (X Y : Region → Bool)
    (hExists : ∃ r : Region, s r = true ∧ X r = true)
    (h : syllAll s X Y = true) :
    syllSome s X Y = true := by
  rw [syllAll_eq_true_iff] at h
  rw [syllSome_eq_true_iff]
  exact subalternation_a_i (F := regionModel)
    (fun r => s r = true ∧ X r = true) (fun r => Y r = true) hExists h

-- ============================================================================
-- §6. Named Syllogisms
-- ============================================================================

/-- Barbara: All A-B, All B-C. Figure 1 — paradigmatic valid syllogism. -/
def barbara : Syllogism := ⟨.all, true, .all, true⟩

/-- All A-B, All C-B. Figure 3 — paradigmatic invalid syllogism. -/
def allAB_allCB : Syllogism := ⟨.all, true, .all, false⟩

/-- Some A-B, Some B-C. Figure 1 (also invalid). -/
def someSome : Syllogism := ⟨.some, true, .some, true⟩

-- ============================================================================
-- §7. Validity: Barbara
-- ============================================================================

/-- **Barbara** (All A-B, All B-C ⊢ All A-C). State-restricted transitivity
    of `every_sem`. Modern reading; existential import not required for the
    All conclusion. -/
theorem barbara_valid (s : VennState)
    (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true) :
    syllAll s hasA hasC = true := by
  rw [syllAll_eq_true_iff] at h1 h2 ⊢
  intro r ⟨hsr, hAr⟩
  exact h2 r ⟨hsr, h1 r ⟨hsr, hAr⟩⟩

/-- Barbara also validates "Some A are C" provided some A exists.
    Composes `barbara_valid` with `syllAll_imp_syllSome`. The Aristotelian
    reading takes existential import on the premises as built-in; the
    modern reading exposes it as an explicit hypothesis. -/
theorem barbara_some_valid (s : VennState)
    (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true)
    (hExists : ∃ r : Region, s r = true ∧ hasA r = true) :
    syllSome s hasA hasC = true :=
  syllAll_imp_syllSome s hasA hasC hExists (barbara_valid s h1 h2)

/-- For Barbara, every state where both premises are literally true also
    satisfies "All A-C". -/
theorem barbara_premises_imply_allAC (s : VennState) :
    premise1Truth barbara s = true →
    premise2Truth barbara s = true →
    concMeaning .allAC s = true := by
  intro h1 h2
  simp only [premise1Truth, premise2Truth, barbara, ↓reduceIte, syllQuantEval] at h1 h2
  exact barbara_valid s h1 h2

-- ============================================================================
-- §8. Witness States and Invalidity
-- ============================================================================

/-- Only AB and BC populated. Witnesses invalidity of certain syllogism
    patterns by falsifying A/I A-C and A/I C-A. -/
def state_AB_BC : VennState
  | .AB => true | .BC => true | _ => false

/-- Only ABC populated. Witnesses invalidity by falsifying E/O A-C and E/O C-A. -/
def state_ABC : VennState
  | .ABC => true | _ => false

/-- Only A and AC populated. `syllSome A-C` holds; `syllAll A-C` fails. -/
def state_A_AC : VennState
  | .A => true | .AC => true | _ => false

/-- Strict informativity: "All A-C" is compatible with strictly fewer states
    than "Some A-C" (witnessed by `state_A_AC`). -/
theorem all_strictly_stronger_than_some :
    concMeaning .someAC state_A_AC = true ∧
    concMeaning .allAC state_A_AC = false := by
  decide

/-- "All A-B, All C-B" is logically invalid: no Aristotelian conclusion holds
    in all compatible states. Two counterexample states cover the eight
    quantified conclusions. -/
theorem allAB_allCB_invalid :
    concMeaning .allAC state_AB_BC = false ∧
    concMeaning .someAC state_AB_BC = false ∧
    concMeaning .allCA state_AB_BC = false ∧
    concMeaning .someCA state_AB_BC = false ∧
    concMeaning .noAC state_ABC = false ∧
    concMeaning .someNotAC state_ABC = false ∧
    concMeaning .noCA state_ABC = false ∧
    concMeaning .someNotCA state_ABC = false := by
  decide

/-- For the invalid syllogism (All A-B, All C-B), some consistent states
    satisfy "All A-C" while others falsify it. -/
theorem allAB_allCB_premises_underdetermine_allAC :
    (premise1Truth allAB_allCB state_ABC = true ∧
     premise2Truth allAB_allCB state_ABC = true ∧
     concMeaning .allAC state_ABC = true) ∧
    (premise1Truth allAB_allCB state_AB_BC = true ∧
     premise2Truth allAB_allCB state_AB_BC = true ∧
     concMeaning .allAC state_AB_BC = false) := by
  decide

end Semantics.Quantification.Syllogistic
