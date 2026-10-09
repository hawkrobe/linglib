module

public import Linglib.Logic.Trivalent.Pointwise

/-!
# Partial propositions

A partial proposition is defined at some evaluation points and not at others. `PartialProp W`
records where it is defined, its presupposition, and what it asserts there, both as predicates on
`W`. Evaluation sends it to a three-valued proposition and forgets the assertion outside the
presupposition.

## Main declarations

* `PartialProp W`: partial propositions, with `presup, assertion : W → Prop`.
* `PartialProp.eval`: evaluation into `W → Trivalent`, with `eval_eq_true_iff`,
  `eval_eq_false_iff` and `eval_eq_indet_iff`; `eval_surjective` and `eval_eq_eval_iff` show
  that `PartialProp` presents the trivalent propositions by total representatives.

The connectives on `PartialProp` live in `Presupposition.Basic` (classical, filtering,
entailment) and `Presupposition.Trivalent` (rival trivalent families).

## Implementation notes

`PartialProp W` is parametric over the evaluation point: `PartialProp World` for possible worlds,
`PartialProp (Possibility W ℕ E)` for dynamic world-assignment pairs. `open Classical` is in scope
in the namespace because most theorems case-split on the `Prop`-valued fields, as in mathlib's
`Order/Filter/Basic.lean`. Belnap's conditional assertion `(A/B)`, which asserts `B` on the
condition `A`, is the constructor itself: `{ presup := A, assertion := B }`.

## References

* [heim-1983]
* [belnap-1970]
-/

@[expose] public section

namespace Presupposition

/-! ### `PartialProp`: Prop-based partial propositions -/

/-- A presuppositional proposition pairs an assertion with the presupposition under which it is
defined. Construct one directly with `{ presup := ..., assertion := ... }`. -/
@[ext]
structure PartialProp (W : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Prop
  /-- The at-issue content (assertion). -/
  assertion : W → Prop

namespace PartialProp

open Classical

variable {W : Type*}

/-! ### Constructors -/

/-- A plain proposition is the partial proposition that presupposes nothing. -/
def ofProp (p : W → Prop) : PartialProp W where
  presup := fun _ => True
  assertion := p

@[simp] theorem ofProp_presup (p : W → Prop) (w : W) : (ofProp p).presup w := trivial

@[simp] theorem ofProp_assertion (p : W → Prop) (w : W) : (ofProp p).assertion w ↔ p w := Iff.rfl

/-- The canonical total representative of a trivalent proposition is defined exactly where
`p` is and asserts that `p` is true there. It is a section of `PartialProp.eval`. -/
def ofTrivalent (p : W → Trivalent) : PartialProp W where
  presup := fun w => p w ≠ .indet
  assertion := fun w => p w = .true

@[simp] theorem ofTrivalent_presup (p : W → Trivalent) (w : W) :
    (ofTrivalent p).presup w ↔ p w ≠ .indet := Iff.rfl

@[simp] theorem ofTrivalent_assertion (p : W → Trivalent) (w : W) :
    (ofTrivalent p).assertion w ↔ p w = .true := Iff.rfl

/-! ### Satisfaction relations -/

/-- `p` holds at `w` when both its presupposition and its assertion do. -/
def holds (p : PartialProp W) (w : W) : Prop := p.presup w ∧ p.assertion w

@[simp] theorem holds_ofProp (p : W → Prop) (w : W) : (ofProp p).holds w ↔ p w :=
  ⟨And.right, fun h => ⟨trivial, h⟩⟩

/-- The worlds where `p` is defined and true. -/
def truthSet (p : PartialProp W) : Set W := {w | p.holds w}

@[simp] theorem mem_truthSet {p : PartialProp W} {w : W} : w ∈ p.truthSet ↔ p.holds w := Iff.rfl

/-! ### Constants -/

/-- The presuppositionless tautology holds everywhere. -/
def top : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => True

/-- The presuppositionless contradiction is defined everywhere and holds nowhere. -/
def bot : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => False

/-- The nowhere-defined proposition fails its presupposition at every point. -/
def undefined : PartialProp W where
  presup := fun _ => False
  assertion := fun _ => False

/-! ### Evaluation -/

/-- Evaluate a presuppositional proposition to three-valued truth.
    Noncomputable because it decides Prop-valued presupposition and
    assertion via classical logic. -/
noncomputable def eval (p : PartialProp W) : W → Trivalent := fun w =>
  if p.presup w then
    if p.assertion w then .true else .false
  else .indet

/-! The simp-normal interface to `eval`: consumers reason through the three value
characterizations rather than the classical `if`-nest. -/

@[simp] theorem eval_eq_true_iff (p : PartialProp W) (w : W) :
    p.eval w = .true ↔ p.presup w ∧ p.assertion w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

@[simp] theorem eval_eq_false_iff (p : PartialProp W) (w : W) :
    p.eval w = .false ↔ p.presup w ∧ ¬p.assertion w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

@[simp] theorem eval_eq_indet_iff (p : PartialProp W) (w : W) :
    p.eval w = .indet ↔ ¬p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

/-- Evaluation is defined iff the presupposition holds. -/
@[simp] theorem isDefined_eval (p : PartialProp W) (w : W) :
    (p.eval w).isDefined ↔ p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;>
    simp [eval, hp, ha, Trivalent.isDefined]

/-! ### Round-trip: trivalent propositions ↔ `PartialProp` -/

/-- The `(W → Trivalent) → PartialProp → (W → Trivalent)` round-trip is the identity. -/
theorem eval_ofTrivalent (p : W → Trivalent) : (ofTrivalent p).eval = p := by
  funext w; cases h : p w <;> simp [eval, ofTrivalent, h]

/-- `eval` is surjective — every trivalent proposition has a total representative,
    `ofTrivalent` being a section. -/
theorem eval_surjective : Function.Surjective (eval : PartialProp W → W → Trivalent) :=
  fun p ↦ ⟨ofTrivalent p, eval_ofTrivalent p⟩

/-- `eval` identifies exactly agreement on definedness and, where defined, on assertion.
    `PartialProp` is the *total-representative* presentation of `W → Trivalent`, carrying
    (linguistically inert) assertion values outside the presupposition that `eval`
    forgets — so `ofTrivalent ∘ eval` is not the identity, only `eval ∘ ofTrivalent` is
    (`eval_ofTrivalent`). -/
theorem eval_eq_eval_iff (p q : PartialProp W) :
    p.eval = q.eval ↔
      ∀ w, (p.presup w ↔ q.presup w) ∧ (p.presup w → (p.assertion w ↔ q.assertion w)) := by
  constructor
  · intro h w
    have hw : p.eval w = q.eval w := congrFun h w
    have hpq : p.presup w ↔ q.presup w := by
      rw [← isDefined_eval p w, ← isDefined_eval q w, hw]
    refine ⟨hpq, fun hp ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩⟩
    · exact ((eval_eq_true_iff q w).mp
        (hw.symm.trans ((eval_eq_true_iff p w).mpr ⟨hp, ha⟩))).2
    · exact ((eval_eq_true_iff p w).mp
        (hw.trans ((eval_eq_true_iff q w).mpr ⟨hpq.mp hp, ha⟩))).2
  · intro h
    funext w
    obtain ⟨hpq, himp⟩ := h w
    by_cases hp : p.presup w
    · by_cases ha : p.assertion w
      · simp [eval, hp, ha, hpq.mp hp, (himp hp).mp ha]
      · have hqa : ¬q.assertion w := fun hqa ↦ ha ((himp hp).mpr hqa)
        simp [eval, hp, ha, hpq.mp hp, hqa]
    · have hq : ¬q.presup w := fun hq ↦ hp (hpq.mpr hq)
      simp [eval, hp, hq]

end PartialProp

end Presupposition
