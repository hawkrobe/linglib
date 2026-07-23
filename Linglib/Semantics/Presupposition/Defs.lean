import Linglib.Core.Logic.Trivalent.Prop3
import Mathlib.Data.Part

/-!
# Partial Propositions

Partial propositions — propositions that may be undefined at some evaluation
points. References: [heim-1983], [belnap-1970], [bale-schwarz-2022].

## Main declarations

* `PartialProp W` — partial proposition with `presup, assertion : W → Prop`.
  The canonical type for partial propositions. Fields are `Prop`-valued
  following the mathlib convention.
* `PartialValue W α` — presupposed value polymorphic in the at-issue content
  type (`α = ℚ` for degrees, `α = E` for entities). Presupposition is
  also `W → Prop`.
* `eval` — evaluation into `Prop3 W`, with the simp-normal interface
  `eval_eq_true_iff`/`eval_eq_false_iff`/`eval_eq_indet_iff`;
  `eval_surjective`/`eval_eq_eval_iff` make precise that `PartialProp` is the
  total-representative presentation of `Prop3` (values outside the
  presupposition are inert).

The connective families on `PartialProp` live in
`Semantics.Presupposition.Basic` (classical, filtering, entailment) and
`Semantics.Presupposition.Trivalent` (rival trivalent families).

## Implementation notes

`PartialProp W` is parametric over the evaluation point. Common instantiations:
`PartialProp World` (classical possible worlds), `PartialProp (Possibility W ℕ E)`
(dynamic world-assignment pairs).

`open Classical` is in scope at the namespace level because most
theorems case-split on `Prop`-valued fields. Mathlib uses the same
idiom in logic-heavy files such as `Mathlib/Order/Filter/Basic.lean`.

## Todo

* `PartialProp W = PartialValue W Prop` unification: `PartialValue` already generalizes
  `PartialProp` at the type level; unifying would let the connective zoo lift
  to arbitrary at-issue carriers.
-/

namespace Semantics.Presupposition

open Trivalent (Prop3)

/-- A presupposed value: a value that is only defined when its
presupposition holds.

`PartialValue W α` generalizes presuppositional propositions: the
presupposition is `W → Prop`, and the at-issue content is any type — a
truth value (`Bool`), a degree (`ℚ`), a measure, etc.

Linguistic motivation: many presupposition triggers return non-boolean
values. The revised *per* entry ([bale-schwarz-2022], eq. 43)
returns a presupposed pure number (`ℚ`). Definite descriptions return
presupposed entities. `PartialValue` handles all of these uniformly. -/
structure PartialValue (W : Type*) (α : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Prop
  /-- The at-issue content (value). -/
  value : W → α

namespace PartialValue

variable {W : Type*} {α : Type*}

/-- A presupposed value is defined at w iff its presupposition holds. -/
def defined (w : W) (pv : PartialValue W α) : Prop := pv.presup w

/-- The mathlib rendering: pointwise, a presupposed value is a `Part`-valued function, the
presupposition as domain. `PartialValue` is the *total-representative* presentation — the
record carries a value everywhere (no proof-carrying `Part.get`); `toPart` forgets the
values outside the presupposition. -/
def toPart (pv : PartialValue W α) : W → Part α := λ w => ⟨pv.presup w, λ _ => pv.value w⟩

open Classical in
/-- Every `Part`-valued function has a total representative: `toPart` is surjective, so the
two presentations differ only by the (linguistically inert) values outside the
presupposition. -/
theorem toPart_surjective [Inhabited α] :
    Function.Surjective (toPart : PartialValue W α → W → Part α) := λ f =>
  ⟨⟨λ w => (f w).Dom, λ w => if h : (f w).Dom then (f w).get h else default⟩, by
    funext w
    exact Part.ext' Iff.rfl (λ h₁ _ => dif_pos h₁)⟩

end PartialValue

/-! ### `PartialProp`: Prop-based partial propositions -/

/-- A presuppositional proposition: assertion + presupposition.

    Fields are `Prop`-valued following the Mathlib convention. Construct
    directly with `{ presup := ..., assertion := ... }`; for finite worlds
    with `DecidableEq`, the predicates are auto-decidable. -/
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

/-- Create a presuppositionless proposition from a `W → Prop`. -/
def ofProp (p : W → Prop) : PartialProp W where
  presup := fun _ => True
  assertion := p

/-- Convert a three-valued proposition to a PartialProp.
    Inverse of `PartialProp.eval`: defined iff value ≠ indet,
    assertion iff value = true. -/
def ofProp3 (p : Prop3 W) : PartialProp W where
  presup := fun w => p w ≠ .indet
  assertion := fun w => p w = .true

/-- Belnap's conditional assertion (A/B): assert B on condition A.

    Assertive_w iff A is true at w; what is asserted = B.
    [belnap-1970], (3): "(A/B) is assertive_w just in case
    A is true_w. (A/B)_w = B_w." -/
def condAssert (A B : W → Prop) : PartialProp W where
  presup := A
  assertion := B

/-! ### Satisfaction relations -/

/-- Full satisfaction relation: both presupposition and assertion hold.

    Argument order `(w : W) (p : PartialProp W)` supports `updateFromSat`:
    `updateFromSat PartialProp.holds p` gives the full CCP (presupposition
    test + assertion filter). -/
def holds (w : W) (p : PartialProp W) : Prop := p.presup w ∧ p.assertion w

/-- Definedness relation: presupposition holds at the evaluation point.

    Argument order `(w : W) (p : PartialProp W)` supports `updateFromSat`:
    `updateFromSat PartialProp.defined p` gives the presupposition test CCP. -/
def defined (w : W) (p : PartialProp W) : Prop := p.presup w

/-! ### Constants -/

/-- Create a tautological presupposition. -/
def top : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => True

/-- Create a contradictory presupposition. -/
def bot : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => False

/-- Create a presupposition failure (never defined). -/
def undefined : PartialProp W where
  presup := fun _ => False
  assertion := fun _ => False

/-! ### Evaluation -/

/-- Evaluate a presuppositional proposition to three-valued truth.
    Noncomputable because it decides Prop-valued presupposition and
    assertion via classical logic. -/
noncomputable def eval (p : PartialProp W) : Prop3 W := fun w =>
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

/-- Evaluation is defined iff presupposition holds. -/
@[simp] theorem eval_isDefined (p : PartialProp W) (w : W) :
    (p.eval w).isDefined ↔ p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;>
    simp [eval, hp, ha, Trivalent.isDefined]

/-! ### Round-trip: `Prop3` ↔ `PartialProp` -/

/-- `Prop3 → PartialProp → Prop3` round-trip is the identity. -/
theorem eval_ofProp3 (p : Prop3 W) : (ofProp3 p).eval = p := by
  funext w; simp only [eval, ofProp3]
  by_cases h1 : p w ≠ .indet
  · rw [if_pos h1]
    by_cases h2 : p w = .true
    · rw [if_pos h2, h2]
    · rw [if_neg h2]; symm
      exact match p w, h1, h2 with | .false, _, _ => rfl
  · rw [if_neg h1]; symm; exact not_not.mp h1

/-- `eval` is surjective — every three-valued proposition has a total representative,
    `ofProp3` being a section. -/
theorem eval_surjective : Function.Surjective (eval : PartialProp W → Prop3 W) :=
  λ p => ⟨ofProp3 p, eval_ofProp3 p⟩

/-- `eval` identifies exactly agreement on definedness and, where defined, on assertion:
    `PartialProp` is the *total-representative* presentation of `Prop3 W`, carrying
    (linguistically inert) assertion values outside the presupposition that `eval`
    forgets — so `ofProp3 ∘ eval` is not the identity, only `eval ∘ ofProp3` is
    (`eval_ofProp3`). -/
theorem eval_eq_eval_iff (p q : PartialProp W) :
    p.eval = q.eval ↔
      ∀ w, (p.presup w ↔ q.presup w) ∧ (p.presup w → (p.assertion w ↔ q.assertion w)) := by
  constructor
  · intro h w
    have hw : p.eval w = q.eval w := congrFun h w
    have hpq : p.presup w ↔ q.presup w := by
      rw [← eval_isDefined p w, ← eval_isDefined q w, hw]
    refine ⟨hpq, λ hp => ⟨λ ha => ?_, λ ha => ?_⟩⟩
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
      · have hqa : ¬q.assertion w := λ hqa => ha ((himp hp).mpr hqa)
        simp [eval, hp, ha, hpq.mp hp, hqa]
    · have hq : ¬q.presup w := λ hq => hp (hpq.mpr hq)
      simp [eval, hp, hq]

end PartialProp

end Semantics.Presupposition
