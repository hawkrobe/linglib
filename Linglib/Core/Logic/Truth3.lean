import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# Three-Valued Truth
@cite{kleene-1952}

Three-valued truth type for trivalent semantics across linglib.
Used for:
- **Plural predication**: homogeneity gaps (all satisfy → true, none → false,
  some but not all → gap). @cite{kriz-2016}, @cite{kriz-spector-2021}
- **Conditionals**: indeterminacy under supervaluation when selection functions
  disagree. @cite{ramotowska-santorio-2025}
- **Presupposition**: undefined when presupposition fails.
- **Duality**: existential vs universal aggregation over three-valued lists.

## Main definitions

- `Truth3`: three-valued truth (`.true`, `.false`, `.indet`)
- `Truth3.gap`: abbreviation for `.indet`, used in homogeneity contexts
- `Truth3.neg`, `join`, `meet`: Strong Kleene connectives
- Lattice instances: `false < indet < true`
-/

namespace Core.Duality

/-- Three-valued truth. -/
inductive Truth3 where
  | true
  | false
  | indet
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Truth3

/-- Alias for `indet`, used in homogeneity contexts where the third value
represents a truth-value gap (some but not all atoms satisfy the predicate). -/
abbrev gap : Truth3 := .indet

/-- Kleene strong negation. -/
def neg : Truth3 → Truth3
  | .true => .false
  | .false => .true
  | .indet => .indet

/-- Existential aggregation (Strong Kleene disjunction). -/
def join : Truth3 → Truth3 → Truth3
  | .true, _ => .true
  | _, .true => .true
  | .false, .false => .false
  | _, _ => .indet

/-- Universal aggregation (Strong Kleene conjunction). -/
def meet : Truth3 → Truth3 → Truth3
  | .false, _ => .false
  | _, .false => .false
  | .true, .true => .true
  | _, _ => .indet

/-- Lattice ordering: false < indet < true. -/
def le : Truth3 → Truth3 → Bool
  | .false, _ => Bool.true
  | .indet, .indet => Bool.true
  | .indet, .true => Bool.true
  | .true, .true => Bool.true
  | _, _ => Bool.false

instance : LE Truth3 where
  le a b := le a b = Bool.true

instance : Preorder Truth3 where
  le a b := le a b = Bool.true
  le_refl a := by cases a <;> rfl
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> trivial

instance : PartialOrder Truth3 where
  le_antisymm a b hab hba := by cases a <;> cases b <;> trivial

instance : SemilatticeSup Truth3 where
  sup := join
  le_sup_left a b := by cases a <;> cases b <;> rfl
  le_sup_right a b := by cases a <;> cases b <;> rfl
  sup_le a b c hac hbc := by cases a <;> cases b <;> cases c <;> trivial

instance : SemilatticeInf Truth3 where
  inf := meet
  inf_le_left a b := by cases a <;> cases b <;> rfl
  inf_le_right a b := by cases a <;> cases b <;> rfl
  le_inf a b c hab hac := by cases a <;> cases b <;> cases c <;> trivial

instance : Lattice Truth3 where
  __ := inferInstanceAs (SemilatticeSup Truth3)
  __ := inferInstanceAs (SemilatticeInf Truth3)

instance : Bot Truth3 := ⟨.false⟩
instance : Top Truth3 := ⟨.true⟩

instance : OrderBot Truth3 where
  bot_le a := by cases a <;> rfl

instance : OrderTop Truth3 where
  le_top a := by cases a <;> rfl

instance : BoundedOrder Truth3 where
  __ := inferInstanceAs (OrderBot Truth3)
  __ := inferInstanceAs (OrderTop Truth3)

@[simp] theorem sup_true (a : Truth3) : a ⊔ .true = .true := by cases a <;> rfl
@[simp] theorem true_sup (a : Truth3) : Truth3.true ⊔ a = .true := by cases a <;> rfl
@[simp] theorem inf_false (a : Truth3) : a ⊓ .false = .false := by cases a <;> rfl
@[simp] theorem false_inf (a : Truth3) : Truth3.false ⊓ a = .false := by cases a <;> rfl

-- Conversion from Bool

/-- Convert Bool to Truth3. -/
def ofBool : Bool → Truth3
  | Bool.true => .true
  | Bool.false => .false

/-- Check if defined (not indet). -/
def isDefined : Truth3 → Bool
  | .true => Bool.true
  | .false => Bool.true
  | .indet => Bool.false

/-- Convert to Bool if defined, else default to false. -/
def toBoolOrFalse : Truth3 → Bool
  | .true => Bool.true
  | .false => Bool.false
  | .indet => Bool.false

-- Strong Kleene theorems

/-- Negation is involutive. -/
theorem neg_neg (v : Truth3) : neg (neg v) = v := by
  cases v <;> rfl

/-- Negation preserves indet. -/
theorem neg_indet : neg .indet = .indet := rfl

/-- Conjunction is commutative. -/
theorem meet_comm (a b : Truth3) : meet a b = meet b a := by
  cases a <;> cases b <;> rfl

/-- Disjunction is commutative. -/
theorem join_comm (a b : Truth3) : join a b = join b a := by
  cases a <;> cases b <;> rfl

/-- false is absorbing for conjunction. -/
theorem meet_false_left (a : Truth3) : meet .false a = .false := rfl
theorem meet_false_right (a : Truth3) : meet a .false = .false := by cases a <;> rfl

/-- true is absorbing for disjunction. -/
theorem join_true_left (a : Truth3) : join .true a = .true := rfl
theorem join_true_right (a : Truth3) : join a .true = .true := by cases a <;> rfl

/-- true is identity for conjunction. -/
theorem meet_true_left (a : Truth3) : meet .true a = a := by cases a <;> rfl
theorem meet_true_right (a : Truth3) : meet a .true = a := by cases a <;> rfl

/-- false is identity for disjunction. -/
theorem join_false_left (a : Truth3) : join .false a = a := by cases a <;> rfl
theorem join_false_right (a : Truth3) : join a .false = a := by cases a <;> rfl

/-- indet propagates in conjunction (when not dominated by false). -/
theorem meet_indet_left (a : Truth3) (h : a ≠ .false) : meet .indet a = .indet := by
  cases a with
  | true => rfl
  | indet => rfl
  | false => exact absurd rfl h

/-- indet propagates in disjunction (when not dominated by true). -/
theorem join_indet_left (a : Truth3) (h : a ≠ .true) : join .indet a = .indet := by
  cases a with
  | false => rfl
  | indet => rfl
  | true => exact absurd rfl h

/-- Conjunction agrees with Bool when both defined. -/
theorem meet_ofBool (a b : Bool) :
    meet (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Disjunction agrees with Bool when both defined. -/
theorem join_ofBool (a b : Bool) :
    join (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- Negation agrees with Bool. -/
theorem neg_ofBool (a : Bool) : neg (ofBool a) = ofBool (!a) := by
  cases a <;> rfl

/-- Conjunction is associative. -/
theorem meet_assoc (a b c : Truth3) : meet (meet a b) c = meet a (meet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Disjunction is associative. -/
theorem join_assoc (a b c : Truth3) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Weak Kleene Logic and Meta-Assertion
-- References:
-- - @cite{kleene-1952}, weak tables (§64)
-- - @cite{beaver-krahmer-2001}. A partial account of presupposition projection.

/-- Weak Kleene disjunction: indet is absorbing (both operands must be defined). -/
def joinWeak : Truth3 → Truth3 → Truth3
  | .true, .true => .true
  | .true, .false => .true
  | .false, .true => .true
  | .false, .false => .false
  | _, _ => .indet

/-- Weak Kleene conjunction: indet is absorbing. -/
def meetWeak : Truth3 → Truth3 → Truth3
  | .true, .true => .true
  | .true, .false => .false
  | .false, .true => .false
  | .false, .false => .false
  | _, _ => .indet

/-- Meta-assertion operator: maps indet to false.
Makes any trivalent value bivalent by treating undefinedness as falsity. -/
def metaAssert : Truth3 → Truth3
  | .true => .true
  | .false => .false
  | .indet => .false

theorem joinWeak_comm (a b : Truth3) : joinWeak a b = joinWeak b a := by
  cases a <;> cases b <;> rfl

theorem meetWeak_comm (a b : Truth3) : meetWeak a b = meetWeak b a := by
  cases a <;> cases b <;> rfl

/-- Meta-assertion always produces a defined value. -/
theorem metaAssert_defined (v : Truth3) : (metaAssert v).isDefined = Bool.true := by
  cases v <;> rfl

/-- Meta-assertion is idempotent. -/
theorem metaAssert_idempotent (v : Truth3) : metaAssert (metaAssert v) = metaAssert v := by
  cases v <;> rfl

/-- Meta-assertion preserves defined values. -/
theorem metaAssert_of_defined (v : Truth3) (h : v.isDefined = Bool.true) : metaAssert v = v := by
  cases v with | true => rfl | false => rfl | indet => simp [isDefined] at h

end Truth3

/-- How truth values aggregate through an operator.
    Conjunctive (universal-like): all must succeed.
    Disjunctive (existential-like): one must succeed. -/
inductive ProjectionType where
  | conjunctive
  | disjunctive
  deriving Repr, DecidableEq

/-- Distributivity operator with homogeneity presupposition.
    TRUE if all satisfy, FALSE if none satisfy, GAP if mixed.

    Shared structure of DIST (for plural individuals) and
    DIST_π (for conditional alternatives, @cite{santorio-2018}). -/
def dist (results : List Bool) : Truth3 :=
  if results.all id then .true
  else if results.all (!·) then .false
  else .gap

/-- `dist` on a homogeneous true list. -/
@[simp] theorem dist_nil : dist [] = .true := rfl

/-- `dist` agrees with `Truth3.ofBool` on singletons. -/
theorem dist_singleton (b : Bool) : dist [b] = Truth3.ofBool b := by
  cases b <;> rfl

/-- Three-valued propositions: functions from worlds to Truth3. -/
abbrev Prop3 (W : Type*) := W → Truth3

namespace Prop3

variable {W : Type*}

/-- Pointwise negation. -/
def neg (p : Prop3 W) : Prop3 W := λ w => Truth3.neg (p w)

/-- Pointwise Strong Kleene conjunction. -/
def and (p q : Prop3 W) : Prop3 W := λ w => Truth3.meet (p w) (q w)

/-- Pointwise Strong Kleene disjunction. -/
def or (p q : Prop3 W) : Prop3 W := λ w => Truth3.join (p w) (q w)

/-- Always true. -/
def top : Prop3 W := λ _ => .true

/-- Always false. -/
def bot : Prop3 W := λ _ => .false

/-- Always undefined. -/
def unk : Prop3 W := λ _ => .indet

/-- Convert BProp to Prop3 (always defined). -/
def ofBProp (p : W → Bool) : Prop3 W := λ w => Truth3.ofBool (p w)

/-- Pointwise Weak Kleene disjunction. -/
def orWeak (p q : Prop3 W) : Prop3 W := λ w => Truth3.joinWeak (p w) (q w)

/-- Pointwise Weak Kleene conjunction. -/
def andWeak (p q : Prop3 W) : Prop3 W := λ w => Truth3.meetWeak (p w) (q w)

/-- Pointwise meta-assertion. -/
def metaAssert (p : Prop3 W) : Prop3 W := λ w => Truth3.metaAssert (p w)

end Prop3

end Core.Duality
