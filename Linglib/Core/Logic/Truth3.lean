import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.BoundedLattice

/-!
# Three-Valued Truth
@cite{kleene-1952}

Three-valued truth type for trivalent semantics across linglib.
Used for:
- **Plural predication**: homogeneity gaps (all satisfy → true, none → false,
  some but not all → gap). @cite{kriz-2016}, @cite{kriz-spector-2021}
- **Conditionals**: indeterminacy under supervaluation when selection functions
  disagree. @cite{ramotowska-marty-romoli-santorio-2025}
- **Presupposition**: undefined when presupposition fails.
- **Duality**: existential vs universal aggregation over three-valued lists.

## Main definitions

- `Truth3`: three-valued truth (`.true`, `.false`, `.indet`)
- `Truth3.neg`, `join`, `meet`: Strong Kleene connectives
- Lattice instances: `false < indet < true`
-/

namespace Core.Duality

/-- Three-valued truth: the 3-element bounded chain `false < indet < true`.
    Strong Kleene logic (@cite{kleene-1952}) corresponds to the order-derived
    operations: `meet` = `min` = `⊓`, `join` = `max` = `⊔`, `neg` is the
    order-reversing involution. -/
inductive Truth3 where
  | true
  | false
  | indet
  deriving Repr, DecidableEq, Inhabited

namespace Truth3

/-- Chain order: `false < indet < true`. Prop-valued (not Bool-wrapped) so
    the `Decidable` instance reduces under `rfl` and `decide`. -/
protected def le : Truth3 → Truth3 → Prop
  | .false, _      => True
  | .indet, .false => False
  | .indet, _      => True
  | .true,  .true  => True
  | _,      _      => False

instance : LE Truth3 := ⟨Truth3.le⟩

/-- Term-mode `Decidable` instance — reduces eagerly under `rfl`/`decide`,
    enabling clean kernel-level computation through the chain order. -/
instance instDecLE (a b : Truth3) : Decidable (a ≤ b) :=
  match a, b with
  | .false, _      => isTrue trivial
  | .indet, .false => isFalse not_false
  | .indet, .indet => isTrue trivial
  | .indet, .true  => isTrue trivial
  | .true,  .false => isFalse not_false
  | .true,  .indet => isFalse not_false
  | .true,  .true  => isTrue trivial

instance : LinearOrder Truth3 where
  le_refl a := by cases a <;> trivial
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> trivial
  le_antisymm a b hab hba := by cases a <;> cases b <;> first | rfl | trivial
  le_total a b := by
    cases a <;> cases b <;> first | exact Or.inl trivial | exact Or.inr trivial
  toDecidableLE := inferInstance

instance : BoundedOrder Truth3 where
  top := .true
  bot := .false
  le_top a := by cases a <;> trivial
  bot_le a := by cases a <;> trivial

/-! ## Strong Kleene operations

Strong Kleene meet/join on a chain ARE `min`/`max`. The bespoke `meet`/`join`
names are kept as `@[reducible] def`s so 91 downstream call sites continue
to work, but the canonical mathlib operations (`⊓`/`⊔`/`min`/`max`) are
preferred. -/

/-- Strong Kleene meet (= `min` on the chain `false < indet < true`). -/
@[reducible] def meet : Truth3 → Truth3 → Truth3 := min

/-- Strong Kleene join (= `max` on the chain `false < indet < true`). -/
@[reducible] def join : Truth3 → Truth3 → Truth3 := max

/-- Strong Kleene negation: order-reversing involution.
    `false ↔ true`, `indet` fixed. -/
def neg : Truth3 → Truth3
  | .true  => .false
  | .indet => .indet
  | .false => .true

@[simp] theorem neg_neg (a : Truth3) : neg (neg a) = a := by cases a <;> rfl

@[simp] theorem neg_indet : neg .indet = .indet := rfl

theorem neg_involutive : Function.Involutive (neg : Truth3 → Truth3) := neg_neg

/-! ## Mathlib-derived simp lemmas

These are inherited from `BoundedOrder` + `Lattice` + `LinearOrder` and
re-exposed under the bespoke `meet`/`join` names for downstream search. -/

@[simp] theorem sup_true (a : Truth3) : a ⊔ .true = .true := sup_top_eq a
@[simp] theorem true_sup (a : Truth3) : Truth3.true ⊔ a = .true := top_sup_eq a
@[simp] theorem inf_false (a : Truth3) : a ⊓ .false = .false := inf_bot_eq a
@[simp] theorem false_inf (a : Truth3) : Truth3.false ⊓ a = .false := bot_inf_eq a

-- Conversion from Bool

/-- Convert Bool to Truth3. -/
def ofBool : Bool → Truth3
  | Bool.true => .true
  | Bool.false => .false

/-- Check if defined (not indet). -/
def isDefined : Truth3 → Prop
  | .true => True
  | .false => True
  | .indet => False

instance : DecidablePred isDefined := fun v => by
  cases v <;> unfold isDefined <;> infer_instance

/-- Convert to Bool if defined, else default to false. -/
def toBoolOrFalse : Truth3 → Bool
  | .true => Bool.true
  | .false => Bool.false
  | .indet => Bool.false

-- ════════════════════════════════════════════════════════════════
-- Strong Kleene theorems (legacy aliases of mathlib lattice lemmas)
-- ════════════════════════════════════════════════════════════════

/-- Conjunction is commutative. (= `min_comm`) -/
theorem meet_comm (a b : Truth3) : meet a b = meet b a := min_comm a b

/-- Disjunction is commutative. (= `max_comm`) -/
theorem join_comm (a b : Truth3) : join a b = join b a := max_comm a b

/-- false is absorbing for conjunction. -/
theorem meet_false_left (a : Truth3) : meet .false a = .false := bot_inf_eq a
theorem meet_false_right (a : Truth3) : meet a .false = .false := inf_bot_eq a

/-- true is absorbing for disjunction. -/
theorem join_true_left (a : Truth3) : join .true a = .true := top_sup_eq a
theorem join_true_right (a : Truth3) : join a .true = .true := sup_top_eq a

/-- true is identity for conjunction. -/
theorem meet_true_left (a : Truth3) : meet .true a = a := top_inf_eq a
theorem meet_true_right (a : Truth3) : meet a .true = a := inf_top_eq a

/-- false is identity for disjunction. -/
theorem join_false_left (a : Truth3) : join .false a = a := bot_sup_eq a
theorem join_false_right (a : Truth3) : join a .false = a := sup_bot_eq a

/-- indet propagates in conjunction (when not dominated by false). -/
theorem meet_indet_left (a : Truth3) (h : a ≠ .false) : meet .indet a = .indet := by
  cases a <;> first | rfl | exact absurd rfl h

/-- indet propagates in disjunction (when not dominated by true). -/
theorem join_indet_left (a : Truth3) (h : a ≠ .true) : join .indet a = .indet := by
  cases a <;> first | rfl | exact absurd rfl h

/-- `Truth3.ofBool` preserves `⊓`/`&&` (canonical typeclass form). -/
@[simp] theorem ofBool_inf (a b : Bool) :
    Truth3.ofBool a ⊓ Truth3.ofBool b = Truth3.ofBool (a && b) := by
  cases a <;> cases b <;> decide

/-- `Truth3.ofBool` preserves `⊔`/`||` (canonical typeclass form). -/
@[simp] theorem ofBool_sup (a b : Bool) :
    Truth3.ofBool a ⊔ Truth3.ofBool b = Truth3.ofBool (a || b) := by
  cases a <;> cases b <;> decide

/-- Negation agrees with Bool. -/
theorem neg_ofBool (a : Bool) : neg (ofBool a) = ofBool (!a) := by
  cases a <;> rfl

/-- `Truth3.ofBool` is a bounded lattice homomorphism from `Bool` into the
    `{⊥, ⊤}` sublattice of `Truth3`. The four homomorphism conditions
    follow from `ofBool_sup`, `ofBool_inf`, and the fact that
    `ofBool false = ⊥` and `ofBool true = ⊤` definitionally.

    Registering this instance lets downstream consumers (e.g.,
    `Core.Duality.aggregate_*_map_ofBool`) appeal to the general
    `LatticeHom` API rather than to bespoke case-split lemmas. -/
def ofBoolHom : BoundedLatticeHom Bool Truth3 where
  toFun := ofBool
  map_sup' a b := (ofBool_sup a b).symm
  map_inf' a b := (ofBool_inf a b).symm
  map_top' := rfl
  map_bot' := rfl

/-- Conjunction is associative. (= `min_assoc`) -/
theorem meet_assoc (a b c : Truth3) : meet (meet a b) c = meet a (meet b c) :=
  min_assoc a b c

/-- Disjunction is associative. (= `max_assoc`) -/
theorem join_assoc (a b c : Truth3) : join (join a b) c = join a (join b c) :=
  max_assoc a b c

-- ════════════════════════════════════════════════════════════════
-- Exclusive Disjunction (XOR)
-- ════════════════════════════════════════════════════════════════

/-- Strong Kleene exclusive disjunction.

    True when exactly one operand is true; false when both or neither;
    undefined when either operand is undefined.

    Unlike inclusive disjunction (`join`), XOR cannot "see past" an
    undefined operand: `join .true .indet = .true` (the true operand
    settles the result), but `xor .true .indet = .indet` (we need to
    know the other's value to determine XOR).

    @cite{wang-davidson-2026} Figure 2. -/
def xor : Truth3 → Truth3 → Truth3
  | .true, .false => .true
  | .false, .true => .true
  | .true, .true => .false
  | .false, .false => .false
  | _, _ => .indet

/-- XOR is commutative. -/
theorem xor_comm (a b : Truth3) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

/-- XOR decomposes as (a ∨ b) ∧ ¬(a ∧ b) under Strong Kleene. -/
theorem xor_eq_join_meet_neg (a b : Truth3) :
    xor a b = meet (join a b) (neg (meet a b)) := by
  cases a <;> cases b <;> rfl

/-- XOR propagates indet unconditionally from the left. -/
theorem xor_indet_left (a : Truth3) : xor .indet a = .indet := by
  cases a <;> rfl

/-- XOR propagates indet unconditionally from the right. -/
theorem xor_indet_right (a : Truth3) : xor a .indet = .indet := by
  cases a <;> rfl

/-- XOR agrees with Bool XOR on defined inputs. -/
theorem xor_ofBool (a b : Bool) : xor (ofBool a) (ofBool b) = ofBool (a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- **Uniform projection under XOR**: XOR returns undefined iff at
    least one operand is undefined. This is the semantic core of
    @cite{wang-davidson-2026}'s prediction: exclusive disjunction
    does not filter presuppositions.

    Contrast with inclusive disjunction (`join`), where
    `join .true .indet = .true` — a true first disjunct "filters"
    the second's presupposition failure. -/
theorem xor_indet_iff (a b : Truth3) :
    xor a b = .indet ↔ a = .indet ∨ b = .indet := by
  cases a <;> cases b <;> simp [xor]

-- ════════════════════════════════════════════════════════════════
-- Weak Kleene Connectives + Meta-Assertion
-- ════════════════════════════════════════════════════════════════

-- Weak Kleene "internal" connectives originate with @cite{bochvar-1937}
-- (Russian original; English translation by Bergmann 1981); subsequently
-- discussed by @cite{kleene-1952}. The "indet propagates" / "nonsense"
-- semantics matches Bochvar's three-valued treatment of paradox-prone
-- statements. The `metaAssert` operator is Beaver-Krahmer's 𝒜
-- (assertion operator) — see @cite{beaver-krahmer-2001} §2 — which
-- collapses any trivalent value to bivalent by treating `.indet` as
-- false.

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

/-- Meta-assertion operator: the **𝒜 (assertion) operator** of
    @cite{beaver-krahmer-2001} §2. Maps `.indet` to `.false`, making
    any trivalent value bivalent by treating undefinedness as falsity.
    Used for "transplication" / closing trivalent contexts to Bool. -/
def metaAssert : Truth3 → Truth3
  | .true => .true
  | .false => .false
  | .indet => .false

-- ════════════════════════════════════════════════════════════════
-- @[simp] truth table for `metaAssert` (Strong Kleene `join` is the
-- lattice `⊔`, already covered by `sup_true`/`true_sup` above).
-- ════════════════════════════════════════════════════════════════

@[simp] theorem metaAssert_true : metaAssert .true = .true := rfl
@[simp] theorem metaAssert_false : metaAssert .false = .false := rfl
@[simp] theorem metaAssert_indet : metaAssert .indet = .false := rfl

theorem joinWeak_comm (a b : Truth3) : joinWeak a b = joinWeak b a := by
  cases a <;> cases b <;> rfl

theorem meetWeak_comm (a b : Truth3) : meetWeak a b = meetWeak b a := by
  cases a <;> cases b <;> rfl

/-- Meta-assertion always produces a defined value. -/
theorem metaAssert_defined (v : Truth3) : (metaAssert v).isDefined := by
  cases v <;> trivial

/-- Meta-assertion is idempotent. -/
theorem metaAssert_idempotent (v : Truth3) : metaAssert (metaAssert v) = metaAssert v := by
  cases v <;> rfl

/-- Meta-assertion preserves defined values. -/
theorem metaAssert_of_defined (v : Truth3) (h : v.isDefined) : metaAssert v = v := by
  cases v with | true => rfl | false => rfl | indet => exact absurd h id

-- ════════════════════════════════════════════════════════════════
-- Middle Kleene Connectives
-- @cite{peters-1979} @cite{beaver-krahmer-2001} @cite{spector-2025}
-- ════════════════════════════════════════════════════════════════

/-- Middle Kleene conjunction: left-undefined absorbs; left-defined
    follows Strong Kleene. **Asymmetric**: `false ∧ # = false` but
    `# ∧ false = #`.

    This captures left-to-right evaluation for conjunction
    (@cite{peters-1979}, @cite{beaver-krahmer-2001}, @cite{spector-2025}):
    if the first conjunct is undefined, the result is undefined regardless
    of the second. If the first conjunct is defined, Strong Kleene applies.

    | meetMiddle | true  | false | indet |
    |------------|-------|-------|-------|
    | true       | true  | false | indet |
    | false      | false | false | false |
    | indet      | indet | indet | indet | -/
def meetMiddle : Truth3 → Truth3 → Truth3
  | .indet, _ => .indet
  | a, b => meet a b

/-- Middle Kleene disjunction: left-undefined absorbs; left-defined
    follows Strong Kleene. **Asymmetric**: `true ∨ # = true` but
    `# ∨ true = #`.

    This captures left-to-right presupposition filtering
    (@cite{peters-1979}): if the first disjunct is defined, its
    truth value can settle the result even when the second is
    undefined. But if the first is undefined, the whole disjunction
    is undefined regardless of the second.

    | joinMiddle | true  | false | indet |
    |------------|-------|-------|-------|
    | true       | true  | true  | true  |
    | false      | true  | false | indet |
    | indet      | indet | indet | indet | -/
def joinMiddle : Truth3 → Truth3 → Truth3
  | .indet, _ => .indet
  | a, b => join a b

/-- Middle Kleene conjunction is NOT commutative.
    `meetMiddle false indet = false` but `meetMiddle indet false = indet`. -/
theorem meetMiddle_not_comm : ¬ ∀ a b : Truth3, meetMiddle a b = meetMiddle b a := by
  intro h; have := h .false .indet; simp [meetMiddle, meet] at this

/-- When the left operand is defined, Middle Kleene conjunction
    equals Strong Kleene conjunction. -/
theorem meetMiddle_eq_meet_of_left_defined (a b : Truth3) (h : a.isDefined) :
    meetMiddle a b = meet a b := by
  cases a with | true => rfl | false => rfl | indet => exact absurd h id

/-- Middle Kleene disjunction is NOT commutative.
    `joinMiddle true indet = true` but `joinMiddle indet true = indet`. -/
theorem joinMiddle_not_comm : ¬ ∀ a b : Truth3, joinMiddle a b = joinMiddle b a := by
  intro h; have := h .true .indet; simp [joinMiddle, join] at this

/-- Left-undefined absorbs Middle Kleene conjunction. -/
theorem meetMiddle_indet_left (a : Truth3) : meetMiddle .indet a = .indet := rfl

/-- Left-undefined absorbs Middle Kleene disjunction. -/
theorem joinMiddle_indet_left (a : Truth3) : joinMiddle .indet a = .indet := rfl

/-- `true` is left identity for Middle Kleene conjunction:
    `true ∧ ψ = ψ`. When the first conjunct is true, the result
    is just the second conjunct. -/
theorem meetMiddle_true_left (a : Truth3) : meetMiddle .true a = a := by cases a <;> rfl

/-- `false` is left zero for Middle Kleene conjunction:
    `false ∧ ψ = false` for all `ψ`. This is the key asymmetry vs
    Weak Kleene: `meetMiddle false indet = false` (defined operand
    absorbs via Strong Kleene) whereas `meetWeak false indet = indet`. -/
theorem meetMiddle_false_left (a : Truth3) : meetMiddle .false a = .false := by
  cases a <;> rfl

/-- `false` is left identity for Middle Kleene disjunction:
    `false ∨ ψ = ψ`. When the first disjunct is false, the result
    is just the second disjunct. -/
theorem joinMiddle_false_left (a : Truth3) : joinMiddle .false a = a := by cases a <;> rfl

/-- Middle Kleene conjunction agrees with Bool on defined inputs. -/
theorem meetMiddle_ofBool (a b : Bool) :
    meetMiddle (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Middle Kleene disjunction agrees with Bool on defined inputs. -/
theorem joinMiddle_ofBool (a b : Bool) :
    joinMiddle (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- When the left operand is defined, Middle Kleene disjunction
    equals Strong Kleene disjunction. -/
theorem joinMiddle_eq_join_of_left_defined (a b : Truth3) (h : a.isDefined) :
    joinMiddle a b = join a b := by
  cases a with | true => rfl | false => rfl | indet => exact absurd h id

-- ════════════════════════════════════════════════════════════════
-- Belnap Conditional Assertion Connectives
-- @cite{belnap-1970}
-- ════════════════════════════════════════════════════════════════

/-- Belnap conjunction: undefined operands are skipped.

    If one operand is undefined, the result equals the other.
    If both are undefined, the result is undefined.
    This models @cite{belnap-1970}'s (8): conjunction is assertive iff
    at least one conjunct is assertive; what it asserts = conjunction
    of assertive conjuncts only. `indet` is the identity element.

    | meetBelnap | true  | false | indet |
    |------------|-------|-------|-------|
    | true       | true  | false | true  |
    | false      | false | false | false |
    | indet      | true  | false | indet |

    Contrast: Strong Kleene `meet` (indet propagates unless dominated),
    Weak Kleene `meetWeak` (indet always propagates). -/
def meetBelnap : Truth3 → Truth3 → Truth3
  | .indet, b => b
  | a, .indet => a
  | a, b => meet a b

/-- Belnap disjunction: undefined operands are skipped.

    Models @cite{belnap-1970}'s (9): disjunction is assertive iff at
    least one disjunct is assertive; what it asserts = disjunction of
    assertive disjuncts only. `indet` is the identity element. -/
def joinBelnap : Truth3 → Truth3 → Truth3
  | .indet, b => b
  | a, .indet => a
  | a, b => join a b

/-- `indet` is left identity for Belnap conjunction. -/
theorem meetBelnap_indet_left (a : Truth3) : meetBelnap .indet a = a := rfl

/-- `indet` is right identity for Belnap conjunction. -/
theorem meetBelnap_indet_right (a : Truth3) : meetBelnap a .indet = a := by
  cases a <;> rfl

/-- Belnap conjunction is commutative. -/
theorem meetBelnap_comm (a b : Truth3) : meetBelnap a b = meetBelnap b a := by
  cases a <;> cases b <;> rfl

/-- `indet` is left identity for Belnap disjunction. -/
theorem joinBelnap_indet_left (a : Truth3) : joinBelnap .indet a = a := rfl

/-- `indet` is right identity for Belnap disjunction. -/
theorem joinBelnap_indet_right (a : Truth3) : joinBelnap a .indet = a := by
  cases a <;> rfl

/-- Belnap disjunction is commutative. -/
theorem joinBelnap_comm (a b : Truth3) : joinBelnap a b = joinBelnap b a := by
  cases a <;> cases b <;> rfl

/-- Belnap conjunction agrees with Bool on defined inputs. -/
theorem meetBelnap_ofBool (a b : Bool) :
    meetBelnap (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Belnap disjunction agrees with Bool on defined inputs. -/
theorem joinBelnap_ofBool (a b : Bool) :
    joinBelnap (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

end Truth3

/-- How truth values aggregate through an operator.
    Conjunctive (universal-like): all must succeed.
    Disjunctive (existential-like): one must succeed. -/
inductive ProjectionType where
  | conjunctive
  | disjunctive
  deriving Repr, DecidableEq

/-- Three-valued propositions: functions from worlds to Truth3. -/
abbrev Prop3 (W : Type*) := W → Truth3

namespace Prop3

variable {W : Type*}

/-! `Prop3 W := W → Truth3` is a `Pi` type. The `Lattice (W → Truth3)`
    instance auto-derives from `Pi.instLattice` once `Truth3` has
    `Lattice` (via `LinearOrder`), so `(p ⊔ q) w = p w ⊔ q w` and
    `(p ⊓ q) w = p w ⊓ q w` come for free from mathlib's `Pi.sup_apply`
    / `Pi.inf_apply`. Use `· ⊔ ·` / `· ⊓ ·` directly instead of bespoke
    `Prop3.or`/`Prop3.and` wrappers.

    The only Truth3-specific operation that needs a pointwise lift here
    is `metaAssert` (Beaver-Krahmer 𝒜) — there's no `Pi`-equivalent of
    a unary type-collapsing operator. -/

/-- Pointwise meta-assertion (Beaver-Krahmer 𝒜 operator). -/
def metaAssert (p : Prop3 W) : Prop3 W := λ w => Truth3.metaAssert (p w)

@[simp] theorem metaAssert_apply (p : Prop3 W) (w : W) :
    Prop3.metaAssert p w = Truth3.metaAssert (p w) := rfl

end Prop3

end Core.Duality
