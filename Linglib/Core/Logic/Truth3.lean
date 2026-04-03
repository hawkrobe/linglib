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
  deriving Repr, DecidableEq, Inhabited

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
theorem meetMiddle_eq_meet_of_left_defined (a b : Truth3) (h : a.isDefined = Bool.true) :
    meetMiddle a b = meet a b := by
  cases a with | true => rfl | false => rfl | indet => simp [isDefined] at h

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
theorem joinMiddle_eq_join_of_left_defined (a b : Truth3) (h : a.isDefined = Bool.true) :
    joinMiddle a b = join a b := by
  cases a with | true => rfl | false => rfl | indet => simp [isDefined] at h

/-- Weak Kleene refines Middle Kleene disjunction: when Weak Kleene
    gives a defined answer, Middle Kleene agrees. -/
theorem weak_refines_middle_join (a b : Truth3) (h : joinWeak a b ≠ .indet) :
    joinMiddle a b = joinWeak a b := by
  cases a <;> cases b <;> simp_all [joinMiddle, joinWeak, join]

/-- Middle Kleene refines Strong Kleene disjunction: when Middle
    Kleene gives a defined answer, Strong Kleene agrees. -/
theorem middle_refines_strong_join (a b : Truth3) (h : joinMiddle a b ≠ .indet) :
    join a b = joinMiddle a b := by
  cases a <;> cases b <;> simp_all [joinMiddle, join]

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

-- ════════════════════════════════════════════════════════════════
-- Gap Policy: Parametric Three-Valued Connectives
-- ════════════════════════════════════════════════════════════════

/-- How undefined/gap values behave under logical connectives.

    Four truth-functional systems for three-valued logic:
    - **Strong Kleene**: gap propagates unless the defined operand
      forces the result (false ∧ _ = false, true ∨ _ = true)
    - **Middle Kleene**: left-gap absorbs; left-defined uses Strong
      Kleene. Both conjunction and disjunction are asymmetric.
      (@cite{peters-1979}, @cite{beaver-krahmer-2001})
    - **Weak Kleene**: gap always propagates (both operands must
      be defined)
    - **Belnap**: gap is skipped (only defined operands contribute;
      gap is the identity element for both ∧ and ∨)

    | Policy | gap ∧ T | gap ∧ F | F ∧ gap | T ∨ gap | gap ∨ T |
    |--------|---------|---------|---------|---------|---------|
    | Strong | gap     | **F**   | **F**   | T       | **T**   |
    | Middle | gap     | gap     | **F**   | **T**   | gap     |
    | Weak   | gap     | gap     | gap     | gap     | gap     |
    | Belnap | **T**   | **F**   | **F**   | T       | **T**   | -/
inductive GapPolicy where
  | strongKleene
  | middleKleene
  | weakKleene
  | belnap
  deriving DecidableEq, Repr

/-- Parametric conjunction indexed by gap policy. -/
def meet3 : GapPolicy → Truth3 → Truth3 → Truth3
  | .strongKleene => meet
  | .middleKleene => meetMiddle
  | .weakKleene => meetWeak
  | .belnap => meetBelnap

/-- Parametric disjunction indexed by gap policy. -/
def join3 : GapPolicy → Truth3 → Truth3 → Truth3
  | .strongKleene => join
  | .middleKleene => joinMiddle
  | .weakKleene => joinWeak
  | .belnap => joinBelnap

/-- All four gap policies agree on fully defined inputs. -/
theorem meet3_agree_defined (pol : GapPolicy) (a b : Bool) :
    meet3 pol (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases pol <;> cases a <;> cases b <;> rfl

/-- All four gap policies agree on fully defined inputs (disjunction). -/
theorem join3_agree_defined (pol : GapPolicy) (a b : Bool) :
    join3 pol (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases pol <;> cases a <;> cases b <;> rfl

/-- Strong Kleene refines Belnap: when Strong Kleene gives a defined
    answer, Belnap agrees. -/
theorem strong_refines_belnap (a b : Truth3) (h : meet a b ≠ .indet) :
    meetBelnap a b = meet a b := by
  cases a <;> cases b <;> simp_all [meet, meetBelnap]

/-- Weak Kleene refines Strong Kleene: when Weak Kleene gives a defined
    answer, Strong Kleene agrees. -/
theorem weak_refines_strong (a b : Truth3) (h : meetWeak a b ≠ .indet) :
    meet a b = meetWeak a b := by
  cases a <;> cases b <;> simp_all [meet, meetWeak]

-- ════════════════════════════════════════════════════════════════
-- Definedness Hierarchy: Weak ≤ Middle ≤ Strong ≤ Belnap
-- ════════════════════════════════════════════════════════════════

/-!
### The definedness hierarchy

The four gap policies form a hierarchy in terms of how often they
produce defined (non-`#`) results:

    Weak Kleene ≤ Middle Kleene ≤ Strong Kleene ≤ Belnap

- **Weak Kleene**: `#` is absorbing — both operands must be defined.
- **Middle Kleene**: `#` absorbs from the left; if left is defined, Strong
  Kleene applies. The left-to-right asymmetry captures presupposition
  filtering (@cite{peters-1979}, @cite{beaver-krahmer-2001},
  @cite{spector-2025}).
- **Strong Kleene**: `#` propagates unless the defined operand forces the
  result (`false ∧ # = false`, `true ∨ # = true`).
- **Belnap**: `#` is the identity — undefined operands are skipped
  entirely (@cite{belnap-1970}).

The **refinement property**: if a weaker system produces a defined result,
every stronger system agrees on that result. The systems only disagree
on cases where the weaker one yields `#` but the stronger one rescues
a defined value.
-/

-- ── Meet (conjunction): missing pairwise refinements ────────────

/-- Weak Kleene refines Middle Kleene conjunction. -/
theorem weak_refines_middle_meet (a b : Truth3) (h : meetWeak a b ≠ .indet) :
    meetMiddle a b = meetWeak a b := by
  cases a <;> cases b <;> simp_all [meetMiddle, meetWeak, meet]

/-- Middle Kleene refines Strong Kleene conjunction. -/
theorem middle_refines_strong_meet (a b : Truth3) (h : meetMiddle a b ≠ .indet) :
    meet a b = meetMiddle a b := by
  cases a <;> cases b <;> simp_all [meetMiddle, meet]

-- ── Join (disjunction): missing pairwise refinements ────────────

/-- Strong Kleene refines Belnap disjunction. -/
theorem strong_refines_belnap_join (a b : Truth3) (h : join a b ≠ .indet) :
    joinBelnap a b = join a b := by
  cases a <;> cases b <;> simp_all [join, joinBelnap]

-- ── Transitive chains ──────────────────────────────────────────

/-- Weak → Strong conjunction (transitive: Weak ≤ Middle ≤ Strong). -/
theorem weak_refines_strong_meet (a b : Truth3) (h : meetWeak a b ≠ .indet) :
    meet a b = meetWeak a b :=
  weak_refines_strong a b h

/-- Weak → Strong disjunction (transitive: Weak ≤ Middle ≤ Strong). -/
theorem weak_refines_strong_join (a b : Truth3) (h : joinWeak a b ≠ .indet) :
    join a b = joinWeak a b := by
  cases a <;> cases b <;> simp_all [join, joinWeak]

/-- Weak → Belnap conjunction (full chain). -/
theorem weak_refines_belnap_meet (a b : Truth3) (h : meetWeak a b ≠ .indet) :
    meetBelnap a b = meetWeak a b := by
  cases a <;> cases b <;> simp_all [meetBelnap, meetWeak, meet]

/-- Weak → Belnap disjunction (full chain). -/
theorem weak_refines_belnap_join (a b : Truth3) (h : joinWeak a b ≠ .indet) :
    joinBelnap a b = joinWeak a b := by
  cases a <;> cases b <;> simp_all [joinBelnap, joinWeak, join]

/-- Middle → Belnap conjunction (two-step chain). -/
theorem middle_refines_belnap_meet (a b : Truth3) (h : meetMiddle a b ≠ .indet) :
    meetBelnap a b = meetMiddle a b := by
  cases a <;> cases b <;> simp_all [meetBelnap, meetMiddle, meet]

/-- Middle → Belnap disjunction (two-step chain). -/
theorem middle_refines_belnap_join (a b : Truth3) (h : joinMiddle a b ≠ .indet) :
    joinBelnap a b = joinMiddle a b := by
  cases a <;> cases b <;> simp_all [joinBelnap, joinMiddle, join]

/-- The full 4-system refinement chain for conjunction:
    if `meetWeak a b` is defined, all four systems agree. -/
theorem meet_full_chain (a b : Truth3) (h : meetWeak a b ≠ .indet) :
    meetWeak a b = meetMiddle a b ∧
    meetMiddle a b = meet a b ∧
    meet a b = meetBelnap a b := by
  cases a <;> cases b <;> simp_all [meetWeak, meetMiddle, meet, meetBelnap]

/-- The full 4-system refinement chain for disjunction:
    if `joinWeak a b` is defined, all four systems agree. -/
theorem join_full_chain (a b : Truth3) (h : joinWeak a b ≠ .indet) :
    joinWeak a b = joinMiddle a b ∧
    joinMiddle a b = join a b ∧
    join a b = joinBelnap a b := by
  cases a <;> cases b <;> simp_all [joinWeak, joinMiddle, join, joinBelnap]

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

/-- Pointwise Belnap conjunction. @cite{belnap-1970} -/
def andBelnap (p q : Prop3 W) : Prop3 W := λ w => Truth3.meetBelnap (p w) (q w)

/-- Pointwise Belnap disjunction. @cite{belnap-1970} -/
def orBelnap (p q : Prop3 W) : Prop3 W := λ w => Truth3.joinBelnap (p w) (q w)

/-- Pointwise Middle Kleene conjunction.
    @cite{peters-1979} @cite{beaver-krahmer-2001} @cite{spector-2025} -/
def andMiddle (p q : Prop3 W) : Prop3 W := λ w => Truth3.meetMiddle (p w) (q w)

/-- Pointwise Middle Kleene disjunction (asymmetric: left-to-right).
    @cite{peters-1979} @cite{beaver-krahmer-2001} @cite{spector-2025} -/
def orMiddle (p q : Prop3 W) : Prop3 W := λ w => Truth3.joinMiddle (p w) (q w)

/-- Pointwise Strong Kleene exclusive disjunction.
    @cite{wang-davidson-2026} -/
def xor (p q : Prop3 W) : Prop3 W := λ w => Truth3.xor (p w) (q w)

end Prop3

end Core.Duality
