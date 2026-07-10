import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.MinMax
import Mathlib.Data.Sign.Defs
import Linglib.Core.Order.Flat

/-!
# Three-Valued Truth
[kleene-1952]

Three-valued truth type for trivalent semantics across linglib.
Used for:
- **Plural predication**: homogeneity gaps (all satisfy → true, none → false,
  some but not all → gap). [kriz-2016], [kriz-spector-2021]
- **Conditionals**: indeterminacy under supervaluation when selection functions
  disagree. [ramotowska-marty-romoli-santorio-2025]
- **Presupposition**: undefined when presupposition fails.
- **Duality**: existential vs universal aggregation over three-valued lists.

## Main definitions

- `Truth3`: three-valued truth (`.true`, `.false`, `.indet`)
- Lattice instances for the truth order `false < indet < true`: Strong Kleene
  conjunction/disjunction are its `⊓`/`⊔`, and `Truth3.neg` is the involutive antitone
  negation (De Morgan: `neg_inf`/`neg_sup`; Kleene law: `inf_neg_le_sup_neg`)
- `Truth3.orderIsoSignType`: order iso with `SignType` (`-1 < 0 < 1`), commuting with
  negation — the truth order's mathlib carrier; `Truth3.equivFlatBool`: carrier iso with
  `Flat Bool`, the *knowledge* order — together the Kleene bilattice
- `Truth3.toFlat_inf_mono_left` etc.: strong Kleene `⊓`/`⊔` are interlaced
  (knowledge-monotone), and weak Kleene is not (`Truth3.meetWeak_not_truthMono`)
- `Truth3.presuppose`, `Truth3.metaAssert`: the ∂ and 𝒜 operators of
  [beaver-krahmer-2001]
-/

namespace Core.Duality

/-- Three-valued truth: the 3-element bounded chain `false < indet < true`.
    Strong Kleene logic ([kleene-1952]) corresponds to the order-derived
    operations: conjunction is `⊓` (= `min`), disjunction `⊔` (= `max`), and
    `neg` the order-reversing involution. -/
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

Strong Kleene meet/join on a chain ARE `min`/`max` = `⊓`/`⊔`; use the mathlib
operations directly. -/

/-- Strong Kleene negation: order-reversing involution.
    `false ↔ true`, `indet` fixed. -/
def neg : Truth3 → Truth3
  | .true  => .false
  | .indet => .indet
  | .false => .true

@[simp] theorem neg_neg (a : Truth3) : neg (neg a) = a := by cases a <;> rfl

@[simp] theorem neg_indet : neg .indet = .indet := rfl

theorem neg_involutive : Function.Involutive (neg : Truth3 → Truth3) := neg_neg

/-- Strong Kleene negation is antitone (order-reversing). -/
theorem neg_antitone : Antitone neg := λ a b h => by
  revert h; cases a <;> cases b <;> decide

/-- De Morgan: negation swaps meet and join — from antitonicity alone. -/
@[simp] theorem neg_inf (a b : Truth3) : neg (a ⊓ b) = neg a ⊔ neg b :=
  neg_antitone.map_min

/-- De Morgan: negation swaps join and meet. -/
@[simp] theorem neg_sup (a b : Truth3) : neg (a ⊔ b) = neg a ⊓ neg b :=
  neg_antitone.map_max

/-- The Kleene law `a ⊓ ¬a ≤ b ⊔ ¬b`: with distributivity, involutivity, and the De
Morgan laws, `Truth3` is the three-element Kleene algebra — the canonical example.
Mathlib has no De Morgan/Kleene *lattice* class (its `KleeneAlgebra` is the
star-semiring); `Truth3` would be the textbook instance of one. -/
theorem inf_neg_le_sup_neg (a b : Truth3) : a ⊓ neg a ≤ b ⊔ neg b := by
  cases a <;> cases b <;> decide

/-! ## Constructor-literal simp lemmas

Inherited from `BoundedOrder` + `Lattice` + `LinearOrder`, restated with the
constructor literals (`⊤ = .true`, `⊥ = .false`) that goals actually mention. -/

@[simp] theorem sup_true (a : Truth3) : a ⊔ .true = .true := sup_top_eq a
@[simp] theorem true_sup (a : Truth3) : Truth3.true ⊔ a = .true := top_sup_eq a
@[simp] theorem inf_false (a : Truth3) : a ⊓ .false = .false := inf_bot_eq a
@[simp] theorem false_inf (a : Truth3) : Truth3.false ⊓ a = .false := bot_inf_eq a

/-- `indet` propagates through `⊓` unless dominated by `false`. -/
theorem indet_inf (a : Truth3) (h : a ≠ .false) : .indet ⊓ a = .indet := by
  cases a <;> first | rfl | exact absurd rfl h

/-- `indet` propagates through `⊔` unless dominated by `true`. -/
theorem indet_sup (a : Truth3) (h : a ≠ .true) : .indet ⊔ a = .indet := by
  cases a <;> first | rfl | exact absurd rfl h

-- Conversion from Bool

/-- Convert Bool to Truth3. -/
def ofBool : Bool → Truth3
  | Bool.true => .true
  | Bool.false => .false

instance : Coe Bool Truth3 := ⟨ofBool⟩

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

-- ════════════════════════════════════════════════════════════════
-- Exclusive Disjunction (XOR)
-- ════════════════════════════════════════════════════════════════

/-- Strong Kleene exclusive disjunction.

    True when exactly one operand is true; false when both or neither;
    undefined when either operand is undefined.

    Unlike inclusive disjunction (`⊔`), XOR cannot "see past" an
    undefined operand: `.true ⊔ .indet = .true` (the true operand
    settles the result), but `xor .true .indet = .indet` (we need to
    know the other's value to determine XOR).

    [wang-davidson-2026] Figure 2. -/
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
theorem xor_eq_sup_inf_neg (a b : Truth3) :
    xor a b = (a ⊔ b) ⊓ neg (a ⊓ b) := by
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
    [wang-davidson-2026]'s prediction: exclusive disjunction
    does not filter presuppositions.

    Contrast with inclusive disjunction (`⊔`), where
    `.true ⊔ .indet = .true` — a true first disjunct "filters"
    the second's presupposition failure. -/
theorem xor_indet_iff (a b : Truth3) :
    xor a b = .indet ↔ a = .indet ∨ b = .indet := by
  cases a <;> cases b <;> simp [xor]

/-! ## The truth order: Truth3 as `SignType`

Mathlib's carrier for a three-element chain with an involutive order-reversing
negation fixing the midpoint is `SignType` (`-1 < 0 < 1`). -/

/-- The truth-order carrier iso: `false ↔ -1`, `indet ↔ 0`, `true ↔ 1`, with Kleene
negation corresponding to `SignType` negation (`orderIsoSignType_neg`). The
knowledge-order counterpart is `equivFlatBool`. -/
def orderIsoSignType : Truth3 ≃o SignType where
  toFun := λ | .false => .neg | .indet => .zero | .true => .pos
  invFun := λ | .neg => .false | .zero => .indet | .pos => .true
  left_inv a := by cases a <;> rfl
  right_inv s := by cases s <;> rfl
  map_rel_iff' {a b} := by cases a <;> cases b <;> decide

@[simp] theorem orderIsoSignType_neg (a : Truth3) :
    orderIsoSignType (neg a) = -orderIsoSignType a := by cases a <;> rfl

/-- `SignType` multiplication transports to the Strong Kleene *biconditional*, so
`Truth3.xor` is its negation. -/
theorem orderIsoSignType_xor (a b : Truth3) :
    orderIsoSignType (xor a b) = -(orderIsoSignType a * orderIsoSignType b) := by
  cases a <;> cases b <;> rfl

-- ════════════════════════════════════════════════════════════════
-- Weak Kleene Connectives + Meta-Assertion
-- ════════════════════════════════════════════════════════════════

-- Weak Kleene "internal" connectives originate with [bochvar-1937]
-- (Russian original; English translation by Bergmann 1981); subsequently
-- discussed by [kleene-1952]. The "indet propagates" / "nonsense"
-- semantics matches Bochvar's three-valued treatment of paradox-prone
-- statements. The `metaAssert` operator is Beaver-Krahmer's 𝒜
-- (assertion operator) — see [beaver-krahmer-2001] §2 — which
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
    [beaver-krahmer-2001] §2. Maps `.indet` to `.false`, making
    any trivalent value bivalent by treating undefinedness as falsity.
    Used for "transplication" / closing trivalent contexts to Bool. -/
def metaAssert : Truth3 → Truth3
  | .true => .true
  | .false => .false
  | .indet => .false

/-- Presupposition operator: the **∂ operator** of [beaver-krahmer-2001] §2,
    the companion of `metaAssert` (𝒜). Presupposing a value asserts it when
    true and is undefined otherwise: `T ↦ T`, `F ↦ #`, `# ↦ #`. -/
def presuppose : Truth3 → Truth3
  | .true => .true
  | _ => .indet

@[simp] theorem presuppose_true : presuppose .true = .true := rfl
@[simp] theorem presuppose_false : presuppose .false = .indet := rfl
@[simp] theorem presuppose_indet : presuppose .indet = .indet := rfl

/-- Meta-asserting a presupposed value falsifies undefinedness: `𝒜 ∘ ∂` sends
    exactly `.true` to `.true`. -/
theorem metaAssert_presuppose (v : Truth3) :
    metaAssert (presuppose v) = if v = .true then .true else .false := by
  cases v <;> rfl

-- ════════════════════════════════════════════════════════════════
-- @[simp] truth table for `metaAssert` (Strong Kleene disjunction is
-- the lattice `⊔`, already covered by `sup_true`/`true_sup` above).
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
-- [peters-1979] [beaver-krahmer-2001] [spector-2025]
-- ════════════════════════════════════════════════════════════════

/-- Middle Kleene conjunction: left-undefined absorbs; left-defined
    follows Strong Kleene. **Asymmetric**: `false ∧ # = false` but
    `# ∧ false = #`.

    This captures left-to-right evaluation for conjunction
    ([peters-1979], [beaver-krahmer-2001], [spector-2025]):
    if the first conjunct is undefined, the result is undefined regardless
    of the second. If the first conjunct is defined, Strong Kleene applies.

    | meetMiddle | true  | false | indet |
    |------------|-------|-------|-------|
    | true       | true  | false | indet |
    | false      | false | false | false |
    | indet      | indet | indet | indet | -/
def meetMiddle : Truth3 → Truth3 → Truth3
  | .indet, _ => .indet
  | a, b => a ⊓ b

/-- Middle Kleene disjunction: left-undefined absorbs; left-defined
    follows Strong Kleene. **Asymmetric**: `true ∨ # = true` but
    `# ∨ true = #`.

    This captures left-to-right presupposition filtering
    ([peters-1979]): if the first disjunct is defined, its
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
  | a, b => a ⊔ b

/-- Middle Kleene conjunction is NOT commutative.
    `meetMiddle false indet = false` but `meetMiddle indet false = indet`. -/
theorem meetMiddle_not_comm : ¬ ∀ a b : Truth3, meetMiddle a b = meetMiddle b a :=
  λ h => absurd (h .false .indet) (by decide)

/-- When the left operand is defined, Middle Kleene conjunction
    equals Strong Kleene conjunction. -/
theorem meetMiddle_eq_inf_of_left_defined (a b : Truth3) (h : a.isDefined) :
    meetMiddle a b = a ⊓ b := by
  cases a with | true => rfl | false => rfl | indet => exact absurd h id

/-- Middle Kleene disjunction is NOT commutative.
    `joinMiddle true indet = true` but `joinMiddle indet true = indet`. -/
theorem joinMiddle_not_comm : ¬ ∀ a b : Truth3, joinMiddle a b = joinMiddle b a :=
  λ h => absurd (h .true .indet) (by decide)

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
theorem joinMiddle_eq_sup_of_left_defined (a b : Truth3) (h : a.isDefined) :
    joinMiddle a b = a ⊔ b := by
  cases a with | true => rfl | false => rfl | indet => exact absurd h id

-- ════════════════════════════════════════════════════════════════
-- Belnap Conditional Assertion Connectives
-- [belnap-1970]
-- ════════════════════════════════════════════════════════════════

/-- Belnap conjunction: undefined operands are skipped.

    If one operand is undefined, the result equals the other.
    If both are undefined, the result is undefined.
    This models [belnap-1970]'s (8): conjunction is assertive iff
    at least one conjunct is assertive; what it asserts = conjunction
    of assertive conjuncts only. `indet` is the identity element.

    | meetBelnap | true  | false | indet |
    |------------|-------|-------|-------|
    | true       | true  | false | true  |
    | false      | false | false | false |
    | indet      | true  | false | indet |

    Contrast: Strong Kleene `⊓` (indet propagates unless dominated),
    Weak Kleene `meetWeak` (indet always propagates). -/
def meetBelnap : Truth3 → Truth3 → Truth3
  | .indet, b => b
  | a, .indet => a
  | a, b => a ⊓ b

/-- Belnap disjunction: undefined operands are skipped.

    Models [belnap-1970]'s (9): disjunction is assertive iff at
    least one disjunct is assertive; what it asserts = disjunction of
    assertive disjuncts only. `indet` is the identity element. -/
def joinBelnap : Truth3 → Truth3 → Truth3
  | .indet, b => b
  | a, .indet => a
  | a, b => a ⊔ b

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
-- The knowledge order: Truth3 as the flat domain `Flat Bool`
-- [kleene-1952]
-- ════════════════════════════════════════════════════════════════

section KnowledgeOrder

/-- The carrier bijection `Truth3 ≃ Flat Bool`: `indet ↔ ⊥`, `true ↔ some true`,
`false ↔ some false`. `Flat Bool` carries the *information/knowledge* order
(`⊥` below both committed values), distinct from `Truth3`'s *truth* order
(`false < indet < true`) — the two orders of the Kleene bilattice. -/
def toFlat : Truth3 → Flat Bool
  | .indet => none
  | .true => some Bool.true
  | .false => some Bool.false

/-- Inverse of `toFlat`. -/
def ofFlat : Flat Bool → Truth3
  | none => .indet
  | some Bool.true => .true
  | some Bool.false => .false

/-- `Truth3` and the flat domain `Flat Bool` share a carrier. -/
def equivFlatBool : Truth3 ≃ Flat Bool where
  toFun := toFlat
  invFun := ofFlat
  left_inv a := by cases a <;> rfl
  right_inv x := by cases x with | none => rfl | some b => cases b <;> rfl

/-- **The Kleene bilattice.** The truth order and the knowledge order genuinely
differ: in the truth order `false ≤ indet`, but in the knowledge order the
committed value `false` is not below the uncommitted `indet = ⊥`. -/
theorem truthOrder_ne_knowledgeOrder :
    Truth3.false ≤ Truth3.indet ∧ ¬ toFlat .false ≤ toFlat .indet := by decide

/-! ### Interlacing: the Kleene bilattice

`Truth3`'s native order is the *truth* order `false < indet < true`; `Flat Bool`
(`equivFlatBool`) carries the *knowledge* order `⊥ ⊑ true`, `⊥ ⊑ false`. Two
orders on one carrier is a *bilattice*. Strong Kleene `∧`/`∨` are the *truth*-
order lattice operations `⊓`/`⊔` (= `min`/`max`); what makes them canonical is
**interlacing** — they are monotone for the *knowledge* order as well
([kleene-1952]'s regularity condition). Weak Kleene is *not* interlaced
(`meetWeak_not_truthMono`), so it is not a bilattice operation.

`Flat Bool`'s `SemilatticeInf` meet `⊓` is the *consensus* `⊗`; its partial join
(`PartialUnify`) is the *gullibility* `⊕`, partial because three values lack the
`⊤` ("both") of a full four-valued bilattice — so `Truth3` is the *consistent
fragment* of that bilattice. -/

/-- Strong Kleene negation is regular (knowledge-monotone); being unary, it is
in fact the *unique* monotone extension of Boolean `not`. -/
theorem toFlat_neg_mono {a b : Truth3} (h : toFlat a ≤ toFlat b) :
    toFlat (neg a) ≤ toFlat (neg b) := by
  cases a <;> cases b <;> revert h <;> decide

/-- Strong Kleene conjunction is regular (knowledge-monotone in each argument). -/
theorem toFlat_inf_mono_left {a a' : Truth3} (b : Truth3)
    (h : toFlat a ≤ toFlat a') : toFlat (a ⊓ b) ≤ toFlat (a' ⊓ b) := by
  cases a <;> cases a' <;> cases b <;> revert h <;> decide

/-- Strong Kleene disjunction is regular (knowledge-monotone in each argument). -/
theorem toFlat_sup_mono_left {a a' : Truth3} (b : Truth3)
    (h : toFlat a ≤ toFlat a') : toFlat (a ⊔ b) ≤ toFlat (a' ⊔ b) := by
  cases a <;> cases a' <;> cases b <;> revert h <;> decide

/-- Weak Kleene conjunction is **not** interlaced — it fails monotonicity in the
*truth* order (`indet ≤ true`, yet `meetWeak indet false = indet ≰ false =
meetWeak true false`). So, unlike strong Kleene `⊓`, it is not a bilattice
operation. -/
theorem meetWeak_not_truthMono :
    ¬ ∀ a a' b : Truth3, a ≤ a' → meetWeak a b ≤ meetWeak a' b :=
  fun h => absurd (h .indet .true .false (by decide)) (by decide)

/-- Weak Kleene disjunction is likewise not interlaced (fails truth-order
monotonicity). -/
theorem joinWeak_not_truthMono :
    ¬ ∀ a a' b : Truth3, a ≤ a' → joinWeak a b ≤ joinWeak a' b :=
  fun h => absurd (h .false .indet .true (by decide)) (by decide)

end KnowledgeOrder

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
