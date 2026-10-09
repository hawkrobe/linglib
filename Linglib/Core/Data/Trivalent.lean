/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.MinMax
public import Mathlib.Basic.Sign.Defs
public import Linglib.Core.Order.DeMorganAlgebra.Basic

/-!
# Three-valued truth

`Trivalent` is the three-element bounded chain `false < indet < true`: the value space of
strong Kleene logic ([kleene-1952]), the bilattice literature's THREE ([fitting-1994]),
and the consistent fragment of Belnap's FOUR. Strong Kleene conjunction and disjunction
are the chain's `⊓`/`⊔`; the carrier is logic-neutral, hosting the rival trivalent
connective families — Weak Kleene ([bochvar-1937]), Middle Kleene ([peters-1979]), Belnap
conditional assertion ([belnap-1970]) — and the partiality operators ∂ and 𝒜 of
[beaver-krahmer-2001].

The upstreamable algebra is the `IsKleene` mixin (`Core/Order/DeMorganAlgebra/Basic.lean`), of
which `Trivalent` is the canonical non-Boolean instance. The dedicated carrier with
truth-named constructors is this library's ergonomic choice; the name follows the
`Boolean` precedent — an adjective nominalized as its truth-value type — with the
`Trivalent` namespace hosting the whole trivalent development (this file's algebra,
`Logic/Trivalent/Propositional.lean`'s formulas).

## Main definitions

- `Trivalent` — three-valued truth (`.true`, `.false`, `.indet`), a `LinearOrder` and
  `BoundedOrder`. Trivalent propositions `W → Trivalent` live in
  `Logic/Trivalent/Prop3.lean`.
- `Trivalent.neg` — Strong Kleene negation: involutive (`neg_neg`), antitone
  (`neg_antitone`), De Morgan (`neg_inf`/`neg_sup`), satisfying the Kleene law
  (`inf_neg_le_sup_neg`) — so `Trivalent` is a Kleene algebra (`IsKleene`), the canonical
  non-Boolean instance (`inf_compl_indet_ne_bot`).
- `Trivalent.meetWeak`/`joinWeak`, `meetMiddle`/`joinMiddle`, `meetBelnap`/`joinBelnap`,
  `xor` — the rival connective families.
- `Trivalent.presuppose`, `Trivalent.metaAssert` — the ∂ and 𝒜 operators of
  [beaver-krahmer-2001].
- `Trivalent.ofBool`, `Trivalent.ofBoolHom` — `Bool` embeds as a bounded lattice homomorphism.
- `Trivalent.supervaluation` — the value of a predicate over a finite family of classical
  valuations ([van-fraassen-1966]), characterized as a knowledge meet in
  `Core/Data/Trivalent/Flat.lean`.

## Main results

- `Trivalent.orderIsoSignType` — the truth order's mathlib carrier is `SignType`
  (`-1 < 0 < 1`), the iso commuting with negation. The knowledge order lives in
  `Core/Data/Trivalent/Flat.lean`, and `Trivalent.orderIsoConsistent`
  (`Core/Order/Bilattice/Four.lean`) identifies `Trivalent` with the consistent part of
  Belnap's `FOUR`.

## References

[kleene-1952] [bochvar-1937] [belnap-1970] [peters-1979] [beaver-krahmer-2001]
[cobreros-etal-2012] [wang-davidson-2026] [kalman-1958] [van-fraassen-1966]
-/

@[expose] public section

/-- Three-valued truth is the 3-element bounded chain `false < indet < true`.
Strong Kleene logic ([kleene-1952]) corresponds to the order-derived operations:
conjunction is `⊓` (= `min`), disjunction `⊔` (= `max`), and `neg` the
order-reversing involution. -/
inductive Trivalent where
  | true
  | false
  | indet
  deriving Repr, DecidableEq, Inhabited, Fintype

namespace Trivalent

/-! ### The truth order -/

/-- The less-than-or-equal relation orders the truth values `false < indet < true`. -/
protected inductive LE : Trivalent → Trivalent → Prop
  | of_false (a) : Trivalent.LE .false a
  | indet : Trivalent.LE .indet .indet
  | of_true (a) : Trivalent.LE a .true

instance : LE Trivalent := ⟨Trivalent.LE⟩

instance instDecidableLE : DecidableLE Trivalent := fun a b => by
  cases a <;> cases b <;>
    first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

instance : LinearOrder Trivalent where
  le_refl a := by cases a <;> constructor
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := instDecidableLE

instance : BoundedOrder Trivalent where
  top := .true
  le_top a := by exact .of_true a
  bot := .false
  bot_le a := by exact .of_false a

/-! ### Strong Kleene negation

Strong Kleene meet/join on a chain ARE `min`/`max` = `⊓`/`⊔`; use the mathlib
operations directly. Negation is the remaining primitive. -/

/-- Strong Kleene negation is the order-reversing involution swapping `false` and
`true`, fixing `indet`. -/
def neg : Trivalent → Trivalent
  | .true  => .false
  | .indet => .indet
  | .false => .true

@[simp] theorem neg_neg (a : Trivalent) : neg (neg a) = a := by cases a <;> rfl

@[simp] theorem neg_indet : neg .indet = .indet := rfl

@[simp] theorem neg_true : neg .true = .false := rfl

@[simp] theorem neg_false : neg .false = .true := rfl

@[simp] theorem neg_eq_indet_iff {a : Trivalent} : neg a = .indet ↔ a = .indet := by
  cases a <;> decide

@[simp] theorem neg_eq_true_iff {a : Trivalent} : neg a = .true ↔ a = .false := by
  cases a <;> decide

@[simp] theorem neg_eq_false_iff {a : Trivalent} : neg a = .false ↔ a = .true := by
  cases a <;> decide

theorem neg_involutive : Function.Involutive (neg : Trivalent → Trivalent) := neg_neg

/-- Strong Kleene negation is antitone (order-reversing). -/
theorem neg_antitone : Antitone neg := fun a b h => by
  revert h; cases a <;> cases b <;> decide

/-- Negation sends a meet to the join of the negations, by antitonicity alone. -/
@[simp] theorem neg_inf (a b : Trivalent) : neg (a ⊓ b) = neg a ⊔ neg b :=
  neg_antitone.map_min

/-- Negation sends a join to the meet of the negations. -/
@[simp] theorem neg_sup (a b : Trivalent) : neg (a ⊔ b) = neg a ⊓ neg b :=
  neg_antitone.map_max

/-- The Kleene law `a ⊓ ¬a ≤ b ⊔ ¬b`. -/
theorem inf_neg_le_sup_neg (a b : Trivalent) : a ⊓ neg a ≤ b ⊔ neg b := by
  cases a <;> cases b <;> decide

/-- `neg` is the involutive antitone complement of the chain. The `ᶜ` notation gives access to
the `InvolutiveCompl` API (`Core/Order/InvolutiveCompl.lean`); `neg` remains the simp-normal
form. -/
instance : InvolutiveCompl Trivalent where
  compl := neg
  compl_compl := neg_neg
  compl_le_compl h := neg_antitone h

/-- `Trivalent` is the canonical non-Boolean Kleene algebra (`IsKleene`), failing
complementation (`inf_compl_indet_ne_bot`); it is [kalman-1958]'s three-element chain. -/
instance : IsKleene Trivalent := ⟨inf_neg_le_sup_neg⟩

/-- `Trivalent` is not complemented — `indet` witnesses the gap between Kleene and Boolean
(so `Trivalent` is no ortholattice either). -/
theorem inf_compl_indet_ne_bot : Trivalent.indet ⊓ Trivalent.indetᶜ ≠ ⊥ := by decide

/-! ### Constructor-literal simp lemmas

Inherited from `BoundedOrder` + `Lattice` + `LinearOrder`, restated with the
constructor literals (`⊤ = .true`, `⊥ = .false`) that goals actually mention. -/

@[simp] theorem sup_true (a : Trivalent) : a ⊔ .true = .true := sup_top_eq a
@[simp] theorem true_sup (a : Trivalent) : Trivalent.true ⊔ a = .true := top_sup_eq a
@[simp] theorem inf_false (a : Trivalent) : a ⊓ .false = .false := inf_bot_eq a
@[simp] theorem false_inf (a : Trivalent) : Trivalent.false ⊓ a = .false := bot_inf_eq a

theorem inf_eq_true_iff {a b : Trivalent} : a ⊓ b = .true ↔ a = .true ∧ b = .true :=
  inf_eq_top_iff

theorem sup_eq_false_iff {a b : Trivalent} : a ⊔ b = .false ↔ a = .false ∧ b = .false :=
  sup_eq_bot_iff

theorem sup_eq_true_iff {a b : Trivalent} : a ⊔ b = .true ↔ a = .true ∨ b = .true := by
  cases a <;> cases b <;> decide

theorem inf_eq_false_iff {a b : Trivalent} : a ⊓ b = .false ↔ a = .false ∨ b = .false := by
  cases a <;> cases b <;> decide

/-- `indet` propagates through `⊓` unless dominated by `false`. -/
theorem indet_inf (a : Trivalent) (h : a ≠ .false) : .indet ⊓ a = .indet := by
  cases a <;> first | rfl | exact absurd rfl h

/-- `indet` propagates through `⊔` unless dominated by `true`. -/
theorem indet_sup (a : Trivalent) (h : a ≠ .true) : .indet ⊔ a = .indet := by
  cases a <;> first | rfl | exact absurd rfl h

/-! ### Designated values

Matrix semantics fixes an upward-closed set of *designated* values; on a chain every such
set is principal, so a designation standard is just a threshold. K3 (strong Kleene)
designates `{.true}` and preserves truth; LP (Priest's Logic of Paradox) designates
`{.indet, .true}` and preserves non-falsity ([cobreros-etal-2012]). Same algebra, dual
logics — and every designation law is an order law. -/

/-- A designation standard, identified by its least designated value (`threshold`). -/
inductive Designation where
  | k3
  | lp
  deriving Repr, DecidableEq, Inhabited, Fintype

/-- The threshold (least designated value) of a standard. -/
def Designation.threshold : Designation → Trivalent
  | .k3 => .true
  | .lp => .indet

/-- The K3/LP duality as an involution on standards. -/
def Designation.dual : Designation → Designation
  | .k3 => .lp
  | .lp => .k3

@[simp] theorem Designation.dual_dual (d : Designation) : d.dual.dual = d := by
  cases d <;> rfl

@[simp] theorem Designation.dual_k3 : Designation.k3.dual = .lp := rfl
@[simp] theorem Designation.dual_lp : Designation.lp.dual = .k3 := rfl

/-- `v` is designated at `d` iff it clears the threshold — the designated set is the
principal filter above `d.threshold`. -/
def designated (d : Designation) (v : Trivalent) : Prop := d.threshold ≤ v

instance (d : Designation) (v : Trivalent) : Decidable (designated d v) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- K3-designation is truth. -/
@[simp] theorem designated_k3_iff (v : Trivalent) : designated .k3 v ↔ v = .true := by
  cases v <;> decide

/-- LP-designation is non-falsity. -/
@[simp] theorem designated_lp_iff (v : Trivalent) : designated .lp v ↔ v ≠ .false := by
  cases v <;> decide

/-- Negation swaps the designation standards — the K3/LP duality (the antitone involution
`neg` fixes `indet`, exchanging the two principal filters' complements). -/
theorem designated_neg_iff (d : Designation) (v : Trivalent) :
    designated d.dual (neg v) ↔ ¬ designated d v := by
  cases d <;> cases v <;> decide

/-- Designation distributes over `⊓`, since the designated set is a filter (`le_inf_iff`). -/
theorem designated_inf (d : Designation) (v w : Trivalent) :
    designated d (v ⊓ w) ↔ designated d v ∧ designated d w := le_inf_iff

/-- Designation distributes over `⊔`, since thresholds are prime on a chain (`le_sup_iff`). -/
theorem designated_sup (d : Designation) (v w : Trivalent) :
    designated d (v ⊔ w) ↔ designated d v ∨ designated d w := le_sup_iff

/-- K3 is the stronger standard, since its threshold dominates LP's. -/
theorem designated_lp_of_k3 {v : Trivalent} (h : designated .k3 v) : designated .lp v :=
  le_trans (by decide) h

/-! ### Conversion from Bool -/

/-- The two-valued fragment embeds by `Bool.true ↦ .true`, `Bool.false ↦ .false`. -/
def ofBool : Bool → Trivalent
  | Bool.true => .true
  | Bool.false => .false

instance : Coe Bool Trivalent := ⟨ofBool⟩

/-- The value of a decidable proposition is `true` or `false`, never `indet`. -/
def ofProp (P : Prop) [Decidable P] : Trivalent := ofBool (decide P)

@[simp] theorem ofProp_eq_true_iff {P : Prop} [Decidable P] : ofProp P = .true ↔ P := by
  by_cases h : P <;> simp [ofProp, ofBool, h]

@[simp] theorem ofProp_eq_false_iff {P : Prop} [Decidable P] : ofProp P = .false ↔ ¬ P := by
  by_cases h : P <;> simp [ofProp, ofBool, h]

@[simp] theorem ofProp_ne_indet {P : Prop} [Decidable P] : ofProp P ≠ .indet := by
  by_cases h : P <;> simp [ofProp, ofBool, h]

@[simp] theorem ofProp_true [Decidable True] : ofProp True = .true := ofProp_eq_true_iff.2 trivial

@[simp] theorem ofProp_false [Decidable False] : ofProp False = .false := ofProp_eq_false_iff.2 id

/-- A value is defined when it is not `indet`. -/
def isDefined : Trivalent → Prop
  | .true => True
  | .false => True
  | .indet => False

instance : DecidablePred isDefined := fun v => by
  cases v <;> unfold isDefined <;> infer_instance

/-- Project to `Bool`, sending `indet` to `false`. -/
def toBoolOrFalse : Trivalent → Bool
  | .true => Bool.true
  | .false => Bool.false
  | .indet => Bool.false

/-- `Trivalent.ofBool` preserves `⊓`/`&&`. -/
@[simp] theorem ofBool_inf (a b : Bool) :
    Trivalent.ofBool a ⊓ Trivalent.ofBool b = Trivalent.ofBool (a && b) := by
  cases a <;> cases b <;> decide

/-- `Trivalent.ofBool` preserves `⊔`/`||`. -/
@[simp] theorem ofBool_sup (a b : Bool) :
    Trivalent.ofBool a ⊔ Trivalent.ofBool b = Trivalent.ofBool (a || b) := by
  cases a <;> cases b <;> decide

/-- Negation agrees with Bool. -/
theorem neg_ofBool (a : Bool) : neg (ofBool a) = ofBool (!a) := by
  cases a <;> rfl

/-- The designation standards agree on the two-valued fragment. -/
theorem designated_ofBool (d : Designation) (b : Bool) :
    designated d (ofBool b) ↔ b = Bool.true := by
  cases d <;> cases b <;> decide

/-- `Trivalent.ofBool` as a bounded lattice homomorphism, onto the `{⊥, ⊤}` sublattice
of `Trivalent` — so consumers can appeal to the general `LatticeHom` API. -/
def ofBoolHom : BoundedLatticeHom Bool Trivalent where
  toFun := ofBool
  map_sup' a b := (ofBool_sup a b).symm
  map_inf' a b := (ofBool_inf a b).symm
  map_top' := rfl
  map_bot' := rfl

/-! ### Exclusive disjunction -/

/-- Strong Kleene exclusive disjunction is true when exactly one operand is true and
undefined when either operand is. Unlike `⊔`, XOR cannot "see past" an undefined
operand — `.true ⊔ .indet = .true`, but `xor .true .indet = .indet`
([wang-davidson-2026], Table 2). -/
def xor : Trivalent → Trivalent → Trivalent
  | .true, .false => .true
  | .false, .true => .true
  | .true, .true => .false
  | .false, .false => .false
  | _, _ => .indet

/-- XOR is commutative. -/
theorem xor_comm (a b : Trivalent) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

/-- XOR decomposes as (a ∨ b) ∧ ¬(a ∧ b) under Strong Kleene. -/
theorem xor_eq_sup_inf_neg (a b : Trivalent) :
    xor a b = (a ⊔ b) ⊓ neg (a ⊓ b) := by
  cases a <;> cases b <;> rfl

/-- XOR propagates indet unconditionally from the left. -/
theorem xor_indet_left (a : Trivalent) : xor .indet a = .indet := by
  cases a <;> rfl

/-- XOR propagates indet unconditionally from the right. -/
theorem xor_indet_right (a : Trivalent) : xor a .indet = .indet := by
  cases a <;> rfl

/-- XOR agrees with Bool XOR on defined inputs. -/
theorem xor_ofBool (a b : Bool) : xor (ofBool a) (ofBool b) = ofBool (a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- XOR is undefined iff at least one operand is — so exclusive disjunction never
filters undefinedness, in contrast with `⊔` (`.true ⊔ .indet = .true`)
([wang-davidson-2026]). -/
theorem xor_indet_iff (a b : Trivalent) :
    xor a b = .indet ↔ a = .indet ∨ b = .indet := by
  cases a <;> cases b <;> simp [xor]

/-! ### The truth order as `SignType`

Mathlib's carrier for a three-element chain with an involutive order-reversing
negation fixing the midpoint is `SignType` (`-1 < 0 < 1`). -/

/-- The truth order is order isomorphic to `SignType`, sending `false`, `indet` and `true` to
`-1`, `0` and `1`, and Kleene negation to `SignType` negation (`orderIsoSignType_neg`). The
knowledge-order counterpart is `equivFlatBool`. -/
def orderIsoSignType : Trivalent ≃o SignType where
  toFun := fun | .false => .neg | .indet => .zero | .true => .pos
  invFun := fun | .neg => .false | .zero => .indet | .pos => .true
  left_inv a := by cases a <;> rfl
  right_inv s := by cases s <;> rfl
  map_rel_iff' {a b} := by cases a <;> cases b <;> decide

@[simp] theorem orderIsoSignType_neg (a : Trivalent) :
    orderIsoSignType (neg a) = -orderIsoSignType a := by cases a <;> rfl

/-- `SignType` multiplication transports to the Strong Kleene *biconditional*, so
`Trivalent.xor` is its negation. -/
theorem orderIsoSignType_xor (a b : Trivalent) :
    orderIsoSignType (xor a b) = -(orderIsoSignType a * orderIsoSignType b) := by
  cases a <;> cases b <;> rfl

/-! ### Weak Kleene and the Beaver-Krahmer operators

The Weak Kleene "internal" connectives originate with [bochvar-1937] (Russian
original; English translation by Bergmann 1981) and are discussed by [kleene-1952]:
`indet` propagates unconditionally, matching Bochvar's "nonsense" reading of
paradox-prone statements. `metaAssert` and `presuppose` are the 𝒜 and ∂ operators
of [beaver-krahmer-2001] §2. -/

/-- In Weak Kleene disjunction `indet` is absorbing, so both operands must be defined. -/
def joinWeak : Trivalent → Trivalent → Trivalent
  | .true, .true => .true
  | .true, .false => .true
  | .false, .true => .true
  | .false, .false => .false
  | _, _ => .indet

/-- In Weak Kleene conjunction `indet` is absorbing. -/
def meetWeak : Trivalent → Trivalent → Trivalent
  | .true, .true => .true
  | .true, .false => .false
  | .false, .true => .false
  | .false, .false => .false
  | _, _ => .indet

theorem joinWeak_comm (a b : Trivalent) : joinWeak a b = joinWeak b a := by
  cases a <;> cases b <;> rfl

/-- The Weak Kleene disjunction is undefined iff a disjunct is. -/
theorem joinWeak_eq_indet_iff (a b : Trivalent) :
    joinWeak a b = .indet ↔ a = .indet ∨ b = .indet := by
  cases a <;> cases b <;> decide

/-- The Weak Kleene disjunction is false iff both disjuncts are. -/
theorem joinWeak_eq_false_iff (a b : Trivalent) :
    joinWeak a b = .false ↔ a = .false ∧ b = .false := by
  cases a <;> cases b <;> decide

theorem meetWeak_comm (a b : Trivalent) : meetWeak a b = meetWeak b a := by
  cases a <;> cases b <;> rfl

/-- Meta-assertion closes a trivalent value to bivalent by treating undefinedness as
falsity: Bochvar's assertion operator ([bochvar-1937]), the 𝒜 of [beaver-krahmer-2001] §2. -/
def metaAssert : Trivalent → Trivalent
  | .true => .true
  | .false => .false
  | .indet => .false

@[simp] theorem metaAssert_true : metaAssert .true = .true := rfl
@[simp] theorem metaAssert_false : metaAssert .false = .false := rfl
@[simp] theorem metaAssert_indet : metaAssert .indet = .false := rfl

/-- Meta-assertion always produces a defined value. -/
theorem metaAssert_defined (v : Trivalent) : (metaAssert v).isDefined := by
  cases v <;> trivial

/-- Meta-assertion is idempotent. -/
theorem metaAssert_idempotent (v : Trivalent) : metaAssert (metaAssert v) = metaAssert v := by
  cases v <;> rfl

/-- Meta-assertion preserves defined values. -/
theorem metaAssert_of_defined (v : Trivalent) (h : v.isDefined) : metaAssert v = v := by
  cases v with | true => rfl | false => rfl | indet => exact absurd h id

@[simp] theorem metaAssert_eq_true_iff {a : Trivalent} : metaAssert a = .true ↔ a = .true := by
  cases a <;> decide

@[simp] theorem metaAssert_eq_false_iff {a : Trivalent} : metaAssert a = .false ↔ a ≠ .true := by
  cases a <;> decide

/-- Meta-assertion distributes over strong Kleene conjunction ([beaver-krahmer-2001]'s
Fact 1). -/
theorem metaAssert_inf (a b : Trivalent) :
    metaAssert (a ⊓ b) = metaAssert a ⊓ metaAssert b := by
  cases a <;> cases b <;> decide

/-- Meta-assertion distributes over strong Kleene disjunction. -/
theorem metaAssert_sup (a b : Trivalent) :
    metaAssert (a ⊔ b) = metaAssert a ⊔ metaAssert b := by
  cases a <;> cases b <;> decide

/-- `metaAssert` is a bounded lattice homomorphism onto the two-valued fragment. -/
def metaAssertHom : BoundedLatticeHom Trivalent Trivalent where
  toFun := metaAssert
  map_sup' := metaAssert_sup
  map_inf' := metaAssert_inf
  map_top' := rfl
  map_bot' := rfl

/-- The presupposition operator ∂ asserts a true value and is undefined otherwise
(`T ↦ T`, `F ↦ #`, `# ↦ #`): Beaver's operator ([beaver-1992]), the companion of
`metaAssert` in [beaver-krahmer-2001] §2. -/
def presuppose : Trivalent → Trivalent
  | .true => .true
  | _ => .indet

@[simp] theorem presuppose_true : presuppose .true = .true := rfl
@[simp] theorem presuppose_false : presuppose .false = .indet := rfl
@[simp] theorem presuppose_indet : presuppose .indet = .indet := rfl

@[simp] theorem presuppose_eq_true_iff {a : Trivalent} : presuppose a = .true ↔ a = .true := by
  cases a <;> decide

@[simp] theorem presuppose_eq_indet_iff {a : Trivalent} : presuppose a = .indet ↔ a ≠ .true := by
  cases a <;> decide

@[simp] theorem presuppose_ne_false (a : Trivalent) : presuppose a ≠ .false := by cases a <;> decide

@[simp] theorem meetWeak_true_left (a : Trivalent) : meetWeak .true a = a := by cases a <;> rfl

@[simp] theorem meetWeak_indet_left (a : Trivalent) : meetWeak .indet a = .indet := rfl

@[simp] theorem meetWeak_indet_right (a : Trivalent) : meetWeak a .indet = .indet := by
  cases a <;> rfl

theorem meetWeak_assoc (a b c : Trivalent) :
    meetWeak (meetWeak a b) c = meetWeak a (meetWeak b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The Weak Kleene conjunction is undefined iff a conjunct is. -/
@[simp] theorem meetWeak_eq_indet_iff (a b : Trivalent) :
    meetWeak a b = .indet ↔ a = .indet ∨ b = .indet := by
  cases a <;> cases b <;> decide

/-- The Weak Kleene conjunction is true iff both conjuncts are. -/
@[simp] theorem meetWeak_eq_true_iff (a b : Trivalent) :
    meetWeak a b = .true ↔ a = .true ∧ b = .true := by
  cases a <;> cases b <;> decide

/-- The Weak Kleene conjunction is false iff a conjunct is false and the other is defined. -/
@[simp] theorem meetWeak_eq_false_iff (a b : Trivalent) :
    meetWeak a b = .false ↔ (a = .false ∧ b ≠ .indet) ∨ (a ≠ .indet ∧ b = .false) := by
  cases a <;> cases b <;> decide

/-- Negation passes through a Weak Kleene conjunction whose first conjunct is never false. -/
theorem neg_meetWeak_of_ne_false {a : Trivalent} (h : a ≠ .false) (b : Trivalent) :
    neg (meetWeak a b) = meetWeak a (neg b) := by
  revert h; cases a <;> cases b <;> decide

/-- Negation projects a presupposed conjunct. -/
theorem neg_meetWeak_presuppose (a b : Trivalent) :
    neg (meetWeak (presuppose a) b) = meetWeak (presuppose a) (neg b) :=
  neg_meetWeak_of_ne_false (presuppose_ne_false a) b

/-- Two values agree once they agree on being undefined and on being true. -/
theorem eq_of_indet_iff_of_true_iff {a b : Trivalent} (h₁ : a = .indet ↔ b = .indet)
    (h₂ : a = .true ↔ b = .true) : a = b := by
  revert h₁ h₂; cases a <;> cases b <;> decide

/-- Meta-asserting a presupposed value falsifies undefinedness: `𝒜 ∘ ∂` sends
exactly `.true` to `.true`. -/
theorem metaAssert_presuppose (v : Trivalent) :
    metaAssert (presuppose v) = if v = .true then .true else .false := by
  cases v <;> rfl

/-! ### Middle Kleene

The asymmetric left-to-right connectives of [peters-1979], the trivalent face of
Karttunen filtering ([beaver-krahmer-2001], [spector-2026]): an undefined first
operand absorbs; a defined one proceeds by Strong Kleene. -/

/-- In Middle Kleene conjunction a left undefined operand absorbs and a defined one
proceeds by Strong Kleene. Asymmetric — `meetMiddle .false .indet = .false` but
`meetMiddle .indet .false = .indet` ([peters-1979]). -/
def meetMiddle : Trivalent → Trivalent → Trivalent
  | .indet, _ => .indet
  | a, b => a ⊓ b

/-- In Middle Kleene disjunction a left undefined operand absorbs and a defined one
proceeds by Strong Kleene — a defined first disjunct can settle the result even when the second
is undefined, the left-to-right filtering pattern ([peters-1979]). -/
def joinMiddle : Trivalent → Trivalent → Trivalent
  | .indet, _ => .indet
  | a, b => a ⊔ b

/-- Middle Kleene conjunction is not commutative. -/
theorem meetMiddle_not_comm : ¬ ∀ a b : Trivalent, meetMiddle a b = meetMiddle b a :=
  fun h => absurd (h .false .indet) (by decide)

/-- Middle Kleene disjunction is not commutative. -/
theorem joinMiddle_not_comm : ¬ ∀ a b : Trivalent, joinMiddle a b = joinMiddle b a :=
  fun h => absurd (h .true .indet) (by decide)

/-- When the left operand is defined, Middle Kleene conjunction equals Strong Kleene. -/
theorem meetMiddle_eq_inf_of_left_defined (a b : Trivalent) (h : a.isDefined) :
    meetMiddle a b = a ⊓ b := by
  cases a with | true => rfl | false => rfl | indet => exact absurd h id

/-- When the left operand is defined, Middle Kleene disjunction equals Strong Kleene. -/
theorem joinMiddle_eq_sup_of_left_defined (a b : Trivalent) (h : a.isDefined) :
    joinMiddle a b = a ⊔ b := by
  cases a with | true => rfl | false => rfl | indet => exact absurd h id

/-- Left-undefined absorbs Middle Kleene conjunction. -/
theorem meetMiddle_indet_left (a : Trivalent) : meetMiddle .indet a = .indet := rfl

/-- Left-undefined absorbs Middle Kleene disjunction. -/
theorem joinMiddle_indet_left (a : Trivalent) : joinMiddle .indet a = .indet := rfl

/-- `true` is a left identity for Middle Kleene conjunction. -/
theorem meetMiddle_true_left (a : Trivalent) : meetMiddle .true a = a := by cases a <;> rfl

/-- `false` is a left zero for Middle Kleene conjunction — the key asymmetry against
Weak Kleene, where `meetWeak .false .indet = .indet`. -/
theorem meetMiddle_false_left (a : Trivalent) : meetMiddle .false a = .false := by
  cases a <;> rfl

/-- `false` is a left identity for Middle Kleene disjunction. -/
theorem joinMiddle_false_left (a : Trivalent) : joinMiddle .false a = a := by cases a <;> rfl

/-- `true` is a left zero for Middle Kleene disjunction. -/
theorem joinMiddle_true_left (a : Trivalent) : joinMiddle .true a = .true := by cases a <;> rfl

/-- `true` is a right identity for Middle Kleene conjunction. -/
theorem meetMiddle_true_right (a : Trivalent) : meetMiddle a .true = a := by cases a <;> rfl

/-- Middle Kleene conjunction reads its right argument only when its left one is true. -/
theorem meetMiddle_congr_right {a b b' : Trivalent} (h : a = .true → b = b') :
    meetMiddle a b = meetMiddle a b' := by
  rcases a with _ | _ | _
  · rw [h rfl]
  · simp [meetMiddle_false_left]
  · rfl

/-- Middle Kleene disjunction reads its right argument only when its left one is false. -/
theorem joinMiddle_congr_right {a b b' : Trivalent} (h : a = .false → b = b') :
    joinMiddle a b = joinMiddle a b' := by
  rcases a with _ | _ | _
  · simp [joinMiddle_true_left]
  · rw [h rfl]
  · rfl

theorem meetMiddle_eq_true_iff {a b : Trivalent} :
    meetMiddle a b = .true ↔ a = .true ∧ b = .true := by
  cases a <;> cases b <;> decide

/-- Middle Kleene conjunction agrees with Bool on defined inputs. -/
theorem meetMiddle_ofBool (a b : Bool) :
    meetMiddle (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Middle Kleene disjunction agrees with Bool on defined inputs. -/
theorem joinMiddle_ofBool (a b : Bool) :
    joinMiddle (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-! ### Belnap conditional assertion

[belnap-1970]'s connectives skip undefined operands: a compound is assertive iff at
least one operand is, and asserts the combination of the assertive operands only —
`indet` is the identity element. Contrast Strong Kleene (indet propagates unless
dominated) and Weak Kleene (indet always propagates). -/

/-- Belnap conjunction skips undefined operands; `indet` is the identity
([belnap-1970], (8)). -/
def meetBelnap : Trivalent → Trivalent → Trivalent
  | .indet, b => b
  | a, .indet => a
  | a, b => a ⊓ b

/-- Belnap disjunction skips undefined operands; `indet` is the identity
([belnap-1970], (9)). -/
def joinBelnap : Trivalent → Trivalent → Trivalent
  | .indet, b => b
  | a, .indet => a
  | a, b => a ⊔ b

/-- `indet` is a left identity for Belnap conjunction. -/
theorem meetBelnap_indet_left (a : Trivalent) : meetBelnap .indet a = a := rfl

/-- `indet` is a right identity for Belnap conjunction. -/
theorem meetBelnap_indet_right (a : Trivalent) : meetBelnap a .indet = a := by
  cases a <;> rfl

/-- Belnap conjunction is commutative. -/
theorem meetBelnap_comm (a b : Trivalent) : meetBelnap a b = meetBelnap b a := by
  cases a <;> cases b <;> rfl

/-- `indet` is a left identity for Belnap disjunction. -/
theorem joinBelnap_indet_left (a : Trivalent) : joinBelnap .indet a = a := rfl

/-- `indet` is a right identity for Belnap disjunction. -/
theorem joinBelnap_indet_right (a : Trivalent) : joinBelnap a .indet = a := by
  cases a <;> rfl

/-- Belnap disjunction is commutative. -/
theorem joinBelnap_comm (a b : Trivalent) : joinBelnap a b = joinBelnap b a := by
  cases a <;> cases b <;> rfl

/-- Belnap conjunction agrees with Bool on defined inputs. -/
theorem meetBelnap_ofBool (a b : Bool) :
    meetBelnap (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Belnap disjunction agrees with Bool on defined inputs. -/
theorem joinBelnap_ofBool (a b : Bool) :
    joinBelnap (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-! ### Supervaluation

The value of a predicate over a finite family of classical valuations. The empty family is
vacuously both all-true and all-false, and `supervaluation` resolves it to `.true`. -/

section Supervaluation

variable {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]

/-- The supervaluation of `P` over the family `s` ([van-fraassen-1966]) is `.true` when `P`
holds at every member, `.false` when it fails at every member of a nonempty `s`, and
`.indet` otherwise. -/
def supervaluation : Trivalent :=
  if ∀ a ∈ s, P a then .true else if ∃ a ∈ s, P a then .indet else .false

theorem supervaluation_eq_true_iff : supervaluation s P = .true ↔ ∀ a ∈ s, P a := by
  unfold supervaluation
  split_ifs with h
  · exact iff_of_true rfl h
  all_goals exact iff_of_false (by decide) h

theorem supervaluation_eq_false_iff :
    supervaluation s P = .false ↔ s.Nonempty ∧ ∀ a ∈ s, ¬ P a := by
  unfold supervaluation
  split_ifs with h₁ h₂
  · simp only [false_iff, not_and, not_forall, not_not]
    exact fun ⟨a, ha⟩ ↦ ⟨a, ha, h₁ a ha⟩
  · simp only [false_iff, not_and, not_forall, not_not]
    exact fun _ ↦ let ⟨a, ha, hp⟩ := h₂; ⟨a, ha, hp⟩
  · push Not at h₁ h₂
    obtain ⟨a, ha, -⟩ := h₁
    exact iff_of_true rfl ⟨⟨a, ha⟩, h₂⟩

theorem supervaluation_eq_indet_iff :
    supervaluation s P = .indet ↔ (∃ a ∈ s, P a) ∧ ∃ a ∈ s, ¬ P a := by
  unfold supervaluation; split_ifs <;> simp_all

@[simp] theorem supervaluation_empty : supervaluation ∅ P = .true := by simp [supervaluation]

/-- Over a single valuation the supervaluation is classical truth. -/
@[simp] theorem supervaluation_singleton (a : α) : supervaluation {a} P = ofProp (P a) := by
  by_cases h : P a <;> simp [supervaluation, ofProp, ofBool, h]

variable {s P} in
/-- The supervaluation depends only on the predicate's values on the family. -/
theorem supervaluation_congr {Q : α → Prop} [DecidablePred Q] (h : ∀ a ∈ s, P a ↔ Q a) :
    supervaluation s P = supervaluation s Q := by
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · simp only [supervaluation_eq_indet_iff]
    exact and_congr (exists_congr fun a ↦ and_congr_right (h a))
      (exists_congr fun a ↦ and_congr_right fun ha ↦ not_congr (h a ha))
  · simp only [supervaluation_eq_true_iff]
    exact forall₂_congr h

/-- Supervaluating over the image of a family is supervaluating the composite over the family. -/
theorem supervaluation_image {β : Type*} [DecidableEq β] (f : α → β) (Q : β → Prop)
    [DecidablePred Q] : supervaluation (s.image f) Q = supervaluation s (Q ∘ f) := by
  refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [supervaluation_eq_indet_iff, supervaluation_eq_true_iff]

variable {s} in
/-- Over a nonempty family a constant predicate supervaluates to its classical value. -/
theorem supervaluation_const (hs : s.Nonempty) (q : Prop) [Decidable q] :
    supervaluation s (fun _ ↦ q) = ofProp q := by
  by_cases h : q <;> simp [supervaluation, h]
  exact hs

/-- Removing the gap leaves classical universal truth. -/
@[simp] theorem metaAssert_supervaluation :
    (supervaluation s P).metaAssert = ofProp (∀ a ∈ s, P a) := by
  unfold supervaluation ofProp
  split_ifs with h
  · rw [decide_eq_true h]; rfl
  all_goals rw [decide_eq_false h]; rfl

variable {s} in
/-- Over a nonempty family, negating the predicate negates the supervaluation, swapping truth
and falsity and fixing the gap. -/
theorem supervaluation_not (hs : s.Nonempty) :
    supervaluation s (¬ P ·) = (supervaluation s P).neg := by
  cases h : supervaluation s P
  · exact (supervaluation_eq_false_iff ..).2
      ⟨hs, fun a ha hn ↦ hn ((supervaluation_eq_true_iff ..).1 h a ha)⟩
  · exact (supervaluation_eq_true_iff ..).2 ((supervaluation_eq_false_iff ..).1 h).2
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_indet_iff ..).1 h
    exact (supervaluation_eq_indet_iff ..).2 ⟨⟨b, hb, hn⟩, a, ha, not_not.2 hp⟩

end Supervaluation

end Trivalent
