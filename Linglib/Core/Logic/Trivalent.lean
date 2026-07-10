/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.MinMax
import Mathlib.Data.Sign.Defs
import Linglib.Core.Order.DeMorganAlgebra
import Linglib.Core.Order.Flat

/-!
# Three-valued truth

`Trivalent` is the three-element bounded chain `false < indet < true`: the value space of
strong Kleene logic ([kleene-1952]), the bilattice literature's THREE ([fitting-1994]),
and the consistent fragment of Belnap's FOUR. Strong Kleene conjunction and disjunction
are the chain's `⊓`/`⊔`; the carrier is logic-neutral, hosting the rival trivalent
connective families — Weak Kleene ([bochvar-1937]), Middle Kleene ([peters-1979]), Belnap
conditional assertion ([belnap-1970]) — and the partiality operators ∂ and 𝒜 of
[beaver-krahmer-2001].

The upstreamable algebra is the `KleeneLattice` class (`Core/Order/DeMorganAlgebra.lean`),
of which `Trivalent` is the canonical non-Boolean instance. The dedicated carrier with
truth-named constructors is this library's ergonomic choice; the name follows the
`Boolean` precedent — an adjective nominalized as its truth-value type — with the
`Trivalent` namespace hosting the whole trivalent development (this file's algebra,
`Core/ModelTheory/Trivalent.lean`'s formulas).

## Main definitions

- `Trivalent` — three-valued truth (`.true`, `.false`, `.indet`), a `LinearOrder` and
  `BoundedOrder`; `Prop3 W` — trivalent propositions `W → Trivalent`.
- `Trivalent.neg` — Strong Kleene negation: involutive (`neg_neg`), antitone
  (`neg_antitone`), De Morgan (`neg_inf`/`neg_sup`), satisfying the Kleene law
  (`inf_neg_le_sup_neg`) — so `Trivalent` is a `KleeneLattice`, the canonical non-Boolean
  instance (`inf_compl_indet_ne_bot`).
- `Trivalent.meetWeak`/`joinWeak`, `meetMiddle`/`joinMiddle`, `meetBelnap`/`joinBelnap`,
  `xor` — the rival connective families.
- `Trivalent.presuppose`, `Trivalent.metaAssert` — the ∂ and 𝒜 operators of
  [beaver-krahmer-2001].
- `Trivalent.ofBool`, `Trivalent.ofBoolHom` — `Bool` embeds as a bounded lattice homomorphism.

## Main results

- `Trivalent.orderIsoSignType` — the truth order's mathlib carrier is `SignType`
  (`-1 < 0 < 1`), the iso commuting with negation; `Trivalent.equivFlatBool` — the same
  carrier under the *knowledge* order is `Flat Bool`. Together: the Kleene bilattice.
- `Trivalent.toFlat_inf_mono_left` etc. — Strong Kleene `⊓`/`⊔` are interlaced
  (knowledge-monotone); Weak Kleene is not (`Trivalent.meetWeak_not_truthMono`).

## References

[kleene-1952] [bochvar-1937] [belnap-1970] [peters-1979] [beaver-krahmer-2001]
[cobreros-etal-2012] [wang-davidson-2026]
-/

/-- Three-valued truth: the 3-element bounded chain `false < indet < true`.
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

/-- The less-than-or-equal relation on truth values: `false < indet < true`. -/
protected inductive LE : Trivalent → Trivalent → Prop
  | of_false (a) : Trivalent.LE .false a
  | indet : Trivalent.LE .indet .indet
  | of_true (a) : Trivalent.LE a .true

instance : LE Trivalent := ⟨Trivalent.LE⟩

instance instDecidableLE : DecidableLE Trivalent := λ a b => by
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

/-- Strong Kleene negation: the order-reversing involution swapping `false` and
`true`, fixing `indet`. -/
def neg : Trivalent → Trivalent
  | .true  => .false
  | .indet => .indet
  | .false => .true

@[simp] theorem neg_neg (a : Trivalent) : neg (neg a) = a := by cases a <;> rfl

@[simp] theorem neg_indet : neg .indet = .indet := rfl

theorem neg_involutive : Function.Involutive (neg : Trivalent → Trivalent) := neg_neg

/-- Strong Kleene negation is antitone (order-reversing). -/
theorem neg_antitone : Antitone neg := λ a b h => by
  revert h; cases a <;> cases b <;> decide

/-- De Morgan: negation swaps meet and join — from antitonicity alone. -/
@[simp] theorem neg_inf (a b : Trivalent) : neg (a ⊓ b) = neg a ⊔ neg b :=
  neg_antitone.map_min

/-- De Morgan: negation swaps join and meet. -/
@[simp] theorem neg_sup (a b : Trivalent) : neg (a ⊔ b) = neg a ⊓ neg b :=
  neg_antitone.map_max

/-- The Kleene law `a ⊓ ¬a ≤ b ⊔ ¬b`. -/
theorem inf_neg_le_sup_neg (a b : Trivalent) : a ⊓ neg a ≤ b ⊔ neg b := by
  cases a <;> cases b <;> decide

instance : Compl Trivalent := ⟨neg⟩

/-- `Trivalent` is the canonical non-Boolean `KleeneLattice`: a distributive chain with
`neg` as the involutive antitone complement, failing complementation
(`inf_compl_indet_ne_bot`). The `ᶜ` instance gives access to the class API
(`Core/Order/DeMorganAlgebra.lean`); `neg` remains the simp-normal form. -/
instance : KleeneLattice Trivalent where
  __ := (inferInstance : DistribLattice Trivalent)
  __ := (inferInstance : BoundedOrder Trivalent)
  compl := neg
  compl_compl := neg_neg
  compl_antitone := λ h => neg_antitone h
  inf_compl_le_sup_compl := inf_neg_le_sup_neg

/-- `Trivalent` is not complemented — `indet` witnesses the gap between Kleene and Boolean
(so `Trivalent` is no `OrthocomplementedLattice` either). -/
theorem inf_compl_indet_ne_bot : Trivalent.indet ⊓ Trivalent.indetᶜ ≠ ⊥ := by decide

/-! ### Constructor-literal simp lemmas

Inherited from `BoundedOrder` + `Lattice` + `LinearOrder`, restated with the
constructor literals (`⊤ = .true`, `⊥ = .false`) that goals actually mention. -/

@[simp] theorem sup_true (a : Trivalent) : a ⊔ .true = .true := sup_top_eq a
@[simp] theorem true_sup (a : Trivalent) : Trivalent.true ⊔ a = .true := top_sup_eq a
@[simp] theorem inf_false (a : Trivalent) : a ⊓ .false = .false := inf_bot_eq a
@[simp] theorem false_inf (a : Trivalent) : Trivalent.false ⊓ a = .false := bot_inf_eq a

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

/-- K3/LP duality via negation: negation swaps the standards (the antitone involution
`neg` fixes `indet`, exchanging the two principal filters' complements). -/
theorem designated_neg_iff (d : Designation) (v : Trivalent) :
    designated d.dual (neg v) ↔ ¬ designated d v := by
  cases d <;> cases v <;> decide

/-- Designation distributes over `⊓`: the designated set is a filter (`le_inf_iff`). -/
theorem designated_inf (d : Designation) (v w : Trivalent) :
    designated d (v ⊓ w) ↔ designated d v ∧ designated d w := le_inf_iff

/-- Designation distributes over `⊔`: thresholds are prime on a chain (`le_sup_iff`). -/
theorem designated_sup (d : Designation) (v w : Trivalent) :
    designated d (v ⊔ w) ↔ designated d v ∨ designated d w := le_sup_iff

/-- K3 is the stronger standard: its threshold dominates LP's. -/
theorem designated_lp_of_k3 {v : Trivalent} (h : designated .k3 v) : designated .lp v :=
  le_trans (by decide) h

/-! ### Conversion from Bool -/

/-- The two-valued fragment: `Bool.true ↦ .true`, `Bool.false ↦ .false`. -/
def ofBool : Bool → Trivalent
  | Bool.true => .true
  | Bool.false => .false

instance : Coe Bool Trivalent := ⟨ofBool⟩

/-- A value is defined when it is not `indet`. -/
def isDefined : Trivalent → Prop
  | .true => True
  | .false => True
  | .indet => False

instance : DecidablePred isDefined := λ v => by
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

/-- Strong Kleene exclusive disjunction: true when exactly one operand is true,
undefined when either operand is. Unlike `⊔`, XOR cannot "see past" an undefined
operand — `.true ⊔ .indet = .true`, but `xor .true .indet = .indet`
([wang-davidson-2026], Figure 2). -/
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

/-- The truth-order carrier iso: `false ↔ -1`, `indet ↔ 0`, `true ↔ 1`, with Kleene
negation corresponding to `SignType` negation (`orderIsoSignType_neg`). The
knowledge-order counterpart is `equivFlatBool`. -/
def orderIsoSignType : Trivalent ≃o SignType where
  toFun := λ | .false => .neg | .indet => .zero | .true => .pos
  invFun := λ | .neg => .false | .zero => .indet | .pos => .true
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

/-- Weak Kleene disjunction: indet is absorbing (both operands must be defined). -/
def joinWeak : Trivalent → Trivalent → Trivalent
  | .true, .true => .true
  | .true, .false => .true
  | .false, .true => .true
  | .false, .false => .false
  | _, _ => .indet

/-- Weak Kleene conjunction: indet is absorbing. -/
def meetWeak : Trivalent → Trivalent → Trivalent
  | .true, .true => .true
  | .true, .false => .false
  | .false, .true => .false
  | .false, .false => .false
  | _, _ => .indet

theorem joinWeak_comm (a b : Trivalent) : joinWeak a b = joinWeak b a := by
  cases a <;> cases b <;> rfl

theorem meetWeak_comm (a b : Trivalent) : meetWeak a b = meetWeak b a := by
  cases a <;> cases b <;> rfl

/-- Meta-assertion: the 𝒜 (assertion) operator of [beaver-krahmer-2001] §2, closing
a trivalent value to bivalent by treating undefinedness as falsity. -/
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

/-- Presupposition: the ∂ operator of [beaver-krahmer-2001] §2, the companion of
`metaAssert` — asserts a true value, undefined otherwise (`T ↦ T`, `F ↦ #`, `# ↦ #`). -/
def presuppose : Trivalent → Trivalent
  | .true => .true
  | _ => .indet

@[simp] theorem presuppose_true : presuppose .true = .true := rfl
@[simp] theorem presuppose_false : presuppose .false = .indet := rfl
@[simp] theorem presuppose_indet : presuppose .indet = .indet := rfl

/-- Meta-asserting a presupposed value falsifies undefinedness: `𝒜 ∘ ∂` sends
exactly `.true` to `.true`. -/
theorem metaAssert_presuppose (v : Trivalent) :
    metaAssert (presuppose v) = if v = .true then .true else .false := by
  cases v <;> rfl

/-! ### Middle Kleene

The asymmetric left-to-right connectives of [peters-1979], the trivalent face of
Karttunen filtering ([beaver-krahmer-2001], [spector-2025]): an undefined first
operand absorbs; a defined one proceeds by Strong Kleene. -/

/-- Middle Kleene conjunction: left-undefined absorbs, left-defined proceeds by
Strong Kleene. Asymmetric — `meetMiddle .false .indet = .false` but
`meetMiddle .indet .false = .indet` ([peters-1979]). -/
def meetMiddle : Trivalent → Trivalent → Trivalent
  | .indet, _ => .indet
  | a, b => a ⊓ b

/-- Middle Kleene disjunction: left-undefined absorbs, left-defined proceeds by
Strong Kleene — a defined first disjunct can settle the result even when the second
is undefined, the left-to-right filtering pattern ([peters-1979]). -/
def joinMiddle : Trivalent → Trivalent → Trivalent
  | .indet, _ => .indet
  | a, b => a ⊔ b

/-- Middle Kleene conjunction is not commutative. -/
theorem meetMiddle_not_comm : ¬ ∀ a b : Trivalent, meetMiddle a b = meetMiddle b a :=
  λ h => absurd (h .false .indet) (by decide)

/-- Middle Kleene disjunction is not commutative. -/
theorem joinMiddle_not_comm : ¬ ∀ a b : Trivalent, joinMiddle a b = joinMiddle b a :=
  λ h => absurd (h .true .indet) (by decide)

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

/-- Belnap conjunction: undefined operands are skipped; `indet` is the identity
([belnap-1970], (8)). -/
def meetBelnap : Trivalent → Trivalent → Trivalent
  | .indet, b => b
  | a, .indet => a
  | a, b => a ⊓ b

/-- Belnap disjunction: undefined operands are skipped; `indet` is the identity
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

/-! ### The knowledge order: `Flat Bool` and the Kleene bilattice

`Trivalent`'s native order is the *truth* order `false < indet < true`; `Flat Bool`
(`equivFlatBool`) carries the *knowledge* order `⊥ ⊑ true`, `⊥ ⊑ false`. Two orders
on one carrier is a *bilattice*. Strong Kleene `∧`/`∨` are the truth-order lattice
operations `⊓`/`⊔`; what makes them canonical is **interlacing** — they are monotone
for the knowledge order as well ([kleene-1952]'s regularity condition), while Weak
Kleene is not (`meetWeak_not_truthMono`).

`Flat Bool`'s `SemilatticeInf` meet `⊓` is the *consensus* `⊗`; its partial join
(`PartialUnify`) is the *gullibility* `⊕`, partial because three values lack the `⊤`
("both") of a full four-valued bilattice — so `Trivalent` is the *consistent fragment*
of that bilattice. -/

section KnowledgeOrder

/-- The carrier bijection `Trivalent ≃ Flat Bool`: `indet ↔ ⊥`, `true ↔ some true`,
`false ↔ some false`. `Flat Bool` carries the knowledge order, distinct from the
truth order — the two orders of the Kleene bilattice. -/
def toFlat : Trivalent → Flat Bool
  | .indet => none
  | .true => some Bool.true
  | .false => some Bool.false

/-- Inverse of `toFlat`. -/
def ofFlat : Flat Bool → Trivalent
  | none => .indet
  | some Bool.true => .true
  | some Bool.false => .false

/-- `Trivalent` and the flat domain `Flat Bool` share a carrier. -/
def equivFlatBool : Trivalent ≃ Flat Bool where
  toFun := toFlat
  invFun := ofFlat
  left_inv a := by cases a <;> rfl
  right_inv x := by cases x with | none => rfl | some b => cases b <;> rfl

/-- The truth order and the knowledge order genuinely differ: in the truth order
`false ≤ indet`, but in the knowledge order the committed value `false` is not below
the uncommitted `indet = ⊥`. -/
theorem truthOrder_ne_knowledgeOrder :
    Trivalent.false ≤ Trivalent.indet ∧ ¬ toFlat .false ≤ toFlat .indet := by decide

/-- Strong Kleene negation is regular (knowledge-monotone); being unary, it is in
fact the unique monotone extension of Boolean `not`. -/
theorem toFlat_neg_mono {a b : Trivalent} (h : toFlat a ≤ toFlat b) :
    toFlat (neg a) ≤ toFlat (neg b) := by
  cases a <;> cases b <;> revert h <;> decide

/-- Strong Kleene conjunction is regular (knowledge-monotone in each argument). -/
theorem toFlat_inf_mono_left {a a' : Trivalent} (b : Trivalent)
    (h : toFlat a ≤ toFlat a') : toFlat (a ⊓ b) ≤ toFlat (a' ⊓ b) := by
  cases a <;> cases a' <;> cases b <;> revert h <;> decide

/-- Strong Kleene disjunction is regular (knowledge-monotone in each argument). -/
theorem toFlat_sup_mono_left {a a' : Trivalent} (b : Trivalent)
    (h : toFlat a ≤ toFlat a') : toFlat (a ⊔ b) ≤ toFlat (a' ⊔ b) := by
  cases a <;> cases a' <;> cases b <;> revert h <;> decide

/-- Weak Kleene conjunction is not interlaced — it fails truth-order monotonicity
(`indet ≤ true`, yet `meetWeak .indet .false = .indet ≰ .false`), so unlike Strong
Kleene `⊓` it is not a bilattice operation. -/
theorem meetWeak_not_truthMono :
    ¬ ∀ a a' b : Trivalent, a ≤ a' → meetWeak a b ≤ meetWeak a' b :=
  λ h => absurd (h .indet .true .false (by decide)) (by decide)

/-- Weak Kleene disjunction is likewise not interlaced. -/
theorem joinWeak_not_truthMono :
    ¬ ∀ a a' b : Trivalent, a ≤ a' → joinWeak a b ≤ joinWeak a' b :=
  λ h => absurd (h .false .indet .true (by decide)) (by decide)

end KnowledgeOrder

/-! ### Trivalent propositions -/

/-- How truth values aggregate through an operator: conjunctive (universal-like, all
must succeed) or disjunctive (existential-like, one must succeed). -/
inductive ProjectionType where
  | conjunctive
  | disjunctive
  deriving Repr, DecidableEq

/-- Three-valued propositions: functions from worlds to `Trivalent`. -/
abbrev Prop3 (W : Type*) := W → Trivalent

namespace Prop3

variable {W : Type*}

/-! `Prop3 W := W → Trivalent` is a `Pi` type: `Lattice (W → Trivalent)` auto-derives from
`Pi.instLattice`, so `(p ⊔ q) w = p w ⊔ q w` and `(p ⊓ q) w = p w ⊓ q w` come for
free from `Pi.sup_apply`/`Pi.inf_apply` — use `⊔`/`⊓` directly rather than bespoke
wrappers. The only Trivalent-specific operation needing a pointwise lift is
`metaAssert`: there is no `Pi` analogue of a unary collapsing operator. -/

/-- Pointwise meta-assertion (Beaver-Krahmer 𝒜 operator). -/
def metaAssert (p : Prop3 W) : Prop3 W := λ w => Trivalent.metaAssert (p w)

@[simp] theorem metaAssert_apply (p : Prop3 W) (w : W) :
    Prop3.metaAssert p w = Trivalent.metaAssert (p w) := rfl

end Prop3

end Trivalent
