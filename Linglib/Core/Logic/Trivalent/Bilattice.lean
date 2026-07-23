/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.Trivalent.Basic
import Linglib.Core.Order.Flat

/-!
# The knowledge order: `Flat Bool` and the Kleene bilattice


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

namespace Trivalent

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
  right_inv x := by cases x with | bot => rfl | coe b => cases b <;> rfl

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

end Trivalent
