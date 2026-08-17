/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.AntiAdditive
import Linglib.Logic.Natural.Basic

/-!
# The Zwarts strength hierarchies
[zwarts-1998] [icard-2012] [ladusaw-1980]

The polarity-facing quotient of the natural-logic signature system: the
DE hierarchy `weak < antiAdditive < antiMorphic` and its UE dual as
linear orders, the bridge maps reading strength off an
`Signature`'s projection behavior, and `DEStrength.HoldsFor`, the
semantic content of each level (weak = `Antitone`, antiAdditive =
`IsAntiAdditive`, antiMorphic = `IsAntiMorphic`), downward closed along
the chain (`HoldsFor.of_le`).

## Main declarations

* `DEStrength`, `UEStrength` — the Zwarts hierarchies.
* `DEStrength.HoldsFor` — the semantic content of a strength level.
* `Signature.toDEStrength`, `Signature.toUEStrength` — the
  signature → strength bridge maps.
* `NaturalLogic.de_signature_licenses_weak_npi`,
  `NaturalLogic.strong_npi_requires_antiadditive` — the Ladusaw/Zwarts
  licensing connections.
-/

namespace Polarity



/-! ### The hierarchies -/

/-- The three levels of the DE hierarchy ([zwarts-1998]): `weak` is
    plain DE (licenses weak NPIs: *ever*, *any*), `antiAdditive` adds
    ∨→∧ distributivity (licenses strong NPIs: *lift a finger*), and
    `antiMorphic` adds ∧→∨ distributivity (= negation). -/
inductive DEStrength where
  | weak
  | antiAdditive
  | antiMorphic
  deriving DecidableEq, Repr

/-- Rank in the Zwarts chain `weak < antiAdditive < antiMorphic`. -/
def DEStrength.toNat : DEStrength → Nat
  | .weak => 0
  | .antiAdditive => 1
  | .antiMorphic => 2

theorem DEStrength.toNat_injective : Function.Injective DEStrength.toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [DEStrength.toNat]

/-- The Zwarts DE hierarchy as the linear order
    `weak < antiAdditive < antiMorphic` — the carrier of the canonical
    `zwartsScale` (`Semantics/Polarity/Licensing.lean`); other theories
    of NPI strength supply other ordered carriers. -/
instance : LinearOrder DEStrength :=
  LinearOrder.lift' DEStrength.toNat DEStrength.toNat_injective

/-- The three levels of the UE hierarchy (dual of `DEStrength`): `weak`
    is plain UE (monotone), `multiplicative` adds ∧-distributivity,
    `additive` ∨-distributivity (strongest). -/
inductive UEStrength where
  | weak
  | multiplicative
  | additive
  deriving DecidableEq, Repr

/-! ### The Zwarts hierarchy semantically -/

/-- The semantic content of a `DEStrength` level for a context function
([icard-2012] §4, after Zwarts): `weak` is antitonicity, `antiAdditive`
the anti-additivity equation, `antiMorphic` the full anti-morphism —
*few* is weak-only, *no* anti-additive, *not* anti-morphic. -/
def DEStrength.HoldsFor {α β : Type*} [Lattice α] [Lattice β]
    (s : DEStrength) (f : α → β) : Prop :=
  match s with
  | .weak => Antitone f
  | .antiAdditive => IsAntiAdditive f
  | .antiMorphic => IsAntiMorphic f

/-- Strength facts are downward closed along the Zwarts chain
`weak < antiAdditive < antiMorphic`: a function holding a level holds
every weaker one. -/
theorem DEStrength.HoldsFor.of_le {α β : Type*}
    [Lattice α] [Lattice β] {f : α → β} {s₁ s₂ : DEStrength}
    (h : s₁ ≤ s₂) (hf : s₂.HoldsFor f) : s₁.HoldsFor f := by
  cases s₁ <;> cases s₂ <;>
    first
      | exact hf
      | exact hf.antitone
      | exact hf.antiAdditive
      | exact absurd h (by decide)

example : DEStrength.antiMorphic.HoldsFor (compl : Set Bool → Set Bool) :=
  isAntiMorphic_compl
example : DEStrength.weak.HoldsFor (compl : Set Bool → Set Bool) :=
  DEStrength.HoldsFor.of_le (s₂ := .antiMorphic) (by decide)
    isAntiMorphic_compl

end Polarity

/-! ### Signature → strength bridge maps -/

namespace NaturalLogic.Signature

open Polarity

/-- The DE strength a signature realizes, derived from `project`: a
    signature is DE iff it reverses forward entailment; within the DE
    side, anti-additivity is detected by the ∨→∧ swap on `cover` and
    anti-morphism additionally by the ∧→∨ swap on `alternation`.
    `none` for UE-side signatures. -/
def toDEStrength (φ : Signature) : Option DEStrength :=
  if project .forward φ != .reverse then none
  else if project .cover φ == .alternation then
    if project .alternation φ == .cover then some .antiMorphic
    else some .antiAdditive
  else some .weak

/-- The UE strength a signature realizes, derived from `project`: a
    signature is UE iff it preserves forward entailment; additivity is
    ∨-preservation on `cover`, multiplicativity ∧-preservation on
    `alternation`. `none` for DE-side signatures. -/
def toUEStrength (φ : Signature) : Option UEStrength :=
  if project .forward φ != .forward then none
  else if project .cover φ == .cover then some .additive
  else if project .alternation φ == .alternation then some .multiplicative
  else some .weak

-- Exhaustive verification against the strength-relevant signatures.
example : toDEStrength .anti = some .weak := rfl
example : toDEStrength .antiAdd = some .antiAdditive := rfl
example : toDEStrength .antiMult = some .weak := rfl
example : toDEStrength .antiAddMult = some .antiMorphic := rfl
example : toDEStrength .mono = none := rfl
example : toUEStrength .mono = some .weak := rfl
example : toUEStrength .addMult = some .additive := rfl
example : toUEStrength .anti = none := rfl

end NaturalLogic.Signature

namespace NaturalLogic

open Polarity

/-- Any DE-side signature licenses weak NPIs ([ladusaw-1980]): a
    signature whose context polarity is downward carries a DE
    strength. -/
theorem de_signature_licenses_weak_npi (σ : Signature) :
    Signature.toContextPolarity σ = .downward →
    (Signature.toDEStrength σ).isSome = true := by
  cases σ <;> decide

/-- Anti-additive or stronger signatures sit on the DE side: the strong
    NPI licensors (antiAdd, antiAddMult) are downward contexts — but
    plain anti and antiMult only reach `weak`. -/
theorem strong_npi_requires_antiadditive (σ : Signature) :
    Signature.toDEStrength σ = some DEStrength.antiAdditive ∨
    Signature.toDEStrength σ = some DEStrength.antiMorphic →
    Signature.toContextPolarity σ = ContextPolarity.downward := by
  cases σ <;> decide

example : Signature.toDEStrength .antiMult = some .weak := rfl
example : Signature.toDEStrength negationSignature =
    some DEStrength.antiMorphic := rfl

end NaturalLogic
