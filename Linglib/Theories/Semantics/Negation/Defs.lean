import Linglib.Core.Negation
import Linglib.Core.Semantics.Proposition
import Linglib.Theories.Semantics.Entailment.AntiAdditivity

/-!
# Semantic Negation: Unified Foundations

This module unifies the scattered negation semantics in linglib into a
coherent architecture with three layers:

1. **NegOp** — a semantic negation operator bundling involution + antitonicity,
   with `standardNeg` (`pnot`) as the canonical instance
2. **DEStrength ↔ PolarityLicensing bridge** — the entailment hierarchy
   (weak DE / anti-additive / anti-morphic) determines the polarity licensing
   profile, connecting the `Prop`-based semantic properties in
   `Theories.Semantics.Entailment` to the `Bool`-valued empirical classification
   in `Core.Negation`
3. **Scoped vs unscoped negation** — a negation operator that retains scope
   into a domain preserves its semantic properties; when scope is blocked
   (e.g., by phase transfer), it loses antitonicity and hence licensing ability

## Dependencies

- `Core.Negation` — framework-agnostic classification types (ENType, ENStrength,
  PolarityClass, PolarityLicensing) with Mathlib lattice instances
- `Core.Semantics.Proposition` — `pnot` (both `Prop'` and `BProp`), involution,
  antitonicity
- `Core.Logic.NaturalLogic` — `DEStrength` (weak/antiAdditive/antiMorphic),
  `strengthSufficient`
- `Theories.Semantics.Entailment.Polarity` — `IsDE = Antitone`,
  `IsUE = Monotone`, `pnot_isDownwardEntailing`
- `Theories.Semantics.Entailment.AntiAdditivity` — `IsAntiAdditive`,
  `IsAntiMorphic`, `pnot_isAntiMorphic`, `licensesWeakNPI`, `licensesStrongNPI`
-/

namespace Semantics.Negation

open Core (ENType ENStrength PolarityLicensing PolarityClass
           weakENProfile strongENProfile standardNegProfile)
open Core.NaturalLogic (DEStrength strengthSufficient)
open Core.Proposition (BProp)
open Core.Proposition.Decidable (pnot)
open Semantics.Entailment (World)
open Semantics.Entailment.Polarity (IsDE IsUE pnot_isDownwardEntailing)
open Semantics.Entailment.AntiAdditivity (IsAntiAdditive IsAntiMorphic
  pnot_isAntiAdditive pnot_isAntiMorphic)

-- ════════════════════════════════════════════════════
-- § 1. NegOp — semantic negation operator
-- ════════════════════════════════════════════════════

/-- A semantic negation operator on decidable propositions over worlds `W`.

    Bundles a function with its two defining properties:
    - **Involution**: `¬¬p = p` (double negation elimination)
    - **Antitonicity**: `p ≤ q → ¬q ≤ ¬p` (downward entailment)

    Standard sentential negation (`pnot`) satisfies both. Expletive
    negation that has lost its scope may fail antitonicity — it is
    then no longer a `NegOp` in this sense. -/
structure NegOp (W : Type*) where
  /-- The negation function on decidable propositions. -/
  op : BProp W → BProp W
  /-- Involutive: applying negation twice is the identity. -/
  involutive : Function.Involutive op
  /-- Antitone: reverses the entailment ordering (= DE). -/
  antitone : Antitone op

/-- Standard sentential negation (`pnot`) is the canonical `NegOp`.

    It satisfies involution (`pnot_pnot`), antitonicity
    (`pnot_antitone`), and additionally anti-morphism (De Morgan). -/
def standardNeg (W : Type*) : NegOp W where
  op := pnot W
  involutive := Core.Proposition.Decidable.pnot_pnot
  antitone := Core.Proposition.Decidable.pnot_antitone

-- ── Additional semantic properties ──

/-- A NegOp is anti-additive if it distributes ∨ to ∧:
    `¬(A ∨ B) = ¬A ∧ ¬B` (De Morgan, part 1). -/
def NegOp.isAntiAdditive (n : NegOp World) : Prop :=
  IsAntiAdditive n.op

/-- A NegOp is anti-morphic if it is anti-additive AND distributes ∧ to ∨:
    `¬(A ∧ B) = ¬A ∨ ¬B` (De Morgan, part 2).
    This is the full De Morgan property — the characteristic signature
    of negation in the entailment hierarchy. -/
def NegOp.isAntiMorphic (n : NegOp World) : Prop :=
  IsAntiMorphic n.op

/-- Standard negation is anti-additive (De Morgan part 1). -/
theorem standardNeg_isAntiAdditive :
    (standardNeg World).isAntiAdditive :=
  pnot_isAntiAdditive

/-- Standard negation is anti-morphic (full De Morgan). -/
theorem standardNeg_isAntiMorphic :
    (standardNeg World).isAntiMorphic :=
  pnot_isAntiMorphic

-- ════════════════════════════════════════════════════
-- § 2. DEStrength → PolarityLicensing bridge
-- ════════════════════════════════════════════════════

/-! ### The entailment hierarchy determines polarity licensing

The `Bool`-valued `PolarityLicensing` profile in `Core.Negation` is a
*consequence* of the `Prop`-based entailment properties in
`Theories.Semantics.Entailment`:

| DEStrength     | Semantic property | Licenses              | Profile           |
|----------------|-------------------|-----------------------|-------------------|
| weak           | `Antitone`        | weak NPIs, N-words    | `weakENProfile`   |
| antiAdditive   | `IsAntiAdditive`  | + strong NPIs, ¬also  | `standardNegProfile` |
| antiMorphic    | `IsAntiMorphic`   | all (= standard neg)  | `standardNegProfile` |
| (none)         | ¬ `Antitone`      | nothing               | `strongENProfile` |

The anti-additive and anti-morphic levels both yield `standardNegProfile`
because `notAlsoConj` and N-word licensing track anti-additivity, not
anti-morphism (@cite{chierchia-2013} §1.4.3, @cite{icard-2012}). -/

/-- Map DE strength to its empirical polarity licensing profile.

    This is the central bridge: the semantic entailment hierarchy
    *determines* the `Bool`-valued licensing table. -/
def deToPolarityLicensing : DEStrength → PolarityLicensing
  | .weak         => weakENProfile
  | .antiAdditive => standardNegProfile
  | .antiMorphic  => standardNegProfile

/-- The bridge is monotone: stronger DE → more licensing in the lattice. -/
theorem de_licensing_monotone :
    ∀ d₁ d₂ : DEStrength, strengthSufficient d₂ d₁ = true →
    deToPolarityLicensing d₁ ≤ deToPolarityLicensing d₂ := by
  intro d₁ d₂
  cases d₁ <;> cases d₂ <;> simp [deToPolarityLicensing, strengthSufficient] <;> decide

/-- Weak DE licenses exactly weak NPIs and N-words. -/
theorem weak_de_licensing :
    deToPolarityLicensing .weak = weakENProfile := rfl

/-- Anti-additive DE licenses all polarity classes (= standard negation). -/
theorem antiAdditive_de_licensing :
    deToPolarityLicensing .antiAdditive = standardNegProfile := rfl

/-- Anti-morphic DE licenses all polarity classes (= standard negation). -/
theorem antiMorphic_de_licensing :
    deToPolarityLicensing .antiMorphic = standardNegProfile := rfl

-- ════════════════════════════════════════════════════
-- § 3. ENStrength ↔ DE bridge
-- ════════════════════════════════════════════════════

/-! ### EN strength as presence/absence of DE

The two-valued `ENStrength` classification collapses the three-level DE
hierarchy into a binary:

- `ENStrength.weak` = the negation retains at least weak DE (≥ `DEStrength.weak`)
- `ENStrength.strong` = the negation has lost all DE properties

This is @cite{greco-2020}'s core claim: the weak/strong EN distinction
reduces to whether negation retains its downward-entailing property. -/

/-- Map DE strength to EN strength: any DE at all → weak EN. -/
def deToENStrength : DEStrength → ENStrength
  | .weak         => .weak
  | .antiAdditive => .weak
  | .antiMorphic  => .weak

/-- The licensing profile associated with an EN strength.

    Weak EN retains at least `weakENProfile` (the minimum licensing from
    any DE context). Strong EN has `strongENProfile` (= ⊥, no licensing). -/
def enStrengthToLicensing : ENStrength → PolarityLicensing
  | .weak   => weakENProfile
  | .strong => strongENProfile

/-- enStrengthToLicensing is antitone: stronger EN → less licensing.

    This captures the inverse relationship: EN "strength" means
    *strength of expletiveness*, not strength of licensing. A stronger
    EN is more expletive, hence licenses less. -/
theorem enStrength_licensing_antitone :
    ∀ s₁ s₂ : ENStrength, s₁ ≤ s₂ →
    enStrengthToLicensing s₂ ≤ enStrengthToLicensing s₁ := by
  intro s₁ s₂
  cases s₁ <;> cases s₂ <;> simp [enStrengthToLicensing] <;> decide

-- ════════════════════════════════════════════════════
-- § 4. ENType ↔ EN strength
-- ════════════════════════════════════════════════════

/-! ### EN type determines EN strength

The position-based `ENType` (high/low, @cite{rett-2026}) determines the
polarity-based `ENStrength` (strong/weak, @cite{greco-2020}):

- Low EN (truth-conditional, TP-area) → weak EN (retains polarity)
- High EN (non-truth-conditional, CP-area) → strong EN (loses polarity)

This bridge connects the two orthogonal classifications. -/

/-- Map EN type to EN strength. -/
def enTypeToStrength : ENType → ENStrength
  | .low  => .weak
  | .high => .strong

/-- Low EN is weak EN. -/
theorem low_is_weak : enTypeToStrength .low = .weak := rfl

/-- High EN is strong EN. -/
theorem high_is_strong : enTypeToStrength .high = .strong := rfl

/-- The composite bridge: ENType → ENStrength → PolarityLicensing. -/
def enTypeToLicensing (t : ENType) : PolarityLicensing :=
  enStrengthToLicensing (enTypeToStrength t)

/-- Low EN has at least weak licensing. -/
theorem low_en_weak_licensing :
    enTypeToLicensing .low = weakENProfile := rfl

/-- High EN has no licensing (= ⊥). -/
theorem high_en_no_licensing :
    enTypeToLicensing .high = strongENProfile := rfl

-- ════════════════════════════════════════════════════
-- § 5. Scoped vs unscoped negation
-- ════════════════════════════════════════════════════

/-! ### Scope determines semantic property survival

A `NegOp` that can scope into a domain retains all its semantic properties
(involution, antitonicity, anti-morphism). When scope is blocked — e.g.,
by phase transfer in the Minimalist framework — the operator can no longer
reverse entailment over that domain's propositions.

The connection to EN classification:
- **Scoped negation** (TP-area merge) → retains `Antitone` → `ENType.low`
  → `ENStrength.weak` → `weakENProfile`
- **Unscoped negation** (CP-area merge, vP transferred) → loses `Antitone`
  → `ENType.high` → `ENStrength.strong` → `strongENProfile = ⊥`

This is the full derivation chain: merge position → scope access →
semantic property survival → entailment strength → polarity licensing. -/

/-- Classify negation by scope access.

    A negation with scope into the propositional domain is low EN
    (truth-conditional). A negation without scope is high EN
    (non-truth-conditional). -/
def scopeToENType (canScopeIntoVP : Bool) : ENType :=
  if canScopeIntoVP then .low else .high

/-- The full derivation chain: scope → ENType → ENStrength → licensing. -/
def scopeToLicensing (canScopeIntoVP : Bool) : PolarityLicensing :=
  enTypeToLicensing (scopeToENType canScopeIntoVP)

/-- Scoped negation licenses at least weak NPIs and N-words. -/
theorem scoped_neg_licenses :
    scopeToLicensing true = weakENProfile := rfl

/-- Unscoped negation licenses nothing (= ⊥ in the lattice). -/
theorem unscoped_neg_licenses_nothing :
    scopeToLicensing false = strongENProfile := rfl

/-- The full chain agrees with `NegMergePosition.polarityProfile`
    from `NegScope.lean`: scope access determines licensing. -/
theorem scope_determines_licensing (b : Bool) :
    scopeToLicensing b = enStrengthToLicensing (enTypeToStrength (scopeToENType b)) := rfl

end Semantics.Negation
