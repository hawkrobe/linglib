import Mathlib.Logic.Function.Basic

/-!
# Bilateral logic — paraconsistent polarity-flip substrate

@cite{anttila-2021} @cite{aloni-2022} @cite{groenendijk-roelofsen-2009}

A **bilateral logic** equips a formula language with two parallel
interpretations (`positive`/`negative`, also called `support`/`antiSupport`,
`assert`/`reject`, `verify`/`falsify`, ...) related by a negation
constructor that swaps them.

## The paraconsistent shape

This file's `IsBilateral` captures the **paraconsistent** form: negation
swaps `positive` and `negative` *as values*, with no commitment to
`negative φ = ¬positive φ`. Examples:

- BSML / QBSML: `positive := support`, `negative := antiSupport`. Both
  produce `Finset α → Prop`. Negation swaps; they are NOT propositional
  negations of each other (a state can fail to support φ without
  antisupporting it).
- BUS / ICDRT-bilateral: `positive`/`negative` are state-update functions
  `State → State`. Negation is bundled-record swap.
- Fine-style truthmaker semantics (`BilProp`): `verifier`/`falsifier` are
  predicates over a state space; negation swaps them.

Distinct from the **classical** bilateral pattern (`SatDuality`, in
`Bilateral/Classical.lean`), where negation IS propositional negation
modulo mode duality: `sat (neg φ) ↔ ¬sat (dual m) φ`. TCS, LP, RM3
satisfy that stronger axiom; BSML and friends do not.

## Why a `Prop`-bundle, not a typeclass

Three free type parameters (`Form`, `Result`, plus `positive`/`negative`/
`negate` as fields) make typeclass elaboration infeasible — the previous
`Bilateral.lean` (deleted in 0.230.649) tried this and failed. A
`Prop`-bundle of axioms parameterised over the data is the working
mathlib pattern (compare `IsLowerSet`, `SatDuality`, `IsLub`).

Consumers provide their `positive`, `negative`, `negate` as ordinary
definitions, then prove `IsBilateral` separately. Derived theorems
(`Bilateral/Polarity.lean`) take the `IsBilateral` proof as a hypothesis.

## Anti-pattern this avoids

A `BilateralLogic` bundled record (data + axioms together) would lose
ergonomics for consumers like BSML, where `support` and `antiSupport`
are already top-level definitions used pervasively. Wrapping them in a
record would force every call site to project. The unbundled-axioms
form lets consumers continue to use their existing names.
-/

namespace Core.Logic.Bilateral

universe u v

variable {Form : Type u} {Result : Type v}

-- ============================================================================
-- §1 The paraconsistent bilateral predicate
-- ============================================================================

/-- A **bilateral structure** on (`Form`, `Result`): two interpretations
    `positive, negative : Form → Result` and a negation constructor
    `negate : Form → Form`, with the swap axioms.

    Captures the paraconsistent pattern shared by BSML, QBSML, BUS,
    ICDRT, and Fine-style truthmaker semantics. The classical pattern
    (negation negates the proposition modulo mode duality) is captured
    by `Core.Logic.Bilateral.Classical.SatDuality`. -/
structure IsBilateral
    (positive negative : Form → Result) (negate : Form → Form) : Prop where
  /-- Negation flips `positive` to `negative`. -/
  positive_negate : ∀ φ : Form, positive (negate φ) = negative φ
  /-- Negation flips `negative` to `positive`. -/
  negative_negate : ∀ φ : Form, negative (negate φ) = positive φ

-- ============================================================================
-- §2 The negation involution
-- ============================================================================

/-- **Negation is involutive on the underlying interpretations**: applying
    `negate` twice restores both `positive` and `negative` to their
    original values. This does NOT imply `negate (negate φ) = φ`
    syntactically; it implies the *interpretations agree*. Consumers
    where `negate (negate φ) = φ` syntactically (e.g., BSML's
    `BSMLFormula.neg`) can derive the syntactic involution separately. -/
theorem IsBilateral.positive_negate_negate
    {positive negative : Form → Result} {negate : Form → Form}
    (h : IsBilateral positive negative negate) (φ : Form) :
    positive (negate (negate φ)) = positive φ := by
  rw [h.positive_negate, h.negative_negate]

theorem IsBilateral.negative_negate_negate
    {positive negative : Form → Result} {negate : Form → Form}
    (h : IsBilateral positive negative negate) (φ : Form) :
    negative (negate (negate φ)) = negative φ := by
  rw [h.negative_negate, h.positive_negate]

end Core.Logic.Bilateral
