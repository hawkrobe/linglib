import Linglib.Theories.Syntax.Minimalist.Derivation
import Linglib.Theories.Syntax.Minimalist.Checking
import Linglib.Core.Order.FeaturePreorder

/-!
# Derivational Economy
@cite{chomsky-1991} @cite{chomsky-1995} @cite{boskovic-1997} @cite{collins-2001}
@cite{citko-gracanin-yuksek-2025}

Economy principles constrain syntactic derivations by comparing
competing derivations that converge on the same PF string and LF
interpretation, selecting the one with fewest operations and lexical
resources.

## Provenance

The "Least Effort" view formalized here draws on @cite{chomsky-1991},
@cite{chomsky-1995}, @cite{boskovic-1997}, and @cite{collins-2001}; it is
not exclusively Chomsky 1995. The current loadbearing consumer is
@cite{citko-gracanin-yuksek-2025} on PF reduction, which adopts a
**global, transderivational** flavor of economy (their fn 3) — the
local-economy alternative due to @cite{collins-2001} is not formalized
here.

## Two principles

- **Least Effort**: among derivations yielding the same PF string and LF
  interpretation, prefer the one Pareto-minimal on lexical items / Merge
  ops / Agree ops / E-feature deletions.
- **Pronunciation Economy** (@cite{citko-gracanin-yuksek-2025} p. 27):
  no PF-affecting operation in the derivation is vacuous (does nothing
  to the PF string). Checked **per operation**, not on the whole
  derivation's PF before/after pair — a derivation containing one real
  deletion plus N vacuous ones must still be banned, and a whole-derivation
  ≠ check would let it through.

## Pre-Phase principles deferred

Procrastinate, Last Resort, and Greed are 1995-era principles. Phase
Theory (Chomsky 2000+) effectively replaces Procrastinate with cyclic
Spell-Out at phase edges, and the Move-only-with-trigger discipline is
absorbed into feature-checking by Probe. Earlier revisions of this file
carried Bool-identity wrappers (`def lastResort (b : Bool) : Bool := b`)
and a `Procrastinate`-vs-Economy interaction whose `overtOps` cost field
was never populated by any producer; both were dead code and have been
removed. Future consumers wanting these principles should formalize them
against actual `Step`/`Phase` infrastructure.

## Architectural realization

`DerivationCost` is a 4-Nat record. Its preorder is the pullback through
the 4-vector projection `DerivationCost.profile : DerivationCost →
Fin 4 → Nat`, with `Pi.preorder` giving pointwise ≤ on the feature
space. This realizes the same shape as `Core/Constraint/Pareto.lean`'s
`paretoFeaturePreorder` (used for OT/HG candidate comparison): both
views Pareto-compare a candidate by a vector of Nat-valued counts. The
OT side requires `ConstraintSystem` (with candidate set + decoder); we
don't need either, so we drop straight to `Core.Order.FeaturePreorder`.

The payoff is real: `Core.Order.FeaturePreorder.coarsen_via_monotone`
becomes available for free on `DerivationCost`, so any future
"Minimalist economy implies qualitative coarsening of Pareto frontier"
bridge to OT optimality (per `Pareto.lean` § "The gap") gets a typed
entry point.
-/

namespace Minimalist

-- ============================================================================
-- § 1: Derivation Cost
-- ============================================================================

/-- 4-dimensional cost of a syntactic derivation, measured by operation
    and resource counts. The dimensions are exactly those
    @cite{citko-gracanin-yuksek-2025} (p. 3) compares when arguing
    multidominance is more economical than ellipsis: lexical items drawn
    from the numeration, Merge operations, Agree operations, and
    E-feature triggered PF deletions. -/
structure DerivationCost where
  lexicalItems : Nat
  mergeOps : Nat
  agreeOps : Nat
  ellipsisOps : Nat
  deriving Repr, DecidableEq

namespace DerivationCost

/-- The 4-vector projection: `profile c i` is the i-th cost dimension
    (0 = lexicalItems, 1 = mergeOps, 2 = agreeOps, 3 = ellipsisOps).
    The feature map for the `Core.Order.FeaturePreorder` instance below. -/
def profile (c : DerivationCost) : Fin 4 → Nat
  | ⟨0, _⟩ => c.lexicalItems
  | ⟨1, _⟩ => c.mergeOps
  | ⟨2, _⟩ => c.agreeOps
  | ⟨3, _⟩ => c.ellipsisOps

/-- Cost-comparison preorder via `FeaturePreorder.ofFeature` pullback
    through `profile`, with `Pi.preorder` (pointwise ≤) on the
    `Fin 4 → Nat` feature space.

    This realizes the architectural parallel with
    `Core/Constraint/Pareto.lean`'s `paretoFeaturePreorder`: both Pareto-
    compare a candidate by a Nat-valued vector under pointwise ≤. The
    OT side wraps this in a `ConstraintSystem` (candidate set + decoder);
    Minimalist economy doesn't need either, so we instantiate
    `FeaturePreorder` directly.

    `coarsen_via_monotone` (`Core/Order/FeaturePreorder.lean`) becomes
    available for free on `DerivationCost`. -/
def featurePreorder : Core.Order.FeaturePreorder DerivationCost (Fin 4 → Nat) :=
  Core.Order.FeaturePreorder.ofFeature profile (fun a a' =>
    decidable_of_iff (∀ i, a.profile i ≤ a'.profile i) Iff.rfl)

instance : Preorder DerivationCost := featurePreorder.toPreorder

end DerivationCost

/-- Extract cost from a core `Derivation` (step-based model).

    `lexicalItems`: each `emL`/`emR`/`wlm` step draws one lexical item
    from the numeration. (Wholesale Late Merger
    @cite{takahashi-hulsey-2009} introduces a restrictor — also a
    numeration draw.)
    `mergeOps`: total step count.
    `agreeOps`/`ellipsisOps`: not tracked by the step-based model. -/
def Derivation.cost (d : Derivation) : DerivationCost where
  lexicalItems :=
    d.steps.filter
      (match · with | .emL _ | .emR _ | .wlm _ _ => true | _ => false)
      |>.length
  mergeOps := d.steps.length
  agreeOps := 0
  ellipsisOps := 0

-- ============================================================================
-- § 2: Economy Comparison (linguistic-named API)
-- ============================================================================

/-- Componentwise Pareto: `c1` is at-least-as-economical as `c2` iff every
    cost dimension is no worse. Linguistic-named alias for the underlying
    `Preorder.le` from `DerivationCost.featurePreorder`.

    NB: this is **not** a flat sum. Earlier revisions used `totalOps :=
    mergeOps + agreeOps + ellipsisOps` followed by 2-tuple
    `(totalOps, lexicalItems)` comparison, which lets a derivation with
    `agreeOps=0, mergeOps=100` "beat" one with `agreeOps=10, mergeOps=50`
    purely on the sum (110 vs 60) — a comparison
    @cite{citko-gracanin-yuksek-2025} (p. 3) explicitly does not endorse:
    they argue MD is more economical than ellipsis on the *each-dimension*
    reading (fewer lexical items AND fewer Merge AND fewer Agree). -/
def atLeastAsEconomical (c1 c2 : DerivationCost) : Prop :=
  c1.lexicalItems ≤ c2.lexicalItems ∧
  c1.mergeOps ≤ c2.mergeOps ∧
  c1.agreeOps ≤ c2.agreeOps ∧
  c1.ellipsisOps ≤ c2.ellipsisOps

instance (c1 c2 : DerivationCost) : Decidable (atLeastAsEconomical c1 c2) := by
  unfold atLeastAsEconomical; infer_instance

/-- Strict Pareto: at-least-as-economical AND strictly better on at least
    one dimension. Equivalent to `<` from the `Preorder` instance
    (cf. `strictlyMoreEconomical_iff_lt`), but not definitionally equal. -/
def strictlyMoreEconomical (c1 c2 : DerivationCost) : Prop :=
  atLeastAsEconomical c1 c2 ∧
  (c1.lexicalItems < c2.lexicalItems ∨ c1.mergeOps < c2.mergeOps ∨
   c1.agreeOps < c2.agreeOps ∨ c1.ellipsisOps < c2.ellipsisOps)

instance (c1 c2 : DerivationCost) : Decidable (strictlyMoreEconomical c1 c2) := by
  unfold strictlyMoreEconomical; infer_instance

/-- The linguistic alias agrees with the `FeaturePreorder.toPreorder`-derived
    `≤` componentwise. Decomposes the `Pi.preorder` `∀ i, profile c1 i ≤
    profile c2 i` quantifier into the 4-conjunction. -/
theorem atLeastAsEconomical_iff_le (c1 c2 : DerivationCost) :
    atLeastAsEconomical c1 c2 ↔ c1 ≤ c2 := by
  refine ⟨fun ⟨h0, h1, h2, h3⟩ i => ?_, fun h => ?_⟩
  · match i with
    | ⟨0, _⟩ => exact h0
    | ⟨1, _⟩ => exact h1
    | ⟨2, _⟩ => exact h2
    | ⟨3, _⟩ => exact h3
  · refine ⟨h ⟨0, by decide⟩, h ⟨1, by decide⟩, h ⟨2, by decide⟩, h ⟨3, by decide⟩⟩

/-- Strict economy is the strict order of the `Preorder` instance:
    `at-least-as-economical AND strictly better on at least one dimension`
    iff `c1 ≤ c2 ∧ ¬ c2 ≤ c1`. -/
theorem strictlyMoreEconomical_iff_lt (c1 c2 : DerivationCost) :
    strictlyMoreEconomical c1 c2 ↔ c1 < c2 := by
  rw [lt_iff_le_not_ge, ← atLeastAsEconomical_iff_le, ← atLeastAsEconomical_iff_le]
  unfold strictlyMoreEconomical atLeastAsEconomical
  constructor
  · rintro ⟨⟨hl, hm, ha, he⟩, hstrict⟩
    refine ⟨⟨hl, hm, ha, he⟩, fun ⟨hl', hm', ha', he'⟩ => ?_⟩
    rcases hstrict with h | h | h | h <;> omega
  · rintro ⟨⟨hl, hm, ha, he⟩, hnot⟩
    refine ⟨⟨hl, hm, ha, he⟩, ?_⟩
    by_contra hbad
    push Not at hbad
    obtain ⟨hl', hm', ha', he'⟩ := hbad
    exact hnot ⟨by omega, by omega, by omega, by omega⟩

-- ============================================================================
-- § 3: Pronunciation Economy (per-operation)
-- ============================================================================

/-- A single PF-affecting operation: PF state immediately before vs
    immediately after the op fires. Used to express
    @cite{citko-gracanin-yuksek-2025}'s **per-operation** vacuity check
    (paper p. 27 ex (39); §3 PF reduction).

    Whole-derivation Pronunciation Economy is the conjunction of per-op
    economy across all PF-affecting operations in the derivation. -/
structure PFOperation where
  pfBefore : List String
  pfAfter : List String
  deriving Repr, DecidableEq

/-- A PF operation is *vacuous* iff it has no effect on the PF string —
    e.g., the deletion targets material already unpronounced because a
    prior deletion removed it (paper p. 32 ex (45c)). -/
def PFOperation.isVacuous (op : PFOperation) : Prop := op.pfBefore = op.pfAfter

instance (op : PFOperation) : Decidable op.isVacuous := by
  unfold PFOperation.isVacuous; infer_instance

/-- **Pronunciation Economy** (@cite{citko-gracanin-yuksek-2025} p. 27,
    ex (39)): no PF-affecting operation in the derivation is vacuous.

    Crucially **per-operation**, not on whole-derivation PF before/after.
    A whole-derivation `pfBefore ≠ pfAfter` check under-rejects: any
    derivation containing one non-vacuous deletion plus N vacuous ones
    would pass, because the non-vacuous deletion alone ensures the whole
    derivation's PF changes. The paper's centerpiece argument (p. 32
    ex (45c)) needs to ban exactly that configuration: a CWH structure
    where a shared C with E-feature deletes two TPs, the second of which
    is vacuous. -/
def pronunciationEconomy (ops : List PFOperation) : Prop :=
  ∀ op ∈ ops, ¬ op.isVacuous

instance (ops : List PFOperation) : Decidable (pronunciationEconomy ops) := by
  unfold pronunciationEconomy; infer_instance

/-- Pronunciation Economy holds iff no individual operation is vacuous. -/
theorem pronunciationEconomy_iff_no_vacuous (ops : List PFOperation) :
    pronunciationEconomy ops ↔ ¬ ∃ op ∈ ops, op.isVacuous := by
  simp only [pronunciationEconomy, not_exists, not_and]

/-- A derivation with any vacuous op violates Pronunciation Economy. -/
theorem pronunciationEconomy_violated_of_vacuous {op : PFOperation}
    {ops : List PFOperation} (hmem : op ∈ ops) (hvac : op.isVacuous) :
    ¬ pronunciationEconomy ops := by
  intro h; exact h op hmem hvac

end Minimalist
