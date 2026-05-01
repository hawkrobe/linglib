import Linglib.Theories.Syntax.Minimalist.Derivation
import Linglib.Theories.Syntax.Minimalist.Checking

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

## Architectural note

`atLeastAsEconomical` instantiates the same Pareto-on-violations shape
as `Core/Constraint/Pareto.lean`'s `paretoFeaturePreorder` (used for
OT/HG candidate comparison). Both views compare a candidate by a vector
of Nat-valued counts under pointwise ≤. The OT side requires
`ConstraintSystem` (which also carries a candidate set + decoder); here
neither is needed, so we register `Preorder DerivationCost` directly.
The unification is structural rather than syntactic: both layers are
instances of `Core.Order.FeaturePreorder` with the appropriate feature
projection.
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
-- § 2: Economy Comparison
-- ============================================================================

/-- Componentwise Pareto: `c1` is at-least-as-economical as `c2` iff every
    cost dimension is no worse.

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
    one dimension. -/
def strictlyMoreEconomical (c1 c2 : DerivationCost) : Prop :=
  atLeastAsEconomical c1 c2 ∧
  (c1.lexicalItems < c2.lexicalItems ∨ c1.mergeOps < c2.mergeOps ∨
   c1.agreeOps < c2.agreeOps ∨ c1.ellipsisOps < c2.ellipsisOps)

instance (c1 c2 : DerivationCost) : Decidable (strictlyMoreEconomical c1 c2) := by
  unfold strictlyMoreEconomical; infer_instance

/-- `Preorder DerivationCost` via componentwise comparison. The bespoke
    refl/trans/asymm lemmas earlier revisions carried (refer to git history
    pre-0.230.5xx) are now `le_refl` / `le_trans` / `lt_irrefl` / `lt_trans`
    / `asymm_of` from this instance.

    `LT.lt` from this preorder is `c1 ≤ c2 ∧ ¬ c2 ≤ c1`, which is
    *equivalent* to `strictlyMoreEconomical c1 c2` for componentwise Pareto
    on `Nat` but not definitionally equal (cf. `strictlyMoreEconomical_iff_lt`).
    Consumers wanting omega-friendly direct conjunctions should use
    `strictlyMoreEconomical`; consumers wanting mathlib's `<`/`≤` algebra
    should use the `Preorder` instance. -/
instance : Preorder DerivationCost where
  le := atLeastAsEconomical
  le_refl _ := ⟨le_refl _, le_refl _, le_refl _, le_refl _⟩
  le_trans _ _ _ h12 h23 :=
    ⟨le_trans h12.1 h23.1, le_trans h12.2.1 h23.2.1,
     le_trans h12.2.2.1 h23.2.2.1, le_trans h12.2.2.2 h23.2.2.2⟩

/-- The linguistic alias agrees with `Preorder.le` definitionally. -/
theorem atLeastAsEconomical_iff_le (c1 c2 : DerivationCost) :
    atLeastAsEconomical c1 c2 ↔ c1 ≤ c2 := Iff.rfl

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

/-- Empty derivations are vacuously Pronunciation-Economy-compliant. -/
theorem pronunciationEconomy_nil : pronunciationEconomy [] := by
  intro _ h; simp at h

/-- Adding a non-vacuous op preserves Pronunciation Economy. -/
theorem pronunciationEconomy_cons {op : PFOperation} {ops : List PFOperation}
    (hop : ¬ op.isVacuous) (hops : pronunciationEconomy ops) :
    pronunciationEconomy (op :: ops) := by
  intro o ho
  rcases List.mem_cons.mp ho with rfl | h
  · exact hop
  · exact hops o h

/-- A derivation with any vacuous op violates Pronunciation Economy. -/
theorem pronunciationEconomy_violated_of_vacuous {op : PFOperation}
    {ops : List PFOperation} (hmem : op ∈ ops) (hvac : op.isVacuous) :
    ¬ pronunciationEconomy ops := by
  intro h; exact h op hmem hvac

end Minimalist
