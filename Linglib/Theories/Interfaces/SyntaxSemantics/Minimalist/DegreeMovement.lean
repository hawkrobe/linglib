import Linglib.Theories.Syntax.Minimalist.LateMerger
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Degree Movement: Minimalism–Degree-Semantics Interface
@cite{bhatt-pancheva-2004} @cite{heim-2000} @cite{williams-1974}

## What this file is about

The interpretation of degree clauses requires them to take scope at LF.
Their *syntactic* placement is constrained by late merger
(@cite{bhatt-pancheva-2004}); their *semantic* scope is constrained by
the Heim-Kennedy Constraint (@cite{heim-2000}). Both constraints
relate the LF position of a DegP to the LF position of any
quantificational DP whose trace appears inside it. This file is the
bridge: it imports late merger from `Theories/Syntax/Minimalism/`
and the comparative operator from `Theories/Semantics/Degree/`, and
expresses the constraints that reach across the two.

## What lives where

- **Syntactic late merger** (`Theories/Syntax/Minimalism/LateMerger.lean`):
  `lateMergerBleeds`, polymorphic over admissibility. Knows nothing
  about degrees.
- **Comparative operator** (`Theories/Semantics/Degree/Comparative.lean`):
  `sComparative`, anti-additive on degree sets. Knows nothing about
  syntax.
- **This file**: degree-clause late-merger admissibility, the
  Heim-Kennedy Constraint as a structural filter, and the Williams
  correlation as a derivable corollary.

## Heim-Kennedy Constraint (@cite{heim-2000})

> If the scope of a quantificational DP contains the trace of a DegP,
> it also contains that DegP itself.

Mechanically: any LF in which a QP scopes between a DegP and the DegP's
trace is illicit. Equivalently, a binding dependency QP → DegP-trace
forces the DegP to scope at or above the QP.

## Williams 1974 generalization (@cite{williams-1974}; B&P §5.2)

> DegPs cannot escape an intensional verb whose subject's trace is in
> the DegP's restrictor.

This is the contrapositive of HKC: the only way for a DegP to scope
above the intensional verb is if no binding dependency forces it down.
B&P §5.2 derives this from HKC + the assumption that intensional
subjects bind into degree predicates.
-/

namespace Minimalist.Semantics.DegreeMovement

open Minimalist

-- ════════════════════════════════════════════════════
-- § 1. Degree-Clause Late-Merger Admissibility
-- ════════════════════════════════════════════════════

/-- A position on a movement chain that could host a degree clause.
    `height` is structural position; `scopeOK` records whether merging
    the degree clause at this position would yield a Heim-Kennedy-
    compliant LF (i.e., DegP-scope is at or above any QP whose trace
    it contains). -/
structure DegreeChainPosition where
  height : Nat
  scopeOK : Bool
  deriving DecidableEq, Repr

/-- The B&P specialization of `lateMergerBleeds` for degree clauses:
    the degree clause can late-merge above a Condition-C-relevant
    binder iff there is a *scope-licit* chain position above the
    binder. -/
def degreeClauseLateMergerBleeds
    (chain : List DegreeChainPosition) (binderHeight : Nat) : Bool :=
  lateMergerBleeds (·.scopeOK) DegreeChainPosition.height chain binderHeight

/-- A scope-licit position above the binder bleeds Condition C for
    degree-clause late merger. Specialization of
    `admissible_above_binder_bleeds`. -/
theorem scopeOK_above_binder_bleeds
    (chain : List DegreeChainPosition) (binderHeight h : Nat)
    (hgt : h > binderHeight) :
    degreeClauseLateMergerBleeds (⟨h, true⟩ :: chain) binderHeight = true :=
  admissible_above_binder_bleeds _ _ chain ⟨h, true⟩ binderHeight rfl hgt

/-- If no chain position is scope-licit, the degree clause is forced to
    reconstruct. Specialization of `no_admissible_no_bleed`. -/
theorem no_scopeOK_forces_reconstruction
    (chain : List DegreeChainPosition) (binderHeight : Nat)
    (h : ∀ p ∈ chain, p.scopeOK = false) :
    degreeClauseLateMergerBleeds chain binderHeight = false :=
  no_admissible_no_bleed _ _ chain binderHeight h

-- ════════════════════════════════════════════════════
-- § 2. Heim-Kennedy Constraint as a Structural Filter
-- ════════════════════════════════════════════════════

/-- A scope binding records the LF heights of a DegP and a QP, plus
    whether the QP's trace appears inside the DegP's restrictor.
    `qpBasePosition` records the QP's base (theta) position separately
    from its surface-scope position `qpHeight`; this is needed for
    @cite{bhatt-takahashi-2011} §4 (43), which states the than-phrase-
    internal scope generalization in terms of the QP's *base* position
    relative to the degree trace, not its surface-scope position. For
    B&P 2004 / Heim 2001 usages where the distinction is irrelevant,
    set `qpBasePosition := qpHeight`. -/
structure ScopeBinding where
  /-- LF height at which the DegP takes scope. -/
  degHeight : Nat
  /-- LF height at which the QP takes scope. -/
  qpHeight : Nat
  /-- LF height of the QP's base (theta) position. For the B&T 2011
      §4 (43) generalization this can differ from `qpHeight`; for the
      B&P / Heim usage it should equal `qpHeight`. -/
  qpBasePosition : Nat
  /-- Whether the QP binds into the DegP's restrictor (i.e., the DegP
      contains a trace of the QP). -/
  qpBindsDeg : Bool
  deriving DecidableEq, Repr

/-- Heim-Kennedy Constraint (@cite{heim-2000}; B&P §4.1):
    a scope binding is licit iff either
    (a) there is no binding dependency from the QP into the DegP, OR
    (b) the DegP scopes at or above the QP. -/
def IsHeimKennedy (b : ScopeBinding) : Prop :=
  ¬ b.qpBindsDeg ∨ b.degHeight ≥ b.qpHeight

instance (b : ScopeBinding) : Decidable (IsHeimKennedy b) := by
  unfold IsHeimKennedy; infer_instance

/-- Without a binding dependency, HKC imposes no scope constraint.
    `qpBasePosition` defaults to `qpH` (irrelevant to HKC). -/
theorem isHeimKennedy_no_dependency (degH qpH : Nat) :
    IsHeimKennedy ⟨degH, qpH, qpH, false⟩ :=
  Or.inl (by simp)

/-- With a binding dependency, HKC requires the DegP to scope at or
    above the binding QP. -/
theorem isHeimKennedy_dependency_requires_high_DegP
    (degH qpH : Nat) (h : degH ≥ qpH) :
    IsHeimKennedy ⟨degH, qpH, qpH, true⟩ :=
  Or.inr h

/-- HKC's characteristic prohibition: a QP scoping strictly above a
    DegP it binds into is illicit. -/
theorem not_isHeimKennedy_QP_above_bound_DegP
    (degH qpH : Nat) (h : degH < qpH) :
    ¬ IsHeimKennedy ⟨degH, qpH, qpH, true⟩ := by
  rintro (h1 | h2)
  · exact h1 rfl
  · exact absurd h2 (Nat.not_le.mpr h)

-- ════════════════════════════════════════════════════
-- § 3. Williams 1974 as a Derivable Corollary
-- ════════════════════════════════════════════════════

/-- Williams 1974 (@cite{williams-1974}; B&P §5.2 (37)): a DegP cannot
    take inverse scope over an intensional verb whose subject's trace
    is in the DegP's restrictor.

    Stated as a contrapositive of HKC: if the QP (intensional subject)
    binds into the DegP and scopes strictly above it, the LF is
    illicit. The Williams generalization is therefore not a primitive
    constraint but a consequence of HKC + the assumption that
    intensional subjects bind into the degree predicate. -/
theorem williams_scope_correlation
    (degH intH : Nat) (h : degH < intH) :
    ¬ IsHeimKennedy ⟨degH, intH, intH, true⟩ :=
  not_isHeimKennedy_QP_above_bound_DegP degH intH h

/-- Conversely: when the intensional subject doesn't bind into the
    DegP, Williams's prohibition is lifted — the DegP is free to
    take wide scope. This is B&P's diagnosis of why the Williams
    generalization shows exceptions. -/
theorem williams_exempt_when_no_binding
    (degH intH : Nat) :
    IsHeimKennedy ⟨degH, intH, intH, false⟩ :=
  isHeimKennedy_no_dependency degH intH

-- ════════════════════════════════════════════════════
-- § 4. Bhatt-Takahashi (43): Base-Position Generalization
-- ════════════════════════════════════════════════════

/-- @cite{bhatt-takahashi-2011} §4 (43): English allows than-phrase-
    internal scope for QPs whose *base position* does not c-command
    the degree trace. Stated as a structural filter on `ScopeBinding`,
    `IsBhattTakahashiScopeLicit` returns `True` when the QP's base
    position is at or below the DegP's height (no c-command of the
    degree trace from the base) — in which case than-internal scope
    is licensed.

    Note this is *distinct* from HKC: HKC is over the QP's *surface*
    scope position relative to the DegP; B&T (43) is over the QP's
    *base* position. The two coincide for in-situ QPs (where surface
    = base) and diverge for QPs that have moved. -/
def IsBhattTakahashiScopeLicit (b : ScopeBinding) : Prop :=
  b.qpBasePosition ≤ b.degHeight

instance (b : ScopeBinding) : Decidable (IsBhattTakahashiScopeLicit b) := by
  unfold IsBhattTakahashiScopeLicit; infer_instance

/-- The structural witness of B&T (43): a QP whose base position is
    strictly above the DegP cannot license than-internal scope. -/
theorem not_isBhattTakahashiScopeLicit_base_above_DegP
    (degH qpH qpBase : Nat) (qpBindsDeg : Bool) (h : qpBase > degH) :
    ¬ IsBhattTakahashiScopeLicit ⟨degH, qpH, qpBase, qpBindsDeg⟩ :=
  Nat.not_le.mpr h

/-- A QP whose base position is at or below the DegP licenses
    than-internal scope under B&T (43). -/
theorem isBhattTakahashiScopeLicit_base_below_DegP
    (degH qpH qpBase : Nat) (qpBindsDeg : Bool) (h : qpBase ≤ degH) :
    IsBhattTakahashiScopeLicit ⟨degH, qpH, qpBase, qpBindsDeg⟩ :=
  h

end Minimalist.Semantics.DegreeMovement
