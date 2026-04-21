import Linglib.Theories.Syntax.Minimalism.Core.LateMerger
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
bridge: it imports late merger from `Theories/Syntax/Minimalism/Core/`
and the comparative operator from `Theories/Semantics/Degree/`, and
expresses the constraints that reach across the two.

## What lives where

- **Syntactic late merger** (`Theories/Syntax/Minimalism/Core/LateMerger.lean`):
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

namespace Minimalism.Semantics.DegreeMovement

open Minimalism

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
    whether the QP's trace appears inside the DegP's restrictor. -/
structure ScopeBinding where
  /-- LF height at which the DegP takes scope. -/
  degHeight : Nat
  /-- LF height at which the QP takes scope. -/
  qpHeight : Nat
  /-- Whether the QP binds into the DegP's restrictor (i.e., the DegP
      contains a trace of the QP). -/
  qpBindsDeg : Bool
  deriving DecidableEq, Repr

/-- Heim-Kennedy Constraint (@cite{heim-2000}; B&P §4.1):
    a scope binding is licit iff either
    (a) there is no binding dependency from the QP into the DegP, OR
    (b) the DegP scopes at or above the QP. -/
def heimKennedyOK (b : ScopeBinding) : Bool :=
  !b.qpBindsDeg || decide (b.degHeight ≥ b.qpHeight)

/-- Without a binding dependency, HKC imposes no scope constraint. -/
theorem heimKennedy_no_dependency (degH qpH : Nat) :
    heimKennedyOK ⟨degH, qpH, false⟩ = true := rfl

/-- With a binding dependency, HKC requires the DegP to scope at or
    above the binding QP. -/
theorem heimKennedy_dependency_requires_high_DegP
    (degH qpH : Nat) (h : degH ≥ qpH) :
    heimKennedyOK ⟨degH, qpH, true⟩ = true := by
  simp [heimKennedyOK, h]

/-- HKC's characteristic prohibition: a QP scoping strictly above a
    DegP it binds into is illicit. -/
theorem heimKennedy_QP_above_bound_DegP_illicit
    (degH qpH : Nat) (h : degH < qpH) :
    heimKennedyOK ⟨degH, qpH, true⟩ = false := by
  simp [heimKennedyOK]; omega

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
    heimKennedyOK ⟨degH, intH, true⟩ = false :=
  heimKennedy_QP_above_bound_DegP_illicit degH intH h

/-- Conversely: when the intensional subject doesn't bind into the
    DegP, Williams's prohibition is lifted — the DegP is free to
    take wide scope. This is B&P's diagnosis of why the Williams
    generalization shows exceptions. -/
theorem williams_exempt_when_no_binding
    (degH intH : Nat) :
    heimKennedyOK ⟨degH, intH, false⟩ = true :=
  heimKennedy_no_dependency degH intH

end Minimalism.Semantics.DegreeMovement
