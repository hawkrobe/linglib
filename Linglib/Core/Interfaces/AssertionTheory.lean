import Linglib.Core.Semantics.CommonGround

/-!
# Assertion Theory Interface

Abstract interface for comparing theories of assertion, following the
same interface-and-instantiation pattern used for `ImplicatureTheory`.

Each theory implements `AssertionTheory` by providing:
- A state type representing the discourse state
- Operations for assertion, context set extraction, and stability
- Boolean flags indicating which phenomena the theory models

## Theories Compared

| Theory | Commitment ≠ Belief | Retraction | Source Marking |
|--------|---------------------|------------|----------------|
| Stalnaker | No | No | No |
| Farkas & Bruce | Yes (dcS/dcL ≠ cg) | No | No |
| Krifka | Yes | Yes | No |
| Brandom | Yes (entitlements) | Yes | No |
| Gunlogson | Yes | Yes | Yes |
| Lauer | Yes (credence) | No | No |

## References

- Stalnaker, R. (1978). Assertion. *Syntax and Semantics* 9.
- Farkas, D. & Bruce, K. (2010). On Reacting to Assertions. *JoS* 27(1).
- Krifka, M. (2015). Bias in Commitment Space Semantics. *L&P* 38.
- Brandom, R. (1994). *Making It Explicit*. Harvard UP.
- Gunlogson, C. (2001). *True to Form*. PhD dissertation, UC Santa Cruz.
- Lauer, S. (2013). *Towards a Dynamic Pragmatics*. PhD dissertation, Stanford.
-/

namespace Interfaces

open Core.CommonGround (ContextSet)

-- ════════════════════════════════════════════════════
-- § 1. Assertion Outcomes
-- ════════════════════════════════════════════════════

/-- The possible outcomes of an assertion in discourse.

    Not all theories distinguish all four outcomes:
    - Stalnaker: only `accepted` (assertion = CG update)
    - Farkas & Bruce: `accepted` vs `pending` (table model)
    - Krifka/Brandom: all four (commitment space / scorekeeping) -/
inductive AssertionOutcome where
  /-- Proposition enters the common ground -/
  | accepted
  /-- Proposition on the table, awaiting resolution -/
  | pending
  /-- Previously accepted proposition withdrawn -/
  | retracted
  /-- Assertion met with a demand for reasons -/
  | challenged
  deriving DecidableEq, Repr, BEq, Inhabited

-- ════════════════════════════════════════════════════
-- § 2. The Interface
-- ════════════════════════════════════════════════════

/-- Abstract interface for theories of assertion.

    Each theory provides a state type, an assertion operation, and
    a way to extract the common ground. Boolean flags indicate which
    discourse phenomena the theory can model.

    Following the `ImplicatureTheory` pattern: the interface is minimal,
    with rich comparison infrastructure built on top. -/
class AssertionTheory (T : Type) where
  /-- The theory's discourse state representation.
      Parameterized by world type (at Type level, matching BProp W). -/
  State : Type → Type

  /-- The initial (empty) discourse state. -/
  initial : {W : Type} → State W

  /-- Assert a proposition, updating the discourse state. -/
  assert : {W : Type} → State W → Core.Proposition.BProp W → State W

  /-- Extract the context set (worlds compatible with common ground). -/
  contextSet : {W : Type} → State W → ContextSet W

  /-- Is the discourse state stable (no pending issues)? -/
  isStable : {W : Type} → State W → Bool

  /-- Does the theory separate public commitment from private belief?

      - `false`: Stalnaker (assertion = adding to shared beliefs)
      - `true`: Krifka, Brandom, Gunlogson (commitment ≠ belief) -/
  separatesCommitmentFromBelief : Bool

  /-- Does the theory support retraction of prior commitments?

      - `false`: Stalnaker, Farkas & Bruce (monotonic CG)
      - `true`: Krifka, Brandom (commitment can be withdrawn) -/
  supportsRetraction : Bool

  /-- Does the theory model source marking (who generated the commitment)?

      - `false`: all theories except Gunlogson
      - `true`: Gunlogson (self- vs other-generated) -/
  modelsSourceMarking : Bool

-- ════════════════════════════════════════════════════
-- § 3. Comparison Infrastructure
-- ════════════════════════════════════════════════════

variable {T1 T2 : Type} [AssertionTheory T1] [AssertionTheory T2]

/-- Two theories agree on the context set after asserting a proposition. -/
def theoriesAgreeOnContextSet {W : Type}
    (s1 : AssertionTheory.State T1 W) (s2 : AssertionTheory.State T2 W)
    (p : Core.Proposition.BProp W) : Prop :=
  AssertionTheory.contextSet (AssertionTheory.assert s1 p) =
  AssertionTheory.contextSet (AssertionTheory.assert s2 p)

/-- Two theories agree on stability after asserting a proposition. -/
def theoriesAgreeOnStability {W : Type}
    (s1 : AssertionTheory.State T1 W) (s2 : AssertionTheory.State T2 W)
    (p : Core.Proposition.BProp W) : Bool :=
  AssertionTheory.isStable (AssertionTheory.assert s1 p) ==
  AssertionTheory.isStable (AssertionTheory.assert s2 p)

/-- Both theories separate commitment from belief. -/
def bothSeparateCommitment : Bool :=
  AssertionTheory.separatesCommitmentFromBelief (T := T1) &&
  AssertionTheory.separatesCommitmentFromBelief (T := T2)

/-- Both theories support retraction. -/
def bothSupportRetraction : Bool :=
  AssertionTheory.supportsRetraction (T := T1) &&
  AssertionTheory.supportsRetraction (T := T2)

-- ════════════════════════════════════════════════════
-- § 4. Coverage and Phenomena
-- ════════════════════════════════════════════════════

/-- Assertion-related phenomena that theories may handle. -/
inductive AssertionPhenomenon where
  /-- Basic assertion adds to common ground -/
  | basicAssertion
  /-- Hedging reduces commitment strength -/
  | hedging
  /-- Oath formulae increase commitment strength -/
  | oathFormulae
  /-- Rising declaratives shift commitment source -/
  | risingDeclaratives
  /-- Retraction / taking back a prior commitment -/
  | retraction
  /-- Lying: commitment without belief -/
  | lying
  /-- Challenging: demanding reasons for a commitment -/
  | challenging
  deriving DecidableEq, Repr, BEq

/-- Whether a theory handles a given phenomenon.

    Derived from the Boolean flags — not a separate configuration. -/
def handlesAssertion (T : Type) [AssertionTheory T] : AssertionPhenomenon → Bool
  | .basicAssertion => true  -- all theories handle this
  | .hedging => AssertionTheory.separatesCommitmentFromBelief (T := T)
  | .oathFormulae => AssertionTheory.separatesCommitmentFromBelief (T := T)
  | .risingDeclaratives => AssertionTheory.modelsSourceMarking (T := T)
  | .retraction => AssertionTheory.supportsRetraction (T := T)
  | .lying => AssertionTheory.separatesCommitmentFromBelief (T := T)
  | .challenging => AssertionTheory.supportsRetraction (T := T)

end Interfaces
