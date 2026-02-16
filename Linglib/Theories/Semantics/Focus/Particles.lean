/-
# Focus Particles: EVEN and Only

Traditional semantic treatments of focus-sensitive particles.

## EVEN and NPI Licensing

Lahiri (1998) and Crnič (2014) propose that NPIs like "anyone" are licensed
by a covert EVEN operator that contributes:

1. **Presupposition**: The focused element is the LEAST LIKELY alternative
2. **Assertion**: The prejacent is true

Structure: EVEN [anyone] saw John
→ Presupposes: For all x, P(x saw John) ≤ P(anyone saw John)
→ Asserts: Someone saw John

This presupposition is satisfied in DE contexts (under negation):
"John didn't see anyone"
→ "anyone" = widest domain = least likely to have ALL seen John
→ EVEN presupposition satisfied

## Comparison with Local RSA

Local RSA derives EVEN effects from polarity-sensitive informativity:
- In DE contexts, wider domains are MORE informative
- RSA preference for informativity mimics EVEN's likelihood presupposition
- No covert operator needed - it's pragmatic!

See `RSAExhMonad/LocalRSA/Unification.lean` for the Local RSA account.

## References

- Lahiri, U. (1998). Focus and negative polarity in Hindi.
- Crnič, L. (2014). Non-monotonicity in NPI licensing.
- Rooth, M. (1992). A theory of focus interpretation.
- Karttunen, L. & Peters, S. (1979). Conventional implicature.
- Chierchia, G. (2013). Logic in Grammar.
-/

import Mathlib.Data.Set.Basic
import Linglib.Core.Proposition

namespace Semantics.FocusParticles

variable {World Entity : Type}

-- Propositions and Alternatives

/-- Alternative semantics: focused element evokes alternatives -/
structure FocusStructure (α : Type) where
  /-- The ordinary semantic value -/
  ordinary : α
  /-- The focus alternatives -/
  alternatives : List α

-- EVEN: The Traditional Account

/-!
## Covert EVEN (Lahiri 1998, Crnič 2014)

EVEN has two semantic contributions:

1. **Scalar presupposition**: The focused element is least likely among alternatives
2. **Additive presupposition**: At least one alternative is true (for "also" reading)
3. **Assertion**: The prejacent is true

For NPI licensing, only the scalar presupposition matters.
-/

/-- Likelihood ordering over propositions (context-dependent) -/
def LikelihoodOrder (World : Type) := BProp World → BProp World → Prop

/-- EVEN presupposition: focused element is least likely -/
structure EvenPresupposition where
  /-- The prejacent (focused proposition) -/
  prejacent : BProp World
  /-- The alternatives (what focus evokes) -/
  alternatives : List (BProp World)
  /-- Likelihood ordering (from context) -/
  likelihood : LikelihoodOrder World
  /-- The presupposition: prejacent is least likely -/
  presupposes : ∀ alt ∈ alternatives, likelihood prejacent alt

/-- Traditional EVEN semantics -/
structure TraditionalEven where
  /-- The prejacent proposition -/
  prejacent : BProp World
  /-- Focus alternatives -/
  alternatives : List (BProp World)
  /-- Likelihood ordering -/
  likelihood : LikelihoodOrder World

/-- EVEN asserts the prejacent -/
def TraditionalEven.assertion (even : TraditionalEven (World := World)) : BProp World :=
  even.prejacent

/-- EVEN presupposes prejacent is least likely -/
def TraditionalEven.presupposition (even : TraditionalEven (World := World)) : Prop :=
  ∀ alt ∈ even.alternatives, even.likelihood even.prejacent alt

/-- EVEN is defined (presupposition satisfied) -/
def TraditionalEven.defined (even : TraditionalEven (World := World)) : Prop :=
  even.presupposition

/-- Full EVEN meaning: defined and true -/
def TraditionalEven.trueAt (even : TraditionalEven (World := World)) (w : World) : Prop :=
  even.defined ∧ even.prejacent w

-- NPI Licensing via EVEN

/-!
## NPI Licensing Mechanism

The key insight: In DE contexts, wide-domain NPIs make the prejacent LESS likely,
satisfying EVEN's presupposition.

"John didn't see anyone"
= EVEN [John didn't see anyone]
= Presupposes: For all x, P(John didn't see x) ≥ P(John didn't see anyone)
= "Not seeing anyone" is less likely than "not seeing some particular person"
= Presupposition SATISFIED (negation creates DE context)

"*John saw anyone"
= EVEN [John saw anyone]
= Presupposes: For all x, P(John saw x) ≥ P(John saw anyone)
= "Seeing anyone" is MORE likely than seeing some particular person
= Presupposition VIOLATED
-/

/-- Whether context is downward-entailing (DE) -/
inductive Polarity where
  | up   -- Upward entailing
  | down -- Downward entailing
  deriving DecidableEq, Repr

/-- NPI licensing condition: EVEN presupposition must be satisfiable -/
def npiLicensed (pol : Polarity) (npiDomain : Set Entity) (regularDomain : Set Entity)
    (_hWider : regularDomain ⊆ npiDomain) : Prop :=
  match pol with
  | .down =>
      -- In DE: wider domain → less likely (after negation applies)
      -- So NPI (wide domain) satisfies EVEN's "least likely" presupposition
      True
  | .up =>
      -- In UE: wider domain → more likely
      -- NPI would violate EVEN's presupposition
      False

/-- NPI licensed in DE contexts -/
theorem npi_licensed_de (npiDomain regularDomain : Set Entity)
    (hWider : regularDomain ⊆ npiDomain) :
    npiLicensed .down npiDomain regularDomain hWider = True := rfl

/-- NPI unlicensed in UE contexts -/
theorem npi_unlicensed_ue (npiDomain regularDomain : Set Entity)
    (hWider : regularDomain ⊆ npiDomain) :
    npiLicensed .up npiDomain regularDomain hWider = False := rfl

-- Only: The Exhaustification Particle

/-!
## Overt "only" (Rooth 1992)

"Only" is the overt counterpart of EXH:
- Presupposes: The prejacent is true
- Asserts: No stronger alternative is true

"Only John came"
= Presupposes: John came
= Asserts: No one other than John came

This is equivalent to EXH with the prejacent as a presupposition.
-/

/-- Traditional "only" semantics -/
structure TraditionalOnly where
  /-- The prejacent (the focused element's contribution) -/
  prejacent : BProp World
  /-- The alternatives (what focus evokes) -/
  alternatives : List (BProp World)

/-- "only" presupposes the prejacent -/
def TraditionalOnly.presupposition (only : TraditionalOnly (World := World)) : BProp World :=
  only.prejacent

/-- "only" asserts no alternative is true (except prejacent) -/
def TraditionalOnly.assertion (only : TraditionalOnly (World := World)) : BProp World :=
  λ w => only.alternatives.all (λ alt => !alt w || (alt w == only.prejacent w))

/-- Full "only" meaning -/
def TraditionalOnly.trueAt (only : TraditionalOnly (World := World)) (w : World) : Prop :=
  only.prejacent w ∧ only.assertion w

-- Comparison: EVEN vs EXH vs Only

/-!
## Focus Particle Comparison

| Particle | Presupposition | Assertion | Polarity Effect |
|----------|----------------|-----------|-----------------|
| EVEN     | Least likely   | Prejacent | Licenses NPIs (DE) |
| EXH      | None           | Prejacent ∧ ¬alternatives | Scalar implicatures (UE) |
| only     | Prejacent      | ¬alternatives | Explicit exhaustivity |

### Key Observations

1. **EVEN and EXH are duals**:
   - EVEN: active in DE contexts (licenses NPIs)
   - EXH: active in UE contexts (generates SIs)

2. **Local RSA unifies them**:
   - Both are informativity maximization
   - Polarity determines which direction is "more informative"

3. **Only is overt EXH**:
   - Same semantic effect as covert EXH
   - But with prejacent as presupposition, not assertion
-/

-- The Circularity Problem (Parallel to GEN)

/-!
## Problem with Covert EVEN

Like covert GEN, covert EVEN has circularity issues:

1. **When is EVEN inserted?** - Only where NPIs appear
2. **What determines likelihood?** - Stipulated to match NPI distribution
3. **Why these alternatives?** - Chosen to give right licensing conditions

The "likelihood" ordering does the work, but it's:
- Context-dependent
- Not independently observable
- Essentially circular (defined to license NPIs where they appear)

### Local RSA Alternative

Local RSA derives EVEN effects from:
- Polarity tracking (automatically computed)
- Informativity comparison (domain size)
- No stipulated likelihood ordering needed

The "least likely" intuition becomes:
"In DE contexts, wider domains have smaller extensions after negation,
making them more informative, hence preferred."
-/

end Semantics.FocusParticles
