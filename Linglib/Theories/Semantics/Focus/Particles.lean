/-
# Focus Particles: EVEN and Only
@cite{lahiri-1998} @cite{crnic-2014} @cite{karttunen-peters-1979}
@cite{bennett-1982} @cite{francescotti-1995}

Traditional semantic treatments of focus-sensitive particles.

## EVEN and NPI Licensing

@cite{lahiri-1998} shows that Hindi NPIs are morphologically composed of
an indefinite plus the overt EVEN particle bhii, and that implicature clash
in positive contexts explains their distribution. @cite{crnic-2014} extends
this to English, proposing that NPIs like "anyone" contain a covert EVEN
operator that contributes:

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
- No covert operator needed — it's pragmatic!

-/

import Mathlib.Data.Set.Basic
import Linglib.Core.Logic.NaturalLogic

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
## Covert EVEN (@cite{crnic-2014}, building on @cite{lahiri-1998})
@cite{rooth-1992}

EVEN has two semantic contributions:

1. **Scalar presupposition**: The focused element is least likely among alternatives
2. **Additive presupposition**: At least one alternative is true (for "also" reading)
3. **Assertion**: The prejacent is true

For NPI licensing, only the scalar presupposition matters.
-/

/-- Likelihood ordering over propositions (context-dependent).
    `likelihood a b` holds when `a` is less likely (more surprising) than `b`. -/
def LikelihoodOrder (World : Type) := (World → Bool) → (World → Bool) → Prop

/-- Traditional EVEN semantics -/
structure TraditionalEven where
  /-- The prejacent proposition -/
  prejacent : (World → Bool)
  /-- Focus alternatives -/
  alternatives : List ((World → Bool))
  /-- Likelihood ordering -/
  likelihood : LikelihoodOrder World

/-- EVEN asserts the prejacent -/
def TraditionalEven.assertion (even : TraditionalEven (World := World)) : (World → Bool) :=
  even.prejacent

/-- EVEN presupposes prejacent is least likely.
    This is @cite{karttunen-peters-1979}'s universal threshold: the prejacent
    must be less likely than ALL alternatives. @cite{francescotti-1995} argues
    this is too strong — see `EvenThreshold.most` for the revised condition. -/
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

open Core.NaturalLogic (ContextPolarity)

/-- NPI licensing condition: EVEN presupposition must be satisfiable.
    Uses `ContextPolarity` from `Core.NaturalLogic`. -/
def npiLicensed (pol : ContextPolarity) (npiDomain : Set Entity) (regularDomain : Set Entity)
    (_hWider : regularDomain ⊆ npiDomain) : Prop :=
  match pol with
  | .downward =>
      -- In DE: wider domain → less likely (after negation applies)
      -- So NPI (wide domain) satisfies EVEN's "least likely" presupposition
      True
  | .upward =>
      -- In UE: wider domain → more likely
      -- NPI would violate EVEN's presupposition
      False
  | .nonMonotonic =>
      -- Non-monotonic contexts (e.g., "exactly three") don't license NPIs
      False

/-- NPI licensed in DE contexts -/
theorem npi_licensed_de (npiDomain regularDomain : Set Entity)
    (hWider : regularDomain ⊆ npiDomain) :
    npiLicensed .downward npiDomain regularDomain hWider = True := rfl

/-- NPI unlicensed in UE contexts -/
theorem npi_unlicensed_ue (npiDomain regularDomain : Set Entity)
    (hWider : regularDomain ⊆ npiDomain) :
    npiLicensed .upward npiDomain regularDomain hWider = False := rfl

/-- NPI unlicensed in non-monotonic contexts -/
theorem npi_unlicensed_nonmon (npiDomain regularDomain : Set Entity)
    (hWider : regularDomain ⊆ npiDomain) :
    npiLicensed .nonMonotonic npiDomain regularDomain hWider = False := rfl

-- Only: The Exhaustification Particle

/-!
## Overt "only"

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
  prejacent : (World → Bool)
  /-- The alternatives (what focus evokes) -/
  alternatives : List ((World → Bool))

/-- "only" presupposes the prejacent -/
def TraditionalOnly.presupposition (only : TraditionalOnly (World := World)) : (World → Bool) :=
  only.prejacent

/-- "only" asserts no alternative is true.
    The alternatives list excludes the prejacent (Roothian focus alternatives
    minus the focused element's contribution). -/
def TraditionalOnly.assertion (only : TraditionalOnly (World := World)) : (World → Bool) :=
  λ w => only.alternatives.all (λ alt => !alt w)

/-- Full "only" meaning -/
def TraditionalOnly.trueAt (only : TraditionalOnly (World := World)) (w : World) : Prop :=
  only.prejacent w ∧ only.assertion w

-- Likelihood Monotonicity

/-- A likelihood ordering is MONOTONE w.r.t. entailment when stronger
    propositions (true in fewer worlds) are less likely.

    If `p` entails `q` (i.e., `p` is true only at worlds where `q` is true),
    then `lessLikely p q` (p is at least as unlikely as q).

    This is the bridge between `Theories/Semantics/Entailment/` and
    focus particle semantics — the connection that @cite{lahiri-1998}
    relies on to derive NPI licensing from the cardinality scale. -/
def LikelihoodMonotone {W : Type} (lessLikely : (W → Bool) → (W → Bool) → Prop) : Prop :=
  ∀ (p q : (W → Bool)), (∀ w, p w = true → q w = true) → lessLikely p q

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

2. **Only is overt EXH**:
   - Same semantic effect as covert EXH
   - But with prejacent as presupposition, not assertion
-/

-- ============================================================
-- Threshold Variants (@cite{francescotti-1995})
-- ============================================================

/-- Threshold variants for the EVEN scalar presupposition.
    The theoretical dispute concerns how many alternatives the prejacent
    must exceed in unlikelihood:
    - @cite{bennett-1982}: at least one (too weak)
    - @cite{karttunen-peters-1979}: all (too strong)
    - @cite{francescotti-1995}: most (correct) -/
inductive EvenThreshold where
  /-- S* more surprising than at least one neighbor -/
  | existential
  /-- S* more surprising than all neighbors -/
  | universal
  /-- S* more surprising than most neighbors -/
  | most
  deriving DecidableEq, Repr

/-- Count of alternatives that the prejacent exceeds under a decidable ordering. -/
def countExceeded {α : Type} (prejacent : α) (alternatives : List α)
    (moreSurprising : α → α → Bool) : Nat :=
  (alternatives.filter (moreSurprising prejacent)).length

/-- Generalized EVEN presupposition parameterized by threshold.
    `moreSurprising a b` returns `true` when `a` is more surprising
    (less likely) than `b`. -/
def evenPresupWith {α : Type} (prejacent : α) (alternatives : List α)
    (moreSurprising : α → α → Bool) (threshold : EvenThreshold) : Bool :=
  let n := countExceeded prejacent alternatives moreSurprising
  match threshold with
  | .existential => decide (n > 0)
  | .universal => decide (n = alternatives.length)
  | .most => decide (n * 2 > alternatives.length)

end Semantics.FocusParticles
