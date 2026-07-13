import Mathlib.Data.Set.Basic
import Linglib.Semantics.Entailment.NaturalLogic

/-!
# Focus-sensitive particles: even and only

Traditional truth-conditional semantics for focus-sensitive particles
(*even*, *only*), with NPI licensing derived from the scalar
presupposition of *even*.

## Main definitions

* `FocusStructure α`: alternative-semantics pair of an ordinary value
  and a list of alternatives.
* `LikelihoodOrder W`: relation on `W → Bool` predicates expressing
  context-dependent likelihood.
* `TraditionalEven`, `TraditionalOnly`: bundled semantics of *even*
  and *only*.
* `EvenThreshold` + `evenPresupWith`: existential / universal / most
  variants of the *even* scalar presupposition.
* `npiLicensed`: NPI licensing condition keyed on `ContextPolarity`.
* `LikelihoodMonotone`: monotonicity of a likelihood ordering with
  respect to entailment.

## References

* [lahiri-1998], [crnic-2014], [karttunen-peters-1979],
  [bennett-1982], [francescotti-1995], [rooth-1992].
-/

namespace Semantics.Focus.Particles

variable {World Entity : Type*}

/-- Alternative-semantics pair: an ordinary value plus a list of
alternatives. -/
structure FocusStructure (α : Type*) where
  /-- The ordinary semantic value. -/
  ordinary : α
  /-- The focus alternatives. -/
  alternatives : List α

/-- Context-dependent likelihood ordering on `World → Bool` predicates.
`lo a b` holds when `a` is less likely (more surprising) than `b`. -/
def LikelihoodOrder (World : Type*) := (World → Bool) → (World → Bool) → Prop

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
    This is [karttunen-peters-1979]'s universal threshold: the prejacent
    must be less likely than ALL alternatives. [francescotti-1995] argues
    this is too strong — see `EvenThreshold.most` for the revised condition. -/
def TraditionalEven.presupposition (even : TraditionalEven (World := World)) : Prop :=
  ∀ alt ∈ even.alternatives, even.likelihood even.prejacent alt

/-- EVEN is defined (presupposition satisfied) -/
def TraditionalEven.defined (even : TraditionalEven (World := World)) : Prop :=
  even.presupposition

/-- Full EVEN meaning: defined and true -/
def TraditionalEven.trueAt (even : TraditionalEven (World := World)) (w : World) : Prop :=
  even.defined ∧ even.prejacent w

open NaturalLogic (ContextPolarity)

/-- NPI licensing condition: EVEN presupposition must be satisfiable.
    Uses `ContextPolarity` from `NaturalLogic`. -/
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

/-- A likelihood ordering is monotone with respect to entailment when a
stronger proposition (true at fewer worlds) is less likely than a weaker
one. -/
def LikelihoodMonotone {W : Type*} (lessLikely : (W → Bool) → (W → Bool) → Prop) : Prop :=
  ∀ (p q : (W → Bool)), (∀ w, p w = true → q w = true) → lessLikely p q

/-- Threshold variants for the EVEN scalar presupposition.
    The theoretical dispute concerns how many alternatives the prejacent
    must exceed in unlikelihood:
    - [bennett-1982]: at least one (too weak)
    - [karttunen-peters-1979]: all (too strong)
    - [francescotti-1995]: most (correct) -/
inductive EvenThreshold where
  /-- S* more surprising than at least one neighbor -/
  | existential
  /-- S* more surprising than all neighbors -/
  | universal
  /-- S* more surprising than most neighbors -/
  | most
  deriving DecidableEq, Repr

/-- Count of alternatives that the prejacent exceeds under a decidable ordering. -/
def countExceeded {α : Type*} (prejacent : α) (alternatives : List α)
    (moreSurprising : α → α → Prop) [DecidableRel moreSurprising] : Nat :=
  (alternatives.filter (fun a => decide (moreSurprising prejacent a))).length

/-- Generalized EVEN presupposition parameterized by threshold.
    `moreSurprising a b` holds when `a` is more surprising (less
    likely) than `b`. -/
def evenPresupWith {α : Type*} (prejacent : α) (alternatives : List α)
    (moreSurprising : α → α → Prop) [DecidableRel moreSurprising]
    (threshold : EvenThreshold) : Prop :=
  let n := countExceeded prejacent alternatives moreSurprising
  match threshold with
  | .existential => n > 0
  | .universal => n = alternatives.length
  | .most => n * 2 > alternatives.length

instance {α : Type*} (prejacent : α) (alternatives : List α)
    (moreSurprising : α → α → Prop) [DecidableRel moreSurprising]
    (threshold : EvenThreshold) :
    Decidable (evenPresupWith prejacent alternatives moreSurprising threshold) := by
  unfold evenPresupWith; exact match threshold with
    | .existential => inferInstanceAs (Decidable (_ > _))
    | .universal => inferInstanceAs (Decidable (_ = _))
    | .most => inferInstanceAs (Decidable (_ > _))

end Semantics.Focus.Particles
