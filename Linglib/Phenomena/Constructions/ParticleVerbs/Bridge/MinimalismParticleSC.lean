import Linglib.Theories.Syntax.Minimalism.Core.SmallClause
import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.Basic
import Linglib.Phenomena.Constructions.ParticleVerbs.Data

/-!
# PVC — Small Clause Bridge (den Dikken 1995)

@cite{dendikken-1995}

Connects particle verb construction data to the SC predication analysis.
Den Dikken (1995, Ch. 2) analyzes particles as P heads of small
clauses: `V [SC DP Prt]`. The particle predicates a result
state/location of the DP subject.

## Particle shift as head movement

The two surface orders are derived from the same underlying SC:

1. **Split** (V DP Prt): DP moves out of SC to Spec,VP for Case
2. **Continuous** (V Prt DP): P incorporates into V (head-to-head
   movement), forming a complex head `[V V+P]`

The pronoun constraint follows: pronouns are obligatorily "light"
and must move for Case, forcing split order. Heavy DPs resist
movement, preferring continuous order (P incorporates instead).

## Cross-references

- `Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause`: SC family
  geometry and tree-shape isomorphism proofs
- `Theories.Syntax.Minimalism.Formal.HeadMovement.Basic`: head-to-head
  movement type and `formComplexLI` for incorporation

## References

- den Dikken, M. (1995). *Particles.* OUP.
- Baker, M. C. (1988). *Incorporation.* U Chicago Press.
-/

namespace Phenomena.Constructions.ParticleVerbs.Bridge.MinimalismParticleSC

open Minimalism
open Phenomena.Constructions.ParticleVerbs

/-! ## §1. Particles as P heads of small clauses -/

/-- A particle verb as a small clause: the particle (P) is the predicate,
    the DP object is the subject. -/
def pvToSmallClause (pv : ParticleVerb) (dpId prtId : Nat) : SmallClause :=
  { subject := mkLeafPhon .D [] "DP" dpId
    predicate := mkLeafPhon .P [] pv.particle prtId
    predCat := .P }

/-- All PVC small clauses have predicate category P. -/
theorem pvc_pred_is_P (pv : ParticleVerb) (dpId prtId : Nat) :
    (pvToSmallClause pv dpId prtId).predCat = .P := rfl

/-- The particle's syntactic category matches SC predicate category P. -/
theorem particle_cat_matches_pred : SCPredCategory.toCat .P = Cat.P := rfl

/-! ## §2. Particle incorporation (P-to-V head movement)

Den Dikken (1995, Ch. 2): particle shift derived by P-to-V
incorporation. The particle head moves to V, forming a complex
head `[V lift+up]`. This uses `formComplexLI` from
`HeadMovement.Basic`, connecting PVCs to the head movement typology. -/

def V_lift_tok : LIToken := ⟨LexicalItem.simple .V [.D] "lift", 0⟩
def Prt_up_tok : LIToken := ⟨LexicalItem.simple .P [] "up", 1⟩

/-- P-to-V incorporation: particle head moves to V, forming `[V lift+up]`. -/
def V_plus_Prt : LIToken := formComplexLI V_lift_tok Prt_up_tok

/-- The incorporated head is complex (result of head movement). -/
theorem incorporation_yields_complex :
    V_plus_Prt.item.isComplex = true := by native_decide

/-- The outer category of the complex head is V (verb reprojects). -/
theorem incorporation_outer_is_V :
    V_plus_Prt.item.outerCat = .V := by native_decide

/-- Incorporation preserves verb identity (target's id). -/
theorem incorporation_preserves_id : V_plus_Prt.id = V_lift_tok.id := rfl

/-! ## §3. Derivation of particle shift

Two derivations from the same underlying SC `V [SC DP Prt]`:

1. **DP movement**: DP moves out of SC to Spec,VP → V DP Prt (split)
2. **P incorporation**: P incorporates into V → V+P DP (continuous)

The pronoun constraint follows: pronouns must move for Case (light
elements always raise), forcing split order. Heavy DPs resist
movement, preferring continuous order (P incorporates instead). -/

/-- Derivation type for particle shift. -/
inductive PVCDerivation where
  | dpMovement     -- DP moves out of SC → split order
  | incorporation  -- P incorporates into V → continuous order
  deriving DecidableEq, BEq, Repr

/-- Map derivation type to surface order. -/
def PVCDerivation.surfaceOrder : PVCDerivation → PVCOrder
  | .dpMovement    => .split
  | .incorporation => .continuous

/-- Map DP weight to forced derivation (if any).
    Pronouns: obligatory DP movement (must raise for Case).
    Heavy DPs: preferred P incorporation (DP too heavy to move).
    Light DPs: either derivation available. -/
def weightToDerivation : DPWeight → Option PVCDerivation
  | .pronoun => some .dpMovement
  | .heavy   => some .incorporation
  | .light   => none

/-- Pronoun derivation forces split order. -/
theorem pronoun_derivation_is_split :
    (weightToDerivation .pronoun).map PVCDerivation.surfaceOrder
      = some .split := rfl

/-- Heavy DP derivation forces continuous order. -/
theorem heavy_derivation_is_continuous :
    (weightToDerivation .heavy).map PVCDerivation.surfaceOrder
      = some .continuous := rfl

/-- Light DPs have no forced derivation — both orders available. -/
theorem light_no_forced_derivation :
    weightToDerivation .light = none := rfl

/-! ## §4. Bridge to empirical data

Connecting derivation predictions to the attested judgments
from `Phenomena.Constructions.ParticleVerbs.Data`. -/

/-- Pronoun prediction matches data: split OK, continuous bad. -/
theorem pronoun_prediction_matches_data :
    pronoun_split.judgment = true ∧
    pronoun_continuous.judgment = false ∧
    (weightToDerivation .pronoun).map PVCDerivation.surfaceOrder = some .split :=
  ⟨rfl, rfl, rfl⟩

/-- Heavy NP prediction matches data: continuous OK, split bad. -/
theorem heavy_prediction_matches_data :
    heavy_continuous.judgment = true ∧
    heavy_split.judgment = false ∧
    (weightToDerivation .heavy).map PVCDerivation.surfaceOrder = some .continuous :=
  ⟨rfl, rfl, rfl⟩

/-- Light NPs allow both: no forced derivation, both judgments positive. -/
theorem light_prediction_matches_data :
    light_split.judgment = true ∧
    light_continuous.judgment = true ∧
    weightToDerivation .light = none :=
  ⟨rfl, rfl, rfl⟩

end Phenomena.Constructions.ParticleVerbs.Bridge.MinimalismParticleSC
