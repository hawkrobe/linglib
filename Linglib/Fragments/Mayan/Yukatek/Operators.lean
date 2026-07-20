import Linglib.Morphology.Exponence.Select
import Linglib.Semantics.Verb.Root.SalienceClass
import Linglib.Fragments.Mayan.Yukatek.Roots

/-!
# Yukatek Maya Derivational Operator Inventory

The four derivational suffixes that determine Yukatek root salience
classes ([lucy-1994]). The first three (`=t`, `=∅`, `=s`) are
transitivisers, used diagnostically to identify a root's salience profile;
the fourth (`-tal`, allomorph `-lah`) is the positional inchoative that
carves out a separate class of stative roots.

## Main declarations

* `Yukatek.Operators.affectiveT`, `zeroDeriv`, `causativeS`,
  `positionalTal`: the four derivational operators.
* `Yukatek.Operators.inventory`: [lucy-1994]'s diagnostic transitiviser
  inventory.

## Implementation notes

[lucy-1994] characterises the diagnostic by which of `=t`, `=∅`, or `=s`
is required to form a transitive stem from an underived root:

| Required suffix | Lucy's class           | Lexical content of root                                    |
|-----------------|------------------------|------------------------------------------------------------|
| `=t` (AFCT)     | agent-salient          | activity / manner-of-action; one (agent) argument salient  |
| `=∅` (root)     | agent-patient salient  | lexically transitive ("require two arguments")            |
| `=s` (CAUS)     | patient-salient        | spontaneous state change; one (patient) argument salient   |

The structural conditions range over B&K-G kind signature × Coon arity
([beavers-koontz-garboden-2020]): zero derivation tracks root transitivity
(`Root.Arity.selectsTheme`); the two intransitive transitivisers split by
signature (manner vs result). Each condition is the corresponding named
predicate of `Roots/SalienceClass.lean` applied to the root's signature and
the fragment's `arity` assignment, so operator applicability matches
predicted salience by construction. The salience classes these suffixes
diagnose interface with [bohnemeyer-2004]'s Yukatek stem classes
(`VerbClasses.lean`).
-/

namespace Yukatek.Operators

open Verb
open Morphology
open Yukatek.Roots

/-! ### The operator carrier -/

/-- A diagnostic derivational operator: a rule of exponence over roots
    (`exponent` is the suffix, `Applies` the structural condition on the
    root's entailments) with bundled decidability so applicability
    profiles compute. Selection/profile machinery comes from the
    `Morphology.Exponence.Rule` class instance below, not re-stipulated. -/
structure DiagOp where
  exponent : String
  Applies : Root → Prop
  decApplies : DecidablePred Applies

instance instExponence : Morphology.Exponence.Rule DiagOp Root String where
  exponent := DiagOp.exponent
  Applies := DiagOp.Applies

instance (r : Root) :
    DecidablePred (fun op : DiagOp => Exponence.Applies op r) :=
  fun op => show Decidable (op.Applies r) from op.decApplies r

@[simp] theorem applies_iff (op : DiagOp) (r : Root) :
    Exponence.Applies op r ↔ op.Applies r := Iff.rfl

/-! ### The four operators -/

/-- Affective `=t`: forms a transitive stem from an *agent-salient*
    root by adding a patient argument. Per [lucy-1994], applies
    to roots whose underived form is intransitive and refers to
    "actions or activities that some entity undertakes" — manner
    without inherent result. -/
def affectiveT : DiagOp :=
  { exponent := "=t"
  , Applies := fun r => IsAgentSalient r.kinds (arity r)
  , decApplies := inferInstance }

/-- Zero derivation `=∅`: signals that the root is already lexically
    transitive — it "require[s] two arguments and refer[s] to events
    involving the action of one entity on another" ([lucy-1994]).
    The condition is root transitivity (`Root.Arity.selectsTheme`),
    not any feature configuration: root transitives like *p'is*
    'measure' entail no change of state. -/
def zeroDeriv : DiagOp :=
  { exponent := "=∅"
  , Applies := fun r => IsAgentPatientSalient (arity r)
  , decApplies := inferInstance }

/-- Causative `=s`: forms a transitive stem from a *patient-salient*
    root by adding an agent argument. Per [lucy-1994], applies
    to roots whose underived form is intransitive and refers to "state
    changes that some entity undergoes more or less spontaneously" —
    result without specified manner. -/
def causativeS : DiagOp :=
  { exponent := "=s"
  , Applies := fun r => IsPatientSalient r.kinds (arity r)
  , decApplies := inferInstance }

/-- Positional inchoative `-tal` (allomorph `-lah`): forms a positional stem from a
    *positional* root (a stative root denoting orientation, posture,
    or configuration). Per [lucy-1994], applies to roots that
    "denote relational states and assume two arguments that are in the
    relation" — encoded here as a pure stative root with no manner,
    result, or cause atoms. -/
def positionalTal : DiagOp :=
  { exponent := "-tal"
  , Applies := fun r => IsPositional r.kinds (arity r)
  , decApplies := inferInstance }

/-! ### The inventory -/

/-- [lucy-1994]'s diagnostic transitiviser inventory. Order is
    chosen to match the presentation in [lucy-1994] ex. (1):
    `=t`, `=∅`, `=s`, with the positional inchoative appended. -/
def inventory : List DiagOp :=
  [affectiveT, zeroDeriv, causativeS, positionalTal]

end Yukatek.Operators
