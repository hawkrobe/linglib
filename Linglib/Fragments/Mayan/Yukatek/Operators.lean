import Linglib.Morphology.Derivation
import Linglib.Semantics.Lexical.Roots.SalienceClass
import Linglib.Fragments.Mayan.Yukatek.Roots

/-!
# Yukatek Maya Derivational Operator Inventory

[lucy-1994] [bohnemeyer-2004]
[beavers-koontz-garboden-2020]

The four derivational suffixes that determine Yukatek root salience
classes ([lucy-1994]). The first three are transitivisers, used
diagnostically to identify a root's salience profile; the fourth
(`-tal`, allomorph `-lah`) is the positional inchoative that carves out a separate
class of stative roots.

[lucy-1994] characterises the diagnostic by which of `=t`, `=∅`,
or `=s` is required to form a transitive stem from an underived root:

| Required suffix | Lucy's class           | Lexical content of root                                    |
|-----------------|------------------------|------------------------------------------------------------|
| `=t` (AFCT)     | agent-salient          | activity / manner-of-action; one (agent) argument salient  |
| `=∅` (root)     | agent-patient salient  | both arguments already salient → transitive without deriv. |
| `=s` (CAUS)     | patient-salient        | spontaneous state change; one (patient) argument salient   |

This translates directly into B&K-G feature conditions: agent-salient
roots have manner without result; agent-patient salient roots have
both manner and result; patient-salient roots have result without
manner. Spelt out structurally below.
-/

namespace Yukatek.Operators

open Semantics.Lexical.Roots
open Morphology.Derivation
open Yukatek.Roots

-- ════════════════════════════════════════════════════
-- § 1. The Four Operators
-- ════════════════════════════════════════════════════

/-- Affective `=t`: forms a transitive stem from an *agent-salient*
    root by adding a patient argument. Per [lucy-1994], applies
    to roots whose underived form is intransitive and refers to
    "actions or activities that some entity undertakes" — manner
    without inherent result. -/
def affectiveT : DerivOp :=
  { name := "=t"
  , applies := Root.IsAgentSalient
  , decApplies := inferInstance }

/-- Zero derivation `=∅`: signals that the root is already lexically
    transitive — both an agent and a patient are salient in the
    underived form. Per [lucy-1994], these roots "refer to events
    involving the action of one entity on another", so the root must
    encode both manner (the action) and result (its effect). -/
def zeroDeriv : DerivOp :=
  { name := "=∅"
  , applies := Root.IsAgentPatientSalient
  , decApplies := inferInstance }

/-- Causative `=s`: forms a transitive stem from a *patient-salient*
    root by adding an agent argument. Per [lucy-1994], applies
    to roots whose underived form is intransitive and refers to "state
    changes that some entity undergoes more or less spontaneously" —
    result without specified manner. -/
def causativeS : DerivOp :=
  { name := "=s"
  , applies := Root.IsPatientSalient
  , decApplies := inferInstance }

/-- Positional inchoative `-tal` (allomorph `-lah`): forms a positional stem from a
    *positional* root (a stative root denoting orientation, posture,
    or configuration). Per [lucy-1994], applies to roots that
    "denote relational states and assume two arguments that are in the
    relation" — encoded here as a pure stative root with no manner,
    result, or cause atoms. -/
def positionalTal : DerivOp :=
  { name := "-tal"
  , applies := Root.IsPositional
  , decApplies := inferInstance }

-- ════════════════════════════════════════════════════
-- § 2. The Inventory
-- ════════════════════════════════════════════════════

/-- [lucy-1994]'s diagnostic transitiviser inventory. Order is
    chosen to match the presentation in [lucy-1994] ex. (1):
    `=t`, `=∅`, `=s`, with the positional inchoative appended. -/
def inventory : Inventory :=
  [affectiveT, zeroDeriv, causativeS, positionalTal]

end Yukatek.Operators
