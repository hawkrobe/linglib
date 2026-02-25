import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Theories.Syntax.Minimalism.Core.Spellout

/-!
# Mam Agreement Fragment @cite{scott-2023}

Agreement morphology and pronoun realization data for San Juan Atitán (SJA)
Mam, a Mayan language with tripartite alignment (Scott 2023).

## The System

Mam has two agreement paradigms on the verb:
- **Set A** (ERG): prefixes cross-referencing the transitive agent
- **Set B** (ABS): preverbal markers cross-referencing the absolutive argument
  (intransitive S or raised transitive subject)

Crucially, transitive *objects* are NOT cross-referenced by either set.
Objects co-occur with default B2/3SG agreement and require full overt
pronouns (Scott 2023, ch. 4). This is the only argument position in Mam
where the pronoun must be overt.

## Argument Positions

| Position | Case | Agreement | Pronoun |
|----------|------|-----------|---------|
| A (transitive agent) | ERG | Set A | null |
| S (intransitive subj) | ABS | Set B | null |
| P (transitive patient) | ACC | default B2/3SG | **overt** |

## References

- Scott, T. (2023). Pronouns and agreement in San Juan Atitán Mam.
  UC Berkeley dissertation.
-/

namespace Fragments.Mam

open Minimalism

-- ============================================================================
-- § 1: Agreement Marker Vocabulary (Set A / Set B)
-- ============================================================================

/-- Set A (ERG) vocabulary entries: φ-features on v → morphological exponent.
    Set A markers are prefixes/proclitics that cross-reference the
    transitive agent (Scott 2023, Table 2.8). -/
def setAVocab : Vocabulary :=
  [ { features := [.valued (.phi (.person 1)), .valued (.phi (.number false))]
    , exponent := "n-/w-"
    , context := some .v }
  , { features := [.valued (.phi (.person 2)), .valued (.phi (.number false))]
    , exponent := "t-"
    , context := some .v }
  , { features := [.valued (.phi (.person 3)), .valued (.phi (.number false))]
    , exponent := "t-"
    , context := some .v }
  , { features := [.valued (.phi (.person 1)), .valued (.phi (.number true))]
    , exponent := "q-"
    , context := some .v }
  , { features := [.valued (.phi (.person 2)), .valued (.phi (.number true))]
    , exponent := "ky-"
    , context := some .v }
  , { features := [.valued (.phi (.person 3)), .valued (.phi (.number true))]
    , exponent := "ky-"
    , context := some .v } ]

/-- Set B (ABS) vocabulary entries: φ-features on T → morphological exponent.
    Set B markers are preverbal clitics that cross-reference the
    absolutive argument (Scott 2023, Table 2.10). -/
def setBVocab : Vocabulary :=
  [ { features := [.valued (.phi (.person 1)), .valued (.phi (.number false))]
    , exponent := "chin"
    , context := some .T }
  , { features := [.valued (.phi (.person 2)), .valued (.phi (.number false))]
    , exponent := "∅"
    , context := some .T }
  , { features := [.valued (.phi (.person 3)), .valued (.phi (.number false))]
    , exponent := "∅"
    , context := some .T }
  , { features := [.valued (.phi (.person 1)), .valued (.phi (.number true))]
    , exponent := "qo"
    , context := some .T }
  , { features := [.valued (.phi (.person 2)), .valued (.phi (.number true))]
    , exponent := "chi"
    , context := some .T }
  , { features := [.valued (.phi (.person 3)), .valued (.phi (.number true))]
    , exponent := "chi"
    , context := some .T } ]

-- ============================================================================
-- § 2: Argument Positions and Agreement Status
-- ============================================================================

/-- Argument positions in a Mam transitive clause (Scott 2023, ch. 3). -/
inductive MamArgPosition where
  | agent    -- A: transitive agent (external argument, Spec,vP)
  | patient  -- P: transitive patient (internal argument, complement of V)
  | intranS  -- S: intransitive subject (sole argument, moves to Spec,TP)
  deriving DecidableEq, BEq, Repr

/-- The case each argument position receives (Scott 2023, ch. 3).
    A gets ERG, P gets ACC, S gets ABS — tripartite alignment. -/
def MamArgPosition.case : MamArgPosition → CaseVal
  | .agent   => .erg
  | .patient => .acc
  | .intranS => .abs

/-- Is this argument position φ-Agreed-with by some probe?

    Agent: v probes for φ, finds agent as closest goal → Set A
    Intransitive S: T probes for φ, finds S in Spec,TP → Set B
    Patient: v's φ-probe targets the agent (closer), NOT the patient;
    T's φ-probe targets Spec,TP (the moved subject), NOT the patient.
    Result: patient is never φ-Agreed-with. -/
def MamArgPosition.isPhiAgreed : MamArgPosition → Bool
  | .agent   => true   -- φ-Agreed by v → Set A
  | .patient => false  -- NOT φ-Agreed by any probe
  | .intranS => true   -- φ-Agreed by T → Set B

/-- Which head φ-Agrees with this argument (if any)?
    Returns the category of the probe head. -/
def MamArgPosition.agreeProbe : MamArgPosition → Option Cat
  | .agent   => some .v   -- v probes, agent is closest goal
  | .patient => none      -- no probe targets patient
  | .intranS => some .T   -- T probes, S is in Spec,TP

-- ============================================================================
-- § 3: Pronoun Realization
-- ============================================================================

/-- Can a pronoun in this argument position be null?

    Scott's generalization (ch. 4): a pronoun can be null iff it has been
    φ-Agreed-with. Agreement morphology on the verb recovers the pronoun's
    referential content, making the overt pronoun redundant. -/
def MamArgPosition.canBeNull : MamArgPosition → Bool
  | .agent   => true   -- Set A recovers φ → null OK
  | .patient => false  -- no agreement → overt required
  | .intranS => true   -- Set B recovers φ → null OK

/-- The three argument positions. -/
def mamArgPositions : List MamArgPosition :=
  [.agent, .patient, .intranS]

-- ============================================================================
-- § 4: Per-Position Verification
-- ============================================================================

/-- Agent gets ERG. -/
theorem agent_case : MamArgPosition.agent.case = .erg := rfl

/-- Patient gets ACC. -/
theorem patient_case : MamArgPosition.patient.case = .acc := rfl

/-- Intransitive S gets ABS. -/
theorem intranS_case : MamArgPosition.intranS.case = .abs := rfl

/-- Three distinct cases — tripartite. -/
theorem tripartite :
    MamArgPosition.agent.case ≠ MamArgPosition.patient.case ∧
    MamArgPosition.agent.case ≠ MamArgPosition.intranS.case ∧
    MamArgPosition.patient.case ≠ MamArgPosition.intranS.case := by
  exact ⟨by decide, by decide, by decide⟩

/-- Scott's generalization: pronoun can be null ↔ φ-Agreed-with. -/
theorem null_iff_phi_agreed :
    mamArgPositions.all (λ pos => pos.canBeNull == pos.isPhiAgreed) = true := by
  native_decide

end Fragments.Mam
