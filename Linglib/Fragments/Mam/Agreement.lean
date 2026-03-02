import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Theories.Syntax.Minimalism.Core.Spellout
import Linglib.Core.Case.Hierarchy

/-!
# Mam Agreement Fragment @cite{scott-2023}
@cite{deal-2021} @cite{woolford-1997} @cite{blake-1994}

Agreement morphology and pronoun realization data for San Juan Atitán (SJA)
Mam, a Mayan language with morphologically tripartite agreement alignment: S, A, and O each trigger distinct marking patterns
on the verb.

## The System

Mam has two agreement paradigms on the verb:
- **Set A** (ERG): prefixes on Voice cross-referencing the transitive agent
- **Set B** (ABS): preverbal markers on Infl cross-referencing the absolutive
  argument (intransitive S). In transitives, Infl's φ-probe is blocked by
  transitive VoiceP and default Set B (∅/tz'=)
  appears instead.

Crucially, transitive *objects* are NOT cross-referenced by either set.
Objects co-occur with default Set B and require full overt pronouns
(Scott 2023, ch. 3–4).

## Case Licensing

Case is NOT assigned via dependent case. Instead:
- **ERG**: inherent case from Voice
- **ACC**: structural case from Voice (object licensing; low-abs syntax)
- **ABS**: structural case from Infl (high-abs morphology; for intransitive S)

This gives a tripartite underlying Case system (ERG, ACC, ABS) despite
Mam having no independent case morphology on DPs — case is visible only
through agreement patterns.

## Argument Positions

| Position | Case | Agreement | Pronoun |
|----------|------|-----------|---------|
| A (transitive agent) | ERG (from Voice) | Set A | reduced/null |
| S (intransitive subj) | ABS (from Infl) | Set B | reduced/null |
| P (transitive patient) | ACC (from Voice) | default Set B | **overt** |

-/

namespace Fragments.Mam

open Minimalism

-- ============================================================================
-- § 1: Agreement Marker Vocabulary (Set A / Set B)
-- ============================================================================

/-- Set A (ERG) vocabulary entries: φ-features on Voice (mapped to.v)
    yield the morphological exponent.
    Set A markers are prefixes/proclitics that cross-reference the
    transitive agent (Scott 2023, Table 2.8). -/
def setAVocab : Vocabulary :=
  [ { features := [.valued (.phi (.person .first)), .valued (.phi (.number false))]
    , exponent := "n-/w-"
    , context := some .v }
  , { features := [.valued (.phi (.person .second)), .valued (.phi (.number false))]
    , exponent := "t-"
    , context := some .v }
  , { features := [.valued (.phi (.person .third)), .valued (.phi (.number false))]
    , exponent := "t-"
    , context := some .v }
  , { features := [.valued (.phi (.person .first)), .valued (.phi (.number true))]
    , exponent := "q-"
    , context := some .v }
  , { features := [.valued (.phi (.person .second)), .valued (.phi (.number true))]
    , exponent := "ky-"
    , context := some .v }
  , { features := [.valued (.phi (.person .third)), .valued (.phi (.number true))]
    , exponent := "ky-"
    , context := some .v } ]

/-- Set B (ABS) vocabulary entries: φ-features on Infl (mapped to.T)
    yield the morphological exponent (Scott 2023, Table 3.5).

    Crucially, the 2/3SG form (∅/tz'=) is the **Elsewhere entry** —
    it has no feature specification and is selected when no more specific
    entry matches. This is the form that appears both for (a) real
    agreement with a 2/3SG intransitive S and (b) default Set B in
    transitives when Infl's probe is blocked by VoiceP. -/
def setBVocab : Vocabulary :=
  [ { features := [.valued (.phi (.person .first)), .valued (.phi (.number false))]
    , exponent := "chin"
    , context := some .T }
  , { features := [.valued (.phi (.person .first)), .valued (.phi (.number true))]
    , exponent := "qo"
    , context := some .T }
  , { features := [.valued (.phi (.person .second)), .valued (.phi (.number true))]
    , exponent := "chi"
    , context := some .T }
  , { features := [.valued (.phi (.person .third)), .valued (.phi (.number true))]
    , exponent := "chi"
    , context := some .T }
  -- Elsewhere: default 2/3SG (∅/tz'=). No features specified — inserted
  -- when no more specific entry matches (Kiparsky 1973 Elsewhere Condition).
  -- This is what surfaces in transitives when Infl's probe is blocked.
  , { features := []
    , exponent := "∅"
    , context := some .T } ]

-- ============================================================================
-- § 2: Argument Positions and Agreement Status
-- ============================================================================

/-- Argument positions in a Mam clause (Scott 2023, ch. 3). -/
inductive MamArgPosition where
  | agent    -- A: transitive agent (external argument, Spec,VoiceP)
  | patient  -- P: transitive patient (internal argument, complement of V)
  | intranS  -- S: intransitive subject (sole argument, moves to Spec,TP)
  deriving DecidableEq, BEq, Repr

/-- The case each argument position receives.
    A gets ERG (inherent, from Voice), P gets ACC (structural, from Voice),
    S gets ABS (structural, from Infl). Three distinct underlying cases. -/
def MamArgPosition.case : MamArgPosition → CaseVal
  | .agent   => .erg
  | .patient => .acc
  | .intranS => .abs

/-- Is this argument position φ-Agreed-with by some probe?

    Agent: Voice probes for φ, finds agent in Spec,VoiceP → Set A
    Intransitive S: Infl probes for φ, finds S → Set B
    Patient: Infl's φ-probe has a disjunctive satisfaction condition
    [SAT: φ or Voice_TR]. In transitives, the
    probe encounters transitive Voice and stops — no φ-features are
    copied, and default Set B (the Elsewhere form) surfaces. -/
def MamArgPosition.isPhiAgreed : MamArgPosition → Bool
  | .agent   => true   -- φ-Agreed by Voice → Set A
  | .patient => false  -- NOT φ-Agreed: Infl probe blocked by Voice_TR
  | .intranS => true   -- φ-Agreed by Infl → Set B

/-- Which head φ-Agrees with this argument (if any)?
    Returns the category of the probe head. Voice is mapped to.v. -/
def MamArgPosition.agreeProbe : MamArgPosition → Option Cat
  | .agent   => some .v   -- Voice probes, agent in Spec,VoiceP
  | .patient => none      -- Infl probe blocked by Voice_TR
  | .intranS => some .T   -- Infl probes, S in its domain

-- ============================================================================
-- § 3: Pronoun Realization
-- ============================================================================

/-- Can a pronoun in this argument position be reduced (or null)?

    Scott's analysis (ch. 4): when a pronoun's φ-features are redundantly
    expressed by agreement morphology on the verb, the pronominal base
    morpheme is deleted. For 2nd/3rd person, this yields a fully null
    pronoun. For 1st person, the disagreement enclitic =i remains
    (realizing [participant], which agreement does not copy).

    This function captures the coarse generalization: agreed-with positions
    allow reduced/null pronouns; unagreed-with positions require full
    overt pronouns. The finer-grained 1st-person =i residue is not
    modeled here. -/
def MamArgPosition.canBeNull : MamArgPosition → Bool
  | .agent   => true   -- Set A recovers φ → reduced/null
  | .patient => false  -- no agreement → overt required
  | .intranS => true   -- Set B recovers φ → reduced/null

/-- The three argument positions. -/
def mamArgPositions : List MamArgPosition :=
  [.agent, .patient, .intranS]

-- ============================================================================
-- § 4: Per-Position Verification
-- ============================================================================

/-- Agent gets ERG (inherent, from Voice). -/
theorem agent_case : MamArgPosition.agent.case = .erg := rfl

/-- Patient gets ACC (structural, from Voice). -/
theorem patient_case : MamArgPosition.patient.case = .acc := rfl

/-- Intransitive S gets ABS (structural, from Infl). -/
theorem intranS_case : MamArgPosition.intranS.case = .abs := rfl

/-- Three distinct underlying cases — morphologically tripartite. -/
theorem tripartite :
    MamArgPosition.agent.case ≠ MamArgPosition.patient.case ∧
    MamArgPosition.agent.case ≠ MamArgPosition.intranS.case ∧
    MamArgPosition.patient.case ≠ MamArgPosition.intranS.case := by
  exact ⟨by decide, by decide, by decide⟩

/-- Pronoun reduction correlates with φ-agreement: an argument position
    allows reduced/null pronouns iff it triggers agreement on the verb. -/
theorem reduction_iff_phi_agreed :
    mamArgPositions.all (λ pos => pos.canBeNull == pos.isPhiAgreed) = true := by
  native_decide

-- ============================================================================
-- § 5: Case Inventory Validation (Blake 1994)
-- ============================================================================

/-- Mam case inventory, derived from argument position case values. -/
def caseInventory : List Core.Case := [.erg, .acc, .abs]

/-- The inventory covers all argument positions. -/
theorem inventory_covers_positions :
    mamArgPositions.all (λ p => caseInventory.any (· == p.case.toCase)) = true := by
  native_decide

/-- Mam's {ERG, ACC, ABS} inventory is valid per Blake's case hierarchy
    (all are core cases at rank 6, trivially no gaps). -/
theorem inventory_valid : Core.validInventory caseInventory = true := by native_decide

end Fragments.Mam
