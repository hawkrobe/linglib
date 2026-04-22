import Linglib.Fragments.Indonesian.VoiceSystem
import Linglib.Phenomena.ArgumentStructure.Studies.Beavers2010
import Linglib.Core.Lexical.DiathesisAlternation
import Linglib.Theories.Semantics.Events.ArgumentRealization
import Linglib.Theories.Interfaces.SyntaxSemantics.VoiceSemantics

/-!
# @cite{beavers-udayana-2022} Middle voice as generalized argument suppression

Beavers, John and I Nyoman Udayana. 2022. Middle voice as generalized
argument suppression: The case from Indonesian. *Natural Language &
Linguistic Theory* 41:51–102.

## Core claim

Indonesian *ber-* middles — reflexive, dispositional/passive,
anticausative, and incorporation — all derive from **one**
underspecified argument-suppression operation. The surface variation
comes from independent argument realization strategies (functional
application vs. noun incorporation) and lexical-semantic/pragmatic
constraints on the suppressed variable.

## Formal analysis

*ber-* suppresses one direct argument of a dyadic VP by leaving it
as an open variable, while preserving truth conditions:

    ⟦ber-⟧ = λP_{<e,α>}[P(z̲)]                           -- UNVERIFIED: (43)

The suppressed argument *z* is interpreted via lexical and pragmatic
conventions: for naturally reflexive roots the convention is
coreferent interpretation; for other roots the convention is
disjoint interpretation. An alternative formulation existentially
binds z with a contextual constraint function f:

    ⟦ber-⟧ = λP_{<e,α>} ∃z[f_{C,P}(z) ∧ P(z)]          -- UNVERIFIED: (47)

The authors note "we see no particular reason to assume (43) over
(47), but maintain the former for consistency with Beavers and Zubair
(2013)" (the paper's §4.2). The "consistency" is notational
(open-variable form): @cite{beavers-zubair-2013}'s final operator
(their ex. (77)) likewise uses an open variable, but adds a sortal
restriction `x ∈ U_I` that does the predictive work for Sinhala
anticausatives (blocks *murder*-type verbs). The 2022 generalization
to Indonesian middle voice drops this restriction because *ber-*
suppresses arguments other than causers. The 2013 operator with the
U_I restriction is formalized at
`Phenomena.ArgumentStructure.Studies.BeaversZubair2013.causerSuppress`.

## 2×2 typology (the paper's (31))

The four middle types are classified along two independent dimensions:
(a) whether the suppressed variable is interpreted as coreferent or
disjoint from the surface subject, and (b) whether the base object is
realized as a full DP (functional application) or an incorporated NP:

|                      | non-reflexive (disjoint)           | reflexive (coreferent)   |
|----------------------|------------------------------------|--------------------------|
| **No incorporation** | dispositional/passive middle       | inherent reflexive       |
| **Incorporation**    | *ber*-V=lexical NP                 | *ber*-V=*diri*           |

## Key generalizations (the paper's (32))

(a) The base V is transitive (dyadic), taking subject and object
    DPs in the active *meN-* form.
(b) *ber-* forms always take a subject DP but never a canonical
    object DP.
(c) The underlying object is always expressed lexically (as an
    NP or DP).
(d) The base subject can be the surface subject if the object
    is an incorporated NP. (The biconditional reading sometimes
    quoted is implied by (32a–c) jointly, not by (32d) on its own.)

## Anticausatives (§5)

Anticausatives (*ter-* forms) are outside the core 2×2 typology
but derive from the same mechanism applied to causer-unspecified
verb roots. They have a unique diagnostic profile: no *oleh*, no
rationale clauses, but YES *dengan sendiri=nya*.

## Cross-linguistic predictions

The core of argument suppression may underlie middles in other
languages, but language-specific argument realization strategies
(and their absence) determine which middle types surface.
-/

namespace BeaversUdayana2022

open Core.Verbs
open Fragments.Indonesian.VoiceSystem
open Minimalism (VoiceParams VoiceFlavor ExternalArgSemantics)
open Beavers2010
open Semantics.Verb.Affectedness (AffectednessDegree)
open Semantics.Events.ArgumentRealization
open Interfaces.SyntaxSemantics.VoiceSemantics
open Core.IntensionalLogic

-- ============================================================================
-- § 2: Indonesian ber- Middle Inventory
-- ============================================================================

/-- Dispositional/passive middle: *Mobil itu ber-jual dengan mudah.*
    'The car sells easily.' (the paper's (2b)) / *Mobil itu ber-jual
    kemarin.* 'The car sold yesterday.' (the paper's (7))

    Surface subject = base patient; agent suppressed with disjoint
    interpretation. Whether the reading is dispositional (generic) or
    passive (episodic) depends on temporal/modal context, not on the
    suppression operation itself. -/
def dispositionalMiddle : MiddleType :=
  { objRealization := .noIncorporation, suppressedVar := .disjoint }

/-- Natural reflexive: *Ali ber-dandan.* 'Ali dressed.' (the paper's (2a))

    Surface subject = base patient (formally); agent suppressed with
    coreferent interpretation. The root class (body care/grooming verbs)
    conventionally expects self-action, triggering coreferent reading. -/
def reflexiveMiddle : MiddleType :=
  { objRealization := .noIncorporation, suppressedVar := .coreferent }

/-- Incorporation middle (non-reflexive): *Orang itu ber-cuci=mata.*
    'The man washed his eyes.' (the paper's (18))

    Surface subject = base agent; patient = incorporated NP. The agent
    is the surface subject because incorporation satisfies the object's
    structural role, leaving the agent as the sole DP argument.
    The suppressed variable (patient) receives a disjoint interpretation. -/
def incorporationMiddle : MiddleType :=
  { objRealization := .incorporation, suppressedVar := .disjoint }

/-- Incorporation middle (reflexive): *Orang itu ber-jual=diri.*
    'The man sold himself.' (the paper's (26b))

    Incorporated *diri* 'self' triggers coreferent interpretation of
    the suppressed variable. -/
def incorporationReflexive : MiddleType :=
  { objRealization := .incorporation, suppressedVar := .coreferent }

-- ============================================================================
-- § 3: Core Generalizations (32a–d)
-- ============================================================================

/-- Which argument surfaces as subject depends on object realization.

    (32d): The base subject can be the surface subject IFF the object
    is an incorporated NP. When the object is a full DP, the patient
    surfaces as subject (agent suppressed). When the object is an
    incorporated NP, the agent surfaces as subject (patient incorporated).

    This is now also derived compositionally from `suppressArg` in § 5
    above: the Montague type of the VP after FA vs. incorporation
    determines which argument remains for the surface subject. -/
def agentSurfaces (m : MiddleType) : Bool := m.agentSurfaces

/-- Incorporation middles have the agent as surface subject. -/
theorem incorporation_agent_surfaces :
    agentSurfaces incorporationMiddle = true := rfl

/-- Non-incorporation middles have the patient as surface subject. -/
theorem noIncorporation_patient_surfaces :
    agentSurfaces dispositionalMiddle = false := rfl

theorem noIncorporation_reflexive_patient :
    agentSurfaces reflexiveMiddle = false := rfl

/-- Agent surfacing depends ONLY on object realization, not on
    suppressed variable interpretation. This captures the paper's
    key insight that the same ber- operation yields different surface
    argument structures through independent object realization. -/
theorem agent_surfacing_independent_of_reading
    (r₁ r₂ : SuppressedVarReading) :
    agentSurfaces ⟨.incorporation, r₁⟩ =
    agentSurfaces ⟨.incorporation, r₂⟩ := rfl

-- ============================================================================
-- § 4: Diagnostic Properties
-- ============================================================================

/-- Diagnostics that distinguish *ber-* middles from *di-* passives
    and *meN-* actives.

    - `licensesOleh`: can the agent be expressed via *oleh* 'by' PP?
    - `licensesRationale`: can a rationale clause (purpose *untuk* PRO V)
      be controlled by the implicit agent?
    - `licensesDenganSendiriNya`: is *dengan sendiri=nya* 'by itself'
      compatible?

    These are the key tests from §§2.1–2.4 and §5 of the paper. -/
structure MiddleDiagnostics where
  licensesOleh : Bool
  licensesRationale : Bool
  licensesDenganSendiriNya : Bool
  deriving DecidableEq, Repr

/-- *ber-* dispositional/passive middles: no *oleh*, no rationale clause,
    no *dengan sendiri=nya* (the paper's (11), (13), (10c)).

    The suppressed agent is syntactically inaccessible: it cannot be
    expressed as a by-phrase, cannot control rationale PRO, and since it
    is not the surface subject, *dengan sendiri=nya* is ruled out. -/
def dispPassiveDiag : MiddleDiagnostics :=
  { licensesOleh := false
  , licensesRationale := false
  , licensesDenganSendiriNya := false }

/-- *di-* passives: *oleh* OK, rationale clause OK (controlled by
    implicit causer), *dengan sendiri=nya* blocked.

    The implicit argument in *di-* passives is syntactically stronger
    (a weak pronoun *e*[-D]) than in *ber-* middles, licensing *oleh*
    and rationale control. -/
def diPassiveDiag : MiddleDiagnostics :=
  { licensesOleh := true
  , licensesRationale := true
  , licensesDenganSendiriNya := false }

/-- *ber-* reflexives: no *oleh*, rationale clause OK (controlled by
    surface subject = agent), *dengan sendiri=nya* OK (the paper's (17)). -/
def reflexiveDiag : MiddleDiagnostics :=
  { licensesOleh := false
  , licensesRationale := true
  , licensesDenganSendiriNya := true }

/-- *ber-* incorporation middles: no *oleh*, rationale clause OK
    (surface subject IS the agent), *dengan sendiri=nya* OK
    (the paper's (23)). -/
def incorporationDiag : MiddleDiagnostics :=
  { licensesOleh := false
  , licensesRationale := true
  , licensesDenganSendiriNya := true }

/-- Anticausative (*ter-*) middles: no *oleh*, no rationale clause,
    YES *dengan sendiri=nya* (the paper's §5, examples (67a–c)).

    This is a UNIQUE diagnostic profile: anticausatives differ from
    dispositional/passive middles (which block *dengan sendiri=nya*)
    and from reflexives (which license rationale clauses). The paper
    argues *dengan sendiri=nya* is licensed because anticausatives
    have causative variants, creating a paradigmatic expectation of
    a causer — the modifier introduces the information that this
    causer is not the surface subject. -/
def anticausativeDiag : MiddleDiagnostics :=
  { licensesOleh := false
  , licensesRationale := false
  , licensesDenganSendiriNya := true }

/-- The three-way diagnostic contrast: *di-* passives allow *oleh*;
    *ber-* dispositionals allow none; *ber-* reflexives/incorporation
    allow rationale + *dengan sendiri=nya* but not *oleh*. -/
theorem oleh_distinguishes_di_from_ber :
    diPassiveDiag.licensesOleh = true ∧
    dispPassiveDiag.licensesOleh = false ∧
    reflexiveDiag.licensesOleh = false ∧
    incorporationDiag.licensesOleh = false ∧
    anticausativeDiag.licensesOleh = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- *dengan sendiri=nya* is licensed when the event has a causer
    (whether the surface subject itself or a paradigmatic expectation
    from the verb's causative variant). It is blocked only for
    dispositional/passive middles and *di-* passives, where the
    implicit participant is not accessible as an effector.

    The licensing condition is NOT simply "agent surfaces as subject" —
    anticausatives license *dengan sendiri=nya* even though the agent
    does not surface. Rather, the condition involves the availability
    of a causer interpretation (from the causative paradigm). -/
theorem sendirinya_licensing :
    reflexiveDiag.licensesDenganSendiriNya = true ∧
    incorporationDiag.licensesDenganSendiriNya = true ∧
    anticausativeDiag.licensesDenganSendiriNya = true ∧
    dispPassiveDiag.licensesDenganSendiriNya = false ∧
    diPassiveDiag.licensesDenganSendiriNya = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Four of the five profiles are pairwise distinct. The exception:
    reflexive and incorporation middles share the same diagnostic
    fingerprint (*{¬oleh, rationale, sendirinya}*). The paper
    distinguishes them by ARGUMENT STRUCTURE (which DP surfaces as
    subject), not by these syntactic diagnostics. -/
theorem diag_profiles_mostly_distinct :
    dispPassiveDiag ≠ diPassiveDiag ∧
    dispPassiveDiag ≠ reflexiveDiag ∧
    dispPassiveDiag ≠ incorporationDiag ∧
    dispPassiveDiag ≠ anticausativeDiag ∧
    diPassiveDiag ≠ reflexiveDiag ∧
    diPassiveDiag ≠ incorporationDiag ∧
    diPassiveDiag ≠ anticausativeDiag ∧
    reflexiveDiag ≠ anticausativeDiag ∧
    incorporationDiag ≠ anticausativeDiag := by
  exact ⟨by decide, by decide, by decide, by decide,
         by decide, by decide, by decide, by decide, by decide⟩

/-- Reflexive and incorporation middles are diagnostically IDENTICAL —
    they are distinguished by argument structure (agent vs. patient
    as surface subject), not by oleh/rationale/sendirinya tests. -/
theorem reflexive_incorporation_same_diag :
    reflexiveDiag = incorporationDiag := rfl

-- ============================================================================
-- § 5: Compositional Derivation via VoiceSemantics
-- ============================================================================

section Compositional

/-! ### Grounding the 2×2 typology in Montague composition

    The four middle types arise from applying ONE operation (`suppressArg`)
    to VPs of different Montague types. The VP type is determined by
    independent argument realization (FA vs. incorporation), not by ber-.

    We prove this for an arbitrary model `m` and transitive verb `V`. -/

variable {m : Frame}
variable (V : m.Denot (.e ⇒ .e ⇒ .t))
variable (np : m.Denot (.e ⇒ .t))
variable (patient z agent : m.Entity)

/-- **Dispositional middle derivation** (the paper's (54)):
    FA saturates the object → VP has type `e ⇒ t` → ber- suppresses
    the remaining (agent) argument → result is type `t`.

    The patient (FA-applied argument) is the surface subject. -/
theorem dispositional_derivation :
    suppressArg z (V patient) = V patient z := rfl

/-- **Incorporation middle derivation** (the paper's (51)):
    Incorporation narrows but preserves the object → VP has type
    `e ⇒ e ⇒ t` → ber- suppresses the first (object) argument →
    result is type `e ⇒ t` → agent fills the remaining position.

    The agent is the surface subject. -/
theorem incorporation_derivation :
    suppressArg z (incorporate V np) agent =
    (V z agent ∧ np z) := rfl

/-- **Active voice derivation** (contrast):
    Active (meN-) applies the identity, preserving both arguments.
    The subject is the agent; the object is the patient. -/
theorem active_derivation :
    activeSem V patient agent = V patient agent := rfl

/-- The argument structure difference between dispositional and
    incorporation middles is a TYPE difference, not an operation
    difference. In both cases ber- = `suppressArg z`. -/
theorem operation_is_identical :
    -- Both use suppressArg:
    suppressArg z (V patient) = V patient z ∧
    suppressArg z (incorporate V np) agent = (V z agent ∧ np z) :=
  ⟨rfl, rfl⟩

/-- Agent surfaces as subject iff the VP retains both arguments
    (incorporation case). This is the paper's (32d), now derived from
    Montague composition rather than stipulated. -/
theorem agent_surfaces_iff_incorporation :
    -- After incorporation: result has type e ⇒ t, so agent fills it
    (fun a => suppressArg z (incorporate V np) a) =
    (fun a => V z a ∧ np z) := rfl

end Compositional

-- ============================================================================
-- § 6: Voice Parameter Bridge
-- ============================================================================

/-- *ber-*'s underspecification means it is compatible with the
    Minimalist Voice parameters of EVERY other Indonesian voice.
    This is the formal content of "generalized argument suppression":
    the morpheme doesn't commit to ±D or ±λx. -/
theorem ber_compatible_with_men :
    berParams.isCompatibleWith menParams = true := rfl

theorem ber_compatible_with_di :
    berParams.isCompatibleWith diParams = true := rfl

/-- *meN-* and *di-* are NOT compatible with each other —
    they differ on ±λx. This is why they are distinct voices,
    while *ber-* can behave like either. -/
theorem men_incompatible_with_di :
    menParams.isCompatibleWith diParams = false := rfl

-- ============================================================================
-- § 7: Bridge to Beavers 2010 (Affectedness Constraint)
-- ============================================================================

/-- **linglib bridge** (not formalized in the paper):

    Dispositional middles are restricted to change-of-state verbs.
    The paper notes (§2.1) that dispositional *ber-* forms "are only
    possible with verbs that describe change-of-state or at least
    some degree of affectedness."

    We formalize this by connecting @cite{beavers-2010}'s
    affectedness hierarchy to the middle typology: verbs licensing
    dispositional middles must have affectedness degree ≥ nonquantized.

    This independently connects to @cite{levin-1993}'s prediction
    that the middle alternation requires `changeOfState` (see
    `predictedAlternation` in Core/RootDimensions.lean) — the same
    verb class restriction viewed through different theoretical lenses. -/
def LicensesDispositionalMiddle (d : AffectednessDegree) : Prop :=
  AffectednessDegree.nonquantized ≤ d

instance (d : AffectednessDegree) : Decidable (LicensesDispositionalMiddle d) := by
  unfold LicensesDispositionalMiddle; infer_instance

/-- Change-of-state verbs (quantized/nonquantized) license dispositionals. -/
theorem cos_verbs_license_dispositional :
    LicensesDispositionalMiddle .quantized ∧
    LicensesDispositionalMiddle .nonquantized := ⟨by decide, by decide⟩

/-- Non-CoS verbs (potential/unspecified) do NOT license dispositionals. -/
theorem non_cos_block_dispositional :
    ¬ LicensesDispositionalMiddle .potential ∧
    ¬ LicensesDispositionalMiddle .unspecified := ⟨by decide, by decide⟩

/-- Bridge: Levin's middle alternation diagnostic and Beavers 2010's
    affectedness constraint make the same prediction. Verbs that
    participate in the middle alternation (i.e., have `changeOfState`)
    are exactly those whose patients are affected enough (≥ nonquantized)
    to license dispositional middles. -/
theorem levin_middle_requires_cos :
    MeaningComponents.predictedAlternation
      ⟨true, false, false, false, false, false⟩ .middle = true ∧   -- CoS → middle OK
    MeaningComponents.predictedAlternation
      ⟨false, true, true, false, false, false⟩ .middle = false     -- no CoS → no middle
    := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Cross-Linguistic Predictions
-- ============================================================================

/-- The paper predicts that which middle types surface in a language
    depends on its argument realization inventory. Languages lacking
    incorporation can only have the no-incorporation row of the
    typology (reflexives and dispositional/passive middles).

    This is a testable prediction: if a language has incorporation, it
    should (ceteris paribus) have incorporation middles. If it lacks
    incorporation, it should lack them. -/
def incorporationPredicted (hasIncorporation : Bool) (m : MiddleType) : Bool :=
  match m.objRealization with
  | .incorporation => hasIncorporation
  | .noIncorporation => true

/-- Indonesian has incorporation → all four types predicted. -/
theorem indonesian_all_types_predicted :
    incorporationPredicted true dispositionalMiddle = true ∧
    incorporationPredicted true reflexiveMiddle = true ∧
    incorporationPredicted true incorporationMiddle = true ∧
    incorporationPredicted true incorporationReflexive = true := ⟨rfl, rfl, rfl, rfl⟩

/-- A language without incorporation → incorporation middles blocked. -/
theorem no_incorporation_blocks_types :
    incorporationPredicted false incorporationMiddle = false ∧
    incorporationPredicted false incorporationReflexive = false := ⟨rfl, rfl⟩

/-- A language without incorporation → reflexive + dispositional still OK.
    This is the predicted pattern for Spanish *se* middles. -/
theorem no_incorporation_allows_core :
    incorporationPredicted false dispositionalMiddle = true ∧
    incorporationPredicted false reflexiveMiddle = true := ⟨rfl, rfl⟩

end BeaversUdayana2022
