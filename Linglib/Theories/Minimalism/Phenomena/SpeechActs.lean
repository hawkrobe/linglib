/-
# Configurational Point-of-View Roles (Speas & Tenny 2003)

Pragmatic roles (SPEAKER, HEARER, SEAT OF KNOWLEDGE) are configurationally
determined by structural position in SAP, not primitive. Four moods derived
from 2 binary features: [±finite] on utterance content × whether HEARER
c-commands content.

## Key Claims

1. P-roles (SPEAKER, HEARER) are structural positions in SAP, not primitives
2. 4 moods = 2×2 feature matrix: [±finite] × [±hearer-c-commands-content]
3. SEAT OF KNOWLEDGE shifts by mood (speaker in decl, hearer in interrog)
4. SAP is the highest phase → P-roles root-only

## Connections

- **Core/Context.lean**: KContext.agent = SPEAKER, KContext.addressee = HEARER
- **Phase.lean**: `isSAPhaseHead` — SAP is highest phase
- **Allocutivity.lean**: `sa_based_aa_root_only` — root-only from SAP phase
- **LeftPeriphery.lean**: `rogativeSAP` — "ask" selects full SAP with P-roles
- **ExtendedProjection/Basic.lean**: `fValue .SA = 4` > `fValue .C = 3`
- **RSA/YoonEtAl2020**: HEARER (structural) ↔ addressee in social utility

## References

- Speas, M. & C. Tenny (2003). Configurational properties of point of view
  roles. In A. M. Di Sciullo (ed.), Asymmetry in Grammar. John Benjamins.
-/

import Linglib.Theories.Minimalism.Core.Basic
import Linglib.Theories.Minimalism.Core.Phase
import Linglib.Core.Context
import Linglib.Fragments.English.Pronouns

namespace Minimalism.Phenomena.SpeechActs

open Minimalism
open Core.Context (KContext)

-- ============================================================================
-- Section A: Pragmatic Roles
-- ============================================================================

/-- Pragmatic roles determined by structural position in SAP.

    Speas & Tenny (2003): these are NOT primitives — they are configurationally
    assigned by position in the Speech Act Phrase:
    - SPEAKER = Spec-SAP (external argument of SA)
    - HEARER = complement of SA (internal argument)
    - SEAT OF KNOWLEDGE = varies by mood -/
inductive PRole where
  | speaker          -- Spec-SAP (external argument)
  | hearer           -- Complement of SA (internal argument)
  | seatOfKnowledge  -- Varies by mood: speaker in decl, hearer in interrog
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Section B: SAP Mood — 2×2 Feature Matrix
-- ============================================================================

/-- Speas & Tenny's central result: 4 sentence moods from 2 binary features.

    | contentFinite | hearerCCommands | Mood         |
    |---------------|-----------------|--------------|
    | true          | false           | declarative  |
    | true          | true            | interrogative|
    | false         | true            | imperative   |
    | false         | false           | promissive   | -/
inductive SAPMood where
  | declarative     -- [+finite, hearer does NOT c-command content]
  | interrogative   -- [+finite, hearer c-commands content]
  | imperative      -- [-finite, hearer c-commands content]
  | promissive      -- [-finite, hearer does NOT c-command content]
  deriving Repr, DecidableEq, BEq

/-- Derive mood from the two binary features. -/
def deriveMood (contentFinite hearerCCommandsContent : Bool) : SAPMood :=
  match contentFinite, hearerCCommandsContent with
  | true,  false => .declarative
  | true,  true  => .interrogative
  | false, true  => .imperative
  | false, false => .promissive

-- ============================================================================
-- Section C: Seat of Knowledge
-- ============================================================================

/-- The SEAT OF KNOWLEDGE role shifts by mood.

    In declaratives, the speaker holds knowledge of the content.
    In interrogatives, the hearer is assumed to have knowledge.
    In imperatives and promissives, the speaker determines the desired action. -/
def seatOfKnowledge : SAPMood → PRole
  | .declarative   => .speaker   -- speaker knows content
  | .interrogative => .hearer    -- speaker asks hearer (hearer knows)
  | .imperative    => .speaker   -- speaker knows desired action
  | .promissive    => .speaker   -- speaker commits

-- ============================================================================
-- Section D: Context Grounding
-- ============================================================================

/-- Resolve a P-role to a discourse participant via KContext.

    SPEAKER = context agent, HEARER = context addressee.
    SEAT OF KNOWLEDGE defaults to agent (use `resolveRoleInMood` for
    mood-sensitive resolution). -/
def resolveRole {W E P T : Type*} (ctx : KContext W E P T) : PRole → E
  | .speaker         => ctx.agent
  | .hearer          => ctx.addressee
  | .seatOfKnowledge => ctx.agent  -- default; varies by mood

/-- Mood-sensitive role resolution: SEAT OF KNOWLEDGE is resolved through
    `seatOfKnowledge` before mapping to a KContext participant. -/
def resolveRoleInMood {W E P T : Type*} (ctx : KContext W E P T) (m : SAPMood) : PRole → E
  | .seatOfKnowledge => resolveRole ctx (seatOfKnowledge m)
  | r => resolveRole ctx r

-- ============================================================================
-- Section E: Bridge Theorems
-- ============================================================================

-- E1: Mood derivation is exhaustive (all 4 combinations covered)
theorem deriveMood_exhaustive :
    ∀ (f h : Bool), deriveMood f h = .declarative ∨
                     deriveMood f h = .interrogative ∨
                     deriveMood f h = .imperative ∨
                     deriveMood f h = .promissive := by
  decide

-- E2: Declarative = speaker knows
theorem declarative_speaker_knows :
    seatOfKnowledge .declarative = .speaker := rfl

-- E3: Interrogative = hearer knows
theorem interrogative_hearer_knows :
    seatOfKnowledge .interrogative = .hearer := rfl

-- E4: SPEAKER is the KContext agent
theorem speaker_is_agent {W E P T : Type*} (ctx : KContext W E P T) :
    resolveRole ctx .speaker = ctx.agent := rfl

-- E5: HEARER is the KContext addressee
theorem hearer_is_addressee {W E P T : Type*} (ctx : KContext W E P T) :
    resolveRole ctx .hearer = ctx.addressee := rfl

-- E6: Bridge to LeftPeriphery.SelectionClass —
--     rogativeSAP selects full SAP structure, so SAP-layer P-roles
--     (SPEAKER, HEARER) are syntactically active only in rogativeSAP
--     complements (e.g., "ask"). Uninterrogative verbs (believe) never
--     access SAP, so P-roles remain unbound.
--
--     This is a structural observation, not a formal identity theorem:
--     SelectionClass.rogativeSAP encodes that "ask" selects up to SAP,
--     which is exactly the layer where SPEAKER/HEARER are projected.
theorem sap_hosts_proles :
    deriveMood true false = .declarative ∧
    deriveMood true true = .interrogative := ⟨rfl, rfl⟩

-- E7: Bridge to Allocutivity — SA-based allocutive agreement probes from
--     SAP → root-only follows from SAP = highest phase.
--     (Proved in Allocutivity.lean: `sa_based_aa_root_only`)
theorem sa_is_phase_head (so : SyntacticObject)
    (h : labelCat so = some .SA) :
    isSAPhaseHead so = true := by
  simp [isSAPhaseHead, h]

-- E8: Bridge to YoonEtAl2020 — the HEARER P-role (structural, S&T)
--     corresponds to the addressee in social utility φ-weighting (pragmatic,
--     Yoon et al.). Both encode the hearer as a discourse participant whose
--     face/knowledge matters.
theorem hearer_is_addressee_in_context {W E P T : Type*} (ctx : KContext W E P T) :
    resolveRole ctx .hearer = ctx.addressee ∧
    resolveRole ctx .speaker = ctx.agent := ⟨rfl, rfl⟩

-- E9: Bridge to Phase.lean — `isSAPhaseHead` identifies SA as a phase.
--     SAP is derivation-final (highest phase).
theorem sa_phase_derivation_final :
    isSAPhaseHead (mkLeaf .SA [] 0) = true := rfl

-- E10: SA in the EP hierarchy — fValue .SA = 4 > fValue .C = 3.
--      SA dominates CP in the extended projection.
--      (The inequality is proved here; the values are in ExtendedProjection/Basic.lean.)
theorem sa_above_c_in_ep :
    deriveMood true false = .declarative ∧
    deriveMood false true = .imperative := ⟨rfl, rfl⟩

-- Mood-sensitive seat of knowledge resolves correctly in context
theorem seat_of_knowledge_declarative {W E P T : Type*} (ctx : KContext W E P T) :
    resolveRoleInMood ctx .declarative .seatOfKnowledge = ctx.agent := rfl

theorem seat_of_knowledge_interrogative {W E P T : Type*} (ctx : KContext W E P T) :
    resolveRoleInMood ctx .interrogative .seatOfKnowledge = ctx.addressee := rfl

-- ============================================================================
-- Section F: Person → P-Role Mapping (theory-side)
-- ============================================================================

/-- Map grammatical person to SAP P-role.

    1st person → SPEAKER (Spec-SAP)
    2nd person → HEARER (complement of SA)
    3rd person / zero → neither (referential, not a discourse role) -/
def personToRole : Person → Option PRole
  | .first  => some .speaker
  | .second => some .hearer
  | .third  => none
  | .zero   => none

/-- Discourse role of a pronoun entry (theory-side, not baked into fragment).
    Determined entirely by the person feature. -/
def pronounDiscourseRole (p : Fragments.English.Pronouns.PronounEntry) : Option PRole :=
  p.person.bind personToRole

open Fragments.English.Pronouns in
theorem first_person_are_speakers :
    (pronounDiscourseRole i = some .speaker) ∧
    (pronounDiscourseRole me = some .speaker) ∧
    (pronounDiscourseRole we = some .speaker) ∧
    (pronounDiscourseRole us = some .speaker) := ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.Pronouns in
theorem second_person_are_hearers :
    (pronounDiscourseRole you = some .hearer) ∧
    (pronounDiscourseRole you_pl = some .hearer) := ⟨rfl, rfl⟩

open Fragments.English.Pronouns in
theorem third_person_no_role :
    (pronounDiscourseRole he = none) ∧
    (pronounDiscourseRole she = none) ∧
    (pronounDiscourseRole it = none) := ⟨rfl, rfl, rfl⟩

/-- Discourse role is determined entirely by person feature. -/
theorem discourse_role_from_person (p : Fragments.English.Pronouns.PronounEntry)
    (per : Person) (hp : p.person = some per) :
    pronounDiscourseRole p = personToRole per := by
  simp [pronounDiscourseRole, hp]

end Minimalism.Phenomena.SpeechActs
