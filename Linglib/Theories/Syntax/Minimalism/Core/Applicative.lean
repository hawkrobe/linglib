import Linglib.Theories.Syntax.Minimalism.Core.VerbalDecomposition
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Applicative Heads
@cite{cuervo-2003} @cite{pylkknen-2008} @cite{wood-2015}

Applicative heads introduce applied arguments (benefactives, goals,
sources) into the verbal structure. The high/low distinction determines
whether the applied argument relates to the event as a whole (high)
or to the theme (low).

Low applicatives further split into **recipient** (transfer *to*) and
**source** (transfer *from*), following @cite{pylkknen-2008} Table 1.1.

## Semantic Denotations (@cite{pylkknen-2008})

- **High Appl**: λx.λe. Appl(e, x) — relates individual to event
  (ethical datives: "he ate food on-me")
- **Low Appl (recipient)**: λx.λy. HAVE(x, y) — transfer TO
  (English DOC: "I sent him a letter")
- **Low Appl (source)**: λx.λy. HAVE-FROM(y, x) — transfer FROM
  (possessive datives: "they broke his arm")

## High/Low Asymmetry (@cite{pylkknen-2008}, @cite{schaefer-2008})

High applicatives require Voice with event semantics; low applicatives
are independent of Voice. This predicts high Appl is blocked when
Voice is semantically null (middles, anticausatives).

Note: @cite{wood-2015} Ch. 5 argues that Icelandic lacks true high
applicatives entirely. The high/low interaction modeled here follows
the cross-linguistic typology of @cite{pylkknen-2008}.
-/

namespace Minimalism

/-- High vs low applicatives (@cite{pylkknen-2008}, Table 1.1).

    - **High**: Above VP, relates applied argument to the event
      (benefactive: Chaga "he ate food for wife")
    - **Low recipient**: Below VP, transfer-of-possession *to* the
      applied argument (English DOC: "I sent him a letter")
    - **Low source**: Below VP, transfer-of-possession *from* the
      applied argument (Korean, Hebrew possessor datives, Japanese
      adversity passives) -/
inductive ApplType where
  | high          -- Above VP: individual-event relation (@cite{pylkknen-2008})
  | lowRecipient  -- Below VP: transfer TO applied arg (@cite{pylkknen-2008})
  | lowSource     -- Below VP: transfer FROM applied arg (@cite{pylkknen-2008} §2.2, §2.3)
  deriving DecidableEq, Repr

/-- Is this a low applicative (either recipient or source)? -/
def ApplType.isLow : ApplType → Bool
  | .lowRecipient => true
  | .lowSource    => true
  | .high         => false

-- ============================================================================
-- § 2: Semantic Relations
-- ============================================================================

/-- The semantic relation an applicative head contributes.

    - `eventRelation`: λx.λe. R(e, x) — relates individual to event (high Appl)
    - `possessionTo`: λx.λy. HAVE(x, y) — transfer-to (low recipient)
    - `possessionFrom`: λx.λy. HAVE-FROM(y, x) — transfer-from (low source) -/
inductive ApplSemantics where
  | eventRelation   -- High: individual-event (ethical dative, benefactive)
  | possessionTo    -- Low recipient: HAVE relation
  | possessionFrom  -- Low source: HAVE-FROM relation
  deriving DecidableEq, Repr

/-- Map each applicative type to its semantic contribution. -/
def ApplType.semantics : ApplType → ApplSemantics
  | .high         => .eventRelation
  | .lowRecipient => .possessionTo
  | .lowSource    => .possessionFrom

/-- Does this applicative type require event-level semantics from Voice?
    High applicatives relate to the event, so they need Voice to contribute
    event semantics. Low applicatives relate to the theme and are
    independent of Voice. -/
def ApplType.requiresEventSemantics : ApplType → Bool
  | .high         => true
  | .lowRecipient => false
  | .lowSource    => false

-- ============================================================================
-- § 3: Applicative Head Structure
-- ============================================================================

/-- An applicative head with its type and properties. -/
structure ApplHead where
  /-- High or low (recipient/source) -/
  applType : ApplType
  /-- Does the applied argument get dative case? -/
  assignsDative : Bool := true
  deriving DecidableEq, Repr

/-- Canonical high applicative (ethical dative). -/
def applHigh : ApplHead :=
  { applType := .high }

/-- Canonical low recipient applicative (DOC, possessive dative). -/
def applLowRecipient : ApplHead :=
  { applType := .lowRecipient }

/-- Canonical low source applicative. -/
def applLowSource : ApplHead :=
  { applType := .lowSource }

-- ============================================================================
-- § 4: Voice–Applicative Interaction (@cite{pylkknen-2008}, @cite{schaefer-2008})
-- ============================================================================

/-- Is this applicative licensed in the context of a given Voice head?

    High applicatives require Voice with event semantics; when Voice is
    semantically null (middles, anticausatives), high Appl is blocked.
    Low applicatives relate to the theme and are always licensed
    (@cite{pylkknen-2008}). -/
def ApplHead.licensedWith (appl : ApplHead) (voice : VoiceHead) : Bool :=
  if appl.applType.requiresEventSemantics then voice.hasSemantics
  else true

-- ============================================================================
-- § 5: Verification Theorems
-- ============================================================================

/-- High applicatives require event semantics. -/
theorem high_requires_event :
    ApplType.requiresEventSemantics .high = true := rfl

/-- Low applicatives do not require event semantics. -/
theorem low_no_event_requirement :
    ApplType.requiresEventSemantics .lowRecipient = false ∧
    ApplType.requiresEventSemantics .lowSource = false := ⟨rfl, rfl⟩

/-- Ethical datives (high Appl) are licensed with agentive Voice. -/
theorem ethical_dative_with_agent :
    applHigh.licensedWith voiceAgent = true := rfl

/-- High Appl is BLOCKED with middle Voice (no event semantics)
    (@cite{pylkknen-2008}). -/
theorem ethical_dative_blocked_in_middle :
    applHigh.licensedWith voiceMiddle = false := rfl

/-- Possessive datives (low Appl) survive in middles. -/
theorem possessive_dative_survives_middle :
    applLowRecipient.licensedWith voiceMiddle = true := rfl

/-- Possessive datives survive in anticausatives. -/
theorem possessive_dative_survives_anticausative :
    applLowRecipient.licensedWith voiceAnticausative = true := rfl

/-- The asymmetry: ethical blocked but possessive survives in middles. -/
theorem ethical_possessive_middle_asymmetry :
    applHigh.licensedWith voiceMiddle = false ∧
    applLowRecipient.licensedWith voiceMiddle = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Case-Based Blocking of SpecApplP (@cite{wood-2015} Ch. 5, §5.3.2)
-- ============================================================================

/-- Can a given element merge in SpecApplP?

    @cite{wood-2015} Ch. 5 (§5.3.2): Appl assigns **dative case** to its
    specifier. Therefore only elements that can bear case can merge
    in SpecApplP. The Icelandic clitic -st lacks case features and
    is thus blocked from SpecApplP, even though it can merge in
    SpecVoiceP and SpecpP (where no case is assigned to the specifier). -/
def ApplHead.specCanBearCase (appl : ApplHead) (bearerHasCase : Bool) : Bool :=
  if appl.assignsDative then bearerHasCase
  else true

/-- -st (caseless) cannot merge in SpecApplP (@cite{wood-2015} §5.3.2). -/
theorem caseless_blocked_in_specAppl :
    applLowRecipient.specCanBearCase false = false := rfl

/-- A case-bearing DP CAN merge in SpecApplP. -/
theorem caseful_ok_in_specAppl :
    applLowRecipient.specCanBearCase true = true := rfl

end Minimalism
