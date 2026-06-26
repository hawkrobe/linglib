import Linglib.Features.Case.Capabilities
import Linglib.Syntax.Minimalist.VerbalDecomposition
import Linglib.Syntax.Minimalist.Voice
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Applicative Heads
[cuervo-2003] [pylkkanen-2008] [wood-2015]

Applicative heads introduce applied arguments (benefactives, goals, sources) into the
verbal structure. The high/low distinction determines whether the applied argument relates
to the event as a whole (high) or to the theme (low); low applicatives further split into
**recipient** (transfer *to*) and **source** (transfer *from*), following [pylkkanen-2008].

## Semantic denotations ([pylkkanen-2008])

- **High Appl**: `λx.λe. Appl(e, x)` — relates an individual to the event
  (ethical datives: "he ate food on-me").
- **Low Appl (recipient)**: `λx.λy. HAVE(x, y)` — transfer TO (English DOC: "I sent him a
  letter").
- **Low Appl (source)**: `λx.λy. HAVE-FROM(y, x)` — transfer FROM (possessive datives:
  "they broke his arm").

## High/low asymmetry ([pylkkanen-2008], [schaefer-2008])

High applicatives require Voice with event semantics; low applicatives are independent of
Voice. This predicts high Appl is blocked when Voice is semantically null (middles,
anticausatives). [wood-2015] argues that Icelandic lacks true high applicatives entirely;
the interaction modeled here follows [pylkkanen-2008]'s cross-linguistic typology.
-/

namespace Minimalist

/-! ### Applicative type and its Merge complement -/

/-- High vs low applicatives ([pylkkanen-2008]).

    - **High**: above VP, relates the applied argument to the event
      (benefactive: Chaga "he ate food for wife").
    - **Low recipient**: below VP, transfer-of-possession *to* the applied argument
      (English DOC: "I sent him a letter").
    - **Low source**: below VP, transfer-of-possession *from* the applied argument
      (Korean, Hebrew possessor datives, Japanese adversity passives). -/
inductive ApplType where
  /-- Above VP: relates the applied argument to the event. -/
  | high
  /-- Below VP: transfer-of-possession *to* the applied argument. -/
  | lowRecipient
  /-- Below VP: transfer-of-possession *from* the applied argument. -/
  | lowSource
  deriving DecidableEq, Repr

/-- The category of the constituent an applicative Merges with — its complement.
    This **is** [pylkkanen-2008]'s high/low distinction (Merge position): a high applicative
    merges with the event projection (the `v`P, `[+V]`); a low applicative merges with the
    theme (a `D`P, `[+N]`). The structural predicates below are read off this complement —
    Pylkkänen's typology *follows from* attachment height. -/
def ApplType.complement : ApplType → Cat
  | .high         => .v    -- the event (vP)
  | .lowRecipient => .D    -- the theme (DP)
  | .lowSource    => .D    -- the theme (DP)

/-- The complement an applicative Merges with, as an actual `SO` constituent: a leaf headed
    by `a.complement` (the event for high, the theme for low). The Merge itself is
    `ApplType.toSO`, whose right child is this. -/
def ApplType.complementSO (a : ApplType) (id : Nat := 0) : SO :=
  SO.mkLeaf a.complement [] id

/-- The categorial features of the actual Merge complement, **read off the `SO` via the
    §1.13 head function** `SO.outerCatC`. The high/low typology below is this read, by
    construction — Pylkkänen's attachment claim is the definition, not a `Cat` table and not
    a separate predicate bridged to the structure. -/
def ApplType.complementFeatures (a : ApplType) : CatFeatures :=
  a.complementSO.outerCatC.elim ⟨false, false⟩ catFeatures

/-- Low iff the applicative Merges with a nominal (theme) complement. -/
def ApplType.IsLow (a : ApplType) : Prop := a.complementFeatures.plusN = true

instance : DecidablePred ApplType.IsLow := fun _ => inferInstanceAs (Decidable (_ = true))

/-- Requires event semantics from Voice iff the applicative Merges with the verbal (event)
    complement — i.e. iff it is high. A low applicative Merges with the theme and is
    independent of Voice. -/
def ApplType.RequiresEventSemantics (a : ApplType) : Prop := a.complementFeatures.plusV = true

instance : DecidablePred ApplType.RequiresEventSemantics :=
  fun _ => inferInstanceAs (Decidable (_ = true))

/-- Requires an unsaturated theme in its complement iff it is low. This drives
    [pylkkanen-2008]'s transitivity restriction: low applicatives cannot combine with
    unergatives, whose VPs lack an unsaturated theme — combining the two would identify the
    applied argument as both agent and theme of one event, a contradiction. -/
def ApplType.RequiresThemeInComplement (a : ApplType) : Prop := a.IsLow

instance : DecidablePred ApplType.RequiresThemeInComplement :=
  fun a => inferInstanceAs (Decidable a.IsLow)

/-! ### Semantic relations -/

/-- The semantic relation an applicative head contributes ([pylkkanen-2008]).

    - `eventRelation`: `λx.λe. R(e, x)` — relates an individual to the event (high Appl).
    - `possessionTo`: `λx.λy. HAVE(x, y)` — transfer-to (low recipient).
    - `possessionFrom`: `λx.λy. HAVE-FROM(y, x)` — transfer-from (low source). -/
inductive ApplSemantics where
  /-- Individual–event relation (high Appl: ethical dative, benefactive). -/
  | eventRelation
  /-- `HAVE` relation (low recipient). -/
  | possessionTo
  /-- `HAVE-FROM` relation (low source). -/
  | possessionFrom
  deriving DecidableEq, Repr

/-- The semantic contribution of each applicative type. -/
def ApplType.semantics : ApplType → ApplSemantics
  | .high         => .eventRelation
  | .lowRecipient => .possessionTo
  | .lowSource    => .possessionFrom

/-! ### The applicative head -/

/-- An applicative head: its type, plus whether it assigns dative case to its specifier. -/
structure ApplHead where
  /-- High or low (recipient/source). -/
  applType : ApplType
  /-- Whether the applied argument receives dative case. -/
  assignsDative : Bool := true
  deriving DecidableEq, Repr

/-- Canonical high applicative (ethical dative). -/
def applHigh : ApplHead := { applType := .high }

/-- Canonical low recipient applicative (DOC, possessive dative). -/
def applLowRecipient : ApplHead := { applType := .lowRecipient }

/-- Canonical low source applicative. -/
def applLowSource : ApplHead := { applType := .lowSource }

/-! ### Voice–applicative licensing ([pylkkanen-2008], [schaefer-2008]) -/

/-- An applicative is **licensed** by a Voice head iff, when it requires event semantics
    (high Appl), that Voice supplies them. Low applicatives relate to the theme and so are
    licensed under any Voice; high applicatives are blocked when Voice is semantically null
    (middles, anticausatives). -/
def ApplHead.Licensed (appl : ApplHead) (voice : VoiceHead) : Prop :=
  appl.applType.RequiresEventSemantics → voice.HasSemantics

instance (appl : ApplHead) (voice : VoiceHead) : Decidable (appl.Licensed voice) :=
  inferInstanceAs (Decidable (_ → _))

/-! ### Licensing predictions -/

variable (v : VoiceHead)

/-- High applicatives require event semantics; low applicatives do not. -/
theorem high_requires_event : ApplType.RequiresEventSemantics .high := by decide

theorem low_no_event_requirement :
    ¬ ApplType.RequiresEventSemantics .lowRecipient ∧
    ¬ ApplType.RequiresEventSemantics .lowSource := by decide

/-- Low applicatives are licensed under any Voice head ([pylkkanen-2008]). -/
theorem low_licensed_with_any :
    applLowRecipient.Licensed v ∧ applLowSource.Licensed v :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- θ-assigning Voice licenses high applicatives: θ-assignment entails event semantics
    (`VoiceHead.AssignsTheta.hasSemantics`), which is all high Appl requires. -/
theorem high_licensed_of_assignsTheta (h : v.AssignsTheta) : applHigh.Licensed v :=
  fun _ => h.hasSemantics

/-- Ethical datives (high Appl) are licensed with agentive Voice. -/
theorem ethical_dative_with_agent : applHigh.Licensed voiceAgent := by decide

/-- High Appl is blocked with middle Voice (no event semantics) ([pylkkanen-2008]). -/
theorem ethical_dative_blocked_in_middle : ¬ applHigh.Licensed voiceMiddle := by decide

/-- Possessive datives (low Appl) survive in middles. -/
theorem possessive_dative_survives_middle : applLowRecipient.Licensed voiceMiddle := by decide

/-- Possessive datives survive in anticausatives. -/
theorem possessive_dative_survives_anticausative :
    applLowRecipient.Licensed voiceAnticausative := by decide

/-- The asymmetry: ethical blocked but possessive survives in middles. -/
theorem ethical_possessive_middle_asymmetry :
    ¬ applHigh.Licensed voiceMiddle ∧ applLowRecipient.Licensed voiceMiddle := by decide

/-! ### Case-based blocking of SpecApplP ([wood-2015]) -/

/-- An element can occupy SpecApplP iff, when Appl assigns dative, it bears case.
    [wood-2015]: Appl assigns dative to its specifier, so only case-bearing elements
    (`caseOf ≠ none`) qualify — the caseless Icelandic clitic -st is blocked from SpecApplP
    though it can occupy SpecVoiceP / Spec-p, where no case is assigned to the specifier. -/
def ApplHead.SpecCanBearCase {α : Type*} [HasCase α] (appl : ApplHead) (x : α) : Prop :=
  appl.assignsDative = true → (HasCase.caseOf x).isSome = true

instance {α : Type*} [HasCase α] (appl : ApplHead) (x : α) :
    Decidable (appl.SpecCanBearCase x) := inferInstanceAs (Decidable (_ → _))

/-- The caseless clitic -st (`caseOf = none`) cannot occupy SpecApplP ([wood-2015]). -/
theorem caseless_blocked_in_specAppl :
    ¬ applLowRecipient.SpecCanBearCase (none : Option Case) := by decide

/-- A case-bearing DP can occupy SpecApplP. -/
theorem caseful_ok_in_specAppl :
    applLowRecipient.SpecCanBearCase (some Case.dat) := by decide

/-! ### The applicative as a Merge -/

/-- An applicative of type `a` realized as an actual Merge: the `Appl` head (selecting
    `a.complement`) `SO.merge`d with its complement. Its right child is `a.complementSO`,
    the very constituent whose head category `RequiresEventSemantics`/`IsLow` read off — so
    the typology *is* a property of this derivation, by construction. -/
noncomputable def ApplType.toSO (a : ApplType) (applId complId : Nat := 0) : SO :=
  SO.merge (SO.mkLeaf .Appl [a.complement] applId) (a.complementSO complId)

end Minimalist
