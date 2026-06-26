/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.Case.Capabilities
import Linglib.Syntax.Minimalist.VerbalDecomposition
import Linglib.Syntax.Minimalist.Voice
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Applicative heads

Applicative heads introduce applied arguments (benefactives, goals, sources). Following
[pylkkanen-2008], a **high** applicative Merges with the event and relates the applied argument
to it; a **low** applicative Merges with the theme (recipient = transfer *to*, source = transfer
*from*). High applicatives need Voice to supply event semantics, so they are blocked under
semantically null Voice (middles, anticausatives); low applicatives are Voice-independent.

The high/low distinction is read off the Merge complement's category via the head function
`SO.outerCatC`, so the typology follows from attachment height by construction.

## Main definitions

- `ApplType`, `ApplType.complement`: the high/low typology and the complement it Merges with.
- `ApplType.RequiresEventSemantics`, `IsLow`: structural predicates read off the complement.
- `ApplHead.Licensed`: licensing of an applicative by a Voice head.
- `ApplHead.SpecCanBearCase`: case-based blocking of SpecApplP ([wood-2015]).
- `ApplType.toSO`: the applicative realized as an actual `SO.merge`.

## References

[cuervo-2003], [pylkkanen-2008], [wood-2015]
-/

namespace Minimalist

/-! ### Applicative type and its Merge complement -/

/-- High vs low applicatives ([pylkkanen-2008]): high relates to the event, low to the theme. -/
inductive ApplType where
  /-- Above VP: relates the applied argument to the event. -/
  | high
  /-- Below VP: transfer-of-possession *to* the applied argument. -/
  | lowRecipient
  /-- Below VP: transfer-of-possession *from* the applied argument. -/
  | lowSource
  deriving DecidableEq, Repr

/-- The category an applicative Merges with: the event `v` (high) or the theme `D` (low). -/
def ApplType.complement : ApplType → Cat
  | .high         => .v
  | .lowRecipient => .D
  | .lowSource    => .D

/-- The complement constituent an applicative Merges with — a leaf headed by `a.complement`. -/
def ApplType.complementSO (a : ApplType) (id : Nat := 0) : SO :=
  SO.mkLeaf a.complement [] id

/-- The Merge complement's categorial features, read via the §1.13 head function `SO.outerCatC`. -/
def ApplType.complementFeatures (a : ApplType) : CatFeatures :=
  a.complementSO.outerCatC.elim ⟨false, false⟩ catFeatures

/-- `a.IsLow`: the applicative Merges with a nominal (theme) complement. -/
def ApplType.IsLow (a : ApplType) : Prop := a.complementFeatures.plusN = true

instance : DecidablePred ApplType.IsLow := fun _ => inferInstanceAs (Decidable (_ = true))

/-- `a.RequiresEventSemantics`: `a` Merges with the verbal (event) complement. -/
def ApplType.RequiresEventSemantics (a : ApplType) : Prop := a.complementFeatures.plusV = true

instance : DecidablePred ApplType.RequiresEventSemantics :=
  fun _ => inferInstanceAs (Decidable (_ = true))

/-- `a.RequiresThemeInComplement`: low applicatives need an unsaturated theme in the complement. -/
def ApplType.RequiresThemeInComplement (a : ApplType) : Prop := a.IsLow

instance : DecidablePred ApplType.RequiresThemeInComplement :=
  fun a => inferInstanceAs (Decidable a.IsLow)

/-! ### Semantic relations -/

/-- The semantic relation an applicative head contributes ([pylkkanen-2008]). -/
inductive ApplSemantics where
  /-- Individual–event relation (high Appl). -/
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

/-- An applicative head: its type, and whether it assigns dative case to its specifier. -/
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

/-- `appl.Licensed voice`: if `appl` requires event semantics, `voice` supplies them. -/
def ApplHead.Licensed (appl : ApplHead) (voice : VoiceHead) : Prop :=
  appl.applType.RequiresEventSemantics → voice.HasSemantics

instance (appl : ApplHead) (voice : VoiceHead) : Decidable (appl.Licensed voice) :=
  inferInstanceAs (Decidable (_ → _))

/-! ### Licensing predictions -/

variable (v : VoiceHead)

/-- High applicatives require event semantics. -/
theorem high_requires_event : ApplType.RequiresEventSemantics .high := by decide

/-- Low applicatives do not require event semantics. -/
theorem low_no_event_requirement :
    ¬ ApplType.RequiresEventSemantics .lowRecipient ∧
    ¬ ApplType.RequiresEventSemantics .lowSource := by decide

/-- Low applicatives are licensed under any Voice head ([pylkkanen-2008]). -/
theorem low_licensed_with_any :
    applLowRecipient.Licensed v ∧ applLowSource.Licensed v :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- θ-assigning Voice licenses high applicatives (θ-assignment entails event semantics). -/
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

/-- `appl.SpecCanBearCase x`: if `appl` assigns dative, `x` must bear case ([wood-2015]). -/
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

/-- An applicative as an actual Merge: the `Appl` head `SO.merge`d with `a.complementSO`. -/
noncomputable def ApplType.toSO (a : ApplType) (applId complId : Nat := 0) : SO :=
  SO.merge (SO.mkLeaf .Appl [a.complement] applId) (a.complementSO complId)

end Minimalist
