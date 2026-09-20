/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Case.Basic
import Linglib.Syntax.Minimalist.Verbal.Decomposition
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.FunctionalSequence
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Applicative heads

This file defines applicative heads, which introduce applied arguments such as benefactives,
goals and sources. Pylkkänen distinguishes a high applicative, which Merges with the event and
relates the applied argument to it, from a low applicative, which Merges with the theme and
relates the applied argument to it by transfer to or from it. A high applicative needs Voice to
supply event semantics, so it is blocked under a semantically null Voice, in middles and
anticausatives, whereas a low applicative is independent of Voice. The high and low types are
read off the category of the Merge complement through the head function
`SyntacticObject.outerCatC`, so the typology follows from attachment height by construction.

## Main definitions

* `ApplType`, `ApplType.complement`: the high and low types and the complement each Merges with.
* `ApplType.RequiresEventSemantics`, `ApplType.IsLow`: structural predicates read off the
  complement.
* `ApplHead.Licensed`: licensing of an applicative by a Voice head.
* `ApplHead.SpecCanBearCase`: case-based blocking of the applicative's specifier.

## References

* [pylkkanen-2008]
* [cuervo-2003]
* [wood-2015]
-/

namespace Minimalist

open SyntacticObject

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

/-- The category an applicative Merges with, the event `v` for a high one and the theme `D` for a
low one. -/
def ApplType.complement : ApplType → Cat
  | .high         => .v
  | .lowRecipient => .D
  | .lowSource    => .D

/-- The complement constituent an applicative Merges with — a leaf headed by `a.complement`. -/
def ApplType.complementSO (a : ApplType) : SyntacticObject := mkLeaf a.complement [] 0

/-- The Merge complement's categorial features, read via the §1.13 head function
`SyntacticObject.outerCatC`. -/
def ApplType.complementFeatures (a : ApplType) : CatFeatures :=
  a.complementSO.outerCatC.elim ⟨false, false⟩ Cat.features

/-- `a.IsLow` holds when the applicative Merges with a nominal theme complement. -/
def ApplType.IsLow (a : ApplType) : Prop := a.complementFeatures.plusN = true

instance : DecidablePred ApplType.IsLow := fun _ => inferInstanceAs (Decidable (_ = true))

/-- `a.RequiresEventSemantics` holds when `a` Merges with the verbal event complement. -/
def ApplType.RequiresEventSemantics (a : ApplType) : Prop := a.complementFeatures.plusV = true

instance : DecidablePred ApplType.RequiresEventSemantics :=
  fun _ => inferInstanceAs (Decidable (_ = true))

/-- `a.RequiresThemeInComplement` holds for low applicatives, which need an unsaturated theme in
the complement. -/
def ApplType.RequiresThemeInComplement (a : ApplType) : Prop := a.IsLow

instance : DecidablePred ApplType.RequiresThemeInComplement :=
  fun a => inferInstanceAs (Decidable a.IsLow)

/-! ### The applicative head -/

/-- An applicative head carries its type and whether it assigns dative case to its specifier. -/
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

/-- `appl.Licensed voice` holds when `voice` supplies the event semantics `appl` requires, if it
requires any. -/
def ApplHead.Licensed (appl : ApplHead) (voice : Voice.Head) : Prop :=
  appl.applType.RequiresEventSemantics → voice.HasSemantics

instance (appl : ApplHead) (voice : Voice.Head) : Decidable (appl.Licensed voice) :=
  inferInstanceAs (Decidable (_ → _))

/-! ### Licensing predictions -/

variable (v : Voice.Head)

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
theorem ethical_dative_with_agent : applHigh.Licensed Voice.agentive := by decide

/-- High Appl is blocked with middle Voice (no event semantics) ([pylkkanen-2008]). -/
theorem ethical_dative_blocked_in_middle : ¬ applHigh.Licensed Voice.middle := by decide

/-- Possessive datives (low Appl) survive in middles. -/
theorem possessive_dative_survives_middle : applLowRecipient.Licensed Voice.middle := by decide

/-- Possessive datives survive in anticausatives. -/
theorem possessive_dative_survives_anticausative :
    applLowRecipient.Licensed Voice.anticausative := by decide

/-- The asymmetry is that the ethical applicative is blocked in middles while the possessive
survives. -/
theorem ethical_possessive_middle_asymmetry :
    ¬ applHigh.Licensed Voice.middle ∧ applLowRecipient.Licensed Voice.middle :=
  ⟨ethical_dative_blocked_in_middle, possessive_dative_survives_middle⟩

/-! ### Case-based blocking of SpecApplP ([wood-2015]) -/

/-- If `appl` assigns dative, its specifier, bearing the case `c`, must bear one
([wood-2015]). -/
def ApplHead.SpecCanBearCase (appl : ApplHead) (c : Option Case) : Prop :=
  appl.assignsDative = true → c.isSome = true

instance (appl : ApplHead) (c : Option Case) : Decidable (appl.SpecCanBearCase c) :=
  inferInstanceAs (Decidable (_ → _))

end Minimalist
