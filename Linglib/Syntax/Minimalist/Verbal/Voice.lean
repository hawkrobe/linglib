module

public import Linglib.Syntax.Minimalist.Features

/-!
# Voice heads

Voice introduces, or fails to introduce, the external argument of the verbal phrase it takes
([kratzer-1996]). A head is a cell of the typology of [alexiadou-schaefer-2015]
after [schaefer-2008]: thematic Voice introduces an external-argument variable with an
instruction for interpreting it, as an agent, a causer or a holder, and expletive Voice
introduces nothing; active Voice bears a D-feature and projects a specifier, non-active Voice
does not, its variable, if any, existentially bound and implicit. The four cells are the
active and non-active thematic heads, the transitive and the passive, and the active and
non-active expletive heads, the *se*-marked anticausative and the non-active middle. Beyond its
cell a head may bind the internal argument to the external one, reflexively or reciprocally
([siloni-2012], [martin-schaefer-kastner-2025]), or demote it to an oblique, the antipassive
([scott-2023]); may check Case ([collins-2005]) and carry Agree features; and may override its
phasehood per construction.

Every property consumers read is derived from the cell: `Head.IsThematic`, `Head.AssignsTheta`,
`Head.ExternalImplicit`, `Head.IsPhasal`, and the underspecified cell `Head.params` that
[beavers-udayana-2022]'s Indonesian *ber-* leaves open.

## Main definitions

* `Instruction`, `Operation`, `Head`: the thematic instruction, the valency operation and the
  head.
* `Head.IsThematic`, `Head.HasD`, `Head.ExternalImplicit`, `Head.AssignsTheta`, `Head.IsPhasal`,
  `Head.ChecksCase`, `Head.DCoherent`: the predicate API.
* `agentive`, `causer`, `experiencer`, `anticausative`, `middle`, `passive`, `impersonal`,
  `reflexive`, `reciprocal`, `antipassive`: the named cells.
* `Params`, `Head.params`, `Params.Compatible`: the ±D/±λx cell with either coordinate left
  open.

## Main results

* `Head.AssignsTheta.isThematic`, `Head.IsPhasal.assignsTheta`: θ-assignment entails a thematic
  head; default phasehood entails θ-assignment.
* `canonical_dCoherent`: every named cell realizes its variable in its specifier exactly when it
  has one.
* `antipassive_not_phasal`: the antipassive is thematic and active yet not a phase.
* `Params.Compatible.refl`, `underspecified_compatible_with_all`.

## Implementation notes

The passive is the thematic non-active cell, its agent implicit, with the Finnish impersonal in
the same cell; [collins-2005]'s passive Voice, which assigns no θ-role and checks Case, is that
paper's analysis, statable here as an expletive active head with `checksCase`. The default
phasehood is that of [chomsky-2001]'s v*, a θ-assigning active head, with the antipassive
excepted because it detransitivizes; [erlewine-sommerlot-2025] treats every Malayic Voice as a
phase, which `phaseOverride` records. [cuervo-2003]'s inchoatives have no Voice at all, and the
event structure below Voice is `Minimalist.LittleV`.

## References

* [alexiadou-schaefer-2015]
* [beavers-udayana-2022]
* [chomsky-2001]
* [collins-2005]
* [coon-mateo-pedro-preminger-2014]
* [cuervo-2003]
* [erlewine-sommerlot-2025]
* [kratzer-1996]
* [martin-schaefer-kastner-2025]
* [munoz-perez-2026]
* [schaefer-2008]
* [schaefer-2017]
* [scott-2023]
* [siloni-2012]
* [wood-2015]
-/

@[expose] public section

namespace Minimalist.Voice

/-! ### The cell -/

/-- The instruction a thematic Voice head gives for interpreting its external-argument
variable ([alexiadou-schaefer-2015]). -/
inductive Instruction where
  | agent
  | causer
  | holder
  deriving DecidableEq, Repr

/-- What a head does to the internal argument beyond introducing an external one: binds it to
the external argument reflexively or reciprocally ([siloni-2012]), or demotes it to an oblique
([scott-2023]). -/
inductive Operation where
  | reflexive
  | reciprocal
  | antipassive
  deriving DecidableEq, Repr

/-- A Voice head: its cell in the thematic/expletive × active/non-active typology, whether its
variable is implicit, its valency operation, and its per-construction properties. -/
structure Head where
  /-- λx: the external-argument variable and its instruction; `none` for expletive Voice. -/
  thematic : Option Instruction
  /-- D: the head projects a specifier. -/
  hasD : Bool
  /-- The variable is existentially bound rather than saturated by a specifier DP. -/
  implicit : Bool := false
  /-- The operation on the internal argument, if any. -/
  operation : Option Operation := none
  /-- Per-construction override of the default phasehood ([erlewine-sommerlot-2025],
      [coon-mateo-pedro-preminger-2014]). -/
  phaseOverride : Option Bool := none
  /-- Checks Case ([collins-2005]). -/
  checksCase : Bool := false
  /-- Agree-relevant features (e.g. [uOblique] for Mam *=(y)a'*). -/
  features : FeatureBundle := ⊥
  deriving DecidableEq, Repr

namespace Head

variable (v : Head)

/-! ### Predicate API -/

/-- Thematic: introduces an external-argument variable, and so has semantics. -/
def IsThematic : Prop := v.thematic.isSome = true

/-- Projects a specifier. -/
def HasD : Prop := v.hasD = true

/-- The external argument is existentially bound. -/
def ExternalImplicit : Prop := v.implicit = true

/-- Assigns a θ-role to a DP in its specifier: thematic, with its variable not implicit. -/
def AssignsTheta : Prop := v.IsThematic ∧ ¬ v.ExternalImplicit

/-- Checks Case. -/
def ChecksCase : Prop := v.checksCase = true

/-- The default phasehood: [chomsky-2001]'s v*, a θ-assigning active head, except that the
antipassive, which detransitivizes, is no phase. -/
def defaultPhasal : Bool :=
  v.thematic.isSome && !v.implicit && v.hasD && v.operation != some .antipassive

/-- Phasal: the per-construction override if present, else the default. -/
def IsPhasal : Prop := v.phaseOverride.getD v.defaultPhasal = true

/-- A thematic head's variable is implicit exactly when the head projects no specifier, as in
[alexiadou-schaefer-2015]'s grid; a head may diverge, and stating the divergence
makes it explicit. -/
def DCoherent : Prop := v.IsThematic → v.implicit = !v.hasD

instance : Decidable v.IsThematic := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.HasD := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.ExternalImplicit := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.AssignsTheta := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable v.ChecksCase := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.IsPhasal := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.DCoherent := inferInstanceAs (Decidable (_ → _))

theorem AssignsTheta.isThematic {v : Head} (h : v.AssignsTheta) : v.IsThematic := h.1

/-- A head phasal by default assigns a θ-role. -/
theorem IsPhasal.assignsTheta {v : Head} (ho : v.phaseOverride = none) (h : v.IsPhasal) :
    v.AssignsTheta := by
  simp only [IsPhasal, ho, Option.getD_none, defaultPhasal, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1.1, by simp [ExternalImplicit, h.1.1.2]⟩

end Head

/-! ### The underspecified cell -/

/-- The ±D/±λx cell with either coordinate left open ([alexiadou-schaefer-2015],
[schaefer-2017]): `none` is underspecified, as Indonesian *ber-* is on both
([beavers-udayana-2022]). -/
structure Params where
  /-- Does the head project a specifier? -/
  hasD : Option Bool
  /-- Does the head introduce an external-argument variable? -/
  thematic : Option Bool
  deriving DecidableEq, Repr

/-- The cell of a head, fully specified. -/
def Head.params (v : Head) : Params := ⟨some v.hasD, some v.thematic.isSome⟩

/-- Compatible: agreeing on every coordinate both specify. -/
def Params.Compatible (p q : Params) : Prop :=
  (∀ s ∈ p.hasD, ∀ t ∈ q.hasD, s = t) ∧ ∀ s ∈ p.thematic, ∀ t ∈ q.thematic, s = t

instance : DecidableRel Params.Compatible := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem Params.Compatible.refl (p : Params) : p.Compatible p :=
  ⟨fun _ hs _ ht ↦ Option.mem_unique hs ht, fun _ hs _ ht ↦ Option.mem_unique hs ht⟩

/-- A cell open on both coordinates is compatible with every head. -/
theorem underspecified_compatible_with_all (v : Head) :
    Params.Compatible ⟨none, none⟩ v.params :=
  ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩

/-! ### The named cells -/

/-- Thematic active Voice introducing an agent: the transitive and unergative head, v*. -/
def agentive : Head := { thematic := some .agent, hasD := true }

/-- Thematic active Voice introducing a causer. -/
def causer : Head := { thematic := some .causer, hasD := true }

/-- Thematic active Voice introducing a holder: the experiencer subject of a psych causative. -/
def experiencer : Head := { thematic := some .holder, hasD := true }

/-- Expletive active Voice: no variable, a specifier for a marker such as Romance *se*, the
marked anticausative ([munoz-perez-2026]). -/
def anticausative : Head := { thematic := none, hasD := true }

/-- Expletive non-active Voice: no variable, no specifier, the dispositional middle. -/
def middle : Head := { thematic := none, hasD := false }

/-- Thematic non-active Voice: an agent existentially bound and implicit, the passive. -/
def passive : Head := { thematic := some .agent, hasD := false, implicit := true }

/-- The Finnish impersonal, the same cell as the passive: an implicit generic agent. -/
def impersonal : Head := passive

/-- Agentive Voice binding the internal argument to the agent: Romance reflexive *se*
([martin-schaefer-kastner-2025]). [wood-2015]'s Icelandic *-st* is a SpecpP clitic, not an
exponent of this head. -/
def reflexive : Head := { agentive with operation := some .reflexive }

/-- Agentive Voice putting the agent in the mutual relation with the internal argument:
[siloni-2012]'s syntactic reciprocalization. Lexically reciprocal verbs enter the syntax
symmetric and are not exponents of this head. -/
def reciprocal : Head := { agentive with operation := some .reciprocal }

/-- Agentive Voice demoting the object to an oblique, with absolutive on the agent
([scott-2023]). -/
def antipassive : Head := { agentive with operation := some .antipassive }

/-! ### Verification -/

/-- The θ-assigning heads are the thematic active ones; the anticausative, the middle and the
passive assign none. -/
theorem assignsTheta_cells :
    agentive.AssignsTheta ∧ causer.AssignsTheta ∧ experiencer.AssignsTheta ∧
      reflexive.AssignsTheta ∧ reciprocal.AssignsTheta ∧ antipassive.AssignsTheta ∧
      ¬ anticausative.AssignsTheta ∧ ¬ middle.AssignsTheta ∧ ¬ passive.AssignsTheta := by
  decide

/-- The passive is thematic with an implicit agent; the anticausative is expletive with a
specifier, the core claim of [munoz-perez-2026] that *se* is a PF phenomenon. -/
theorem passive_anticausative :
    passive.IsThematic ∧ passive.ExternalImplicit ∧ ¬ anticausative.IsThematic ∧
      anticausative.HasD := by
  decide

/-- Every named thematic cell keeps its variable implicit exactly when it lacks a specifier. -/
theorem canonical_dCoherent :
    agentive.DCoherent ∧ causer.DCoherent ∧ experiencer.DCoherent ∧
      anticausative.DCoherent ∧ middle.DCoherent ∧ passive.DCoherent ∧ reflexive.DCoherent ∧
      reciprocal.DCoherent ∧ antipassive.DCoherent := by
  decide

/-- Agentive and causer Voice are phase heads, v*; the anticausative, the middle and the passive
are not. -/
theorem phasal_cells :
    agentive.IsPhasal ∧ causer.IsPhasal ∧ ¬ anticausative.IsPhasal ∧ ¬ middle.IsPhasal ∧
      ¬ passive.IsPhasal := by
  decide

/-- The antipassive anomaly: a thematic active head that is no phase, phasehood tracking v*
transitivity ([chomsky-2001]) and the antipassive detransitivizing. -/
theorem antipassive_not_phasal : antipassive.AssignsTheta ∧ ¬ antipassive.IsPhasal := by decide

end Minimalist.Voice
