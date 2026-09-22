import Linglib.Fragments.Indonesian.Verbs
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Studies.BeaversZubair2013
import Linglib.Data.Examples.BeaversUdayana2022

/-!
# Beavers & Udayana (2022): Middle voice as generalized argument suppression

This file formalizes Beavers and Udayana's analysis of the Indonesian middle prefix *ber-*.

The prefix saturates the first open argument of its VP with a free variable. Which argument
that is depends on how the object is realized. An object DP combines with the verb first, so
*ber-* suppresses the agent and the patient is the subject. An incorporated noun is predicated
of the patient without saturating it, so *ber-* suppresses the patient and the agent is the
subject. The free variable is read as coreferent with the subject or as disjoint from it, which
gives the four middles of the paper.

## Main definitions

* `ber`, `incorporate`: the denotation of *ber-* and the incorporating variant of a verb.
* `MiddleType`, `MiddleType.denote`: a cell of the two-by-two classification, and the truth
  conditions that *ber-* derives for it.
* `RootClass`: the classes of root that fix the default reading.
* `Voice`, `Voice.LicensesOleh`, `Voice.LicensesRationale`, `Voice.LicensesSendirinya`: the
  voice forms and the licensing conditions of the three diagnostics.

## Main results

* `denote_dispositional`, `denote_reflexive`, `denote_incorporation`,
  `denote_incorporationReflexive`: the truth conditions of the four middles.
* `denote_incorporationReflexive_iff_reflexive`: incorporated *diri* and an inherent reflexive
  have the same truth conditions.
* `causerSuppress_eq_ber`, `denote_reflexive_iff_resolve`: *ber-* generalizes the causer
  suppression of Beavers and Zubair.
* `subjectIsAgent_iff`, `separateAgent_of_dispositional`: the subject is the agent in every
  cell but the dispositional one, which entails an agent other than the subject.
* `licensesOleh_iff`, `licensesSendirinya_not_licensesRationale_iff`: only *di-* licenses
  *oleh*, and only anticausative *ter-* licenses *dengan sendirinya* without a rationale clause.

## References

* [beavers-udayana-2022]
* [beavers-zubair-2013]
* [alexiadou-schaefer-2015]
-/

namespace BeaversUdayana2022

open Minimalist.Voice (Params Flavor)

/-! ### The middles -/

/-- How the variable that *ber-* leaves free is read relative to the subject. -/
inductive Reading where
  | coreferent
  | disjoint
  deriving DecidableEq, Repr

/-- How the object of the base verb is realized, as an incorporated noun or as a DP that is
promoted to subject. -/
inductive ObjectRealization where
  | incorporation
  | promotion
  deriving DecidableEq, Repr

/-- A cell of the classification of middles by object realization and reading. -/
structure MiddleType where
  objRealization : ObjectRealization
  reading : Reading
  deriving DecidableEq, Repr

/-- The dispositional or passive middle, as in *Mobil itu berjual dengan mudah* 'The car sells
easily'. -/
def dispositional : MiddleType := ⟨.promotion, .disjoint⟩

/-- The inherent reflexive, as in *Ali berdandan* 'Ali dressed'. -/
def reflexive : MiddleType := ⟨.promotion, .coreferent⟩

/-- The incorporation middle, as in *Orang itu bercuci mata* 'The man washed his eyes'. -/
def incorporation : MiddleType := ⟨.incorporation, .disjoint⟩

/-- The incorporated reflexive, as in *Orang itu berjual diri* 'The man sold himself'. -/
def incorporationReflexive : MiddleType := ⟨.incorporation, .coreferent⟩

/-! ### Composition

A dyadic root is a relation `V patient agent`, with the event variable closed off. -/

section Composition

variable {E : Type} (V : E → E → Prop) (P : E → Prop) (s z : E)

/-- *ber-* saturates the first open argument of its VP with the free variable `z` (43). -/
def ber {α : Type} (z : E) (vp : E → α) : α := vp z

/-- An incorporating verb predicates the noun of its patient and keeps the patient as an
argument (49). -/
def incorporate : E → E → Prop := fun x y ↦ V x y ∧ P x

/-- The VP of a middle before *ber-* applies, as a function of its first open argument. With a
promoted object, whose trace the verb has combined with, that argument is the agent, and with an
incorporated noun it is the patient. -/
def vp : ObjectRealization → E → Prop
  | .promotion => V s
  | .incorporation => fun x ↦ incorporate V P x s

/-- A reading resolves the free variable, to the subject or to something else. -/
def Reading.resolve (φ : E → Prop) : Reading → Prop
  | .coreferent => φ s
  | .disjoint => ∃ z, z ≠ s ∧ φ z

/-- The truth conditions of a middle with subject `s`, which are those of *ber-* applied to the
VP, with the free variable resolved by the reading. -/
def MiddleType.denote (m : MiddleType) : Prop :=
  m.reading.resolve s fun z ↦ ber z (vp V P s m.objRealization)

/-- As an incorporated noun *diri* 'self' is semantically vacuous. -/
def diri : E → Prop := fun x ↦ ∃ y, y = x

/-- A dispositional middle says that something other than the subject acted on it. -/
theorem denote_dispositional : dispositional.denote V P s ↔ ∃ z, z ≠ s ∧ V s z := Iff.rfl

/-- An inherent reflexive says that the subject acted on itself. -/
theorem denote_reflexive : reflexive.denote V P s ↔ V s s := Iff.rfl

/-- An incorporation middle says that the subject acted on something else that the noun
describes. -/
theorem denote_incorporation : incorporation.denote V P s ↔ ∃ z, z ≠ s ∧ V z s ∧ P z := Iff.rfl

/-- An incorporated reflexive says that the subject acted on itself and that the noun describes
it. -/
theorem denote_incorporationReflexive : incorporationReflexive.denote V P s ↔ V s s ∧ P s :=
  Iff.rfl

/-- With *diri* incorporated, the reflexive incorporation middle has the truth conditions of an
inherent reflexive. -/
theorem denote_incorporationReflexive_iff_reflexive :
    incorporationReflexive.denote V diri s ↔ reflexive.denote V P s :=
  ⟨And.left, fun h ↦ ⟨h, s, rfl⟩⟩

/-- The subject of a middle is understood as the agent of the base verb in every cell but the
dispositional one. -/
def MiddleType.SubjectIsAgent (m : MiddleType) : Prop :=
  m.objRealization = .incorporation ∨ m.reading = .coreferent

instance : DecidablePred MiddleType.SubjectIsAgent := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Where the subject is the agent, the middle entails that it acted on something. -/
theorem exists_patient_of_subjectIsAgent {m : MiddleType} (hm : m.SubjectIsAgent)
    (h : m.denote V P s) : ∃ x, V x s := by
  obtain ⟨_ | _, _ | _⟩ := m
  · exact ⟨s, h.1⟩
  · obtain ⟨z, -, hz, -⟩ := h; exact ⟨z, hz⟩
  · exact ⟨s, h⟩
  · simp [MiddleType.SubjectIsAgent] at hm

/-- The subject is the agent exactly when the cell is not the dispositional one. -/
theorem subjectIsAgent_iff (m : MiddleType) : m.SubjectIsAgent ↔ m ≠ dispositional := by
  obtain ⟨_ | _, _ | _⟩ := m <;> decide

/-- A dispositional middle entails an agent other than its subject. -/
theorem separateAgent_of_dispositional (h : dispositional.denote V P s) : ∃ z, z ≠ s ∧ V s z := h

end Composition

/-! ### Causer suppression (§3.3)

*ber-* generalizes the causer suppression of Beavers and Zubair, which applies to a causer of
the individual sort alone. Their verbs take the causer first. -/

section CauserSuppression

open BeaversZubair2013 Causation

variable {E : Type} {c : CauserSort} (h : c.admitsIndividual) (V : E → E → Prop) (P : E → Prop)
  (s : E)

/-- Causer suppression is *ber-* under a condition on the sort of the causer. -/
theorem causerSuppress_eq_ber {α : Type} (z : E) (vp : E → α) :
    causerSuppress c h z vp = ber z vp :=
  rfl

/-- An inherent reflexive is the reflexive resolution of a suppressed causer. -/
theorem denote_reflexive_iff_resolve :
    reflexive.denote V P s ↔ BeaversZubair2013.Reading.reflexive.resolve h (flip V) s :=
  Iff.rfl

/-- A dispositional middle entails the existential resolution of a suppressed causer, to which
it adds that the causer is not the subject. -/
theorem resolve_existential_of_dispositional (hs : dispositional.denote V P s) :
    BeaversZubair2013.Reading.existential.resolve h (flip V) s :=
  let ⟨z, _, hz⟩ := hs; ⟨z, hz⟩

end CauserSuppression

/-! ### A model

Tono sold the car, and Ali dressed himself. -/

/-- The individuals of the model. -/
inductive Entity where
  | tono | ali | car
  deriving DecidableEq, Repr

open Entity in
/-- The selling and dressing events of the model, as one relation of patient and agent. -/
def acted : Entity → Entity → Prop
  | car, tono | ali, ali => True
  | _, _ => False

instance : Fintype Entity := ⟨{.tono, .ali, .car}, fun x ↦ by cases x <;> decide⟩

instance : DecidableRel acted := fun x y ↦ by
  cases x <;> cases y <;> unfold acted <;> infer_instance

/-- The car has a dispositional middle and no reflexive one, Ali a reflexive one and no
dispositional one, and Tono the incorporation middle with a noun true of the car. -/
theorem model :
    dispositional.denote acted diri .car ∧ ¬ reflexive.denote acted diri .car ∧
      reflexive.denote acted diri .ali ∧ ¬ dispositional.denote acted diri .ali ∧
      incorporation.denote acted (· = .car) .tono ∧
      ¬ incorporation.denote acted (· = .car) .ali := by
  simp only [denote_dispositional, denote_reflexive, denote_incorporation]
  decide

/-! ### Root classes (§3.5, §5)

The default reading of a plain *ber-* form follows the class of its root. The members are the
paper's own roots, as entries of `Fragments/Indonesian/Verbs.lean`. -/

/-- The classes of dyadic root. -/
inductive RootClass where
  /-- The conventional expectation is self-action, as with verbs of body care. -/
  | naturallyReflexive
  /-- The conventional expectation is disjoint reference, as with every other dyadic root. -/
  | obviative
  /-- A change of state whose root entails no external causer. -/
  | causerUnspecified
  deriving DecidableEq, Repr

namespace RootClass

/-- The paper's roots of each class, which are the body-care verbs of (15), the roots of (4)
with a dispositional or passive *ber-* form, and *buka* 'open' and *pecah* 'break' of §5. -/
def roots : RootClass → List Indonesian.Verb
  | .naturallyReflexive =>
    [Indonesian.dandan, Indonesian.cukur, Indonesian.jemur, Indonesian.sisir]
  | .obviative => [Indonesian.masak, Indonesian.jual, Indonesian.cuci, Indonesian.tambat]
  | .causerUnspecified => [Indonesian.buka, Indonesian.pecah]

/-- The default middle of a plain *ber-* form, which matches the conventional expectation of
the root class. A causer-unspecified root has no *ber-* form. -/
def defaultMiddle : RootClass → Option MiddleType
  | .naturallyReflexive => some reflexive
  | .obviative => some dispositional
  | .causerUnspecified => none

/-- A root has a *ber-* form exactly when its class has a default middle, and a form in *ter-*
otherwise. -/
theorem ber_iff_defaultMiddle (c : RootClass) :
    ∀ v ∈ c.roots, (v.ber ↔ c.defaultMiddle.isSome) ∧ (v.terClass.isSome ↔ ¬ v.ber) := by
  cases c <;> decide

end RootClass

/-- An obviative root gets its reflexive reading from incorporated *diri* 'self', as in
*berjual diri* (26b), the marked form that blocks the reading for the plain *ber-* form. -/
theorem jual_incorporatesDiri : Indonesian.jual.IncorporatesDiri := by decide

/-! ### The diagnostics (§2, §5)

A *di-* passive projects a weak implicit argument, which an *oleh* phrase realizes and which
can control into a rationale clause. A *ber-* form has a free variable in the semantics and no
such argument in the syntax. -/

/-- The voice forms that the diagnostics compare. -/
inductive Voice where
  /-- The active in *meN-*. -/
  | meN
  /-- The passive in *di-*. -/
  | di
  /-- A middle in *ber-*. -/
  | ber (m : MiddleType)
  /-- The anticausative in *ter-* of a causer-unspecified root. -/
  | ter
  deriving DecidableEq, Repr

namespace Voice

/-- The subject is the agent in the active and in the middles where *ber-* leaves it so. -/
def SubjectIsAgent : Voice → Prop
  | .meN => True
  | .ber m => m.SubjectIsAgent
  | .di | .ter => False

/-- An agent other than the subject is entailed by the passive and by the dispositional middle.
A causer-unspecified root entails none. -/
def SeparateAgentEntailed : Voice → Prop
  | .di => True
  | .ber m => m = dispositional
  | .meN | .ter => False

/-- An *oleh* 'by' phrase realizes the weak implicit argument of *di-*. -/
def LicensesOleh (v : Voice) : Prop := v = .di

/-- The null subject of a rationale clause is controlled by an agentive subject or by the weak
implicit argument of *di-*. -/
def LicensesRationale (v : Voice) : Prop := v.SubjectIsAgent ∨ v = .di

/-- *dengan sendirinya* 'by itself' denies an agent other than the subject. -/
def LicensesSendirinya (v : Voice) : Prop := ¬ v.SeparateAgentEntailed

instance : DecidablePred SubjectIsAgent := fun v ↦ by
  cases v <;> unfold SubjectIsAgent <;> infer_instance

instance : DecidablePred SeparateAgentEntailed := fun v ↦ by
  cases v <;> unfold SeparateAgentEntailed <;> infer_instance

instance : DecidablePred LicensesOleh := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred LicensesRationale := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred LicensesSendirinya := fun _ ↦ inferInstanceAs (Decidable (¬ _))

/-- Only *di-* licenses *oleh*. -/
theorem licensesOleh_iff (v : Voice) : v.LicensesOleh ↔ v = .di := Iff.rfl

/-- The dispositional middle fails all three diagnostics. -/
theorem dispositional_rejects :
    ¬ (ber dispositional).LicensesOleh ∧ ¬ (ber dispositional).LicensesRationale ∧
      ¬ (ber dispositional).LicensesSendirinya := by
  decide

/-- The middles whose subject is the agent license a rationale clause and *dengan sendirinya*
and no *oleh* phrase. -/
theorem ber_of_subjectIsAgent {m : MiddleType} (hm : m.SubjectIsAgent) :
    ¬ (ber m).LicensesOleh ∧ (ber m).LicensesRationale ∧ (ber m).LicensesSendirinya := by
  obtain ⟨_ | _, _ | _⟩ := m <;> first | decide | exact absurd hm (by decide)

/-- Among the forms without an agent subject, anticausative *ter-* alone licenses *dengan
sendirinya*, and it licenses no rationale clause. -/
theorem licensesSendirinya_not_licensesRationale_iff (v : Voice) :
    v.LicensesSendirinya ∧ ¬ v.LicensesRationale ↔ v = .ter := by
  rcases v with _ | _ | ⟨⟨_ | _, _ | _⟩⟩ | _ <;> decide

/-- The paper's judgments agree with the licensing conditions on an *oleh* phrase with *di-*
(11), on *dengan sendirinya* with a dispositional middle (10c) and with a reflexive one (17b),
and on a rationale clause with a dispositional middle (13). -/
theorem judgments :
    (Examples.bu2022_11.judgment = .acceptable ↔ di.LicensesOleh) ∧
      (Examples.bu2022_10c.judgment = .acceptable ↔ (ber dispositional).LicensesSendirinya) ∧
      (Examples.bu2022_17b.judgment = .acceptable ↔ (ber reflexive).LicensesSendirinya) ∧
      (Examples.bu2022_13.judgment = .acceptable ↔ (ber dispositional).LicensesRationale) := by
  decide

end Voice

/-! ### Relational nouns (§4) -/

/-- A relational noun such as *topi* 'hat' denotes a relation of possessum and possessor, and
*ber-* suppresses the possessum, so that *Tono bertopi* says that Tono has some hat on. A sortal
noun has one argument, and suppressing it leaves none for a subject. -/
theorem ber_relationalNoun {E : Type} (π : E → E → Prop) (possessum possessor : E) :
    ber possessum π possessor ↔ π possessum possessor :=
  Iff.rfl

/-! ### The voice typology of Alexiadou and Schäfer (§7.3) -/

/-- *meN-* corresponds to the thematic active voice. -/
def meNParams : Params := Flavor.agentive.toParams

/-- *di-* corresponds to the passive. -/
def diParams : Params := Flavor.passive.toParams

/-- *ber-* fixes neither whether a specifier is selected nor whether an agent is introduced. -/
def berParams : Params := ⟨none, none⟩

/-- *ber-* is compatible with every voice of the typology, and *meN-* and *di-* with each other
are not. -/
theorem berParams_compatible (f : Flavor) :
    berParams.Compatible f.toParams ∧ ¬ meNParams.Compatible diParams := by
  cases f <;> decide

end BeaversUdayana2022
