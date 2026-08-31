import Linglib.Fragments.Indonesian.VoiceSystem
import Linglib.Studies.Beavers2010
import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
import Linglib.Syntax.Voice.Middle
import Linglib.Semantics.ArgumentStructure.VoiceSemantics
import Linglib.Data.Examples.BeaversUdayana2022

/-!
# Beavers & Udayana (2022): Middle Voice as Generalized Argument Suppression

Indonesian *ber-* middles — dispositional/passive, inherent reflexive, and
both incorporation types — derive from one underspecified operation: *ber-*
suppresses one direct argument of a dyadic VP, leaving it as an open
variable ((43); the existential alternative (47) is set aside in §3.3 for
consistency with [beavers-zubair-2013]). Which argument goes is fixed by
the VP shape — functional application leaves the agent open, incorporation
the patient — carried by `VoiceSemantics.suppression_after_FA` and
`suppression_after_incorporation` ((54), (51)); the 2×2 typology (31) is
the product of that dimension with the suppressed variable's reading.
This file derives the paper's diagnostic battery — *oleh*, rationale
clauses, *dengan sendiri=nya* ((10)–(13), (17), (23), (67)) — from voice
argument-structure profiles and the paper's licensing conditions, rather
than stipulating the outcomes per voice. Languages without incorporation
realize only the no-incorporation row (§7.1); anticausative *ter-* is the
same suppression over causer-unspecified roots (§5).

## Main statements

* `middleType_profiles`: each cell of the 2×2 determines its
  argument-structure profile; the diagnostic fingerprints then follow
  from the licensing conditions ((10)–(13), (17), (23)).
* `anticausative_unique_profile`: *ter-*'s (67) fingerprint — *dengan
  sendiri=nya* without rationale — falls out of the causative-paradigm
  expectation (§5) and is shared by no other non-active voice.
* `reflexive_incorporation_same_fingerprint`: the two agent-subject
  middles are diagnostically identical and distinguished by argument
  structure alone.

## References

* [beavers-udayana-2022]: Middle voice as generalized argument suppression:
  The case from Indonesian. *NLLT* 41.
* [beavers-zubair-2013]: Anticausatives in Sinhala: Involitivity and causer
  suppression.
* [kemmer-1993]: The Middle Voice.
* [beavers-2011]: On affectedness.
* [barker-1995]: Possessive Descriptions.
-/

namespace BeaversUdayana2022

open ArgumentStructure
open Indonesian.VoiceSystem
open Minimalist.Voice (Params)
open Beavers2010
open ArgumentStructure (AffectednessDegree)
open Voice
open ArgumentStructure.VoiceSemantics
open Intensional

/-! ### The 2×2 middle typology ((31)) -/

/-- A cell of the paper's 2×2 middle classification (31): object
realization × suppressed-variable reading. The `Voice` substrate exposes
the two dimensions as independent enums; this paper's analysis names the
four cells. -/
structure MiddleType where
  objRealization : ObjectRealization
  suppressedVar : SuppressedVarReading
  deriving DecidableEq, Repr

/-- Dispositional/passive middle: *Mobil itu ber-jual dengan mudah* 'the
car sells easily' (2b), *ber-jual kemarin* 'sold yesterday' (7). The
generic vs episodic difference is temporal/modal context, not the
suppression operation. -/
def dispositionalMiddle : MiddleType := ⟨.noIncorporation, .disjoint⟩

/-- Inherent reflexive: *Ali ber-dandan* 'Ali dressed' (2a); body-care
roots conventionally expect self-action, fixing the coreferent reading. -/
def reflexiveMiddle : MiddleType := ⟨.noIncorporation, .coreferent⟩

/-- Incorporation middle: *Orang itu ber-cuci=mata* 'the man washed his
eyes' (18); the agent surfaces because incorporation leaves it the sole
DP. -/
def incorporationMiddle : MiddleType := ⟨.incorporation, .disjoint⟩

/-- Incorporated reflexive: *Orang itu ber-jual=diri* 'the man sold
himself' (26b); incorporated *diri* 'self' fixes the coreferent reading. -/
def incorporationReflexive : MiddleType := ⟨.incorporation, .coreferent⟩

/-! ### Voice profiles ((35), (39), (58))

The paper's syntax (35) and semantics (39)/(43) assign each voice form an
argument-structure profile: whether the surface subject is the event's
causer, what kind of implicit participant the unexpressed argument is —
none (both overt), the weak syntactic `e[-D]` of *di-* passives, or the
purely semantic open variable of (43) — and how the form relates to
causation. The diagnostics are then licensing conditions over these
profiles, not per-construction stipulations. -/

/-- The kind of implicit participant a voice form leaves unexpressed. -/
inductive ImplicitArg where
  /-- Both base arguments are overt (actives, incorporation middles). -/
  | noImplicit
  /-- The weak syntactic implicit argument `e[-D]` of *di-* passives (35c). -/
  | weakImplicit
  /-- The purely semantic open variable of ber- suppression (43). -/
  | openVariable
  deriving DecidableEq, Repr

/-- A voice form's argument-structure profile. -/
structure VoiceForm where
  /-- The surface subject is the event's causer/agent. -/
  subjectIsCauser : Bool
  /-- The unexpressed participant, if any. -/
  implicitArg : ImplicitArg
  /-- The event is understood to have a causer — entailed by the verb, or
  expected from its causative paradigm (§5). -/
  causerUnderstood : Bool
  /-- A causer distinct from the surface subject is entailed. -/
  separateCauserEntailed : Bool
  deriving DecidableEq, Repr

/-- *oleh* 'by' realizes the weak implicit argument `e[-D]`, so only *di-*
passives license it (11). -/
def VoiceForm.licensesOleh (v : VoiceForm) : Prop :=
  v.implicitArg = .weakImplicit

/-- Rationale-clause PRO is grammatically controlled by an agentive surface
subject or by `e[-D]` ((12)–(13); pragmatic higher-authority control as in
(14) needs contextual support and is set aside). -/
def VoiceForm.licensesRationale (v : VoiceForm) : Prop :=
  v.subjectIsCauser ∨ v.implicitArg = .weakImplicit

/-- *dengan sendiri=nya* 'by itself' is licensed when the event is
understood to have a causer and denies causation prior to the surface
subject — contradicted when a separate causer is entailed (§2.1, §5). -/
def VoiceForm.licensesSendirinya (v : VoiceForm) : Prop :=
  v.causerUnderstood ∧ ¬v.separateCauserEntailed

instance (v : VoiceForm) : Decidable v.licensesOleh :=
  inferInstanceAs (Decidable (_ = _))
instance (v : VoiceForm) : Decidable v.licensesRationale :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (v : VoiceForm) : Decidable v.licensesSendirinya :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Active *meN-*: both arguments overt, agent subject (3a). -/
def menActive : VoiceForm := ⟨true, .noImplicit, true, false⟩

/-- Passive *di-*: patient subject, weak implicit agent, separate causer
entailed (3c), (35c). -/
def diPassive : VoiceForm := ⟨false, .weakImplicit, true, true⟩

/-- Dispositional/passive *ber-*: patient subject, open-variable agent with
disjoint reading, separate causer entailed (9a). -/
def dispositionalBer : VoiceForm := ⟨false, .openVariable, true, true⟩

/-- Inherent-reflexive *ber-*: the open variable is coreferent with the
subject, which is therefore the causer (16). -/
def reflexiveBer : VoiceForm := ⟨true, .openVariable, true, false⟩

/-- Incorporation *ber-*: agent subject, patient overt as incorporated NP
(18), (26b). -/
def incorporationBer : VoiceForm := ⟨true, .noImplicit, true, false⟩

/-- Anticausative *ter-*: causer-unspecified root, so no separate causer is
entailed (67a), but the causative variant creates the paradigmatic
expectation of one (§5). -/
def terAnticausative : VoiceForm := ⟨false, .openVariable, true, false⟩

/-- An unergative activity (*ber-jalan* 'walk'): no causal structure is
understood, so *dengan sendiri=nya* needs rich context (72). -/
def unergativeActivity : VoiceForm := ⟨true, .noImplicit, false, false⟩

/-! ### The diagnostic battery, derived -/

/-- Only *di-* licenses *oleh* among the six voice forms (11): the by-phrase
realizes `e[-D]`, which only *di-* projects. -/
theorem oleh_only_di :
    ∀ v ∈ [menActive, diPassive, dispositionalBer, reflexiveBer,
           incorporationBer, terAnticausative],
      (v.licensesOleh ↔ v = diPassive) := by decide

/-- The dispositional/passive middle rejects the whole battery ((9a),
(10c), (11), (13)): its open-variable agent is neither the subject nor
syntactically accessible, and it is entailed to be a separate causer. -/
theorem dispositional_rejects_battery :
    ¬dispositionalBer.licensesOleh ∧ ¬dispositionalBer.licensesRationale ∧
      ¬dispositionalBer.licensesSendirinya := by decide

/-- *di-* passives differ from dispositional middles only in the implicit
argument's syntactic status — which is exactly what rationale control and
*oleh* detect ((11)–(13)). -/
theorem di_dispositional_differ_in_implicit :
    diPassive.licensesRationale ∧ ¬dispositionalBer.licensesRationale ∧
      diPassive.subjectIsCauser = dispositionalBer.subjectIsCauser ∧
      diPassive.separateCauserEntailed = dispositionalBer.separateCauserEntailed := by
  decide

/-- The reflexive and incorporation middles are diagnostically identical —
no *oleh*, rationale fine (17a)/(23a), *sendiri=nya* fine (17b)/(23b) — yet
their profiles differ: what distinguishes them is argument structure, not
the battery. -/
theorem reflexive_incorporation_same_fingerprint :
    (reflexiveBer.licensesOleh ↔ incorporationBer.licensesOleh) ∧
      (reflexiveBer.licensesRationale ↔ incorporationBer.licensesRationale) ∧
      (reflexiveBer.licensesSendirinya ↔ incorporationBer.licensesSendirinya) ∧
      reflexiveBer ≠ incorporationBer := by decide

/-- Anticausative *ter-* licenses *dengan sendiri=nya* without licensing
rationale clauses ((67b) vs (67c)) — a combination no other non-active
voice shows. It falls out of the profile: no separate causer is entailed
(so *sendiri=nya* is consistent) while the subject is not a causer and
there is no `e[-D]` (so rationale control fails). -/
theorem anticausative_unique_profile :
    (terAnticausative.licensesSendirinya ∧ ¬terAnticausative.licensesRationale) ∧
      ∀ v ∈ [diPassive, dispositionalBer, reflexiveBer, incorporationBer],
        ¬(v.licensesSendirinya ∧ ¬v.licensesRationale) := by decide

/-- *Dengan sendiri=nya* tracks the causer expectation, not entailed
causation: the anticausative licenses it through its causative paradigm
(67b) while a plain unergative does not (72). -/
theorem sendirinya_from_paradigm :
    terAnticausative.licensesSendirinya ∧
      ¬unergativeActivity.licensesSendirinya := by decide

/-! ### The 2×2 cells determine the profiles

Each cell's profile is a function of its two coordinates: incorporation
leaves both arguments overt and the agent as subject ((51),
`VoiceSemantics.suppression_after_incorporation`); without incorporation
the suppressed agent is an open variable and the patient raises ((54),
`VoiceSemantics.suppression_after_FA`), the subject being the causer
exactly on the coreferent reading. A separate causer is entailed only in
the disjoint no-incorporation cell. -/

/-- The argument-structure profile of a 2×2 cell, computed from its
coordinates. -/
def MiddleType.voiceForm (m : MiddleType) : VoiceForm where
  subjectIsCauser :=
    m.objRealization = .incorporation ∨ m.suppressedVar = .coreferent
  implicitArg :=
    if m.objRealization = .incorporation then .noImplicit else .openVariable
  causerUnderstood := true
  separateCauserEntailed :=
    m.objRealization = .noIncorporation ∧ m.suppressedVar = .disjoint

/-- The four cells compute the three attested middle profiles — both
incorporation cells share one, since both arguments are overt either
way (58). -/
theorem middleType_profiles :
    dispositionalMiddle.voiceForm = dispositionalBer ∧
      reflexiveMiddle.voiceForm = reflexiveBer ∧
      incorporationMiddle.voiceForm = incorporationBer ∧
      incorporationReflexive.voiceForm = incorporationBer := by decide

/-- (32d), derived: the base subject surfaces exactly when the cell's
profile keeps it as causer with no implicit argument — the incorporation
column. -/
theorem agent_surfaces_iff_incorporation :
    ∀ m : MiddleType,
      m.objRealization.agentSurfaces ↔ m.voiceForm.implicitArg = .noImplicit := by
  rintro ⟨o, s⟩; cases o <;> cases s <;> decide

/-! ### Conflation middles from relational nouns (§4) -/

section Conflation

variable {E W : Type}

/-- **Conflation middle derivation** ((64)–(65)): a relational noun (*topi*
'hat', *istri* 'wife') denotes a possession relation π ([barker-1995])
with the possessum as first argument; category-neutral ber- suppresses
it and the possessor surfaces as subject — *Tono ber-topi* 'Tono has a
hat on' (59). Sortal nouns are monadic, so suppression leaves no slot
for a subject: *ber-buku is a type mismatch, deriving the relational
restriction (61). -/
theorem conflation_derivation (pi : Denot E W (.e ⇒ .e ⇒ .t))
    (possessum possessor : E) :
    suppressArg possessum pi possessor = pi possessum possessor := rfl

end Conflation

/-! ### Parameter underspecification (§7.3) -/

/-- *ber-* is parameter-compatible with active *meN-*: the formal content
of covering "some type of thematic active Voice". -/
theorem ber_compatible_with_men :
    berParams.isCompatibleWith menParams = true := rfl

/-- *ber-* is parameter-compatible with passive *di-* as well — one
underspecified head covering both non-active and active-like uses. -/
theorem ber_compatible_with_di :
    berParams.isCompatibleWith diParams = true := rfl

/-- *meN-* and *di-* are incompatible with each other: they are distinct
voices, while *ber-* can behave like either. -/
theorem men_incompatible_with_di :
    menParams.isCompatibleWith diParams = false := rfl

/-! ### Bridge to the affectedness hierarchy (§2.1) -/

/-- Dispositional *ber-* is restricted to verbs of "change-of-state or at
least some degree of affectedness" (§2.1, citing [beavers-2011]) — on
[beavers-2010]'s hierarchy, at least nonquantized change. The threshold is
a linglib bridge; the paper states the verb-class restriction without a
hierarchy cut. -/
def LicensesDispositionalMiddle (d : AffectednessDegree) : Prop :=
  AffectednessDegree.nonquantized ≤ d

instance (d : AffectednessDegree) : Decidable (LicensesDispositionalMiddle d) := by
  unfold LicensesDispositionalMiddle; infer_instance

/-- The licensed degrees are exactly the change-of-state ones. -/
theorem licensesDispositional_iff :
    ∀ d, LicensesDispositionalMiddle d ↔
      (d = .nonquantized ∨ d = .quantized) := by decide

/-- [levin-1993]'s middle-alternation diagnostic draws the same verb-class
line: *break* (change of state) participates, *hit* (contact without
change) does not. -/
theorem levin_middle_requires_cos :
    MeaningComponents.break_.predictedAlternation .middle = true ∧
      MeaningComponents.hit.predictedAlternation .middle = false := ⟨rfl, rfl⟩

end BeaversUdayana2022
