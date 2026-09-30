module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Linglib.Syntax.ConstructionGrammar.Constructicon
public import Linglib.Syntax.ConstructionGrammar.Fusion

/-!
# Goldberg (1995): Constructions

This file formalizes Goldberg's account of argument structure, in which argument structure
constructions carry meaning of their own and a verb's participant roles fuse with a
construction's argument roles. The constructions are the ditransitive (CAUSE-RECEIVE), caused
motion (CAUSE-MOVE), the resultative (CAUSE-BECOME), intransitive motion (MOVE) and the conative
(DIRECT-ACTION-AT). The fusions the book draws follow from its Semantic Coherence and
Correspondence Principles, and the constructions form a network of normal-mode inheritance links.

## Main results

* `isFusion_kick_iff`: *kick* fuses with the ditransitive in only one way (Fig. 2.9)
* `put_uses_exception`: *put* fuses with caused motion only through the three-role exception
  (Fig. 2.7)
* `isFusion_mail`: the ditransitive profiles *mail*'s mailee (Fig. 2.8)
* `wipe_talk_contributed`: the resultative adds a result-goal to *wipe* and a patient as well to
  *talk* (Fig. 8.2)
* `not_isFusion_become`: *become* cannot fuse with the resultative (p. 190)
* `exists_fused`: every construction shares a participant with its verb (p. 65)
* `network_wellTyped`, `inherited_statedForm`, `ditransitive_meaning_ne`: the network's links
  respect their types, and the ditransitive's senses share its form but not its meaning

## Implementation notes

Forms are sequences of single-word slots, each carrying the grammatical function its role is
linked to. The argument roles a participant role can be construed as are the book's judgments in
its figures. Caused motion's theme is contributable, as in Fig. 7.1 (p. 160) and the sneeze
case; Fig. 2.6 (p. 52) draws it as required.

## TODO

The conative admits a verb of its intended result only if the verb is [+motion, +contact]
(Figs. 2.13–2.15, p. 63), features the book takes from Guerssel, Hale, Laughren, Levin and White
Eagle (1985). Until those features are formalized the conative lists only the instance relation,
and no construction restricts a relation by features (`Feature` is empty). Adding the
intended-result relation will not by itself admit *kick at*: the conative's theme is oblique and
so not profiled, and the Correspondence Principle forbids a verb profiling two roles, as *kick*
does in Fig. 2.9, from fusing one with a nonprofiled role; the book does not say how a verb of the
intended result fuses. The intransitive resultative (Fig. 8.3), the passive's thematic hierarchy
(p. 57), *send* (Fig. 2.11) and the senses of caused motion (p. 76) are not modelled.

## References

* [goldberg-1995]
-/

@[expose] public section

namespace Goldberg1995

open ConstructionGrammar

/-! ### Roles and predicates -/

/-- A `TransferModality` is the modality of CAUSE-RECEIVE that distinguishes a sense of the
ditransitive (pp. 75–77). -/
inductive TransferModality where
  /-- Actual transfer, the central sense, X CAUSES Y TO RECEIVE Z. -/
  | actual
  /-- Conditions of satisfaction imply X CAUSES Y TO RECEIVE Z. -/
  | satisfaction
  /-- X ENABLES Y TO RECEIVE Z. -/
  | enablement
  /-- X CAUSES Y NOT TO RECEIVE Z. -/
  | negated
  /-- X INTENDS TO CAUSE Y TO RECEIVE Z. -/
  | intended
  /-- X ACTS TO CAUSE Y TO RECEIVE Z at some future point in time. -/
  | future
  deriving DecidableEq, Fintype, Repr

/-- `Role` enumerates the argument roles of the book's diagrams, whose labels "have no
theoretical significance" (p. 49). -/
inductive Role where
  | agent
  | recipient
  | patient
  | cause
  | goal
  | theme
  | resultGoal
  deriving DecidableEq, Fintype, Repr

/-- `Predicate` enumerates the constructions' predicates; the ditransitive's carries the modality
of its sense. -/
inductive Predicate where
  | causeReceive (m : TransferModality)
  | causeMove
  | causeBecome
  | move
  | directActionAt
  deriving DecidableEq, Repr

/-- `Feature` is the type of verb features that can restrict a relation, empty until the
features the conative uses are formalized. -/
abbrev Feature := Empty

/-- `Sem` is the meaning of the book's argument structure constructions. -/
abbrev Sem := ArgStructure Predicate Role Feature

/-! ### The argument structure constructions -/

/-- The ditransitive [Subj V Obj Obj₂] in the sense `m` means CAUSE-RECEIVE ⟨agt rec pat⟩, with
the recipient contributable and the verb an instance or the means (Fig. 2.4; *Pat faxed Bill the
letter*). In the benefactive sense the verb designates a precondition (Fig. 3.2), and the other
senses keep the central sense's relations. -/
def ditransitive (m : TransferModality) : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN, gf := some .subj }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN, gf := some .obj }
      , { filler := .open_ .NOUN, gf := some .obj2 } ]
  , meaning :=
      { pred := .causeReceive m
        roles := [⟨.agent, .subj, true⟩, ⟨.recipient, .obj, false⟩, ⟨.patient, .obj2, true⟩]
        relations :=
          if m = .intended then [(.precondition, ∅)] else [(.subtype, ∅), (.means, ∅)] } }

/-- The caused-motion construction [Subj V Obj Obl] means CAUSE-MOVE ⟨cause goal theme⟩, with goal
and theme contributable (Fig. 7.1), so that *sneeze* acquires motion and causation from it (*Pat
sneezed the napkin off the table*). -/
def causedMotion : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN, gf := some .subj }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN, gf := some .obj }
      , { filler := .open_ .ADP, gf := some .obl } ]
  , meaning :=
      { pred := .causeMove
        roles := [⟨.cause, .subj, true⟩, ⟨.goal, .obl, false⟩, ⟨.theme, .obj, false⟩]
        relations := [(.subtype, ∅), (.means, ∅)] } }

/-- The resultative [Subj V Obj Obl] means CAUSE-BECOME ⟨agt pat result-goal⟩, with patient and
result-goal contributable (Fig. 8.1; *She hammered the metal flat*). -/
def resultative : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN, gf := some .subj }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN, gf := some .obj }
      , { filler := .open_ .ADJ, gf := some .obl } ]
  , meaning :=
      { pred := .causeBecome
        roles := [⟨.agent, .subj, true⟩, ⟨.patient, .obj, false⟩, ⟨.resultGoal, .obl, false⟩]
        relations := [(.subtype, ∅), (.means, ∅)] } }

/-- The intransitive motion construction [Subj V Obl] means MOVE ⟨theme goal⟩, with the goal
contributable (Fig. 7.2; *The fly buzzed into the room*). -/
def intransitiveMotion : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN, gf := some .subj }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP, gf := some .obl } ]
  , meaning :=
      { pred := .move
        roles := [⟨.theme, .subj, true⟩, ⟨.goal, .obl, false⟩]
        relations := [(.subtype, ∅), (.means, ∅)] } }

/-- The conative [Subj V Obl_at] means DIRECT-ACTION-AT ⟨agt theme⟩ (Figs. 2.13–2.15; *Sam kicked
at Bill*); its at-phrase marks the target without entailing contact. -/
def conative : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN, gf := some .subj }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP, gf := some .obl } ]
  , meaning :=
      { pred := .directActionAt
        roles := [⟨.agent, .subj, true⟩, ⟨.theme, .obl, true⟩]
        relations := [(.subtype, ∅)] } }

/-- The goal of caused motion is not profiled: "we can tell because it is linked to an oblique
function" (p. 53). -/
theorem not_isProfiled_goal : ¬ causedMotion.meaning.IsProfiled .goal := by decide

/-! ### Verbs in constructions (§2.4) -/

/-- `HandRole` enumerates the participant roles of *hand* (Fig. 2.5). -/
inductive HandRole | hander | handee | handed
  deriving DecidableEq, Fintype

/-- *hand* profiles all three of its participant roles, each an instance of one argument role of
the ditransitive. -/
def hand : Participants HandRole Role where
  profiled := .univ
  construals | .hander => {.agent} | .handee => {.recipient} | .handed => {.patient}

/-- `handFusion` fuses *hand* with the ditransitive (Fig. 2.5). -/
def handFusion : HandRole → Option Role
  | .hander => some .agent | .handee => some .recipient | .handed => some .patient

/-- *hand* fuses one-to-one with the ditransitive, which contributes nothing (Fig. 2.5). -/
theorem isFusion_hand : (ditransitive .actual).meaning.IsFusion hand handFusion ∧
    (ditransitive .actual).meaning.contributed handFusion = [] := by decide

/-- `PutRole` enumerates the participant roles of *put* (Fig. 2.7). -/
inductive PutRole | putter | putPlace | puttee
  deriving DecidableEq, Fintype

/-- *put* profiles all three roles: "a putter is a type of cause", the put.place role "is a type
of goal", and the put-thing is compatible with the theme (pp. 52–53). -/
def put : Participants PutRole Role where
  profiled := .univ
  construals | .putter => {.cause} | .putPlace => {.goal} | .puttee => {.theme}

/-- `putFusion` fuses *put* with caused motion (Fig. 2.7). -/
def putFusion : PutRole → Option Role
  | .putter => some .cause | .putPlace => some .goal | .puttee => some .theme

theorem isFusion_put : causedMotion.meaning.IsFusion put putFusion := by decide

/-- *put* fuses with caused motion only through the three-role exception: "The Correspondence
Principle allows for one participant role to be linked to a nonprofiled argument role in cases
in which the verb lexically profiles three participant roles" (p. 53). -/
theorem put_uses_exception (f : PutRole → Option Role)
    (h : causedMotion.meaning.IsFusion put f) :
    ∃ p ∈ put.profiled, ∃ r ∈ f p, ¬ causedMotion.meaning.IsProfiled r := by
  revert f; decide +kernel

/-- `MailRole` enumerates the participant roles of *mail* (Fig. 2.8). -/
inductive MailRole | mailer | mailee | mailed
  deriving DecidableEq, Fintype

/-- *mail* profiles only its mailer and mailed (*Paul mailed a letter*, p. 53). -/
def mail : Participants MailRole Role where
  profiled := {.mailer, .mailed}
  construals | .mailer => {.agent} | .mailee => {.recipient} | .mailed => {.patient}

/-- `mailFusion` fuses *mail* with the ditransitive (Fig. 2.8). -/
def mailFusion : MailRole → Option Role
  | .mailer => some .agent | .mailee => some .recipient | .mailed => some .patient

/-- The ditransitive "imposes a profiled status" on the mailee: not lexically profiled, it fuses
with a profiled argument role (p. 53). -/
theorem isFusion_mail : (ditransitive .actual).meaning.IsFusion mail mailFusion ∧
    .mailee ∉ mail.profiled ∧
    ∃ r ∈ mailFusion .mailee, (ditransitive .actual).meaning.IsProfiled r := by
  decide

/-- `KickRole` enumerates the participant roles of *kick* (Fig. 2.9). -/
inductive KickRole | kicker | kicked
  deriving DecidableEq, Fintype

/-- *kick* profiles both its roles, and "the kicker role can only fuse with the agent role ... the
kicked role is an instance of the patient role but not an instance of the recipient role"
(p. 54). -/
def kick : Participants KickRole Role where
  profiled := .univ
  construals | .kicker => {.agent} | .kicked => {.patient}

/-- `kickFusion` fuses *kick* with the ditransitive (Fig. 2.9). -/
def kickFusion : KickRole → Option Role
  | .kicker => some .agent | .kicked => some .patient

/-- *kick* fuses with the ditransitive in only one way: "The participant roles cannot fuse with
the argument roles in any other way" (p. 54). -/
theorem isFusion_kick_iff (f : KickRole → Option Role) :
    (ditransitive .actual).meaning.IsFusion kick f ↔ f = kickFusion := by
  revert f; decide

/-- The ditransitive contributes the recipient to *kick*: "Crucially, the recipient role is
contributed by the construction" (p. 54). -/
theorem contributed_kick :
    (ditransitive .actual).meaning.contributed kickFusion = [.recipient] := by
  decide

/-- `SneezeRole` enumerates the participant role of *sneeze* (Fig. 2.10). -/
inductive SneezeRole | sneezer
  deriving DecidableEq, Fintype

/-- *sneeze* "has a single profiled participant role, a sneezer" (p. 54). -/
def sneeze : Participants SneezeRole Role where
  profiled := .univ
  construals _ := {.cause}

/-- *sneeze* fuses its sneezer with the cause, and caused motion contributes the goal and the
theme (Fig. 2.10). -/
theorem isFusion_sneeze :
    causedMotion.meaning.IsFusion sneeze (fun _ ↦ some .cause) ∧
      causedMotion.meaning.contributed (fun _ : SneezeRole ↦ some .cause) = [.goal, .theme] := by
  decide

/-- `WipeRole` enumerates the participant roles of *wipe* (Fig. 8.2). -/
inductive WipeRole | wiper | wiped
  deriving DecidableEq, Fintype

/-- *wipe* profiles its participant roles ⟨wiper wiped⟩ (p. 189). -/
def wipe : Participants WipeRole Role where
  profiled := .univ
  construals | .wiper => {.agent} | .wiped => {.patient}

/-- `wipeFusion` fuses *wipe* with the resultative (Fig. 8.2). -/
def wipeFusion : WipeRole → Option Role
  | .wiper => some .agent | .wiped => some .patient

/-- `TalkRole` enumerates the participant role of *talk* (Fig. 8.2). -/
inductive TalkRole | talker
  deriving DecidableEq, Fintype

/-- *talk* profiles its single participant role ⟨talker⟩ (p. 189). -/
def talk : Participants TalkRole Role where
  profiled := .univ
  construals _ := {.agent}

/-- The resultative adds only a result-goal to *wipe*, and a patient as well to *talk*: "the
construction can contribute both patient and result-goal roles, as is done in the case of *talk*"
(p. 190). -/
theorem wipe_talk_contributed :
    resultative.meaning.IsFusion wipe wipeFusion ∧
      resultative.meaning.contributed wipeFusion = [.resultGoal] ∧
      resultative.meaning.IsFusion talk (fun _ ↦ some .agent) ∧
      resultative.meaning.contributed (fun _ : TalkRole ↦ some .agent) =
        [.patient, .resultGoal] := by
  decide

/-- `BecomeRole` enumerates the participant roles of *become* (p. 190). -/
inductive BecomeRole | patient | resultGoal
  deriving DecidableEq, Fintype

/-- *become* profiles its participant roles ⟨patient result-goal⟩ (p. 190). -/
def become : Participants BecomeRole Role where
  profiled := .univ
  construals | .patient => {.patient} | .resultGoal => {.resultGoal}

/-- *become* "cannot integrate with the construction, because the construction specifies that
the agent role must be fused with an independently existing participant role of the verb"
(p. 190). -/
theorem not_isFusion_become (f : BecomeRole → Option Role) :
    ¬ resultative.meaning.IsFusion become f := by
  revert f; decide

/-- `AimRole` enumerates the participant roles of *aim* (Fig. 2.14). -/
inductive AimRole | aimer | target
  deriving DecidableEq, Fintype

/-- *aim* ⟨aimer target⟩, an instance of DIRECT-ACTION-AT (p. 64), profiling only its aimer:
the target is not in boldface in Fig. 2.14. -/
def aim : Participants AimRole Role where
  profiled := {.aimer}
  construals | .aimer => {.agent} | .target => {.theme}

/-- *aim* fuses with the conative as an instance of it (Fig. 2.14). -/
theorem isFusion_aim :
    conative.meaning.IsFusion aim (fun | .aimer => some .agent | .target => some .theme) ∧
      conative.meaning.Admits ∅ .subtype := by
  decide

/-! ### The network (§3.3) -/

/-- `Node` enumerates the constructions of the book's network, the ditransitive in each of its
senses and the other argument structure constructions. -/
inductive Node where
  | ditransitive (m : TransferModality)
  | causedMotion
  | intransitiveMotion
  | resultative
  | conative
  deriving DecidableEq, Fintype

/-- `construction n` is the construction at the node `n`; the senses of the ditransitive share its
form. -/
def construction : Node → Construction Sem
  | .ditransitive m => ditransitive m
  | .causedMotion => causedMotion
  | .intransitiveMotion => intransitiveMotion
  | .resultative => resultative
  | .conative => conative

/-- Each construction bears on its form the grammatical functions its meaning links to. -/
theorem construction_linked (n : Node) : (construction n).Linked := by
  revert n; decide

/-- Every construction of the network has a role the verb must supply. -/
theorem exists_obligatory (n : Node) : ∃ a ∈ (construction n).meaning.roles, a.obligatory := by
  revert n; decide

/-- The Shared Participant Condition holds of every construction of the network: it shares a
participant with any verb it fuses with (p. 65). -/
theorem exists_fused {π : Type*} (n : Node) {V : Participants π Role} {f : π → Option Role}
    (h : (construction n).meaning.IsFusion V f) : ∃ p, ∃ r, r ∈ f p :=
  h.exists_fused (exists_obligatory n)

/-- The senses of the ditransitive differ in meaning from its central sense (pp. 75–77). -/
theorem ditransitive_meaning_ne {m : TransferModality} (hm : m ≠ .actual) :
    (ditransitive m).meaning ≠ (ditransitive .actual).meaning := by
  revert m; decide

/-- `network` is the network of chapters 2 and 3, "the entire collection of constructions as
forming a lattice, with individual constructions related by specific types of asymmetric normal
mode inheritance links" (§3.7, p. 99). Each extension of the ditransitive inherits from the
central sense by a polysemy link (pp. 75–77), intransitive motion from caused motion by a subpart
link (p. 78), and the resultative from caused motion by a metaphorical link, change of state as
change of location (pp. 81–84). The conative is in the book's inventory (p. 4) but in no link. -/
def network : Constructicon Node Sem where
  cxn := construction
  mothers
    | .ditransitive .actual => []
    | .ditransitive _ => [(.ditransitive .actual, some .polysemy)]
    | .intransitiveMotion => [(.causedMotion, some .subpart)]
    | .resultative => [(.causedMotion, some .metaphorical)]
    | _ => []

/-- `Node.rank n` is the depth of `n` below the constructions it inherits from. -/
def Node.rank : Node → ℕ
  | .ditransitive .actual | .causedMotion | .conative => 0
  | _ => 1

instance : PartialOrder Node := network.partialOrder Node.rank (by decide)

instance : DecidableLE Node :=
  network.decidableLE [.ditransitive .actual, .causedMotion] (by decide)

/-- Every link respects its type: the extensions of the ditransitive have its form, and
intransitive motion is a proper subpart of caused motion. -/
theorem network_wellTyped : network.WellTyped := by decide

/-- The links make caused motion the resultative's only mother. -/
theorem isMother_resultative_iff (n : Node) :
    network.IsMother .resultative n ↔ n = .causedMotion := by
  revert n; decide

/-- `statedForm n` is the form the construction at `n` states itself, none for the extensions of
the ditransitive: "the
syntactic specifications of the central sense are inherited by the extensions; therefore we do
not need to state the syntactic realization for each extension" (p. 75). -/
def statedForm : Node → Option (TypedForm String)
  | .ditransitive .actual => some (ditransitive .actual).form
  | .ditransitive _ => none
  | n => some (construction n).form

/-- Each sense of the ditransitive inherits the central sense's form. -/
theorem inherited_statedForm (m : TransferModality) :
    DefaultInheritance.inherited statedForm (.ditransitive m) = {(ditransitive .actual).form} := by
  cases m <;> exact DefaultInheritance.inherited_eq_singleton_of_isLeast
    (m := .ditransitive .actual) (by decide) rfl

end Goldberg1995
