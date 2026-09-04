import Mathlib.Data.Fin.VecNotation
import Linglib.Data.Examples.ColeHermon2008
import Linglib.Fragments.TobaBatak.Basic
import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Syntax.Minimalist.Linearization.Replay
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Cole and Hermon 2008: VP raising in a VOS language

Toba Batak is verb-initial: the unmarked clause is V-O-S, with indirect objects and adverbials
after the subject; direct objects and passive agents cannot be extracted while subjects,
indirect objects and adverbials can; and the active subject binds a reflexive object, the
passive agent a reflexive passive subject and, on the authors' own fieldwork, the passive
subject a reflexive passive agent, while the active object cannot bind a reflexive subject. The
paper derives all three from one derivation. The verb adjoins to Voice, the indirect object and
then the subject raise out of VoiceP to specifiers of functional heads, and the remnant VoiceP
raises over them, so word order is the order of extraction.

Whatever is still inside VoiceP when it raises is frozen there, so the object and the passive
agent, which never leave, cannot be extracted. Binding requires c-command at some stage of the
derivation, so the passive agent binds from the base and the passive subject after it raises
past the agent, while the active object never c-commands the subject. Schachter and Sugamoto's
Semantic Hierarchy Condition, actor over patient over dative, licenses the passive agent but
cannot separate the passive subject as antecedent, acceptable if less usual (Table 1's Type
B), from the active object as antecedent, ill-formed for every speaker (Type C); surface
c-command fits neither VOS passive and reconstruction to the last stage before VoiceP raises
only one of them.

Surface SVO clauses raise the subject once more, past the fronted VoiceP, so they freeze the
object as VOS clauses do, against the hypothesis that VoiceP stays in place. The sides at
which Merge attaches the material inside vP change neither the derived objects nor the
surface order, which the paper takes as grounds to propose that Merge is unordered and order
a by-product of Move. English, whose passive agent is an adjunct below the patient, lets the
patient bind it but never the converse.

The derivation is a `Derivation` on the syntactic-object carrier with its stages read by the
replay, `Frozen` is containment in a moved constituent, `CCommandsAt` c-command at a stage
and `BindsAtSomeStage` at some stage, and the paper's examples are the rows:
`vos_hypothesis_only` and `derivational_only` single out, among the candidate analyses of
word order and of binding, the paper's own, `table1` derives its three grades, `stageAt_sides`
and `surface_sides` are the §6 claim over every attachment choice, and `english_passive` the
§7 contrast.

## Implementation notes

* The clause is a token of the paper's transitive frame on the carrier; the substrate's
  clause types serve other theories (Landau's inflection–complementizer pair, the surface
  Binding-Principle clause over words, valency frames). Its slots are the two positions of
  vP, `ArgPosition`, extended by the ditransitive goal, and the paper's roles are read off
  them.
* Voice and v are separate heads (fn. 20). The carrier has no head adjunction: the verb and
  then Voice re-Merge at the VoiceP root, standing in for the two raisings of (51)–(52) that
  the paper draws as one right adjunction (53), so the raised VoiceP is
  `{Voice, {V, {t, vP}}}` rather than a complex head over vP; nothing about the DPs depends
  on the difference. The functional heads F, whether T or Asp (fn. 22), are `Cat.T`; the
  paper's unfilled XP in Spec,VoiceP is omitted.
* The replay externalizes leaf Merge only, so a goal PP enters as one leaf, as the paper
  fronts it. The wh-step itself is not modelled: freezing asks whether the argument sits in a
  constituent some step of the derivation moved, which the remnant, carrying the evacuees'
  traces, decides; fn. 18's caveat on extraction from moved complements is the paper's.
* Binding and freezing are stated on the derivation's own stages: the replay's object at a
  stage forgets to `Derivation.stageAt`, so a c-command fact decided on the replay is one
  about the unordered syntactic object. A stage whose replay fails c-commands nothing; the
  surface-order theorems witness that every derivation here replays.
* The rows record their configuration in paper features; the theorems decode it into a
  schematic clause and compare the derivation's prediction with the row's judgment.

## TODO

* Adverbials ((15)–(16), (47)–(48)), which fn. 25 evacuates like the goal, the NP- and
  PP-internal antecedents of §3.6 ((30)–(34)) and the object–goal data of §3.4 ((18)–(20),
  (22)–(23)) are not modelled, since a PP is a leaf.
* Fn. 28 offers two readings of the Type A over Type B preference, a preference for
  reconstruction or the Semantic Hierarchy as a separate constraint; only the second is
  formalized.
* The paper's conditional remark that its English passive excludes Collins's smuggling
  derivation is prose; a smuggling derivation on the carrier belongs with Collins 2005.

## References

* [P. Cole and G. Hermon, *VP Raising in a VOS Language* (2008)][cole-hermon-2008]
* [S. Chung, *Properties of VOS Languages* (2006)][chung-2006]
* [P. Schachter, *Semantic-Role-Based Syntax in Toba Batak* (1984)][schachter-1984]
* [N. Sugamoto, *Reflexives in Toba Batak* (1984)][sugamoto-1984]
* [R. K. Larson, *On the Double Object Construction* (1988)][larson-1988]
* [J. R. Ross, *Constraints on Variables in Syntax* (1967)][ross-1967]
* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
-/

namespace ColeHermon2008

open Minimalist SyntacticObject
open TobaBatak (Voice)
open Data.Examples (LinguisticExample)

/-! ### Stages, freezing and binding -/

/-- `x` c-commands `y` at stage `n` of `d`: in the ordered object the replay reaches after `n`
steps, which forgets to `d.stageAt n`. -/
def CCommandsAt (d : Derivation) (n : ℕ) (x y : SyntacticObject) : Prop :=
  ∃ p ∈ (d.take n).externalize?, cCommandsIn p x y

instance (d : Derivation) (n : ℕ) (x y : SyntacticObject) : Decidable (CCommandsAt d n x y) := by
  unfold CCommandsAt; infer_instance

/-- The stage the predicate looks at is the derivation's own. -/
theorem CCommandsAt.cCommandsIn_stageAt {d : Derivation} {n : ℕ} {x y : SyntacticObject}
    (h : CCommandsAt d n x y) : cCommandsIn (d.stageAt n) x y :=
  let ⟨_, hp, hc⟩ := h
  d.externalize?_take_faithful n hp ▸ hc

/-- Derivational binding, the paper's optional reconstruction (fn. 28): the antecedent
c-commands the reflexive at some stage of the derivation. -/
def BindsAtSomeStage (d : Derivation) (x y : SyntacticObject) : Prop :=
  ∃ n ≤ d.length, CCommandsAt d n x y

instance (d : Derivation) (x y : SyntacticObject) : Decidable (BindsAtSomeStage d x y) := by
  unfold BindsAtSomeStage; infer_instance

/-- `x` is frozen in `d`: it sits inside a constituent the derivation has moved, an island for
later extraction (§4, after [ross-1967]'s Sentential Subject Constraint). -/
def Frozen (d : Derivation) (x : SyntacticObject) : Prop := ∃ m ∈ d.movedItems, contains m x

instance (d : Derivation) (x : SyntacticObject) : Decidable (Frozen d x) := by
  unfold Frozen; infer_instance

/-! ### The clause and its derivations (§4.1–§4.2) -/

/-- The slots a clause's arguments fill: the two core positions of vP, the external one the
agent's and the internal one the patient's, and the goal of a ditransitive. -/
inductive Arg
  | core (p : ArgumentStructure.ArgPosition)
  | goal
  deriving DecidableEq, Repr

/-- The role the slot bears in the paper's clauses, the Semantic Hierarchy's actor, patient and
dative. -/
def Arg.role : Arg → ThetaRole
  | .core .external => .agent
  | .core .internal => .patient
  | .goal => .goal

/-- A transitive clause: its voice, verb, agent and patient, and the goal PP of a ditransitive,
which enters as one leaf. -/
structure Clause where
  /-- The voice, which picks the pivot. -/
  voice : Voice
  /-- The verb, the derivation's initial object. -/
  verb : LIToken
  /-- The agent, Merged as the specifier of vP. -/
  agent : LIToken
  /-- The patient, the verb's complement or, in a ditransitive, the specifier of VP. -/
  patient : LIToken
  /-- The goal PP of a ditransitive, one leaf. -/
  goal : Option LIToken

/-- The silent light verb. -/
private def v₀ : LIToken := ⟨.simple .v [], 6⟩

/-- The `i`-th functional head F, for `i ≥ 1`. -/
private def F (i : ℕ) : LIToken := ⟨.simple .T [], 6 + i⟩

/-- The side at which each of the five base Merges attaches its item, `true` on the left. -/
abbrev Sides := Fin 5 → Bool

/-- External Merge on the side `left`. -/
def em (left : Bool) (item : SyntacticObject) : Step := if left then .emL item else .emR item

namespace Clause

/-- A clause from its words, the tokens numbered verb, agent, patient and goal after the voice
head. -/
def of (voice : Voice) (verb agent patient : String) (goal : Option String := none) : Clause :=
  ⟨voice, ⟨.simple .V [] (phonForm := verb), 2⟩, ⟨.simple .N [] (phonForm := agent), 3⟩,
    ⟨.simple .N [] (phonForm := patient), 4⟩,
    goal.map fun g => ⟨.simple .P [] (phonForm := g), 5⟩⟩

variable (c : Clause)

/-- The voice head, *mang-* or *di-*. -/
def voiceHead : LIToken := ⟨.simple .Voice [] (phonForm := c.voice.affix), 1⟩

/-- The argument as a token, the goal when there is one. -/
def arg? : Arg → Option LIToken
  | .core .external => some c.agent
  | .core .internal => some c.patient
  | .goal => c.goal

/-- The pivot, the argument the voice raises to subject position: the agent in the active and
the patient in the passive. -/
def pivot : LIToken := if c.voice.promotes = .agent then c.agent else c.patient

/-- The sides of the paper's own trees (50) and (57): complements on the right; the light verb,
the agent, Voice and, in a ditransitive, the patient, [larson-1988]'s specifier of VP, on the
left. -/
def paperSides : Sides := ![false, c.goal.isSome, true, true, true]

/-- The base (50), (57), `{Voice, {Agent, {v, VP}}}`: the verb takes the patient, or the goal
and then the patient, then the light verb, the agent and Voice, each Merge on the side `σ`
gives. -/
def base (σ : Sides) : List Step :=
  c.goal.toList.map (em (σ 0)) ++
    [em (σ 1) c.patient, em (σ 2) v₀, em (σ 3) c.agent, em (σ 4) c.voiceHead]

/-- The verb adjoins to Voice, (51)–(52): the verb raises and Voice raises over it. -/
def verbToVoice : List Step := [.im c.verb, .im c.voiceHead]

/-- The goal, then the pivot, raise to specifiers of F, (59)–(60), (63)–(64), (72)–(73): the
order of extraction that places the goal after the subject. -/
def evacuate : List Step :=
  (c.goal.toList.flatMap fun pp => [.emL (F 1), .im pp]) ++ [.emL (F 2), .im c.pivot]

/-- The remnant VoiceP that raises, (55), (61): Voice and the verb over their traces, the pivot
and the goal replaced by theirs. -/
def remnant : PlanarSyntacticObject :=
  let leaf := PlanarSyntacticObject.leaf
  let trace := PlanarSyntacticObject.traceOf
  let stranded (tok : LIToken) := if tok = c.pivot then trace tok else leaf tok
  let vp : PlanarSyntacticObject := match c.goal with
    | some pp => {stranded c.patient, {trace c.verb, trace pp}}
    | none => {trace c.verb, stranded c.patient}
  {leaf c.voiceHead, {leaf c.verb, {trace c.voiceHead, {stranded c.agent, {leaf v₀, vp}}}}}

/-- The derivation up to the last stage before VoiceP raises, an SVO stage: (54), (60), (64),
(73), (76). -/
def svoStage (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ c.verbToVoice ++ c.evacuate⟩

/-- The VOS derivation, (55), (61), (65), (74), (77): the remnant VoiceP raises over the
evacuated goal and pivot. -/
def vos (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, (c.svoStage σ).steps ++ [.emL (F 3), .im c.remnant]⟩

/-- The SVO derivation under the VOS Hypothesis, (83)–(84): the pivot raises once more, past
the fronted VoiceP. -/
def svo (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, (c.vos σ).steps ++ [.emL (F 4), .im c.pivot]⟩

/-- The SVO derivation under the SVO Hypothesis (§5), for which the paper draws no tree: the
pivot raises and VoiceP, the goal inside it, stays. -/
def svoInPlace (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ c.verbToVoice ++ [.emL (F 2), .im c.pivot]⟩

/-- The marked V-O-IO-S order (14), the pivot extracted before the goal; fn. 25 derives the
adverbial (16) the same way. -/
def vois (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ c.verbToVoice ++ [.emL (F 1), .im c.pivot] ++
    (c.goal.toList.flatMap fun pp => [.emL (F 2), .im pp]) ++ [.emL (F 3), .im c.remnant]⟩

end Clause

/-! ### Word order (§3.1, §3.3, §4.1, §4.2, §5) -/

/-- (49) *Mang-ida si-Mary si-John* 'John saw Mary'. -/
def ex49 : Clause := .of .av "ida" "si-John" "si-Mary"

/-- (56) *Mang-alean buku si-John tu si-Mary* 'John gave a book to Mary'. -/
def ex56 : Clause := .of .av "alean" "si-John" "buku" "tu si-Mary"

/-- (13) without *sada* 'one', *Di-lean si-John buku tu si-Mary* 'The book was given to Mary by
John', and (14). -/
def ex13 : Clause := .of .ov "lean" "si-John" "buku" "tu si-Mary"

/-- (67) *Di-ida si-Torus dirina* 'Himself was seen by Torus'. -/
def ex67 : Clause := .of .ov "ida" "si-Torus" "dirina"

/-- (81) *Dakdanak-on mang-atuk biang-i* 'This boy hit the dog'. -/
def ex81 : Clause := .of .av "atuk" "dakdanak-on" "biang-i"

/-- (85) *Si-John mang-alean aha tu si-Mary* 'What did John give to Mary?'. -/
def ex85 : Clause := .of .av "alean" "si-John" "aha" "tu si-Mary"

/-- The monotransitive VOS clause (49) and the passive (67). -/
theorem vos_orders :
    ex49.vos.surfacePhon = ["mang-", "ida", "si-Mary", "si-John"] ∧
      ex67.vos.surfacePhon = ["di-", "ida", "si-Torus", "dirina"] := by
  decide

/-- The ditransitive V-O-S-IO clause (56), the goal evacuated before the subject. -/
theorem ex56_vosi :
    ex56.vos.surfacePhon = ["mang-", "alean", "buku", "si-John", "tu si-Mary"] := by decide

/-- The passive (13) and, with the subject evacuated first, the marked (14). -/
theorem ex13_orders :
    ex13.vos.surfacePhon = ["di-", "lean", "si-John", "buku", "tu si-Mary"] ∧
      ex13.vois.surfacePhon = ["di-", "lean", "si-John", "tu si-Mary", "buku"] := by
  decide

/-- (81) in both orders: the SVO derivation raises the subject past the fronted VoiceP. -/
theorem ex81_orders :
    ex81.vos.surfacePhon = ["mang-", "atuk", "biang-i", "dakdanak-on"] ∧
      ex81.svo.surfacePhon = ["dakdanak-on", "mang-", "atuk", "biang-i"] := by
  decide

/-- The SVO ditransitive (85), S-V-O-IO. -/
theorem ex85_svoi :
    ex85.svo.surfacePhon = ["si-John", "mang-", "alean", "aha", "tu si-Mary"] := by decide

/-! ### Every clause goes through a VOS stage (§5) -/

/-- The SVO derivation extends the VOS derivation. -/
theorem svo_take_vos (c : Clause) (σ : Sides) : (c.svo σ).take (c.vos σ).length = c.vos σ := by
  unfold Derivation.take
  rw [Derivation.length, Clause.svo, List.take_left]
  rfl

/-- Freezing is the same in SVO and VOS clauses: the further raising of the pivot, a leaf,
freezes nothing. -/
theorem frozen_svo_iff (c : Clause) (σ : Sides) (x : SyntacticObject) :
    Frozen (c.svo σ) x ↔ Frozen (c.vos σ) x := by
  simp [Frozen, Derivation.movedItems, Clause.svo, List.filterMap_append]

/-! ### The rows -/

/-- The word order of a clause. -/
inductive WordOrder
  | vos | svo
  deriving DecidableEq, Repr

/-- The two analyses of SVO clauses (§5): every clause passes through VOS, or VoiceP stays in
place in SVO clauses. -/
inductive OrderHypothesis
  | vosHypothesis | svoHypothesis
  deriving DecidableEq, Repr

/-- The derivation of a clause in the given order under the hypothesis. -/
def Clause.derivation (c : Clause) : OrderHypothesis → WordOrder → Derivation
  | _, .vos => c.vos
  | .vosHypothesis, .svo => c.svo
  | .svoHypothesis, .svo => c.svoInPlace

/-- The value of a row's feature, read through a table; `List.lookup` keeps key and value in
one universe. -/
private def parse? {α : Type} (table : List (String × α)) (row : LinguisticExample)
    (key : String) : Option α :=
  row.feature? key >>= (List.lookup · table)

private def voices : List (String × Voice) := [("active", .av), ("passive", .ov)]
private def orders : List (String × WordOrder) := [("VOS", .vos), ("SVO", .svo)]
private def args : List (String × Arg) :=
  [("agent", .core .external), ("patient", .core .internal), ("goal", .goal)]

/-- Toba Batak's Glottocode. -/
private def tobaBatak : Data.Examples.Glottocode := "bata1289"

/-- English's Glottocode. -/
private def english : Data.Examples.Glottocode := "stan1293"

/-! ### Extraction (§3.2, §4, §5) -/

/-- An extraction datum's configuration: a wh-phrase in the given argument slot, fronted or in
situ, in a clause of the given voice, order and transitivity. -/
structure Extraction where
  /-- The clause's voice. -/
  voice : Voice
  /-- The clause's word order. -/
  order : WordOrder
  /-- Whether the clause has a goal PP. -/
  ditransitive : Bool
  /-- The argument slot the wh-phrase fills. -/
  extracted : Arg
  /-- Whether the wh-phrase is fronted rather than in situ. -/
  fronted : Bool

namespace Extraction

/-- A schematic clause of the configuration. -/
def clause (e : Extraction) : Clause :=
  .of e.voice "V" "Agent" "Patient" (if e.ditransitive then some "PP" else none)

/-- The prediction under a hypothesis: a fronted wh-phrase is licit exactly when it is not
frozen; in situ it is unconstrained. -/
def Licit (e : Extraction) (hyp : OrderHypothesis) : Prop :=
  e.fronted → ∃ x ∈ e.clause.arg? e.extracted, ¬ Frozen (e.clause.derivation hyp e.order) x

instance (e : Extraction) (hyp : OrderHypothesis) : Decidable (e.Licit hyp) := by
  unfold Licit; infer_instance

/-- The configuration a row records. -/
def ofRow (row : LinguisticExample) : Option Extraction := do
  guard (row.feature? "construction" = some "extraction")
  return ⟨← parse? voices row "voice", ← parse? orders row "order",
    ← parse? [("monotransitive", false), ("ditransitive", true)] row "transitivity",
    ← parse? args row "extracted", ← parse? [("fronted", true), ("inSitu", false)] row "wh"⟩

end Extraction

/-- Only the VOS Hypothesis fits the extraction data ((7)–(10), (43)–(44), (85)–(88)): the
direct object and the passive agent, frozen in the fronted VoiceP, cannot be fronted in either
order, the goal, evacuated before VoiceP raises, can, and with VoiceP in place the object of an
SVO clause would be free. -/
theorem vos_hypothesis_only (hyp : OrderHypothesis) :
    (∀ row ∈ Examples.all, ∀ e ∈ Extraction.ofRow row,
      (row.judgment ≠ .ungrammatical ↔ e.Licit hyp)) ↔ hyp = .vosHypothesis := by
  cases hyp <;> decide

/-! ### Binding (§3.4–§3.7, §4.3) -/

/-- [schachter-1984]'s Semantic Hierarchy (28a), actor > patient > dative, as ranks. -/
def rank : ThetaRole → Option ℕ
  | .agent => some 0
  | .patient => some 1
  | .goal => some 2
  | _ => none

/-- `r` outranks `s` on the Semantic Hierarchy, the antecedency condition (28b) of
[schachter-1984] and [sugamoto-1984], strictly: fn. 14 reads it so, since only then does the
absence of dative antecedents follow. -/
def Outranks (r s : ThetaRole) : Prop := ∃ i ∈ rank r, ∃ j ∈ rank s, i < j

instance : DecidableRel Outranks := fun _ _ => by unfold Outranks; infer_instance

/-- A binding datum's configuration: the antecedent's and the reflexive's argument slots in a
clause of the given voice and order. -/
structure Reflexivization where
  /-- The clause's voice. -/
  voice : Voice
  /-- The clause's word order. -/
  order : WordOrder
  /-- The argument slot of the antecedent. -/
  antecedent : Arg
  /-- The argument slot of the reflexive. -/
  reflexive : Arg

namespace Reflexivization

/-- A schematic clause of the configuration. -/
def clause (a : Reflexivization) : Clause := .of a.voice "V" "Agent" "Patient"

/-- The antecedent and the reflexive as objects. -/
def pair? (a : Reflexivization) : Option (SyntacticObject × SyntacticObject) := do
  return ((← a.clause.arg? a.antecedent), (← a.clause.arg? a.reflexive))

/-- The derivation of the clause, through VOS. -/
def derivation (a : Reflexivization) : Derivation := a.clause.derivation .vosHypothesis a.order

/-- The configuration a row records. -/
def ofRow (row : LinguisticExample) : Option Reflexivization := do
  guard (row.feature? "construction" = some "binding" ∧ row.language = tobaBatak)
  return ⟨← parse? voices row "voice", ← parse? orders row "order",
    ← parse? args row "antecedent", ← parse? args row "reflexive"⟩

end Reflexivization

/-- The candidate binding conditions of §4.3: c-command at the surface, at the last stage
before VoiceP raises, at some stage, and the Semantic Hierarchy Condition. -/
inductive BindingTheory
  | surface | lastSVOStage | derivational | semanticHierarchy
  deriving DecidableEq, Repr

/-- The condition licenses the configuration. -/
def BindingTheory.Licenses : BindingTheory → Reflexivization → Prop
  | .surface, a => ∃ p ∈ a.pair?, CCommandsAt a.derivation a.derivation.length p.1 p.2
  | .lastSVOStage, a =>
      ∃ p ∈ a.pair?, CCommandsAt a.clause.svoStage a.clause.svoStage.length p.1 p.2
  | .derivational, a => ∃ p ∈ a.pair?, BindsAtSomeStage a.derivation p.1 p.2
  | .semanticHierarchy, a => Outranks a.antecedent.role a.reflexive.role

instance (th : BindingTheory) (a : Reflexivization) : Decidable (th.Licenses a) := by
  cases th <;> (unfold BindingTheory.Licenses; infer_instance)

/-- Only c-command at some stage fits the binding data of Table 1 ((17), (21), (37), (62),
(66)–(68)): surface c-command loses every VOS antecedent, (62) and both passive orders
(67)–(68), reconstruction to the last SVO stage loses the passive agent (67), and the Semantic
Hierarchy loses the passive subject ((37), (68)). -/
theorem derivational_only (th : BindingTheory) :
    (∀ row ∈ Examples.all, ∀ a ∈ Reflexivization.ofRow row,
      (row.judgment ≠ .ungrammatical ↔ th.Licenses a)) ↔ th = .derivational := by
  cases th <;> decide

/-- Table 1's grades. -/
inductive Grade
  | typeA | typeB | typeC
  deriving DecidableEq, Repr

/-- The grade of a configuration, reading the Semantic Hierarchy Condition as an addition to
derivational binding rather than a substitute for it (§3.7): Type A when the antecedent
c-commands the reflexive at some stage and outranks it, Type B when it c-commands without
outranking, Type C when it never c-commands. -/
def Reflexivization.grade (a : Reflexivization) : Grade :=
  if BindingTheory.derivational.Licenses a then
    if BindingTheory.semanticHierarchy.Licenses a then .typeA else .typeB
  else .typeC

/-- Table 1 derived: each row's grade. -/
theorem table1 : ∀ row ∈ Examples.all, ∀ a ∈ Reflexivization.ofRow row,
    ∀ g ∈ parse? [("A", Grade.typeA), ("B", .typeB), ("C", .typeC)] row "tableOne",
      a.grade = g := by
  decide

/-- The passive (67)–(68) stage by stage, (72)–(74) and (75)–(77): the agent c-commands the
patient once the verb has adjoined to Voice, stage 6, and not once the patient has raised, the
patient c-commands the agent once raised and not before, and neither does at the surface, once
VoiceP has raised. -/
theorem passive_stages :
    (CCommandsAt ex67.vos 6 ex67.agent ex67.patient ∧
      ¬ CCommandsAt ex67.vos ex67.svoStage.length ex67.agent ex67.patient) ∧
    (¬ CCommandsAt ex67.vos 6 ex67.patient ex67.agent ∧
      CCommandsAt ex67.vos ex67.svoStage.length ex67.patient ex67.agent) ∧
    (¬ CCommandsAt ex67.vos ex67.vos.length ex67.agent ex67.patient ∧
      ¬ CCommandsAt ex67.vos ex67.vos.length ex67.patient ex67.agent) := by
  decide

/-! ### Merge is unordered (§6) -/

/-- External Merge on either side has the same leftward form. -/
@[simp] theorem leftward_em (left : Bool) (item : SyntacticObject) :
    (em left item).leftward = .emL item := by
  cases left <;> rfl

/-- Up to the sides of its Merges, the VOS derivation is one derivation. -/
theorem vos_leftward (c : Clause) (σ σ' : Sides) :
    (c.vos σ).leftward = (c.vos σ').leftward := by
  simp [Derivation.leftward, Clause.vos, Clause.svoStage, Clause.base]

/-- The sides at which the base Merges attach change no stage of the derivation, so binding,
which reads the stages, cannot see them ((89)–(94)). -/
theorem stageAt_sides (c : Clause) (σ σ' : Sides) (n : ℕ) :
    (c.vos σ).stageAt n = (c.vos σ').stageAt n := by
  rw [← Derivation.stageAt_leftward, vos_leftward c σ σ', Derivation.stageAt_leftward]

/-- Nor can freezing, which reads the movers. -/
theorem frozen_sides (c : Clause) (σ σ' : Sides) (x : SyntacticObject) :
    Frozen (c.vos σ) x ↔ Frozen (c.vos σ') x := by
  unfold Frozen
  rw [← Derivation.movedItems_leftward, vos_leftward c σ σ', Derivation.movedItems_leftward]

/-- Nor the surface order (56): every one of the thirty-two attachments, (57), (91) and, up to
the omitted XP, (89) among them, externalizes to V-O-S-IO. -/
theorem surface_sides (σ : Sides) :
    (ex56.vos σ).surfacePhon = ["mang-", "alean", "buku", "si-John", "tu si-Mary"] := by
  revert σ; decide

/-! ### English passives (§7) -/

private def wasInjured : LIToken := ⟨.simple .V [] (phonForm := "was injured"), 21⟩
private def theBoy : LIToken := ⟨.simple .N [] (phonForm := "the boy"), 22⟩
private def byHimself : LIToken := ⟨.simple .P [] (phonForm := "by himself"), 23⟩

/-- The English passive (97)–(98) of (95): the patient as [larson-1988]'s specifier of VP, the
agent an adjunct, a *by*-phrase leaf below it, and no argument in Spec,vP, since the passive
participle projects none; the patient raises to Spec,FP, Spec,TP in English. -/
def englishPassive : Derivation :=
  ⟨wasInjured, [.emR byHimself, .emL theBoy, .emL v₀, .emL (F 1), .im theBoy]⟩

/-- (95) externalizes. -/
theorem english_order :
    englishPassive.surfacePhon = ["the boy", "was injured", "by himself"] := by decide

/-- The pair a row's roles pick out in the English derivation: the patient is the raised DP,
the agent the *by*-phrase, which fills no core position. -/
def englishPair? (row : LinguisticExample) : Option (SyntacticObject × SyntacticObject) := do
  guard (row.feature? "construction" = some "binding" ∧ row.language = english)
  let slot (a : Arg) : Option SyntacticObject := match a.role with
    | .patient => some theBoy
    | .agent => some byHimself
    | _ => none
  let antecedent ← slot (← parse? args row "antecedent")
  let reflexive ← slot (← parse? args row "reflexive")
  return (antecedent, reflexive)

/-- (95)–(96): the patient binds the agent, which never c-commands it. Raising the patient
reverses its c-command relation with the agent only when the agent is an argument above it, as
in Toba Batak; the paper remarks, without arguing it, that if this treatment of English is
right, [collins-2005]'s smuggling derivation, in which the passive agent is Merged as in the
active, cannot be maintained. -/
theorem english_passive : ∀ row ∈ Examples.all, ∀ p ∈ englishPair? row,
    (row.judgment ≠ .ungrammatical ↔ BindsAtSomeStage englishPassive p.1 p.2) := by
  decide

end ColeHermon2008
