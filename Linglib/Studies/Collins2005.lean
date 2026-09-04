import Linglib.Data.Examples.Collins2005
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Movement.Freezing
import Linglib.Syntax.Minimalist.Movement.Remnant
import Linglib.Syntax.Minimalist.Movement.Smuggling

/-!
# Collins 2005: a smuggling approach to the passive in English

The principles-and-parameters passive lets the suffix *-en* absorb accusative Case and the
external θ-role, so that the agent of *The book was written by John* is Merged nowhere near
where the agent of the active is Merged, against the uniformity of θ-assignment. Collins
returns to Syntactic Structures on this point: the external argument is Merged in Spec,vP in
the passive exactly as in the active, the participle head Part takes the VP and vP takes PartP,
and the verb precedes the external argument because PartP moves to the specifier of a VoiceP
headed by *by*, a head of uninterpretable features that takes a vP complement and checks the
Case that v checks in the active. That the movement is of the phrase and not of the verb's
head is shown by particles and stranded prepositions, which precede the external argument and
cannot follow it. The structure also orders the auxiliaries: *have* c-selects a participle,
Voice attracts one, and a participle must be licensed by exactly one of them, which admits
*has seen* and *was seen by* and excludes *has seen by* and *was seen*.

The movement is smuggling: the object inside PartP, which the external argument in Spec,vP
c-commands and so shields from Infl by Relativized Minimality, is carried past it, after which
the object is Infl's closest goal and raises to Spec,IP. Without the movement, or with head
movement of the verb alone, the object stays behind the external argument and the passive
cannot be derived; the derivation extracts the object from a moved constituent, and the paper
takes Freezing not to hold of PartP movement. A PP that follows the by-phrase has evacuated
PartP before the remnant fronted, so the external argument c-commands it, and a PP that precedes
the by-phrase has not, so it does not: negative polarity, *each* … *the other* and Principle C
line up with the position of the PP. A reflexive or a bound variable inside the fronted PartP
is bound only by reconstruction, which the paper takes to be marginal, and Principle B applies
as the external argument is Merged, so a coindexed pronoun inside PartP is out however PartP
later moves.

The passive is a `Derivation` on the syntactic-object carrier under each of the three analyses,
the surface strings are its externalizations, Relativized Minimality is the substrate's
closest-goal relation at the stage where Infl attracts, smuggling and remnant fronting are the
substrate's step predicates, and the paper's examples are the rows: `rm_converges` singles out
PartP movement, `licensing_rows` derives the c-command and binding judgments from surface and
derivational c-command, `participle_rows` the auxiliary paradigm from the licensing principle,
and `active_shares_vP` is the θ-uniformity the analysis was built for.

## Implementation notes

* Part is `Cat.Asp`, silent, and the verb's raising to it (8) is not modelled: the participle
  is the verb's leaf. Voice is `by` with selection stack `[v]`, so a by-phrase over a DP is
  exocentric, the paper's (29). The evacuation host X of (58), AgrP or LkP for the paper, is a
  second `Cat.Asp` layer selecting PartP and the PP, so that v's selection is uniform; the
  object sits in Spec,VP rather than the paper's Spec,PartP. A PP enters as one leaf, and
  c-command of the leaf stands for c-command of the DP inside it.
* The rival analyses of (11) are the same derivation up to VoiceP: PartP movement raises the
  participle phrase, head movement re-Merges the verb's leaf at the root, standing in for the
  adjunction of (13), and the in-situ analysis raises nothing before the object moves.
  Convergence is whether the object is a closest D-goal for Infl at the stage where it raises;
  the Case side of the argument is prose.
* Principle A and bound-variable binding are evaluated at the surface, with reconstruction to
  any stage as the degraded option; Principle B at any stage, without the local-domain and
  Case-checked clauses of (83), which the monoclausal rows never exercise; Principle C at the
  surface, as §9 argues.

## TODO

* The double-object (53)–(54), the ECM and CP cases of (55), (57) and (81), the Principle C
  data (76)–(77), the freezing and reciprocal data of §10 ((88)–(93)), the quantifier-raising
  data of (94)–(98), and the Kiswahili and Japanese passives of §5 are not modelled.
* The Case checking by *by* and by the null Voice of short passives (§4, §6) is stated in
  prose; nothing here derives (47).

## References

* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
* [A. Barss and H. Lasnik, *A Note on Anaphora and Double Objects* (1986)][barss-lasnik-1986]
* [G. Müller, *Incomplete Category Fronting* (1998)][muller-1998]
* [J. Sabel, *Restrukturierung und Lokalität* (1996)][sabel-1996]
-/

namespace Collins2005

open Minimalist SyntacticObject
open Data.Examples (LinguisticExample)

/-! ### The passive and its rival derivations (§2–§5) -/

/-- What places the participle before the external argument (§3, (11)–(14)): PartP moves to
Spec,VoiceP, the verb alone moves to Voice, or nothing moves. -/
inductive Analysis
  | partP | headMovement | inSitu
  deriving DecidableEq, Repr

/-- A transitive clause: its verb, external and internal arguments, the auxiliary of its passive,
and an optional third element of VP, one leaf: a particle, the complement of V with the object
in Spec,VP (17), or a PP, the leaf standing in for the PP the pseudo-passive strands its
preposition from. -/
structure Clause where
  /-- The verb, in its participial form. -/
  verb : LIToken
  /-- The external argument, Merged in Spec,vP. -/
  agent : LIToken
  /-- The internal argument. -/
  patient : LIToken
  /-- The auxiliary *be*. -/
  be : LIToken
  /-- A particle, stranded preposition or PP, the verb's complement with the patient in Spec,VP
  (17). -/
  extra : Option LIToken

/-- The participle head, silent, over the VP. -/
private def part₀ : LIToken := ⟨.simple .Asp [.V], 5⟩

/-- The light verb, over PartP and the external argument. -/
private def v₀ : LIToken := ⟨.simple .v [.Asp, .D], 6⟩

/-- Voice, *by*, which takes a vP (§4). -/
private def by₀ : LIToken := ⟨.simple .Voice [.v] (phonForm := "by"), 7⟩

/-- The host X of an evacuated PP, (58): a second participial layer over PartP that takes the
PP, so that v selects the same category with or without evacuation. -/
private def x₀ : LIToken := ⟨.simple .Asp [.Asp, .P], 8⟩

/-- Infl. -/
private def infl₀ : LIToken := ⟨.simple .T [], 9⟩

/-- The auxiliary *have* of the active perfect (26). -/
private def has₀ : LIToken := ⟨.simple .V [] (phonForm := "has"), 10⟩

/-- A leaf is a DP. -/
def hasD (s : SyntacticObject) : Bool := s.getLIToken.any (·.item.outerCat == .D)

namespace Clause

/-- A clause from its words. -/
def of (verb agent patient : String) (extra : Option String := none) (be : String := "was") :
    Clause :=
  ⟨⟨.simple .V (if extra.isSome then [.P, .D] else [.D]) (phonForm := verb), 1⟩,
    ⟨.simple .D [] (phonForm := agent), 2⟩,
    ⟨.simple .D [] (phonForm := patient), 3⟩, ⟨.simple .V [] (phonForm := be), 4⟩,
    extra.map λ x => ⟨.simple .P [] (phonForm := x), 11⟩⟩

variable (p : Clause)

/-- The VP: the verb and its object (8), or with a third element `{Patient, {V, X}}` (17). -/
def vpSteps : List Step :=
  match p.extra with
  | some x => [.em .right x, .em .left p.patient]
  | none => [.em .right p.patient]

/-- The PartP at the point it fronts: over the VP, with the evacuated element's trace when it
has left. -/
def partP (evacuate : Bool) : PlanarSyntacticObject :=
  let leaf := PlanarSyntacticObject.leaf
  let vp : PlanarSyntacticObject := match p.extra with
    | some x => {leaf p.patient, {leaf p.verb, if evacuate then .traceOf x else leaf x}}
    | none => {leaf p.verb, leaf p.patient}
  {leaf part₀, vp}

/-- The evacuation of the third element to Spec,XP before PartP fronts, (58a)–(58b). -/
def evacuation (evacuate : Bool) : List Step :=
  match p.extra with
  | some x => if evacuate then [.em .left x₀, .im x] else []
  | none => []

/-- The derivation through vP, the same in the active and the passive (§2): VP, PartP, the
light verb and the external argument. -/
def vP (evacuate : Bool) : Derivation :=
  ⟨p.verb, p.vpSteps ++ [.em .left part₀] ++ p.evacuation evacuate ++
    [.em .left v₀, .em .left p.agent]⟩

/-- Voice Merges over vP, (30). -/
def voiceP (evacuate : Bool) : Derivation := (p.vP evacuate).append [.em .left by₀]

/-- The three analyses: PartP to Spec,VoiceP (14), the verb to Voice (13), or nothing. -/
def fronted (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.voiceP evacuate).append <| match a with
    | .partP => [.im (p.partP evacuate)]
    | .headMovement => [.im p.verb]
    | .inSitu => []

/-- The stage at which Infl attracts: the auxiliary and Infl over VoiceP. -/
def preRaising (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.fronted a evacuate).append [.em .left p.be, .em .left infl₀]

/-- The passive: the object raised to Spec,IP, (22). -/
def passive (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.preRaising a evacuate).append [.im p.patient]

/-- The active perfect (26): *have* and Infl over vP, and the external argument to Spec,IP. -/
def active : Derivation := (p.vP false).append [.em .left has₀, .em .left infl₀, .im p.agent]

/-- The analysis converges: at the stage where Infl attracts, the object is one of its closest
D-goals, so its raising violates neither the Minimal Link Condition nor Relativized
Minimality (§5). -/
def Converges (a : Analysis) (evacuate : Bool) : Prop :=
  ∃ q ∈ (p.preRaising a evacuate).externalize?, isClosestGoalIn q infl₀ p.patient hasD

instance (a : Analysis) (evacuate : Bool) : Decidable (p.Converges a evacuate) := by
  unfold Converges; infer_instance

end Clause

/-- (9), (22), (30): *The book was written by John*. -/
def ex9 : Clause := .of "written" "John" "the book"

/-- (15): *The argument was summed up by the coach*. -/
def ex15 : Clause := .of "summed" "the coach" "the argument" "up"

/-- (18): *John was spoken to by Mary*. -/
def ex18 : Clause := .of "spoken" "Mary" "John" "to"

/-- (56): *The book was given to Mary by John*. -/
def ex56 : Clause := .of "given" "John" "the book" "to Mary"

/-- (23a), (26): *John has seen the book*. -/
def ex23 : Clause := .of "seen" "John" "the book"

/-- The three analyses externalize (9b), and, for the two that do not converge, (9a). -/
theorem ex9_orders :
    (ex9.passive .partP false).surfacePhon = ["the book", "was", "written", "by", "John"] ∧
      (ex9.passive .headMovement false).surfacePhon
        = ["the book", "was", "written", "by", "John"] ∧
      (ex9.passive .inSitu false).surfacePhon
        = ["the book", "was", "by", "John", "written"] := by
  decide

/-- Particles (15) and stranded prepositions (18) tell the analyses apart: PartP movement
carries them before the external argument, head movement strands them after it. -/
theorem particle_orders :
    (ex15.passive .partP false).surfacePhon
        = ["the argument", "was", "summed", "up", "by", "the coach"] ∧
      (ex15.passive .headMovement false).surfacePhon
        = ["the argument", "was", "summed", "by", "the coach", "up"] ∧
      (ex18.passive .partP false).surfacePhon
        = ["John", "was", "spoken", "to", "by", "Mary"] ∧
      (ex18.passive .headMovement false).surfacePhon
        = ["John", "was", "spoken", "by", "Mary", "to"] := by
  decide

/-- A PP pied-piped inside PartP precedes the by-phrase (56c); evacuated to Spec,XP before the
remnant fronts, it follows it (56d). -/
theorem pp_orders :
    (ex56.passive .partP false).surfacePhon
        = ["the book", "was", "given", "to Mary", "by", "John"] ∧
      (ex56.passive .partP true).surfacePhon
        = ["the book", "was", "given", "by", "John", "to Mary"] := by
  decide

/-- The active perfect (23a). -/
theorem active_order : ex23.active.surfacePhon = ["John", "has", "seen", "the book"] := by decide

/-- θ-uniformity (§2): the active and the passive share the derivation through vP, so the
external argument is Merged in Spec,vP in both. -/
theorem active_shares_vP (p : Clause) (a : Analysis) :
    p.active.take (p.vP false).length = (p.passive a false).take (p.vP false).length := by
  simp [Clause.active, Clause.passive, Clause.preRaising, Clause.fronted, Clause.voiceP]

/-! ### Smuggling (§5) -/

/-- PartP movement smuggles the object past the external argument, (34): the external argument
c-commands the object before the step and the fronted PartP c-commands it after; the verb's
head, moved alone, carries no object. -/
theorem partP_smuggles :
    (ex9.passive .partP false).IsSmugglingStep (ex9.voiceP false).length ex9.patient
        ex9.agent ∧
      ¬ (ex9.passive .headMovement false).IsSmugglingStep (ex9.voiceP false).length
        ex9.patient ex9.agent := by
  decide

/-- Relativized Minimality (§5): the object is a closest D-goal for Infl only once smuggled;
in place, or with the verb moved alone, the external argument intervenes, so *The book was by
John written* (9a) and head movement both fail. -/
theorem rm_converges (a : Analysis) :
    ex9.Converges a false ↔ a = .partP := by
  cases a <;> decide

/-- The smuggled object is extracted from a moved constituent: the paper assumes that
[muller-1998]'s Freezing, (35), does not hold of PartP movement (fn. 25). -/
theorem smuggled_frozen : (ex9.passive .partP false).Frozen ex9.patient := by decide

/-- θ-uniformity in the structure: at the vP stage of the active and of the passive alike, the
external argument c-commands the internal one. -/
theorem agent_over_patient_at_vP :
    ex9.active.CCommandsAt (ex9.vP false).length ex9.agent ex9.patient ∧
      (ex9.passive .partP false).CCommandsAt (ex9.vP false).length ex9.agent ex9.patient := by
  decide

/-- The evacuated-PP derivation (58) fronts a remnant: PartP carries the PP's trace. -/
theorem pp_remnant : (ex56.passive .partP true).IsRemnantStep (ex56.voiceP true).length := by
  decide

/-! ### *By* takes a vP (§4) -/

/-- The by-phrase of (29), *by the book*, has no projecting head: *by* selects a vP, and a DP
does not satisfy it; over the vP of (30) it projects. -/
theorem by_selects_vP :
    (({PlanarSyntacticObject.leaf by₀, PlanarSyntacticObject.leaf ex9.patient} :
      PlanarSyntacticObject).toSyntacticObject).selHead = none ∧
    ∃ q ∈ (ex9.voiceP false).externalize?, q.toSyntacticObject.selHead = some by₀ := by
  decide

/-! ### The rows -/

/-- The value of a row's feature, read through a table. -/
private def parse? {α : Type*} (table : List (String × α)) (row : LinguisticExample)
    (key : String) : Option α :=
  (row.feature? key).bind (List.lookup · table)

private def bools : List (String × Bool) := [("true", true), ("false", false)]

/-- The clause a row records. -/
def Clause.ofRow (row : LinguisticExample) : Option Clause := do
  let verb ← row.feature? "verb"
  let agent ← row.feature? "agent"
  let patient ← row.feature? "patient"
  return .of verb agent patient (row.feature? "particle" <|> row.feature? "pp")

/-! ### Word order and convergence (§3, §5) -/

/-- A word-order row's configuration: its clause, the analysis that derives its string, and
whether the PP evacuated. -/
structure Order where
  /-- The clause. -/
  clause : Clause
  /-- The analysis that derives the row's string. -/
  analysis : Analysis
  /-- Whether the PP evacuated PartP. -/
  evacuated : Bool

/-- The configuration a row records. -/
def Order.ofRow (row : LinguisticExample) : Option Order := do
  guard (row.feature? "construction" = some "passive")
  return ⟨← Clause.ofRow row,
    ← parse? [("partP", .partP), ("headMovement", .headMovement), ("inSitu", .inSitu)] row
      "analysis",
    (parse? bools row "evacuated").getD false⟩

/-- A word-order row is grammatical exactly when the analysis that derives its string
converges: PartP movement does, head movement and no movement leave the external argument
between Infl and the object. -/
theorem order_rows : ∀ row ∈ Examples.all, ∀ o ∈ Order.ofRow row,
    (row.judgment ≠ .ungrammatical ↔ o.clause.Converges o.analysis o.evacuated) := by
  decide

/-! ### C-command and binding across the by-phrase (§3, §7, §9, §10) -/

/-- The two positions the tests relate: the external argument and the third element of VP. -/
inductive Position
  | external | pp
  deriving DecidableEq, Repr

/-- The leaf at a position. -/
def Clause.at? (p : Clause) : Position → Option LIToken
  | .external => some p.agent
  | .pp => p.extra

/-- The dependencies the rows test: a negative polarity item and *the other* need a
c-commanding licensor at the surface; a reflexive and a bound variable likewise, with
reconstruction of PartP to a stage where the licensor c-commanded it as the degraded option,
(72) and (75) (§9.1); a pronoun may not be c-commanded by a coindexed DP at any stage, Principle
B applying as the DP is Merged, (83)–(84) after [sabel-1996] (§9.3); a name may not be
c-commanded by a coindexed pronoun at the surface, Principle C without reconstruction (§9.2). -/
inductive Dependency
  | npi | other | variable | reflexive | pronoun | name
  deriving DecidableEq, Repr

/-- The judgment a dependency predicts for `d` when `x` must, or must not, c-command `y`; the
reconstructed reflexive is `??` and the reconstructed bound variable `?`, as the paper grades
them. -/
def Dependency.predict (dep : Dependency) (d : Derivation) (x y : SyntacticObject) :
    Features.Judgment :=
  match dep with
  | .reflexive =>
      if d.BindsAtSurface x y then .acceptable
      else if d.BindsAtSomeStage x y then .questionable else .ungrammatical
  | .variable =>
      if d.BindsAtSurface x y then .acceptable
      else if d.BindsAtSomeStage x y then .marginal else .ungrammatical
  | .pronoun => if d.BindsAtSomeStage x y then .ungrammatical else .acceptable
  | .name => if d.BindsAtSurface x y then .ungrammatical else .acceptable
  | _ => if d.BindsAtSurface x y then .acceptable else .ungrammatical

/-- A licensing row's configuration. -/
structure Licensing where
  /-- The clause. -/
  clause : Clause
  /-- Whether the PP evacuated PartP. -/
  evacuated : Bool
  /-- The dependency. -/
  dependency : Dependency
  /-- The position that must, or must not, c-command. -/
  antecedent : Position
  /-- The position of the dependent element. -/
  dependent : Position

/-- The configuration a row records. -/
def Licensing.ofRow (row : LinguisticExample) : Option Licensing := do
  guard (row.feature? "construction" = some "licensing")
  let positions := [("external", Position.external), ("pp", .pp)]
  return ⟨← Clause.ofRow row, ← parse? bools row "evacuated",
    ← parse? [("npi", Dependency.npi), ("other", .other), ("variable", .variable),
      ("reflexive", .reflexive), ("pronoun", .pronoun), ("name", .name)] row "dependency",
    ← parse? positions row "antecedent", ← parse? positions row "dependent"⟩

/-- The judgment the configuration predicts on the PartP-movement derivation. -/
def Licensing.predict? (c : Licensing) : Option Features.Judgment := do
  let x ← c.clause.at? c.antecedent
  let y ← c.clause.at? c.dependent
  return c.dependency.predict (c.clause.passive .partP c.evacuated) x y

/-- The [barss-lasnik-1986] tests (10), Principle A (72), (74), the bound variable (75),
Principle B (80) and Principle C (85) all follow from where the PP sits: evacuated to Spec,XP
it is c-commanded by the external argument at the surface, inside the fronted PartP only before
PartP moved. -/
theorem licensing_rows : ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row,
    ∀ j ∈ c.predict?, j = row.judgment := by
  decide

/-! ### Participle licensing (§3, (23)–(28)) -/

/-- The auxiliary over the participle: *have*, *be*, or none, as in a participial modifier. -/
inductive Auxiliary
  | have | be | bare
  deriving DecidableEq, Repr

/-- A participle clause: its auxiliary and whether a VoiceP is present. -/
structure Participle where
  /-- The auxiliary. -/
  auxiliary : Auxiliary
  /-- Whether a Voice head is present. -/
  voiceP : Bool

/-- A participle must be licensed by exactly one of *have*, which c-selects it, and Voice, which
attracts it, (24)–(25): (24) requires one, a participle Voice has licensed cannot also be
checked by *have*, and *be* imposes nothing (§3). -/
def Participle.Licensed (c : Participle) : Prop := Xor (c.auxiliary = .have) c.voiceP

instance (c : Participle) : Decidable c.Licensed := inferInstanceAs (Decidable (Xor _ _))

/-- The configuration a row records. -/
def Participle.ofRow (row : LinguisticExample) : Option Participle := do
  guard (row.feature? "construction" = some "participle")
  return ⟨← parse? [("have", Auxiliary.have), ("be", .be), ("none", .bare)] row "auxiliary",
    ← parse? bools row "voiceP"⟩

/-- The auxiliary paradigm (23) and the participial modifiers (27): a participle clause is
acceptable exactly when its participle has one licenser. -/
theorem participle_rows : ∀ row ∈ Examples.all, ∀ c ∈ Participle.ofRow row,
    (row.judgment = .acceptable ↔ c.Licensed) := by
  decide

end Collins2005
