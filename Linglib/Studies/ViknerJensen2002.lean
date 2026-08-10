import Linglib.Semantics.Possessive.Basic

/-!
# Vikner & Jensen 2002: A semantic analysis of the English genitive

[vikner-jensen-2002]'s uniform argument-only analysis of the English prenominal
genitive: the genitive always combines with a *relational* noun — a
non-relational head is coerced via Barker's `π`, the relation type supplied by
the noun's qualia (`availableRelations`). The genitive itself is a narrow-scope
definite: the worked examples prove `iotaPresupposition` and feed the
`Possessive.Definite` carrier's `existsUnique_possessee`.
-/

namespace ViknerJensen2002

open ArgumentStructure.Relational
open Possessive

/-! ### Qualia structure (Pustejovsky, as used by Vikner & Jensen) -/

/-- The relation-bearing lexical structure Vikner & Jensen read off a head
noun. Their lexical entries also carry telic and formal qualia, but those
license no genitive relation type, so they are omitted. -/
structure NounQualia where
  /-- Inherently relational (e.g. *sister*, *teacher*) — bears its own relatum. -/
  isRelational : Prop
  /-- Bears a constitutive quale (*nose*: part-of a body). -/
  hasConstitutive : Prop
  /-- Bears an agentive quale (*poem*: composed by someone). -/
  hasAgentive : Prop

/-! ### Deriving the relation type from qualia -/

/-- Vikner & Jensen's central thesis: the genitive's relation type is *derived*
from the head noun's lexical structure, not stipulated. A noun licenses the
inherent relation iff it is relational, the part-whole relation iff it bears a
constitutive quale, the agentive relation iff it bears an agentive quale; the
control relation is always available, ownership being only one special case of
control. Selectional restrictions on the possessor slot (control wants an
animate possessor, a quale constrains its own arguments) are idealized away. -/
def availableRelations (q : NounQualia) : Set PossessionRelationType :=
  {r | r = .inherent ∧ q.isRelational ∨ r = .partWhole ∧ q.hasConstitutive ∨
    r = .agentive ∧ q.hasAgentive ∨ r = .control}

/-- Control is available whatever the noun's qualia. -/
theorem control_always (q : NounQualia) :
    PossessionRelationType.control ∈ availableRelations q :=
  .inr <| .inr <| .inr rfl

/-! ### Lexical entries -/

/-- *sister* — inherently relational. -/
def sister : NounQualia := ⟨True, False, False⟩
/-- *nose* — constitutive quale (part-of a body). -/
def nose : NounQualia := ⟨False, True, False⟩
/-- *poem* — agentive quale (composed). -/
def poem : NounQualia := ⟨False, False, True⟩
/-- *picture* — relational (*picture of*) and agentive (*picture made by*). -/
def picture : NounQualia := ⟨True, False, True⟩

/-- *the girl's sister*: inherent relation, plus the ever-present control. -/
theorem sister_inherent :
    availableRelations sister = {.inherent, .control} := by
  ext r; simp [availableRelations, sister]

/-- *the girl's nose*: part-whole, via the constitutive quale (no inherent or
agentive reading). -/
theorem nose_partWhole :
    availableRelations nose = {.partWhole, .control} := by
  ext r; simp [availableRelations, nose]

/-- *the girl's poem*: agentive, via the agentive quale. -/
theorem poem_agentive :
    availableRelations poem = {.agentive, .control} := by
  ext r; simp [availableRelations, poem]

/-- *the girl's picture* is three ways ambiguous: inherent (*picture of the
girl*), agentive (*picture the girl made*), and control (*picture at her
disposal*) — but **not** part-whole. -/
theorem picture_three_ways :
    availableRelations picture = {.inherent, .agentive, .control} := by
  ext r; simp [availableRelations, picture]

/-! ### The denotation: possessor + narrow-scope definite

Model over `Fin 4` (girl `0`, her teacher `1`, her car `2`, an unrelated `3`),
single situation. The genitive picks the unique entity standing in the resolved
relation to the possessor. -/

/-- The (inherent) teacher relation: `0`'s teacher is `1`. -/
def teacherRel : Pred2 (Fin 4) Unit := fun x y _ => x = 0 ∧ y = 1

/-- *the girl's teacher* (inherent): the possessee predicate is the relational
noun's own relation applied to the possessor (`viaArgument`), and there is a
unique satisfier — the narrow-scope definite, here as `iotaPresupposition`. -/
theorem girlsTeacher_unique (s : Unit) :
    iotaPresupposition (viaArgument (E := Fin 4) 0 teacherRel) s :=
  ⟨1, ⟨rfl, rfl⟩, fun _ hy => hy.2⟩

/-- *the girl's teacher* as a `Possessive.Definite` carrier: its unique referent
is delivered by the carrier API's `existsUnique_possessee`, no bespoke proof. -/
def theGirlsTeacher : Possessive.Definite (Fin 4) Unit where
  possessor := 0
  predicate := viaArgument 0 teacherRel
  presupposition := girlsTeacher_unique

theorem girlsTeacher_existsUnique (s : Unit) :
    ∃! y : Fin 4, HasPossesseePredicate.possesseePredicate theGirlsTeacher y s :=
  existsUnique_possessee theGirlsTeacher s

/-- The control relation: the girl `0` controls the car `2`. -/
def controlRel : Pred2 (Fin 4) Unit := fun x y _ => x = 0 ∧ y = 2

/-- *car* as a sortal noun predicate. -/
def carPred : Pred1 (Fin 4) Unit := fun y _ => y = 2

/-- *the girl's car* (coerced, control): the sortal noun is first shifted to a
relation by Barker's `π` with the control relation, then combines exactly like
a relational noun (`viaArgument`) — the uniform argument-only analysis. The
result again carries the definite's unique witness. -/
theorem girlsCar_unique (s : Unit) :
    iotaPresupposition (viaArgument (E := Fin 4) 0 (π carPred controlRel)) s :=
  ⟨2, ⟨rfl, rfl, rfl⟩, fun _ hy => hy.1⟩

end ViknerJensen2002
