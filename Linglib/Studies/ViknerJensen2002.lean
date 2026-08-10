import Linglib.Semantics.Possessive.Basic

/-!
# Vikner & Jensen 2002: A semantic analysis of the English genitive

[vikner-jensen-2002]'s uniform argument-only analysis of the English prenominal
genitive: the genitive always combines with a *relational* noun — a
non-relational head is coerced via Barker's `π`, the relation type supplied by
the noun's qualia (`availableRelations`, §3.1.2). The genitive clitic itself
(`clitic`, their (16)) embeds a narrow-scope definite: the worked examples
prove `iotaPresupposition` and feed the `Possessive.Definite` carrier's
`existsUnique_possessee`.
-/

namespace ViknerJensen2002

open ArgumentStructure.Relational
open Possessive

/-! ### Qualia structure (Pustejovsky, as used by Vikner & Jensen) -/

/-- The relation-bearing lexical structure of a head noun. Telic and formal
qualia license no genitive relation type and are omitted. -/
structure NounQualia where
  /-- Inherently relational (e.g. *sister*, *teacher*) — bears its own relatum. -/
  isRelational : Prop
  /-- Bears a constitutive quale (*nose*: part-of a body). -/
  hasConstitutive : Prop
  /-- Bears an agentive quale (*poem*: composed by someone). -/
  hasAgentive : Prop

/-! ### Deriving the relation type from qualia -/

/-- The genitive relation types a head noun licenses: inherent iff it is
relational, part-whole iff it bears a constitutive quale, agentive iff it bears
an agentive quale, and control unconditionally. Possessor-side selectional
restrictions are left out, as in the paper's own derivations. -/
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
disposal*) — but not part-whole. -/
theorem picture_three_ways :
    availableRelations picture = {.inherent, .agentive, .control} := by
  ext r; simp [availableRelations, picture]

/-! ### The genitive clitic -/

/-- The genitive clitic: from the possessor quantifier and the genitive
relation to the head NP's quantifier, with an implicit definite — the unique
relatum — scoping under the possessor quantifier. -/
def clitic {E : Type*} (Q : Quantification.Quantifier E) (R : E → E → Prop) :
    Quantification.Quantifier E :=
  fun P => Q fun u => ∃ x, (∀ y, R u y ↔ y = x) ∧ P x

/-! ### The denotation: possessor + narrow-scope definite

Model over `Fin 4` (girl `0`, her teacher `1`, her car `2`, an unrelated `3`),
single situation. The genitive picks the unique entity standing in the resolved
relation to the possessor. -/

/-- The (inherent) teacher relation: `0`'s teacher is `1`. -/
def teacherRel : Fin 4 → Fin 4 → Unit → Prop := fun x y _ => x = 0 ∧ y = 1

/-- *the girl's teacher* (inherent): the relational noun's own relation applied
to the possessor (`viaArgument`) has a unique satisfier. -/
theorem girlsTeacher_unique (s : Unit) :
    iotaPresupposition (viaArgument (E := Fin 4) 0 teacherRel) s :=
  ⟨1, ⟨rfl, rfl⟩, fun _ hy => hy.2⟩

/-- *a girl* as an indefinite possessor quantifier. -/
def aGirl : Quantification.Quantifier (Fin 4) := fun P => ∃ z, z = 0 ∧ P z

/-- *a girl's teacher* holds of `P` iff some girl has a unique teacher who is
`P` — in this model, iff `P 1`. -/
theorem aGirlsTeacher (P : Fin 4 → Prop) :
    clitic aGirl (fun u y => teacherRel u y ()) P ↔ P 1 := by
  simp only [clitic, aGirl, teacherRel]
  constructor
  · rintro ⟨z, rfl, x, hx, hP⟩
    rwa [← (hx 1).mp ⟨rfl, rfl⟩] at hP
  · exact fun hP => ⟨0, rfl, 1, fun y => by simp, hP⟩

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
def controlRel : Fin 4 → Fin 4 → Unit → Prop := fun x y _ => x = 0 ∧ y = 2

/-- *car* as a sortal noun predicate. -/
def carPred : Fin 4 → Unit → Prop := fun y _ => y = 2

/-- *the girl's car* (coerced, control): the sortal noun is `π`-shifted with
the control relation, then combines exactly like a relational noun
(`viaArgument`). The result again carries the definite's unique witness. -/
theorem girlsCar_unique (s : Unit) :
    iotaPresupposition (viaArgument (E := Fin 4) 0 (π carPred controlRel)) s :=
  ⟨2, ⟨rfl, rfl, rfl⟩, fun _ hy => hy.1⟩

end ViknerJensen2002
