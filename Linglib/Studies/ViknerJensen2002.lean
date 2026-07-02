import Linglib.Semantics.Possessive.Basic

/-!
# Vikner & Jensen 2002: A semantic analysis of the English genitive

Paper-anchored consumer of the relational/possessive substrate for
[vikner-jensen-2002]. V&J give the prenominal genitive a single syntactic type
(it always combines with a *relational* noun); a non-relational head noun is
coerced to relational, with the genitive relation *derived* from the noun's
Pustejovsky qualia rather than stipulated.

* **Four lexical relation types** (§3.1.2): inherent, part-whole, agentive,
  control. These *are* the project's `PossessionRelationType` — V&J is the
  source of that taxonomy (cited in `Semantics/Possessive/Basic.lean`), and
  this study is its first consumer.
* **Qualia derivation** (§3.2.3): the relation type follows from lexical
  structure — inherent from relationality, part-whole from the constitutive
  quale, agentive from the agentive quale; control is always available. So the
  three-way ambiguity of *the girl's picture* is derived, not listed.
* **The denotation** (§3.2.3, (20)–(21)): the genitive is the possessor plus a
  narrow-scope definite — the unique entity standing in the resolved relation to
  the possessor. The relation combines with the noun via Barker's `π`
  (`viaArgument` for a relational noun, `viaModifier` for a coerced
  sortal noun); uniqueness is `iotaPresupposition`, and a worked entry feeds the
  `Possessive.Definite` carrier's `existsUnique_possessee`.

## Main statements

* `control_always`, `picture_three_ways`, `nose_partWhole`, … — the
  qualia-derivation predictions (decide-checked).
* `girlsTeacher_existsUnique` — V&J's inherent genitive as a carrier-API
  definite (unique referent via `existsUnique_possessee`).
* `girlsCar_eq_sortal` — V&J's coerced (control) genitive as `viaModifier`.

## References

* [vikner-jensen-2002]: A semantic analysis of the English genitive.
-/

namespace ViknerJensen2002

open ArgumentStructure.Relational
open Possessive

/-! ### Qualia structure (Pustejovsky, as used by V&J §3.2.1) -/

/-- The relation-bearing qualia V&J read off a head noun. The telic and formal
qualia do not contribute a genitive relation type in V&J's four-way taxonomy, so
they are omitted. -/
structure NounQualia where
  /-- Inherently relational (e.g. *sister*, *teacher*) — bears its own relatum. -/
  isRelational : Bool
  /-- Bears a constitutive quale (*nose*: part-of a body). -/
  hasConstitutive : Bool
  /-- Bears an agentive quale (*poem*: composed by someone). -/
  hasAgentive : Bool
  deriving DecidableEq, Repr

/-! ### Deriving the relation type from qualia (V&J §3.2.3) -/

/-- V&J's central thesis: the genitive's relation type is *derived* from the head
noun's lexical structure, not stipulated. A noun licenses the inherent relation
iff it is relational, the part-whole relation iff it bears a constitutive quale,
the agentive relation iff it bears an agentive quale; the control relation is
always available (the default, independent of qualia, §3.1.2). The codomain is
the project's `PossessionRelationType` — V&J is the source of that taxonomy. -/
def availableRelations (q : NounQualia) : List PossessionRelationType :=
  (if q.isRelational then [PossessionRelationType.inherent] else []) ++
  (if q.hasConstitutive then [PossessionRelationType.partWhole] else []) ++
  (if q.hasAgentive then [PossessionRelationType.agentive] else []) ++
  [PossessionRelationType.control]

/-- Control is available whatever the noun's qualia (V&J §3.1.2: it is always
available, ownership being only one special case of control). -/
theorem control_always (q : NounQualia) :
    PossessionRelationType.control ∈ availableRelations q := by
  simp [availableRelations]

/-! ### Lexical entries (V&J (9), §3.1.2) -/

/-- *sister* — inherently relational. -/
def sister : NounQualia := ⟨true, false, false⟩
/-- *nose* — constitutive quale (part-of a body). -/
def nose : NounQualia := ⟨false, true, false⟩
/-- *poem* — agentive quale (composed). -/
def poem : NounQualia := ⟨false, false, true⟩
/-- *car* — agentive quale (constructed); the salient reading is control. -/
def car : NounQualia := ⟨false, false, true⟩
/-- *picture* — relational (*picture of*) and agentive (*picture made by*). -/
def picture : NounQualia := ⟨true, false, true⟩

/-- *the girl's sister*: inherent relation, plus the ever-present control. -/
theorem sister_inherent :
    availableRelations sister = [.inherent, .control] := by decide

/-- *the girl's nose*: part-whole, via the constitutive quale (no inherent or
agentive reading). -/
theorem nose_partWhole :
    availableRelations nose = [.partWhole, .control] := by decide

/-- *the girl's poem*: agentive, via the agentive quale. -/
theorem poem_agentive :
    availableRelations poem = [.agentive, .control] := by decide

/-- *the girl's picture* is three ways ambiguous (V&J §3.1.2): inherent
(*picture of the girl*), agentive (*picture the girl made*), and control
(*picture at her disposal*) — but **not** part-whole. -/
theorem picture_three_ways :
    availableRelations picture = [.inherent, .agentive, .control] := by decide

/-- The qualia derivation distinguishes the readings: *picture* is three-way
ambiguous, *nose* only two-way. -/
theorem picture_more_ambiguous_than_nose :
    (availableRelations picture).length = 3 ∧ (availableRelations nose).length = 2 := by
  decide

/-! ### The denotation: possessor + narrow-scope definite (V&J §3.2.3)

Model over `Fin 4` (girl `0`, her teacher `1`, her car `2`, an unrelated `3`),
single situation. The genitive picks the unique entity standing in the resolved
relation to the possessor. -/

/-- The (inherent) teacher relation: `0`'s teacher is `1`. -/
def teacherRel : Pred2 (Fin 4) Unit := fun x y _ => x = 0 ∧ y = 1

/-- *the girl's teacher* (inherent, V&J (21)): the possessee predicate is the
relation applied to the possessor (`viaArgument`), and there is a unique
satisfier — V&J's narrow-scope definite, here as `iotaPresupposition`. -/
theorem girlsTeacher_unique (s : Unit) :
    iotaPresupposition (viaArgument (E := Fin 4) 0 teacherRel) s := by
  refine ⟨1, ⟨rfl, rfl⟩, ?_⟩
  rintro y ⟨-, hy⟩
  exact hy

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

/-- *the girl's car* (coerced, control): the sortal noun is shifted to a relation
via Barker's `π` (`viaModifier`), and the result selects the controlled car.
This is V&J's coercion of a non-relational head noun. -/
theorem girlsCar_eq_sortal (y : Fin 4) :
    viaModifier (E := Fin 4) 0 carPred controlRel y () ↔ y = 2 := by
  constructor
  · rintro ⟨hcar, -, -⟩; exact hcar
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩

end ViknerJensen2002
