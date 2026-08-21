import Linglib.Syntax.Tree.Basic
import Linglib.Fragments.Swahili.Relativization
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.FeatureBundle
import Linglib.Syntax.Minimalist.Features
import Linglib.Data.Examples.Scott2021

/-!
# Two types of resumptive pronouns in Swahili

[scott-2021]: the resumptive pronouns that objects of monosyllabic
prepositions require are of two kinds. Bound pronouns, the only option in
adjunct islands ((31)–(33)), match the head in person; movement copies,
diagnosed by parasitic gaps ((35)–(37)), never carry person. Both follow
from one Vocabulary ((28)) and the copy theory of movement: a movement copy
in a position with a phonological requirement is reduced rather than deleted
([landau-2006]), and MaxElide removes the largest constituent whose residue
can still be spelled out — PersP, since *-ye* spells out `[sg + n_anim]`
while nothing spells out Num alone ((46)–(48)).

## Main definitions

* `pronoun`: the pronoun structures of (40)–(44), with PersP only for local
  persons.
* `resumptiveVocab`, `spellout`: the Vocabulary Items of (28) over a
  pronoun's features.
* `Deletable`, `maxElideTarget`: a layer is deletable when its residue has an
  exponent; MaxElide takes the largest such layer.
* `pronounce`: the chain reduction of a copy — full deletion, or PersP
  deletion where Minimality forbids deleting the copy — against a bound
  pronoun's full spell-out.

## Main results

* `table2`: the paradigm of the Fragment's `resumptivePronoun` is (28) over
  the structures (42) and (44).
* `maxElide_persP`: PersP is the unique deletable layer, by the Vocabulary.
* `cleft_rows`, `island_rows`, `parasitic_rows`: the data pool — clefts
  allow either pronoun but fix number, islands allow only the bound pronoun,
  and a personless parasitic pronoun needs a personless true gap for every
  speaker of Table 4.
* `person_entails_number`: any deletion that keeps person keeps number,
  since Num is above Pers (§6).

## Implementation notes

The structures are `Syntax.Tree`s over the four DP-internal categories, so
MaxElide is structural deletion rather than feature removal; features are
read off the terminals for Vocabulary Insertion. The interspeaker variation
of Table 4 beyond its first two rows is not derived, as the paper does not
derive it.
-/

namespace Scott2021

open Swahili Syntax Data.Examples
open Minimalist (FeatureBundle FeatureVal PhiFeature GramFeature Vocabulary VocabEntry)

/-! ### The structure of pronouns (§5.1) -/

/-- The DP-internal projections of (40)–(41): D, Num, the animate n, and the
Person projection that only local-person pronouns have. -/
inductive DPCat where
  | D | Num | n | Pers
  deriving DecidableEq, Repr, Fintype

/-- A pronoun ((41)): `[DP D [NumP Num [nP n_anim [PersP Pers]]]]`, without
PersP for the personless pronouns of (42). -/
def pronoun (person : Option Person) (number : Number) : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num (if number = .plural then "pl" else "sg"),
      .node .n ((.terminal .n "anim") ::
        match person with
        | some .first => [.node .Pers [.terminal .Pers "1"]]
        | some .second => [.node .Pers [.terminal .Pers "2"]]
        | _ => [])]]

/-- The feature a terminal contributes: person, number, or the animate gender
(encoded as gender 1). -/
def terminalFeature : DPCat → String → Option FeatureVal
  | .Pers, "1" => some (.phi (.person .first))
  | .Pers, "2" => some (.phi (.person .second))
  | .Num, "sg" => some (.phi (.number .singular))
  | .Num, "pl" => some (.phi (.number .plural))
  | .n, "anim" => some (.phi (.gender 1))
  | _, _ => none

mutual
/-- The features at a tree's terminals, in depth-first order. -/
def featureList : Tree DPCat String → List GramFeature
  | .terminal c w => match terminalFeature c w with
    | some fv => [.valued fv]
    | none => []
  | .node _ children => featureListAll children
  | .trace _ _ => []
  | .bind _ _ body => featureList body

private def featureListAll : List (Tree DPCat String) → List GramFeature
  | [] => []
  | t :: ts => featureList t ++ featureListAll ts
end

/-- The feature bundle of a tree. -/
def features (t : Tree DPCat String) : FeatureBundle :=
  Minimalist.FeatureBundle.ofGramFeatures (featureList t)

/-! ### Vocabulary Insertion (§3.4) -/

/-- The Vocabulary Items of (28): person-specified animate entries and the
personless animate defaults *-ye* and *-o*. -/
def resumptiveVocab : Vocabulary :=
  let entry (fs : List GramFeature) (e : String) : VocabEntry :=
    { features := Minimalist.FeatureBundle.ofGramFeatures fs, exponent := e }
  [ entry [.valued (.phi (.person .first)), .valued (.phi (.gender 1)),
      .valued (.phi (.number .singular))] "mi",
    entry [.valued (.phi (.person .first)), .valued (.phi (.gender 1)),
      .valued (.phi (.number .plural))] "si",
    entry [.valued (.phi (.person .second)), .valued (.phi (.gender 1)),
      .valued (.phi (.number .singular))] "we",
    entry [.valued (.phi (.person .second)), .valued (.phi (.gender 1)),
      .valued (.phi (.number .plural))] "nyi",
    entry [.valued (.phi (.gender 1)), .valued (.phi (.number .singular))] "ye",
    entry [.valued (.phi (.gender 1)), .valued (.phi (.number .plural))] "o" ]

/-- The exponent of a pronoun structure, by the Subset Principle over (28). -/
def spellout (t : Tree DPCat String) : Option String :=
  Minimalist.spellout resumptiveVocab (features t) none

/-- The Fragment's person cells as the structures' person: third person is the
absence of PersP. -/
def relPerson : RelPerson → Option Person
  | .first => some .first
  | .second => some .second
  | .third => none

/-- **Table 2 from (28)**: every cell of the Fragment's resumptive paradigm is
the Subset Principle's choice for the corresponding structure ((43), (45)). -/
theorem table2 :
    ∀ (p : RelPerson) (n : RelGramNum),
      (spellout (pronoun (relPerson p) n.toNumber)).map ("-" ++ ·) =
        some (resumptivePronoun p n) := by
  intro p n; cases p <;> cases n <;> decide

/-! ### MaxElide (§5.2–5.3) -/

mutual
/-- Delete the constituent of category `c` — the subtree it heads — from a
tree. -/
def deleteLayer (c : DPCat) : Tree DPCat String → Tree DPCat String
  | .node k children => .node k (deleteLayerAll c children)
  | other => other

private def deleteLayerAll (c : DPCat) : List (Tree DPCat String) → List (Tree DPCat String)
  | [] => []
  | t :: ts => if t.cat = c then deleteLayerAll c ts else deleteLayer c t :: deleteLayerAll c ts
end

/-- A layer of a pronoun is deletable when what remains can still be spelled
out — MaxElide's condition ((48)): deleting PersP leaves `[sg + n_anim]`,
which *-ye* spells out, while deleting nP leaves Num alone, which nothing
spells out. -/
def Deletable (t : Tree DPCat String) (c : DPCat) : Prop :=
  c ≠ .D ∧ (spellout (deleteLayer c t)).isSome = true

instance (t : Tree DPCat String) (c : DPCat) : Decidable (Deletable t c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The layers of a pronoun, outermost first. -/
def layers : List DPCat := [.D, .Num, .n, .Pers]

/-- MaxElide: the largest deletable constituent. -/
def maxElideTarget (t : Tree DPCat String) : Option DPCat :=
  layers.find? fun c => decide (Deletable t c)

/-- In a local-person pronoun PersP is the unique deletable layer, so MaxElide
deletes it ((46)–(47)). -/
theorem maxElide_persP :
    ∀ (p : Person) (n : Number), p = .first ∨ p = .second →
      maxElideTarget (pronoun (some p) n) = some .Pers := by
  decide

/-- Deleting a layer can keep person only if it keeps number: Num is above
Pers (§6). -/
theorem person_entails_number :
    ∀ (c : DPCat) (n : Number),
      (featureList (deleteLayer c (pronoun (some .first) n))).any
          (fun f => match f with | .valued (.phi (.person _)) => true | _ => false) = true →
        (featureList (deleteLayer c (pronoun (some .first) n))).any
          (fun f => match f with | .valued (.phi (.number _)) => true | _ => false) = true := by
  decide

/-! ### Chain reduction (§5.2–5.3) -/

/-- How a resumptive relates to the head: a base-generated bound pronoun, or
a lower copy of Ā-movement. -/
inductive Origin where
  | bound | movementCopy
  deriving DecidableEq, Repr

/-- The pronounced form. A bound pronoun is spelled out in full. A movement
copy is deleted by Economy of Pronunciation unless its position carries the
bimoraic Minimality requirement of a monosyllabic preposition (§3.3), where
Phonological Recoverability forces partial deletion: MaxElide removes PersP
and the residue is spelled out. -/
def pronounce (t : Tree DPCat String) : Origin → (minimality : Bool) → Option String
  | .bound, _ => spellout t
  | .movementCopy, true => spellout (deleteLayer .Pers t)
  | .movementCopy, false => none

/-- Subjects and objects, with no Minimality requirement, leave a gap
((17)–(18)). -/
theorem gap_without_minimality (t : Tree DPCat String) :
    pronounce t .movementCopy false = none := rfl

/-- A movement copy under Minimality loses its person and surfaces as the
personless pronoun ((36)). -/
theorem movement_copy_personless :
    ∀ (p : Person) (n : Number), p = .first ∨ p = .second →
      pronounce (pronoun (some p) n) .movementCopy true =
        pronounce (pronoun none n) .bound true := by
  decide

/-! ### The data pool (§3.4, §4) -/

/-- A cell of the pool: the antecedent's person and number, the construction,
the resumptive form or forms, and the judgment. -/
structure Row where
  construction : String
  person : Person
  number : Number
  form : String
  parasitic : Option String
  accepted : Bool
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let fs := ex.paperFeatures
  let construction ← fs.lookup "construction"
  let person ← match fs.lookup "antecedentPerson" with
    | some "1" => some Person.first | some "2" => some Person.second | _ => none
  let number ← match fs.lookup "antecedentNumber" with
    | some "sg" => some Number.singular | some "pl" => some Number.plural | _ => none
  let form ← fs.lookup "form" <|> fs.lookup "trueGap"
  pure ⟨construction, person, number, form, fs.lookup "parasitic", ex.judgment = .acceptable⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The antecedent's structure. -/
def Row.tree (r : Row) : Tree DPCat String := pronoun (some r.person) r.number

/-- **Clefts** ((24)–(25), (29)): either the bound pronoun or the movement
copy is available, so the form is accepted iff it is one of the two — which
fixes number while leaving person optional. -/
theorem cleft_rows :
    ∀ r ∈ rows, r.construction = "cleft" →
      (r.accepted = (pronounce r.tree .bound true = some r.form ∨
        pronounce r.tree .movementCopy true = some r.form)) := by
  decide

/-- **Adjunct islands** ((31)–(33)): movement is blocked, so the form is
accepted iff it is the bound pronoun's. -/
theorem island_rows :
    ∀ r ∈ rows, r.construction = "island" →
      (r.accepted = (pronounce r.tree .bound true = some r.form)) := by
  decide

/-- **Parasitic gaps** ((36)–(37), Table 4): a movement copy in the parasitic
position is licensed only by a movement copy in the true-gap position — for
every speaker, *ye … ye* is in and *mi … ye* is out. -/
theorem parasitic_rows :
    ∀ r ∈ rows, r.construction = "parasiticGap" →
      r.parasitic = pronounce r.tree .movementCopy true →
        (r.accepted = (some r.form = pronounce r.tree .movementCopy true)) := by
  decide

end Scott2021
