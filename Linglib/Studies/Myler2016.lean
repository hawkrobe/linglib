import Linglib.Morphology.DistributedMorphology.Allosemy
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Data.Examples.Myler2016

/-!
# Building and interpreting possession sentences

[myler-2016] treats every *have* and *be* as one meaningless copula v, whose
meaning is the identity function and whose form is fixed by its syntactic
surroundings: *have* under a transitive Voice — one that bears the specifier
feature {D} and φ-features — and *be* otherwise. The possession relation
comes from inside the DP complement, and Voice adds a θ-role only when the
complement is a predicate of eventualities. Icelandic's two *have* verbs
divide the transitive context by what lies below v: *hafa* over a PredP,
*eiga* elsewhere.

## Main definitions

* `Context`, `englishItems`, `icelandicItems`: what v's insertion sees and
  the Vocabulary Items of English and Icelandic.
* `Attributive`: the two DP-internal possession structures, a PP possessor
  under Pred or a possessor in Spec,PossP.
* `voiceAlloseme`: the Voice alloseme a complement selects, the substrate's
  `Voice.Alloseme.fromComplement`.

## Main results

* `have_iff_transitive`: *have* is *be* in a transitive Voice context.
* `hafa_iff_predP`, `eiga_only_if_no_pp`, `hafa_only_if_pp`: the Icelandic
  items and the two generalizations that follow from the structures.
* `clausal_rows`, `attributive_rows`: the items reproduce the Icelandic data
  pool, clausal and attributive.
* `expletive_voice_passes_complement`: with a relational complement Voice
  is the identity, so the sentence means what its complement means.

## Implementation notes

The dissertation text ([myler-2016] revises Myler's 2014 NYU dissertation) was
checked; example numbers cited here are the dissertation's. The Minimalist
`Voice.Head` flavors are not used for the insertion context: Myler's
condition is syntactic ({D} and φ), and relational *have* has an expletive
Voice at LF while still surfacing as *have*.
-/

namespace Myler2016

open DistributedMorphology DistributedMorphology.Allosemy Data.Examples

/-! ### The copula's context and form -/

/-- What the insertion of v sees: the specifier feature {D} and the
φ-features on the Voice above, and a PredP complement below. -/
inductive Feature where
  | d | phi | pred
  deriving DecidableEq, Repr

/-- A clause's context for v. -/
structure Context where
  voiceD : Bool
  voicePhi : Bool
  predComplement : Bool
  deriving DecidableEq, Repr, Fintype

/-- The features a context exposes. -/
def Context.features (c : Context) : List Feature :=
  (if c.voiceD then [.d] else []) ++ (if c.voicePhi then [.phi] else []) ++
    (if c.predComplement then [.pred] else [])

/-- A transitive context: Voice introduces an external argument and bears
φ-features that license v's complement. -/
def Context.Transitive (c : Context) : Prop := c.voiceD = true ∧ c.voicePhi = true

instance (c : Context) : Decidable c.Transitive := inferInstanceAs (Decidable (_ ∧ _))

/-- English: *have* in a transitive context, *be* elsewhere. -/
def englishItems : List (VocabularyItem Feature String) := [⟨[.d, .phi], "have"⟩, ⟨[], "be"⟩]

/-- Icelandic ((15)): *hafa* in a transitive context over a PredP, *eiga* in
a transitive context otherwise, and the copula *vera* elsewhere. -/
def icelandicItems : List (VocabularyItem Feature String) :=
  [⟨[.d, .phi, .pred], "hafa"⟩, ⟨[.d, .phi], "eiga"⟩, ⟨[], "vera"⟩]

/-- The form of v in a context, by the Subset Principle over a language's
items. -/
def spellout (items : List (VocabularyItem Feature String)) (c : Context) : Option String :=
  subsetPrinciple items c.features

/-- *have* is *be* plus transitivity. -/
theorem have_iff_transitive :
    ∀ c : Context, spellout englishItems c = some "have" ↔ c.Transitive := by
  decide

/-- *hafa* is the transitive spell-out over a PredP; the rule is conditioned
from both sides of v. -/
theorem hafa_iff_predP :
    ∀ c : Context,
      spellout icelandicItems c = some "hafa" ↔ c.Transitive ∧ c.predComplement = true := by
  decide

/-! ### Attributive possession and the two generalizations (§5) -/

/-- The two DP-internal possession structures ((19), (20)): the possessor in
a PP under Pred, or in Spec,PossP. -/
inductive Attributive where
  | predP | possP
  deriving DecidableEq, Repr, Fintype

/-- A PP possessor is available exactly under the PredP structure ((18),
column C). -/
def Attributive.AllowsPP : Attributive → Prop
  | .predP => True
  | .possP => False

instance : DecidablePred Attributive.AllowsPP :=
  fun a => by cases a <;> unfold Attributive.AllowsPP <;> infer_instance

/-- Clausal possession embeds the attributive structure under v in a
transitive context ((21), (22)). -/
def Attributive.context (a : Attributive) : Context := ⟨true, true, a = .predP⟩

/-- Generalization 1 ((16a)): clausal possession with *eiga* only if
DP-internal possession cannot use a PP. -/
theorem eiga_only_if_no_pp (a : Attributive) (h : spellout icelandicItems a.context = some "eiga") :
    ¬ a.AllowsPP := by
  revert h; cases a <;> decide

/-- Generalization 2 ((16b)): clausal possession with *hafa* only if
DP-internal possession can use a PP. -/
theorem hafa_only_if_pp (a : Attributive) (h : spellout icelandicItems a.context = some "hafa") :
    a.AllowsPP := by
  revert h; cases a <;> decide

/-! ### The Icelandic data pool -/

/-- The possession relations of (17) and (18). -/
inductive Relation where
  | concrete | kinship | bodyPart | abstract
  deriving DecidableEq, Repr, Fintype

def Relation.ofString : String → Option Relation
  | "concrete" => some .concrete | "kinship" => some .kinship | "bodyPart" => some .bodyPart
  | "abstract" => some .abstract | _ => none

/-- The structure each relation is built with: body parts and abstract
relations under Pred with a PP possessor, concrete and kinship relations
under Poss ((18)–(20)). -/
def Relation.attributive : Relation → Attributive
  | .concrete | .kinship => .possP
  | .bodyPart | .abstract => .predP

/-- A clausal row of (17): the relation, the verb, and whether it is
accepted. -/
structure ClausalRow where
  relation : Relation
  verb : String
  accepted : Bool
  deriving DecidableEq, Repr

def ClausalRow.ofExample (ex : LinguisticExample) : Option ClausalRow := do
  guard (ex.paperFeatures.lookup "construction" = some "clausal")
  let relation ← ex.paperFeatures.lookup "relation" >>= Relation.ofString
  let verb ← ex.paperFeatures.lookup "verb"
  pure ⟨relation, verb, ex.judgment = .acceptable⟩

/-- A column-C row of (18): the relation and whether the PP possessor is
accepted. -/
structure PPRow where
  relation : Relation
  accepted : Bool
  deriving DecidableEq, Repr

def PPRow.ofExample (ex : LinguisticExample) : Option PPRow := do
  guard (ex.paperFeatures.lookup "construction" = some "attributiveC")
  let relation ← ex.paperFeatures.lookup "relation" >>= Relation.ofString
  pure ⟨relation, ex.judgment = .acceptable⟩

def clausalRows : List ClausalRow := Examples.all.filterMap ClausalRow.ofExample

def ppRows : List PPRow := Examples.all.filterMap PPRow.ofExample

/-- Every example is a clausal row or an attributive row. -/
theorem rows_cover :
    ∀ ex ∈ Examples.all,
      (ClausalRow.ofExample ex).isSome ∨
        ex.paperFeatures.lookup "construction" ≠ some "clausal" := by
  decide

/-- **Clausal possession** ((17)): each relation's structure spells out as
exactly the accepted verb. -/
theorem clausal_rows :
    ∀ r ∈ clausalRows,
      (spellout icelandicItems r.relation.attributive.context = some r.verb) = r.accepted := by
  decide

/-- **Attributive possession** ((18), column C): a PP possessor is accepted
exactly for the relations built under Pred. -/
theorem attributive_rows :
    ∀ r ∈ ppRows, decide r.relation.attributive.AllowsPP = r.accepted := by
  decide

/-! ### The meaning of a *have* sentence -/

/-- The Voice alloseme a *have* sentence's complement selects ((61)): the
substrate's competition over `Voice.vocabulary`. -/
def voiceAlloseme (eventiveVoiceP stative : Bool) : Voice.Alloseme :=
  Voice.Alloseme.fromComplement (eventiveVoiceP = true) (stative = true)

/-- ⟦v⟧ = λx.x ((60)) and, over a relational complement — neither an
eventive VoiceP nor a state — Voice is the expletive identity: the
sentence means what its complement means. Relational, locative, and
experiencer *have* are this case. -/
theorem expletive_voice_passes_complement : voiceAlloseme false false = .expletive := by decide

/-- Over an eventuality predicate Voice adds a θ-role — the holder of a
state, the engineer of an eventive VoiceP — so light-verb and ECM *have*
mean more than their complement. -/
theorem contentful_voice_adds_theta :
    (voiceAlloseme false true).AssignsTheta ∧ (voiceAlloseme true false).AssignsTheta := by
  decide

end Myler2016
