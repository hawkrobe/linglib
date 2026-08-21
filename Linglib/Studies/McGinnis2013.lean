import Linglib.Features.Phi.Geometry
import Linglib.Morphology.DistributedMorphology.Fission
import Linglib.Data.Examples.McGinnis2013
import Mathlib.Data.Prod.Lex

/-!
# Agree and Fission in Georgian plurals

[mcginnis-2013]: the interactions among the number suffixes of the Georgian
verb follow from one number-agreement feature on T, specified [Group], and
from Fission of the fused Tense/Aspect/Mood node during Vocabulary Insertion.
T's [Group] probes the subject, then a first- or second-person object clitic,
so one argument per clause triggers plural agreement ((5)–(6)); the TAM node
is realized by strict scansion, each item discharging its intrinsic features
and the residue passing on, so the third-person plural screeve *-es* leaves
no Group for *-t* (`*g-nax-es-t`, (3)), *-t* [#, Group] leaves no # for the
default *-s* [#] (`*g-nax-o-s-t`, (15), (20)), and *-s*'s TAM restriction is
contextual, not discharged ((13)–(14)). The dative first-person plural bears
the collective person feature Multispeaker with its Group impoverished ((8)),
so *gv-* marks it and no *-t* follows ((23)), while *gv-nax-e-t* (21) has a
single Group, the subject's. The person prefixes (9) are ranked by the
feature geometry (4): a dependent node brings every node it depends on, so
*gv-* [Multispeaker] ⊃ *m-* [Speaker] ⊃ *g-* [Participant], and the
geometry supplies the [#] of the revised *-t* (13c).

## Main definitions

* `Feature`, `site`: geometry nodes, case, and TAM features; a site as the
  lower set of the nodes it mentions.
* `Argument`, `numberTarget`, `personTarget`: the arguments and the two
  probes.
* `prefixes`, `Screeve.vocabulary`: the Vocabularies (9), (10), (13).
* `personPrefix`, `suffixes`: the person prefix by the Subset Principle and the
  TAM suffixes by scansion.

## Main results

* `rows_realized`: every row of the pool is grammatical iff the prefix and
  suffixes are what the analysis inserts.
* `dependent_more_specific`, `prefix_ranking`: geometric dependence is site
  inclusion, so the engine ranks (9a) > (9b) > (9c) and (9d) > (9e) > (9f).
* `t_revised`: the geometry gives *-t* its [#].
* `sites_lowerSets`, `screeve_first`, `number_ranked`: every site is a lower
  set, interpretable features are discharged first, and the number items
  are ranked by intrinsic then contextual features.
* `count_group_le_one`: the TAM node never carries two Groups.

## References

* [S. Béjar, *Phi-syntax*][bejar-2003]
* [S. R. Anderson, *On representations in morphology*][anderson-1984]
* [H. Harley and E. Ritter, *Person and number in pronouns*][harley-ritter-2002]
* [A. González Poot and M. McGinnis, *Local versus long-distance
  Fission*][gonzalez-poot-mcginnis-2006]
-/

namespace McGinnis2013

open DistributedMorphology Phi.Geometry Data.Examples
open scoped DistributedMorphology.VocabularyItem

/-! ### Features and arguments -/

/-- Geometry nodes, dative case, and the interpretable TAM features: aorist,
optative, and the feature the optative shares with the present, future, and
conjunctive. -/
inductive Feature where
  | node (n : Node)
  | dat
  | aorist
  | optative
  | ftam
  deriving DecidableEq, Repr

/-- A site as the geometry reads it: every node at or below those mentioned —
a dependent brings what it depends on — with any further feature. -/
def site (ns : List Node) (extra : List Feature) : List Feature :=
  (ns.flatMap Node.below).eraseDups.map .node ++ extra

/-- An agreeing argument: person, plurality, and dative case. -/
structure Argument where
  person : Person
  plural : Bool
  dat : Bool
  deriving DecidableEq, Repr

/-- Georgian activates Speaker but not Addressee: first person is Participant
with Speaker — and Multispeaker when plural — second person bare Participant,
third person nothing. -/
def Argument.personNodes (a : Argument) : List Node :=
  match a.person with
  | .first => [.participant, .speaker] ++ if a.plural then [.multispeaker] else []
  | .second => [.participant]
  | _ => []

/-- Group survives on a plural argument unless Impoverishment deletes it: the
dative first-person plural ((8)). -/
def Argument.hasGroup (a : Argument) : Bool :=
  a.plural && !(a.dat && decide (a.person = .first))

/-- A first- or second-person argument: a clitic, within T's reach. -/
def Argument.IsParticipant (a : Argument) : Prop := a.person = .first ∨ a.person = .second

instance : DecidablePred Argument.IsParticipant := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-! ### Agree -/

/-- T's [Group] probe: the subject if plural; probing again, a plural
participant object clitic; otherwise nothing, and Group deletes ((5)–(7)). -/
def numberTarget (subj obj : Argument) : Option Argument :=
  if subj.hasGroup then some subj
  else if obj.IsParticipant ∧ obj.hasGroup then some obj
  else none

/-- v's [Participant] probe: a participant object first, else a participant
subject ((7), (9)). -/
def personTarget (subj obj : Argument) : Option Argument :=
  if obj.IsParticipant then some obj else if subj.IsParticipant then some subj else none

/-- The Individuation content T copies from its target: Group, and Class for a
third-person argument; the bare # node when no argument is plural. -/
def numberNodes : Option Argument → List Node
  | some a => [.individuation, .group] ++ if a.person = .third then [.nounClass] else []
  | none => [.individuation]

/-- The person-agreement node on v: the target's person content with its case. -/
def prefixNode (subj obj : Argument) : List Feature :=
  ((personTarget subj obj).map fun a =>
    a.personNodes.map Feature.node ++ if a.dat then [.dat] else []).getD []

/-- The two screeves treated: aorist (10) and optative (13). -/
inductive Screeve where
  | aorist
  | optative
  deriving DecidableEq, Repr

/-- The screeve's interpretable features. -/
def Screeve.features : Screeve → List Feature
  | .aorist => [.aorist]
  | .optative => [.ftam, .optative]

/-- The fused TAM node: the screeve's features, person agreement with the
subject, and the number content T agreed with. -/
def tamNode (s : Screeve) (subj obj : Argument) : List Feature :=
  s.features ++ subj.personNodes.map .node ++ (numberNodes (numberTarget subj obj)).map .node

/-! ### Vocabulary -/

/-- The prefix items (9), (9e) without its *x-* allomorph. -/
def gv : VocabularyItem Feature String := site [.multispeaker] [.dat] ⟷ "gv"
def m : VocabularyItem Feature String := site [.speaker] [.dat] ⟷ "m"
def g : VocabularyItem Feature String := site [.participant] [.dat] ⟷ "g"
def v : VocabularyItem Feature String := site [.speaker] [] ⟷ "v"
def participantNull : VocabularyItem Feature String := site [.participant] [] ⟷ ""
def elsewhere : VocabularyItem Feature String := [] ⟷ ""

def prefixes : List (VocabularyItem Feature String) := [gv, m, g, v, participantNull, elsewhere]

/-- The aorist screeve items (10a–c). -/
def aoristScreeve : List (VocabularyItem Feature String) :=
  [site [.group, .nounClass] [.aorist] ⟷ "es", site [.participant] [.aorist] ⟷ "e",
    [.aorist] ⟷ "a"]

/-- The aorist number items: *-t* (13c) and the elsewhere. -/
def aoristNumber : List (VocabularyItem Feature String) := [site [.group] [] ⟷ "t", elsewhere]

/-- The optative screeve item (13a). -/
def optativeScreeve : List (VocabularyItem Feature String) := [[.ftam, .optative] ⟷ "o"]

/-- The optative number items (13b–e): contextual features condition insertion
without being discharged. -/
def optativeNumber : List (VocabularyItem Feature String) :=
  [⟨⟨site [.group, .nounClass] [], [[.optative]], []⟩, "n"⟩, site [.group] [] ⟷ "t",
    ⟨⟨site [.individuation] [], [[.ftam, .node .participant]], []⟩, ""⟩,
    ⟨⟨site [.individuation] [], [[.ftam]], []⟩, "s"⟩, elsewhere]

/-- A screeve's Vocabulary in scansion order: interpretable features first. -/
def Screeve.vocabulary : Screeve → List (VocabularyItem Feature String)
  | .aorist => aoristScreeve ++ aoristNumber
  | .optative => optativeScreeve ++ optativeNumber

/-- The person prefix: Elsewhere competition at v's agreement node. -/
def personPrefix (subj obj : Argument) : Option String :=
  subsetPrinciple prefixes (prefixNode subj obj)

/-- The overt TAM suffixes: strict scansion with local Fission at the fused
node, whose own features stand as context to every item. -/
def suffixes (s : Screeve) (subj obj : Argument) : List String :=
  let node := tamNode s subj obj
  (scansion s.vocabulary ⟨[], [node], []⟩ [node]).filter (· ≠ "")

/-! ### The data pool -/

/-- A row: the arguments, screeve, and the attested prefix and suffixes. -/
structure Row where
  subj : Argument
  obj : Argument
  screeve : Screeve
  prefix_ : String
  suffixes : List String
  accepted : Bool
  deriving Repr

def Person.ofLabel : String → Option Person
  | "1" => some .first
  | "2" => some .second
  | "3" => some .third
  | _ => none

def Screeve.ofLabel : String → Option Screeve
  | "aorist" => some .aorist
  | "optative" => some .optative
  | _ => none

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let sp ← ex.feature? "subjPerson" >>= Person.ofLabel
  let sn ← ex.feature? "subjNumber"
  let op ← ex.feature? "objPerson" >>= Person.ofLabel
  let on ← ex.feature? "objNumber"
  let screeve ← ex.feature? "screeve" >>= Screeve.ofLabel
  let prefix_ ← ex.feature? "prefix"
  pure ⟨⟨sp, sn = "pl", false⟩, ⟨op, on = "pl", true⟩, screeve, prefix_,
    ["suffix1", "suffix2", "suffix3"].filterMap ex.feature?, ex.judgment = .acceptable⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

/-- The forms of (2)–(6), (12), (15), (21)–(23), (26). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- **Agree and Fission**: a form is grammatical iff its prefix is the Subset
Principle's winner and its suffixes are what scansion inserts — one Group per
clause, no *-t* after *-es*, no *-s* beside *-t*, no *-t* for a dative
first-person plural. -/
theorem rows_realized :
    ∀ r ∈ rows, r.accepted =
      (personPrefix r.subj r.obj = some r.prefix_ ∧
        suffixes r.screeve r.subj r.obj = r.suffixes) := by
  decide

/-! ### The geometry's ranking -/

/-- A dependent node's site contains its dominator's: geometric dependence is
site inclusion, hence engine ranking (`VocabularyItem.le_iff`). -/
theorem dependent_more_specific {a b : Node} (h : a ≤ b) (extra : List Feature) :
    site [a] extra ⊆ site [b] extra := by
  intro x hx
  simp only [site, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_map, List.mem_eraseDups] at hx ⊢
  rcases hx with ⟨n, hn, rfl⟩ | hx
  · exact .inl ⟨n, Node.below_subset_below h hn, rfl⟩
  · exact .inr hx

/-- (9a) ⊃ (9b) ⊃ (9c) and (9d) ⊃ (9e) ⊃ (9f): the prefixes are ranked by
the geometry, Multispeaker depending on Speaker on Participant. -/
theorem prefix_ranking :
    m.site.focus ⊆ gv.site.focus ∧ g.site.focus ⊆ m.site.focus ∧
      participantNull.site.focus ⊆ v.site.focus ∧
        elsewhere.site.focus ⊆ participantNull.site.focus :=
  ⟨dependent_more_specific (by decide) _, dependent_more_specific (by decide) _,
    dependent_more_specific (by decide) _, List.nil_subset _⟩

/-- The geometry supplies the [#] of the revised *-t* (13c): the site of Group
is [#, Group]. -/
theorem t_revised : site [.group] [] = [.node .individuation, .node .group] := by decide

/-- The geometry nodes of every site form a lower set with the root. -/
theorem sites_lowerSets :
    ∀ i ∈ prefixes ++ aoristScreeve ++ aoristNumber ++ optativeScreeve ++ optativeNumber,
      IsLowerSet (↑(insert ⊥ (i.site.focus.filterMap fun f =>
        match f with | .node n => some n | _ => none).toFinset) : Set Node) := by
  decide

/-! ### The ranking of the number items -/

/-- Interpretable features are discharged first: every screeve item carries
one and no number item does. -/
theorem screeve_first :
    (∀ i ∈ aoristScreeve, Feature.aorist ∈ i.site.focus) ∧
      (∀ i ∈ aoristNumber, Feature.aorist ∉ i.site.focus) ∧
      (∀ i ∈ optativeScreeve, Feature.ftam ∈ i.site.focus) ∧
      ∀ i ∈ optativeNumber, Feature.ftam ∉ i.site.focus ∧ Feature.optative ∉ i.site.focus := by
  decide

/-- Pāṇinian ranking with intrinsic features leading and contextual features
deciding ties: the number items descend lexicographically in (intrinsic,
contextual) feature count, *-t* above *-s* ((20)). -/
theorem number_ranked :
    optativeNumber.Pairwise fun i j =>
      toLex (j.site.focus.length, j.site.leftCtx.flatten.length) <
        toLex (i.site.focus.length, i.site.leftCtx.flatten.length) := by
  decide

/-! ### One Group per clause -/

theorem count_group_personNodes (a : Argument) : a.personNodes.count Node.group = 0 := by
  unfold Argument.personNodes; split <;> (try split_ifs) <;> simp

theorem count_group_numberNodes (t : Option Argument) : (numberNodes t).count Node.group ≤ 1 := by
  rcases t with _ | a
  · simp [numberNodes]
  · simp [numberNodes]; split_ifs <;> simp

/-- T carries at most one Group: plural agreement with one argument ((5),
§3.3.1). -/
theorem count_group_le_one (s : Screeve) (subj obj : Argument) :
    (tamNode s subj obj).count (.node .group) ≤ 1 := by
  have h₁ : (s.features.count (Feature.node .group)) = 0 := by cases s <;> rfl
  have h₂ : ((subj.personNodes.map Feature.node).count (.node .group)) = 0 := by
    rw [List.count_map_of_injective _ _ (fun _ _ h => Feature.node.inj h)]
    exact count_group_personNodes subj
  have h₃ := count_group_numberNodes (numberTarget subj obj)
  rw [← List.count_map_of_injective _ Feature.node (fun _ _ h => Feature.node.inj h)] at h₃
  simp only [tamNode, List.count_append]
  omega

end McGinnis2013
