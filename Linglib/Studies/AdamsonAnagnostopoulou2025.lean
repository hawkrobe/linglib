import Linglib.Syntax.Minimalist.Agree.Coordination
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Fragments.Greek.StandardModern.Gender
import Linglib.Fragments.Icelandic.Gender
import Linglib.Fragments.Slavic.Serbian.Gender
import Linglib.Data.Examples.AdamsonAnagnostopoulou2025

/-!
# Gender features and coordination resolution

Adamson and Anagnostopoulou derive the resolution of gender on coordinated nominals in Greek,
Icelandic, and Bosnian/Croatian/Serbian from three components and no default insertion: a
language-particular geometry of privative gender features, a dual-feature system in which
interpretable features go to LF and uninterpretable ones to PF, and the universal mechanism of
percolation and conversion (`Minimalist.Coordination.resolve`). A system (`System`) fixes the
geometry, the node each referent type and each grammatical gender contributes, and the vocabulary
of inflectional exponents; every derivation is then a computation. In Greek, where FEM entails
MASC, mismatched humans keep MASC and resolve masculine while inanimates, whose only
interpretable feature is CLASS, resolve neuter (`Greek.human_mismatch`, `Greek.inanimate_mismatch`),
and the fixed-gender nouns *megalofiia* and *thima* resolve by their referents
(`Greek.genius_sister`, `Greek.victim_mother`). Uninterpretable features are realized set by set:
uniform inanimates converge on their shared exponent (`Greek.inanimate_uniform`), mismatched
ones do not (`Greek.inanimate_clash`), and a human coordinated with an inanimate is grammatical
exactly when the human's interpretable features and the inanimate's uninterpretable ones receive
the same exponent (`Greek.human_inanimate_match`, `Greek.human_inanimate_crash`,
`Greek.victim_painting`). Neuter is the least specified gender, so it realizes clausal subjects
(`Greek.clausal`), and the vocabulary's containment rules out a neuter–feminine syncretism that
excludes the masculine (`Greek.no_aba`, from `Morphology.Exponence.Realizes.of_realizes`).

Icelandic differs only in its geometry, with MASC meaning male and FEM independent of it, so
mismatched humans resolve neuter (`Icelandic.human_mismatch`) while fixed-gender *skáld* still
resolves by its referent (`Icelandic.poet_jon`). In Bosnian/Croatian/Serbian MASC sits under
INDIV, ANIM under MASC, and neuter is mass; a plural coordination bears GRP and hence INDIV
(`System.plural`), so every coordination realizes masculine, even of two neuters
(`BCS.human_mismatch`, `BCS.inanimate_mismatch`, `BCS.neuter_pair`). All three geometries satisfy
mismatch resolution (`mismatchResolution`), and Table 2 follows from the geometries alone
(`table2`).

## References

* [adamson-anagnostopoulou-2025]
* [smith-2015]
* [harley-ritter-2002]
* [kramer-2015]
* [halle-1997]
* [harbour-2016]
* [bobaljik-2012]
* [corbett-1991]
-/

namespace AdamsonAnagnostopoulou2025

open Minimalist.Coordination DistributedMorphology Morphology.Exponence
open scoped DistributedMorphology.VocabularyItem

/-- The privative gender nodes of the three geometries. -/
inductive Node where
  | cls
  | masc
  | fem
  | indiv
  | grp
  | anim
  deriving DecidableEq, Repr

/-- What a nominal refers to: a man, a woman, an individuated inanimate, or a mass. -/
inductive Referent where
  | man
  | woman
  | thing
  | mass
  deriving DecidableEq, Repr

/-- A three-gender system: its geometry, the node a referent contributes as interpretable
gender and a grammatical gender contributes as uninterpretable gender, the features a plural
coordination adds, and its vocabulary. -/
structure System where
  geometry : Geometry Node
  iNode : Referent → Node
  uNode : Gender → Bool → Node
  plural : List Node := []
  vocabulary : List (VocabularyItem Node Gender)

namespace System

variable (L : System)

/-- The interpretable features of a nominal with referent `r`. -/
def conceptual (r : Referent) : Bundle Node := interpretable (L.geometry.above (L.iNode r))

/-- The uninterpretable features of a nominal of grammatical gender `g`. -/
def arbitrary (g : Gender) (human : Bool := false) : Bundle Node :=
  uninterpretable (L.geometry.above (L.uNode g human))

/-- The exponent of a feature set under the Subset Principle. -/
def realize (fs : List Node) : Option Gender := subsetPrinciple L.vocabulary fs

/-- Resolution through conversion: percolated interpretable features are intersected and the
single result, with the coordination's plural features, realized. -/
def converted (a b : Bundle Node) : Option Gender :=
  (resolve a b).bind fun vs => L.realize (vs ++ L.plural)

/-- Resolution of two nominals by their referents. -/
def resolved (r₁ r₂ : Referent) : Option Gender := L.converted (L.conceptual r₁) (L.conceptual r₂)

/-- Resolution through uninterpretable features: each conjunct's set is realized, converging on
one exponent or crashing. -/
def formal (a b : Bundle Node) : Option Gender := realizeAll L.realize [percolateU a, percolateU b]

/-- A human's interpretable features beside an inanimate's uninterpretable ones: the former fill
the empty uninterpretable slot at Transfer, and both sets are realized. -/
def mixed (human inan : Bundle Node) : Option Gender :=
  realizeAll L.realize [redundancy (percolate human) (percolateU human), percolateU inan]

end System

/-- The three-way vocabulary shared by Greek and Icelandic. -/
def threeWay : List (VocabularyItem Node Gender) :=
  [[.fem, .masc] ⟷ .feminine, [.masc] ⟷ .masculine, [] ⟷ .neuter]

/-! ### Greek -/

namespace Greek

open _root_.Greek.StandardModern.Gender

/-- CLASS > MASC > FEM. -/
def system : System where
  geometry :=
    { nodes := [.cls, .masc, .fem]
      above
        | .fem => [.fem, .masc, .cls]
        | .masc => [.masc, .cls]
        | .cls => [.cls]
        | _ => [] }
  iNode
    | .man => .masc
    | .woman => .fem
    | _ => .cls
  uNode g _ :=
    match g with
    | .masculine => .masc
    | .feminine => .fem
    | _ => .cls
  vocabulary := threeWay

/-- An inanimate's bundle: interpretable CLASS beside its arbitrary gender. -/
def inanimate (n : Noun) : Bundle Node := system.conceptual .thing ++ system.arbitrary n.gender

theorem fem_entails_masc : system.geometry.Entails .fem .masc := by decide

/-- Uniform humans resolve to their shared gender. -/
theorem human_uniform :
    system.resolved .woman .woman = some .feminine ∧
      system.resolved .man .man = some .masculine := by
  decide

/-- *O andras ke i gineka ine eksipni*: FEM is lost, MASC kept. -/
theorem human_mismatch : system.resolved .man .woman = some .masculine := by decide

/-- *I gineka ke to koritsi ine eksipnes*: the neuter *koritsi* resolves by its referent. -/
theorem woman_girl : koritsi.gender = .neuter ∧ system.resolved .woman .woman = some .feminine := by
  decide

/-- *I megalofiia ke i adherfi tu ine charumeni*: two grammatically feminine nouns resolve
masculine because the genius is a man. -/
theorem genius_sister :
    megalofiia.gender = .feminine ∧ system.resolved .man .woman = some .masculine := by
  decide

/-- *To thima ke i mitera tis ine charumenes*: the neuter *thima* resolves feminine for a woman. -/
theorem victim_mother :
    thima.gender = .neuter ∧ system.resolved .woman .woman = some .feminine := by
  decide

/-- Uniform inanimates realize their shared arbitrary gender. -/
theorem inanimate_uniform :
    system.formal (inanimate fusta) (inanimate bluza) = some .feminine ∧
      system.formal (inanimate anaptiras) (inanimate fakos) = some .masculine ∧
      system.formal (inanimate piruni) (inanimate kutali) = some .neuter := by
  decide

/-- Mismatched inanimates resolve neuter through their interpretable CLASS. -/
theorem inanimate_mismatch :
    system.converted (inanimate pinakas) (inanimate karekla) = some .neuter ∧
      system.converted (inanimate scholio) (inanimate ekklisia) = some .neuter ∧
      system.converted (inanimate balkoni) (inanimate dhiadhromos) = some .neuter := by
  decide

/-- Percolating their uninterpretable features instead clashes at PF. -/
theorem inanimate_clash :
    system.formal (inanimate pinakas) (inanimate karekla) = none ∧
      system.formal (inanimate scholio) (inanimate ekklisia) = none := by
  decide

/-- Uniform inanimates may also percolate CLASS and resolve neuter. -/
theorem inanimate_uniform_neuter :
    system.converted (inanimate fusta) (inanimate bluza) = some .neuter := by
  decide

/-- Closest conjunct agreement is with uninterpretable features: feminine for *megalofiia*
whatever its referent, masculine for *pinakas*. -/
theorem closest_conjunct :
    system.realize (percolateU (system.arbitrary megalofiia.gender)) = some .feminine ∧
      system.realize (percolateU (inanimate pinakas)) = some .masculine := by
  decide

/-- *O kleftis ke to daxtilidi*: the thief's MASC and the ring's CLASS clash at PF; the paper
excludes the remaining, all-interpretable option at LF. -/
theorem human_inanimate_crash :
    system.mixed (system.conceptual .man) (inanimate daxtilidi) = none ∧
      resolve (system.conceptual .man) (inanimate daxtilidi) = some [.cls] := by
  decide

/-- Matched humans and inanimates converge: *o kleftis ke o pinakas*, *i gineka ke i ombrela*. -/
theorem human_inanimate_match :
    system.mixed (system.conceptual .man) (inanimate pinakas) = some .masculine ∧
      system.mixed (system.conceptual .woman) (inanimate ombrela) = some .feminine := by
  decide

/-- The fixed-gender *thima* and *megalofiia* match an inanimate by their referents. -/
theorem victim_painting :
    system.mixed (system.conceptual .man) (inanimate pinakas) = some .masculine ∧
      system.mixed (system.conceptual .woman) (inanimate fotografia) = some .feminine ∧
      system.mixed (system.conceptual .man) (inanimate fotografia) = none := by
  decide

/-- Clausal subjects bear no gender features and are realized neuter. -/
theorem clausal : system.realize [] = some .neuter := by decide

/-- No neuter–feminine syncretism to the exclusion of masculine, for any vocabulary with one
item per exponent over the Greek feature sets. -/
theorem no_aba (v : List (VocabularyItem Node Gender)) (hinj : (v.map exponent).Nodup) {φ : Gender}
    (hn : Realizes v (Neighborhood.ofBundle [.cls]) φ)
    (hf : Realizes v (Neighborhood.ofBundle [.fem, .masc, .cls]) φ) :
    Realizes v (Neighborhood.ofBundle [.masc, .cls]) φ :=
  Realizes.of_realizes hinj (fun _ h => List.Subset.trans h (by decide))
    (fun _ h => List.Subset.trans h (by decide)) hn hf

end Greek

/-! ### Icelandic -/

namespace Icelandic

open _root_.Icelandic.Gender

/-- CLASS above independent MASC and FEM. -/
def system : System where
  geometry :=
    { nodes := [.cls, .masc, .fem]
      above
        | .fem => [.fem, .cls]
        | .masc => [.masc, .cls]
        | .cls => [.cls]
        | _ => [] }
  iNode
    | .man => .masc
    | .woman => .fem
    | _ => .cls
  uNode g _ :=
    match g with
    | .masculine => .masc
    | .feminine => .fem
    | _ => .cls
  vocabulary := threeWay

def inanimate (n : Noun) : Bundle Node := system.conceptual .thing ++ system.arbitrary n.gender

theorem fem_not_entails_masc : ¬ system.geometry.Entails .fem .masc := by decide

/-- *Maðurinn og konan eru þreytt*: only CLASS survives. -/
theorem human_mismatch : system.resolved .man .woman = some .neuter := by decide

/-- *Skáldið og Jón eru frægir*: the neuter *skáld* resolves masculine for a man. -/
theorem poet_jon : skald.gender = .neuter ∧ system.resolved .man .man = some .masculine := by
  decide

/-- *Frægð og frami eru tvíeggjuð*. -/
theorem inanimate_mismatch :
    system.converted (inanimate fraegd) (inanimate frami) = some .neuter ∧
      system.formal (inanimate fraegd) (inanimate frami) = none := by
  decide

end Icelandic

/-! ### Bosnian/Croatian/Serbian -/

namespace BCS

open _root_.Serbian.Gender

/-- CLASS > INDIV > {GRP, MASC > ANIM > FEM}; a plural coordination bears GRP, and with it
INDIV. -/
def system : System where
  geometry :=
    { nodes := [.cls, .indiv, .grp, .masc, .anim, .fem]
      above
        | .fem => [.fem, .anim, .masc, .indiv, .cls]
        | .anim => [.anim, .masc, .indiv, .cls]
        | .masc => [.masc, .indiv, .cls]
        | .grp => [.grp, .indiv, .cls]
        | .indiv => [.indiv, .cls]
        | .cls => [.cls] }
  iNode
    | .man => .anim
    | .woman => .fem
    | .thing => .masc
    | .mass => .cls
  uNode g human :=
    match g, human with
    | .masculine, true => .anim
    | .masculine, false => .masc
    | .feminine, _ => .fem
    | _, _ => .cls
  plural := [.grp, .indiv, .cls]
  vocabulary :=
    [[.fem, .anim, .masc, .indiv] ⟷ .feminine, [.anim, .masc, .indiv] ⟷ .masculine,
      [.indiv] ⟷ .masculine, [] ⟷ .neuter]

def inanimate (n : Noun) : Bundle Node :=
  system.conceptual (if n.gender = .neuter then .mass else .thing) ++ system.arbitrary n.gender

/-- *Muškarac i žena su sretni*. -/
theorem human_mismatch : system.resolved .man .woman = some .masculine := by decide

/-- Uniform women still resolve feminine. -/
theorem women : system.resolved .woman .woman = some .feminine := by decide

/-- *Znanje i intuicija su saradivali*: INDIV from the coordination's GRP realizes masculine. -/
theorem inanimate_mismatch :
    system.converted (inanimate znanje) (inanimate intuicija) = some .masculine := by
  decide

/-- *Naše selo i celo jedno brdo su izgoreli*: two neuters resolve masculine. -/
theorem neuter_pair : system.converted (inanimate selo) (inanimate brdo) = some .masculine := by
  decide

/-- Neuter alone is mass: without GRP it stays neuter. -/
theorem neuter_mass : system.realize (system.geometry.above .cls) = some .neuter := by decide

end BCS

/-! ### The geometries -/

/-- All three geometries satisfy mismatch resolution: no pair of nodes needs a default. -/
theorem mismatchResolution :
    Greek.system.geometry.MismatchResolution ∧ Icelandic.system.geometry.MismatchResolution ∧
      BCS.system.geometry.MismatchResolution := by
  decide

/-- Table 2: the resolution of mismatched humans and of mismatched inanimates in Greek,
Icelandic, and Bosnian/Croatian/Serbian. -/
theorem table2 :
    [Greek.system, Icelandic.system, BCS.system].map
        (fun L => (L.resolved .man .woman, L.resolved .thing .thing)) =
      [(some .masculine, some .neuter), (some .neuter, some .neuter),
        (some .masculine, some .masculine)] := by
  decide

end AdamsonAnagnostopoulou2025
