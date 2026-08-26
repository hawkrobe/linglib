import Linglib.Morphology.DistributedMorphology.NominalProjection
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Morphology.DistributedMorphology.Impoverishment
import Linglib.Fragments.Teop.Nouns
import Linglib.Fragments.Jarawara.PossessedNouns
import Linglib.Fragments.Italian.NumberGender
import Linglib.Fragments.Yanyuwa.Gender
import Linglib.Fragments.CoastalMarind.Gender
import Linglib.Semantics.Possessive.Relational
import Linglib.Data.Examples.Adamson2024

/-!
# Gender assignment is local

Adamson's gender locality hypothesis says that the gender feature on a nominalizer n is valued
within nP (`DistributedMorphology.genderLocalityHypothesis`), so an inalienable possessor in
Spec,nP can bear on a noun's gender while an alienable possessor in Spec,PossP cannot
(`possession_asymmetry`). Possession bears on gender in two ways. Under *possessee gender* the
nominalizer that licenses a possessor carries a gender of its own: Teop body-part roots take a
gender I nominalizer that introduces the body-part relation with or without the selectional
feature licensing a possessor, and the possessor-less variant is renominalized by a gender II
alienator that closes the possessor slot (`Teop.relationalN`, `Teop.alienatorN`,
`Teop.freeDenot_iff`), so *a bina-naa* 'my spleen' is gender I and *o bina* 'the spleen' gender
II (`Teop.switch`); the article vocabulary derives the whole paradigm, including the
cross-identity of singular gender I with plural gender II (`Teop.article_eq_articleForm`,
`Teop.cross_identity`). Jarawara's possessed nouns are the unmarked feminine, and the *mano* ~
*mani* alternation is agreement with the possessor: gender impoverishment next to a plural or
participant feature bleeds the masculine exponent (`Jarawara.decl_masc_only`,
`Jarawara.mano_eq_manoParadigm`), and a monomoraic possessor prefix forms one word with the noun
it possesses and is invisible beyond it, so in *o-mano baki* the outer noun agrees with the
possessed noun's own feminine (`Jarawara.complex_match`, `Jarawara.complex_mismatch`).

Under *inherited gender* the nominalizer is unvalued and probes its possessor
(`DistributedMorphology.inheritedGender`): Yanyuwa *wini* 'name' and Coastal Marind *igih* 'name'
and *nanVh* 'face' take the gender of an inalienable possessor on their agreement targets and, for
*nanVh*, in their own form (`Yanyuwa.name_agreement`, `CoastalMarind.name_demonstrative`,
`CoastalMarind.face_inherits`), and an alienable possessor leaves them unvalued
(`Yanyuwa.name_alienable`). The hypothesis extends beyond possession: Standard Italian plurals in
*-a* carry number on n and change gender, regular plurals carry number on Num and do not
(`Italian.gender_change_iff_local`).

## References

* [adamson-2024]
* [kramer-2015]
* [dixon-2004]
* [myler-2016]
-/

namespace Adamson2024

open DistributedMorphology
open scoped DistributedMorphology.VocabularyItem
open DistributedMorphology.Categorizer (Head)

/-! ### The gender locality hypothesis -/

/-- An inalienable possessor can bear on gender, an alienable one cannot. -/
theorem possession_asymmetry :
    PossessionType.inalienable.canAffectGender = true ∧
      PossessionType.alienable.canAffectGender = false := by
  decide

/-! ### Teop: possessee gender -/

namespace Teop

open _root_.Teop (ArticleCtx articleForm)

/-- The nominalizer of a body-part or kinship root: it introduces the relation and bears
u[animate], with or without the selectional feature {D} that licenses a possessor. -/
def relationalN (selectsD : Bool) : Head where
  categorizer := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }
  selectsD := selectsD

/-- The alienator, a further n of gender II that closes the possessor slot. -/
def alienatorN : Head := Head.n_plain

/-- A head bears the gender I feature [animate]. -/
def Animate (h : Head) : Prop := h.phi.gender.map (·.val.dim) = some .anim

instance : DecidablePred Animate :=
  fun h => inferInstanceAs (Decidable (h.phi.gender.map (·.val.dim) = some .anim))

/-- The gender of a nominal, read off its highest n; gender II is the absence of [animate]. -/
def outerGender (stack : List Head) : _root_.Teop.Gender :=
  match stack.getLast? with
  | some h => if Animate h then .gI else .gII
  | none => .gII

/-- The possessed body-part noun: the root under the {D} nominalizer. -/
def ipossessed : List Head := [relationalN true]

/-- The free, alienably possessed, or compounded body-part noun: the {D}-less nominalizer under
the alienator. -/
def free : List Head := [relationalN false, alienatorN]

/-- *a bina-naa* 'my spleen' is gender I, *o bina* 'the spleen' gender II. -/
theorem switch : outerGender ipossessed = .gI ∧ outerGender free = .gII := by decide

/-- The article's features, percolated to D by concord: [animate] is gender I, [proper] the
proprial class. -/
inductive ArticleFeature where
  | animate
  | pl
  | proper
  deriving DecidableEq, Repr

/-- The article vocabulary, in the paper's order. -/
def articles : List (VocabularyItem ArticleFeature String) :=
  [[.animate, .pl] ⟷ "o", [.pl] ⟷ "a", [.animate, .proper] ⟷ "e", [.animate] ⟷ "a",
    [] ⟷ "o"]

/-- The article's bundle for a Fragment `ArticleCtx`. -/
def articleFeatures (c : ArticleCtx) : List ArticleFeature :=
  (if c.gender = .gI then [.animate] else []) ++ (if c.plural then [.pl] else []) ++
    (if c.proprial then [.proper] else [])

/-- The article the Subset Principle inserts. -/
def article (c : ArticleCtx) : Option String := subsetPrinciple articles (articleFeatures c)

/-- The vocabulary derives the Fragment's paradigm, the neutralization of the proprial article
in the plural included. -/
theorem article_eq_articleForm : ∀ c, article c = some (articleForm c) := by decide

/-- The cross-identity: singular gender I and plural gender II share *a*, plural gender I and
singular gender II share *o*. -/
theorem cross_identity :
    article ⟨.gI, false, false⟩ = article ⟨.gII, true, false⟩ ∧
      article ⟨.gI, true, false⟩ = article ⟨.gII, false, false⟩ := by
  decide

/-- The body-part noun's article follows its nominalizer, whatever the possessor's gender: *a*
possessed, *o* free, alienably possessed, or compounded. -/
theorem bodyPart_article :
    article ⟨outerGender ipossessed, false, false⟩ = some "a" ∧
      article ⟨outerGender free, false, false⟩ = some "o" := by
  decide

/-- Kinship roots take the proprial article when possessed and switch to gender II under the
alienator *-na*. -/
theorem kinship :
    article ⟨outerGender ipossessed, false, true⟩ = some "e" ∧
      article ⟨outerGender free, false, false⟩ = some "o" := by
  decide

section Denotation

open ArgumentStructure.Relational

variable {E S : Type*} (isSpleen : E → S → Prop) (bodyPartOf : E → E → S → Prop)

/-- The possessed body-part noun: the root relationalized by the body-part-of relation, awaiting
its possessor. -/
def ipossessedDenot : E → E → S → Prop := π isSpleen bodyPartOf

/-- The free body-part noun: the alienator closes the possessor slot. -/
def freeDenot : E → S → Prop := ExPossessor (π isSpleen bodyPartOf)

/-- One root, two types: the possessor slot is open under the {D} nominalizer and existentially
closed under the alienator. -/
theorem freeDenot_iff (y : E) (s : S) :
    freeDenot isSpleen bodyPartOf y s ↔ isSpleen y s ∧ ∃ x, bodyPartOf x y s :=
  exPossessor_pi ..

end Denotation

end Teop

/-! ### Jarawara: possessee gender and possessor agreement -/

namespace Jarawara

open _root_.Jarawara (Possessor PossessedForm manoParadigm paradigmCells form)

/-- The privative φ-features: [masc], [pl], and [participant] for first and second person. -/
inductive Phi where
  | masc
  | pl
  | participant
  deriving DecidableEq, Repr

/-- The features a possessor contributes to agreement. -/
def possessorPhi (p : Possessor) : List Phi :=
  (if p.person = .third then [] else [.participant]) ++ (if p.number = .Plur then [.pl] else []) ++
    (if p.gender = some .masc then [.masc] else [])

/-- Gender impoverishment: [masc] is deleted next to [pl] and next to [participant]. -/
def impoverishment : List (ImpoverishmentRule (List Phi) Phi) :=
  [.paradigmatic (·.contains .pl) .masc, .paradigmatic (·.contains .participant) .masc]

/-- The φ-bundle after impoverishment. -/
def impoverish (φ : List Phi) : List Phi :=
  runChain (ImpoverishmentRule.apply List.erase) impoverishment (Neighborhood.ofBundle φ)

/-- The declarative marker's items: *ka* for [masc], *ke* elsewhere. -/
def declarative : List (VocabularyItem Phi String) := [[.masc] ⟷ "ka", [] ⟷ "ke"]

/-- The declarative marker agreeing with a nominal of features `φ`. -/
def decl (φ : List Phi) : Option String := subsetPrinciple declarative (impoverish φ)

/-- Masculine singular takes *ka*, everything else *ke*: impoverishment bleeds the specific
exponent. -/
theorem decl_masc_only :
    decl [.masc] = some "ka" ∧ decl [] = some "ke" ∧ decl [.participant] = some "ke" ∧
      decl [.masc, .pl] = some "ke" := by
  decide

/-- The items of a possessed noun: its marked form for [participant] or a surviving [masc], its
unmarked form elsewhere. -/
def possessedItems (marked unmarked : String) : List (VocabularyItem Phi String) :=
  [[.participant] ⟷ marked, [.masc] ⟷ marked, [] ⟷ unmarked]

/-- The form of *mano* 'arm' agreeing with possessor `p`. -/
def mano (p : Possessor) : Option String :=
  subsetPrinciple (possessedItems "mano" "mani") (impoverish (possessorPhi p))

/-- Impoverishment then insertion derives the paradigm of *mano*; the third masculine plural
*mani* is the cell where impoverishment does the work. -/
theorem mano_eq_manoParadigm : ∀ p ∈ paradigmCells, mano p = some (form (manoParadigm p)).1 := by
  decide

/-- The features a possessor makes visible outside the word of the noun it possesses: none for
a pronoun below the two-mora minimal word, which forms one word with that noun. -/
def visibleOutside (p : Possessor) : List Phi :=
  match p.pronoun with
  | some (_, m) => if m < 2 then [] else possessorPhi p
  | none => possessorPhi p

/-- The form of *bako* 'inside' in `[[p mano] bako]`: agreement with the possessor when its
features percolate, and with the feminine possessed noun otherwise. -/
def inside (p : Possessor) : Option String :=
  subsetPrinciple (possessedItems "bako" "baki") (impoverish (visibleOutside p))

/-- Possessors of two or more moras percolate: the inner and outer nouns match. -/
theorem complex_match :
    ∀ p ∈ paradigmCells, (∀ f ∈ p.pronoun, 2 ≤ f.2) →
      inside p = some (form (manoParadigm p)).2 := by
  decide

/-- The monomoraic *o-* and *ti-* do not: *o-mano baki*, *ti-mano baki*. -/
theorem complex_mismatch :
    mano ⟨.first, .Sing, none⟩ = some "mano" ∧ inside ⟨.first, .Sing, none⟩ = some "baki" ∧
      mano ⟨.second, .Sing, none⟩ = some "mano" ∧ inside ⟨.second, .Sing, none⟩ = some "baki" := by
  decide

end Jarawara

/-! ### Yanyuwa and Coastal Marind: inherited gender -/

namespace Yanyuwa

open _root_.Yanyuwa

/-- The gender *wini* 'name' acquires from a possessor of class `g` at `pos`. -/
def nameGender (pos : NominalProjection.Position) (g : _root_.Yanyuwa.Gender) :
    Option _root_.Yanyuwa.Gender :=
  inheritedGender pos g

/-- Quantifiers and demonstratives agreeing with *wini* take the possessor's class prefix. -/
theorem name_agreement (g : _root_.Yanyuwa.Gender) :
    (nameGender PossessionType.inalienable.possessorPosition g).map agreementPrefix =
      some (agreementPrefix g) :=
  rfl

/-- An alienable possessor is out of the probe's reach. -/
theorem name_alienable (g : _root_.Yanyuwa.Gender) :
    nameGender PossessionType.alienable.possessorPosition g = none :=
  rfl

end Yanyuwa

namespace CoastalMarind

open _root_.CoastalMarind

/-- The demonstrative agreeing with *igih* 'name' takes the possessor's gender. -/
theorem name_demonstrative (g : _root_.CoastalMarind.Gender) :
    (inheritedGender PossessionType.inalienable.possessorPosition g).map demonstrative =
      some (demonstrative g) :=
  rfl

/-- *nanVh* 'face' is *nanih* with a gender I possessor and *nanuh* with a gender II one, the
similative agreeing alongside. -/
theorem face_inherits :
    (inheritedGender PossessionType.inalienable.possessorPosition .gI).map face = some "nanih" ∧
      (inheritedGender PossessionType.inalienable.possessorPosition .gII).map face =
        some "nanuh" ∧
      similative .gI = some "hi" ∧ similative .gII = some "hu" := by
  decide

end CoastalMarind

/-! ### Number on n -/

namespace Italian

open _root_.Italian.NumberGender

/-- Where a plural class's number feature sits: *-a* plurals on n, regular plurals on Num. -/
def numberPosition : PluralClass → NumberPosition
  | .aPlural => .onN
  | .regular => .onNum

/-- Gender changes between singular and plural exactly when number sits within the hypothesis's
reach. -/
theorem gender_change_iff_local :
    ∀ n ∈ aPlurals ++ regulars,
      n.sgGender ≠ n.plGender ↔
        genderLocalityHypothesis (numberPosition n.pluralClass).toPosition = true := by
  decide

end Italian

end Adamson2024
