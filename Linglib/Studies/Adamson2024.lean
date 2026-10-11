module

public import Linglib.Morphology.DistributedMorphology.NominalProjection
public import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Impoverishment
public import Linglib.Fragments.Teop.Nouns
public import Linglib.Syntax.Agreement.Classes
public import Linglib.Fragments.Jarawara.PossessedNouns
public import Linglib.Fragments.Romance.Italian.NumberGender
public import Linglib.Fragments.Yanyuwa.Gender
public import Linglib.Fragments.CoastalMarind.Gender
public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Data.Examples.Adamson2024

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
II (`Teop.switch`, `Teop.rows_outerClass`). Mosel and Spriggs's gender I-E is gender I with a
proprial feature. The article vocabulary derives the article of every class
(`Teop.article_eq_headArticle`), and agreeing adjectives and numerals distinguish only gender
(`Teop.agreementClasses_targetArticle`). Jarawara's possessed nouns are the unmarked
feminine, and the *mano* ~ *mani* alternation is agreement with the possessor: gender
impoverishment next to a plural or participant feature bleeds the masculine exponent
(`Jarawara.decl_masc_only`, `Jarawara.mano_eq_manoParadigm`), and a monomoraic possessor prefix
forms one word with the noun it possesses and is invisible beyond it, so in *o-mano baki* the
outer noun agrees with the possessed noun's own feminine (`Jarawara.complex_match`,
`Jarawara.complex_mismatch`).

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
* [mosel-spriggs-2000]
* [dixon-2004]
* [myler-2016]
-/

@[expose] public section

namespace Adamson2024

open DistributedMorphology
open DistributedMorphology.Categorizer (Head)

/-! ### The gender locality hypothesis -/

/-- An inalienable possessor can bear on gender, an alienable one cannot. -/
theorem possession_asymmetry :
    PossessionType.inalienable.canAffectGender = true ∧
      PossessionType.alienable.canAffectGender = false := by
  decide

/-! ### Teop: possessee gender -/

namespace Teop

open _root_.Teop

/-- The nominalizer of a body-part or kinship root, bearing u[animate] and, when `selectsD`,
the feature {D} that licenses a possessor. -/
def relationalN (selectsD : Bool) : Head := { Head.n_uAnim with selectsD }

/-- The alienator, a gender II n that closes the possessor slot. -/
def alienatorN : Head := Head.n_plain

/-- A head is animate when it bears [+ANIM], the gender I feature. -/
def Animate (h : Head) : Prop := h.gender.map (·.val) = some ⟨.anim, .pos⟩

instance : DecidablePred Animate := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The class of a nominal, read off its highest n. -/
def outerClass (stack : List Head) : NounClass :=
  match stack.getLast? with
  | some h => if Animate h then .a else .o
  | none => .o

/-- The possessed body-part noun, a root under the {D} nominalizer. -/
def ipossessed : List Head := [relationalN true]

/-- The unpossessed body-part noun, with the {D}-less nominalizer under the alienator. Alienably
possessed and compounded body-part nouns have the same structure. -/
def free : List Head := [relationalN false, alienatorN]

/-- *a bina-naa* 'my spleen' is a-class and *o bina* 'the spleen' is o-class. -/
theorem switch : outerClass ipossessed = .a ∧ outerClass free = .o := by decide

/-- Every body-part term of the fragment has the class of the unpossessed noun. -/
theorem bodyPartTerms_free : ∀ n ∈ bodyPartTerms, n.gender = outerClass free := by decide

/-- The structure of a body-part or kinship noun, by how it is possessed. -/
def possession : List (String × List Head) :=
  [("inalienable", ipossessed), ("alienable", free), ("none", free)]

/-- The analysis predicts the class of every attested body-part and kinship phrase from how its
noun is possessed, (39), (40), (44), (45), (48) and (51). -/
theorem rows_outerClass : ∀ e ∈ Examples.all, e.language = "teop1238" →
    ∀ s ∈ e.parse? "possession" possession,
      ∀ c ∈ e.parse? "gender" [("I", NounClass.a), ("II", .o)], outerClass s = c := by
  decide

/-- The features of the article, copied from DP by concord. -/
inductive ArticleFeature where
  | animate
  | pl
  | proper
  deriving DecidableEq, Repr

/-- The article vocabulary (32). -/
def articles : List (VocabularyItem ArticleFeature Article) :=
  [[.animate, .pl] ⟷ .o, [.pl] ⟷ .a, [.animate, .proper] ⟷ .e, [.animate] ⟷ .a, [] ⟷ .o]

/-- The article features of each class. Gender I-E is gender I with [proper]. -/
def classFeatures : NounClass → List ArticleFeature
  | .e => [.animate, .proper]
  | .a => [.animate]
  | .o => []

/-- The article inserted by the Subset Principle, by class and number. -/
def article (c : NounClass) (plural : Bool) : Option Article :=
  subsetPrinciple articles (classFeatures c ++ if plural then [ArticleFeature.pl] else [])

/-- The vocabulary derives the basic article of every class and number. -/
theorem article_eq_headArticle : ∀ c pl, article c pl = some (headArticle c pl) := by decide

/-- The agreement classes of adjectives and numerals are the fibres of [animate], so gender I-E
is not a gender. -/
theorem agreementClasses_targetArticle :
    Gender.agreementClasses targetArticle =
      Setoid.ker fun c ↦ (classFeatures c).contains .animate := by
  ext c c'
  simp only [Setoid.ker_def]
  cases c <;> cases c' <;> decide

/-- A possessed kinship term takes the proprial article *e*, (50), and one under the alienator
takes *o*, (51). -/
theorem kinship :
    subsetPrinciple articles (.proper :: classFeatures (outerClass ipossessed)) = some .e ∧
      subsetPrinciple articles (.proper :: classFeatures (outerClass free)) = some .o := by
  decide

section Denotation

open Possession

variable {E S : Type*} (isSpleen : E → S → Prop) (bodyPartOf : E → E → S → Prop)

/-- The possessed body-part noun, the root relationalized by the body-part-of relation. -/
def ipossessedDenot : E → E → S → Prop := π isSpleen bodyPartOf

/-- The unpossessed body-part noun, whose possessor slot the alienator closes. -/
def freeDenot : E → S → Prop := ExPossessor (π isSpleen bodyPartOf)

/-- The possessor slot is open under the {D} nominalizer and existentially closed under the
alienator. -/
theorem freeDenot_iff (y : E) (s : S) :
    freeDenot isSpleen bodyPartOf y s ↔ isSpleen y s ∧ ∃ x, bodyPartOf x y s :=
  exPossessor_pi ..

end Denotation

end Teop

/-! ### Jarawara: possessee gender and possessor agreement -/

namespace Jarawara

open _root_.Jarawara (Possessor PossessedForm manoParadigm paradigmCells form)

/-- The privative φ-features are [masc], [pl], and [participant] for first and second person. -/
inductive Phi where
  | masc
  | pl
  | participant
  deriving DecidableEq, Repr

/-- The features a possessor contributes to agreement. -/
def possessorPhi (p : Possessor) : List Phi :=
  (if p.person = .third then [] else [.participant]) ++ (if p.number = .Plur then [.pl] else []) ++
    (if p.gender = some .masc then [.masc] else [])

/-- Gender impoverishment deletes [masc] next to [pl] and next to [participant]. -/
def impoverishment : List (ImpoverishmentRule (List Phi) Phi) :=
  [.ofFocus (.pl ∈ ·) .masc, .ofFocus (.participant ∈ ·) .masc]

/-- The φ-bundle after impoverishment. -/
def impoverish (φ : List Phi) : List Phi :=
  runChain (ImpoverishmentRule.apply List.erase) impoverishment (Neighborhood.ofBundle φ)

/-- The declarative marker is *ka* for [masc] and *ke* elsewhere. -/
def declarative : List (VocabularyItem Phi String) := [[.masc] ⟷ "ka", [] ⟷ "ke"]

/-- The declarative marker agreeing with a nominal of features `φ`. -/
def decl (φ : List Phi) : Option String := subsetPrinciple declarative (impoverish φ)

/-- Masculine singular takes *ka* and everything else *ke*, so impoverishment bleeds the specific
exponent. -/
theorem decl_masc_only :
    decl [.masc] = some "ka" ∧ decl [] = some "ke" ∧ decl [.participant] = some "ke" ∧
      decl [.masc, .pl] = some "ke" := by
  decide

/-- A possessed noun takes its marked form for [participant] or a surviving [masc] and its
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

/-- A possessor makes its features visible outside the word of the noun it possesses unless it
is a pronoun below the two-mora minimal word, which forms one word with that noun. -/
def visibleOutside (p : Possessor) : List Phi :=
  match p.pronoun with
  | some (_, m) => if m < 2 then [] else possessorPhi p
  | none => possessorPhi p

/-- *bako* 'inside' in `[[p mano] bako]` agrees with the possessor when its features percolate
and with the feminine possessed noun otherwise. -/
def inside (p : Possessor) : Option String :=
  subsetPrinciple (possessedItems "bako" "baki") (impoverish (visibleOutside p))

/-- Possessors of two or more moras percolate, so the inner and outer nouns match. -/
theorem complex_match :
    ∀ p ∈ paradigmCells, (∀ f ∈ p.pronoun, 2 ≤ f.2) →
      inside p = some (form (manoParadigm p)).2 := by
  decide

/-- The monomoraic *o-* and *ti-* do not, as in *o-mano baki* and *ti-mano baki*. -/
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

/-- A plural class's number feature sits on n for the *-a* plurals and on Num for regular
plurals. -/
def numberPosition : PluralClass → NumberPosition
  | .aPlural => .onN
  | .regular => .onNum

/-- Gender changes between singular and plural exactly when number sits within the hypothesis's
reach. -/
theorem gender_change_iff_local :
    ∀ n ∈ aPlurals ++ regulars,
      n.gender ≠ n.plGender ↔
        genderLocalityHypothesis (numberPosition n.pluralClass).toPosition = true := by
  decide

end Italian

end Adamson2024
