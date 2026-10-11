module

public import Mathlib.Order.Basic
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
within nP (`GenderLocal`), so an inalienable possessor in
Spec,nP can bear on a noun's gender while an alienable possessor in Spec,PossP cannot
(`possession_asymmetry`). Possession bears on gender in two ways. Under *possessee gender* the
nominalizer that licenses a possessor carries a gender of its own: Teop body-part roots take a
gender I nominalizer that introduces the body-part relation with or without the selectional
feature licensing a possessor, and the possessor-less variant is renominalized by a gender II
alienator that closes the possessor slot (`Teop.relationalN`, `Teop.alienatorN`,
`Teop.freeDenot_iff`), so *a bina-naa* 'my spleen' is gender I and *o bina* 'the spleen' gender
II (`Teop.switch`, `Teop.rows_class`). The alienator is a plain n over a gendered one, so the
default gender II is what the cyclic explanation of Kramer's Highest Gender Hypothesis predicts
and not the hierarchical one (`Teop.free_cyclic`). Mosel and Spriggs's gender I-E is gender I with a
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
(`inheritedGender`): Yanyuwa *wini* 'name' and Coastal Marind *igih* 'name'
and *nanVh* 'face' take the gender of an inalienable possessor on their agreement targets and, for
*nanVh*, in their own form (`Yanyuwa.name_agreement`, `CoastalMarind.name_demonstrative`,
`CoastalMarind.face_inherits`), and an alienable possessor leaves them unvalued
(`Yanyuwa.name_alienable`). The hypothesis extends beyond possession: Standard Italian plurals in
*-a* carry number on n and change gender, regular plurals carry number on Num and do not
(`Italian.gender_change_iff_local`).

## Implementation notes

* An inalienable possessor sits in Spec,nP, following Myler; Alexiadou makes it the complement
  of the noun. Both places are within nP, which is all the locality hypothesis uses.
* A Teop nominal's class is the gender a probe finds on its highest n alone, the cyclic
  explanation of Kramer's Highest Gender Hypothesis.

## References

* [adamson-2024]
* [kramer-2015]
* [alexiadou-2003]
* [mosel-spriggs-2000]
* [dixon-2004]
* [myler-2016]
-/

@[expose] public section

namespace Adamson2024

open DistributedMorphology
open DistributedMorphology.Categorizer (Head)

/-! ### The gender locality hypothesis -/

/-- The layers of the nominal projection, from the root up. -/
inductive Layer where
  | root
  | n
  | poss
  | num
  | d
  deriving DecidableEq, Repr, Fintype

/-- The height of a layer. -/
def Layer.height : Layer → ℕ
  | .root => 0
  | .n => 1
  | .poss => 2
  | .num => 3
  | .d => 4

instance : LinearOrder Layer := LinearOrder.lift' Layer.height (by decide)

/-- The positions of a possessor or of a number feature. -/
inductive Position where
  | nHead
  | specN
  | specPoss
  | num
  deriving DecidableEq, Repr, Fintype

/-- The layer a position attaches at. -/
def Position.layer : Position → Layer
  | .nHead | .specN => .n
  | .specPoss => .poss
  | .num => .num

/-- A position is local to gender when it attaches within nP. The gender locality hypothesis says
that only local positions can value gender on n. -/
def GenderLocal (p : Position) : Prop := p.layer ≤ .n

instance : DecidablePred GenderLocal := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

/-- Inalienable and alienable possession. -/
inductive PossessionType where
  | inalienable
  | alienable
  deriving DecidableEq, Repr, Fintype

/-- An inalienable possessor sits in Spec,nP and an alienable one in Spec,PossP. -/
def PossessionType.possessorPosition : PossessionType → Position
  | .inalienable => .specN
  | .alienable => .specPoss

/-- An inalienable possessor can bear on gender, an alienable one cannot. -/
theorem possession_asymmetry :
    GenderLocal PossessionType.inalienable.possessorPosition ∧
      ¬ GenderLocal PossessionType.alienable.possessorPosition := by
  decide

/-- The gender an unvalued n acquires from a possessor of gender `g` at `pos`, when the
possessor is local. -/
def inheritedGender {G : Type*} (pos : Position) (g : G) : Option G :=
  if GenderLocal pos then some g else none

/-! ### Teop: possessee gender -/

namespace Teop

open _root_.Teop

/-- The nominalizer of a body-part or kinship root, bearing u[animate] and, when `selectsD`,
the feature {D} that licenses a possessor. -/
def relationalN (selectsD : Bool) : Head := { Head.n_uAnim with selectsD }

/-- The alienator, a gender II n that closes the possessor slot. -/
def alienatorN : Head := Head.n_plain

/-- The class a head gives a nominal, the a-class for the gender I feature [+ANIM] and none
otherwise. -/
def headClass (h : Head) : Option NounClass :=
  if h.gender.map (·.val) = some ⟨.anim, .pos⟩ then some .a else none

/-- The n's of a possessed body-part noun, the {D} nominalizer. -/
def ipossessed : List Head := [relationalN true]

/-- The n's of an unpossessed body-part noun, the alienator over the {D}-less nominalizer, the
highest first. Alienably possessed and compounded body-part nouns have the same n's. -/
def free : List Head := [alienatorN, relationalN false]

/-- *a bina-naa* 'my spleen' is a-class and *o bina* 'the spleen' is o-class, the o-class being
gender II, the default. -/
theorem switch :
    agreeingGender headClass .o (ipossessed.take 1) = .a ∧
      agreeingGender headClass .o (free.take 1) = .o := by
  decide

/-- The plain alienator over the gender I nominalizer gives *o bina* the default o-class, as on
the cyclic explanation of the Highest Gender Hypothesis, where the probe sees the alienator
alone; on the hierarchical explanation it would find the lower n and give the a-class. -/
theorem free_cyclic :
    agreeingGender headClass .o (free.take 1) = .o ∧ agreeingGender headClass .o free = .a :=
  agreeingGender_plain_cons (hs := []) (by decide) (by decide)

/-- Every body-part term of the fragment has the class of the unpossessed noun. -/
theorem bodyPartTerms_free :
    ∀ n ∈ bodyPartTerms, n.gender = agreeingGender headClass .o (free.take 1) := by
  decide

/-- The n's of a body-part or kinship noun, by how it is possessed. -/
def possession : List (String × List Head) :=
  [("inalienable", ipossessed), ("alienable", free), ("none", free)]

/-- The analysis predicts the class of every attested body-part and kinship phrase from how its
noun is possessed, (39), (40), (44), (45), (48) and (51). -/
theorem rows_class : ∀ e ∈ Examples.all, e.language = "teop1238" →
    ∀ s ∈ e.parse? "possession" possession,
      ∀ c ∈ e.parse? "gender" [("I", NounClass.a), ("II", .o)],
        agreeingGender headClass .o (s.take 1) = c := by
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
    subsetPrinciple articles
        (.proper :: classFeatures (agreeingGender headClass .o (ipossessed.take 1))) = some .e ∧
      subsetPrinciple articles
        (.proper :: classFeatures (agreeingGender headClass .o (free.take 1))) = some .o := by
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

/-- Quantifiers and demonstratives agreeing with *wini* 'name' take the prefix of an
inalienable possessor's class. -/
theorem name_agreement (g : _root_.Yanyuwa.Gender) :
    (inheritedGender PossessionType.inalienable.possessorPosition g).map agreementPrefix =
      some (agreementPrefix g) :=
  rfl

/-- An alienable possessor is out of the probe's reach. -/
theorem name_alienable (g : _root_.Yanyuwa.Gender) :
    inheritedGender PossessionType.alienable.possessorPosition g = none :=
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
def numberPosition : PluralClass → Position
  | .aPlural => .nHead
  | .regular => .num

/-- Gender changes between singular and plural exactly when number sits within the hypothesis's
reach. -/
theorem gender_change_iff_local :
    ∀ n ∈ aPlurals ++ regulars,
      n.gender ≠ n.plGender ↔
        GenderLocal (numberPosition n.pluralClass) := by
  decide

end Italian

end Adamson2024
