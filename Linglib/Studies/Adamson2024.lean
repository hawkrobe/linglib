import Linglib.Morphology.DistributedMorphology.NominalSpine
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Morphology.DistributedMorphology.Impoverishment
import Linglib.Fragments.Teop.Nouns
import Linglib.Fragments.Jarawara.PossessedNouns
import Linglib.Fragments.Italian.NumberGender
import Linglib.Semantics.Possessive.Relational

/-!
# Gender assignment is local

[adamson-2024] proposes the Gender Locality Hypothesis: the gender feature
on a nominalizer n is valued within nP. An inalienable possessor sits in
Spec,nP and can therefore determine a noun's gender; an alienable possessor
sits in Spec,PossP and cannot. The hypothesis itself is
`DistributedMorphology.genderLocalityHypothesis`. This file derives the
paper's case studies from it and from the shared Vocabulary Insertion and
Impoverishment engines.

## Main definitions

* `Teop.relationalN`, `Teop.alienatorN`: the two nominalizers available to a
  body-part or kinship root — one licensing an inalienable possessor, the
  other stacked above it to close the possessor slot.
* `Teop.outerGender`: the gender of a nominal, read off its highest n.
* `Teop.articles`: the article vocabulary, the paper's (32).
* `Teop.ipossessedDenot`, `Teop.freeDenot`: the two nominalizers'
  denotations, Barker's relationalizer and its possessor-closing inverse.
* `Jarawara.impoverish`, `Jarawara.decl`, `Jarawara.mano`: gender
  impoverishment feeding the declarative agreement marker and the possessed
  noun *mano* ~ *mani*.
* `possesseeGender`: the two ways a possessor can fix a possessee's gender.

## Main results

* `Teop.article_eq_articleForm`: the Subset Principle over (32) yields the
  Fragment's article paradigm, including the cross-identity of singular
  gender I with plural gender II.
* `Teop.switch`: one body-part root is gender I under the possessor-licensing
  nominalizer and gender II under the alienator; `Teop.freeDenot_iff` is the
  semantic side of the same switch.
* `Jarawara.mano_eq_manoForm`: impoverishment followed by insertion derives
  the possessed-noun paradigm of Table 6.
* `Italian.aPlural_changes_gender`: number on n changes gender; number on
  Num does not.

## Implementation notes

A nominal is a stack of heads, innermost first, and its gender is that of
the highest n — the paper's rule for stacked nominalizers. Jarawara's
features `[masc]`, `[pl]`, `[participant]` are privative, as in the paper;
the secondary feature `[marked]` of (A7) is rendered as one Vocabulary Item
per marked feature.
-/

namespace Adamson2024

open DistributedMorphology
open DistributedMorphology.Categorizer (Head)

/-! ### The Gender Locality Hypothesis -/

/-- The asymmetry of (16): an inalienable possessor can bear on gender, an
alienable one cannot. -/
theorem possession_asymmetry :
    PossessionType.inalienable.canAffectGender = true ∧
      PossessionType.alienable.canAffectGender = false := by
  decide

/-- What fixes a possessee's gender under each mechanism of §2.3: its own
nominalizer (possessee gender, Teop and Jarawara) or its iPossessor's gender
(inherited gender, Yanyuwa and Coastal Marind, the probe of (90)). -/
def possesseeGender {G : Type*} : PossessionGenderMechanism → G → G → G
  | .possesseeGender, own, _ => own
  | .inheritedGender, _, possessor => possessor

/-- Under inherited gender the possessee matches its possessor (fn. 8). -/
theorem inheritedGender_eq_possessor {G : Type*} (own possessor : G) :
    possesseeGender .inheritedGender own possessor = possessor := rfl

/-! ### Teop: possessee gender (§3.1) -/

namespace Teop

open _root_.Teop (ArticleCtx articleForm)

/-- The nominalizer of a body-part or kinship root: it introduces the
relation and bears u[animate], with or without the selectional feature {D}
that licenses an iPossessor ((36), (43)). -/
def relationalN (selectsD : Bool) : Head where
  categorizer := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }
  selectsD := selectsD

/-- The alienator, a further n of gender II that closes the possessor slot
((43)). -/
def alienatorN : Head := Head.n_plain

/-- A head bears the gender I feature [animate] ((24)). -/
def Animate (h : Head) : Prop := h.phi.gender.map (·.val.dim) = some .anim

instance : DecidablePred Animate :=
  fun h => inferInstanceAs (Decidable (h.phi.gender.map (·.val.dim) = some .anim))

/-- The gender of a nominal, read off its highest n: gender II is the absence
of [animate]. -/
def outerGender (stack : List Head) : _root_.Teop.Gender :=
  match stack.getLast? with
  | some h => if Animate h then .gI else .gII
  | none => .gII

/-- The iPossessed body-part noun: the root under the {D} nominalizer ((36)). -/
def ipossessed : List Head := [relationalN true]

/-- The free (or aPossessed, or compounded) body-part noun: the {D}-less
nominalizer under the alienator ((43), (44)–(47)). -/
def free : List Head := [relationalN false, alienatorN]

/-- The gender switch of (39)–(40): *a bina-naa* 'my spleen' is gender I,
*o bina* 'the spleen' gender II. -/
theorem switch : outerGender ipossessed = .gI ∧ outerGender free = .gII := by decide

/-- The article vocabulary (32), features percolated to D by concord:
`[animate]` is gender I, `[proper]` the proprial class. -/
inductive ArticleFeature where
  | animate | pl | proper
  deriving DecidableEq, Repr

/-- The items of (32), in the paper's order. -/
def articles : List (VocabularyItem ArticleFeature String) :=
  [⟨[.animate, .pl], "o"⟩, ⟨[.pl], "a"⟩, ⟨[.animate, .proper], "e"⟩, ⟨[.animate], "a"⟩,
    ⟨[], "o"⟩]

/-- The article's bundle for a Fragment `ArticleCtx`. -/
def articleFeatures (c : ArticleCtx) : List ArticleFeature :=
  (if c.gender = .gI then [.animate] else []) ++ (if c.plural then [.pl] else []) ++
    (if c.proprial then [.proper] else [])

/-- The article the Subset Principle inserts. -/
def article (c : ArticleCtx) : Option String := subsetPrinciple articles (articleFeatures c)

/-- (32) derives the Fragment's paradigm, including the cross-identities of
(25)–(26) and the neutralization of the proprial article in the plural
(29). -/
theorem article_eq_articleForm (c : ArticleCtx) : article c = some (articleForm c) := by
  rcases c with ⟨g, p, q⟩; cases g <;> cases p <;> cases q <;> decide

/-- The cross-identity: i.sg and ii.pl share *a*, i.pl and ii.sg share *o*. -/
theorem cross_identity :
    article ⟨.gI, false, false⟩ = article ⟨.gII, true, false⟩ ∧
      article ⟨.gI, true, false⟩ = article ⟨.gII, false, false⟩ := by
  decide

/-- The body-part noun's article follows its nominalizer: *a* iPossessed, *o*
free ((39)). -/
theorem bodyPart_article :
    article ⟨outerGender ipossessed, false, false⟩ = some "a" ∧
      article ⟨outerGender free, false, false⟩ = some "o" := by
  decide

/-- The iPossessor's own gender is immaterial ((48)–(49)): possessee gender
reads the nominalizer, not the possessor. -/
theorem possessor_gender_immaterial (possessor : _root_.Teop.Gender) :
    possesseeGender .possesseeGender (outerGender ipossessed) possessor = .gI := rfl

/-- Kinship roots take the proprial article when iPossessed ((41), (50)) and
switch to gender II under the alienator *-na* ((51)). -/
theorem kinship :
    article ⟨outerGender ipossessed, false, true⟩ = some "e" ∧
      article ⟨outerGender free, false, false⟩ = some "o" := by
  decide

/-! #### The denotations of (36) and (43) -/

section Denotation

open ArgumentStructure.Relational

variable {E S : Type*} (isSpleen : E → S → Prop) (bodyPartOf : E → E → S → Prop)

/-- The iPossessed body-part noun ((36)): the root relationalized by the
body-part-of relation — Barker's π, possessor first — awaiting its possessor. -/
def ipossessedDenot : E → E → S → Prop := π isSpleen bodyPartOf

/-- The free body-part noun ((43)): the alienator closes the possessor slot. -/
def freeDenot : E → S → Prop := ExPossessor (π isSpleen bodyPartOf)

/-- One root, two types: the possessor slot is open under the {D} nominalizer
and existentially closed under the alienator. -/
theorem freeDenot_iff (y : E) (s : S) :
    freeDenot isSpleen bodyPartOf y s ↔ isSpleen y s ∧ ∃ x, bodyPartOf x y s :=
  exPossessor_pi ..

end Denotation

end Teop

/-! ### Jarawara: possessee gender and agreement (§3.2) -/

namespace Jarawara

open _root_.Jarawara (Possessor PossessedForm manoForm)

/-- The privative φ-features of §3.2: `[masc]` ((58)), `[pl]`, and
`[participant]` for first and second person. -/
inductive Phi where
  | masc | pl | participant
  deriving DecidableEq, Repr

/-- The features a possessor contributes to agreement. -/
def possessorPhi (p : Possessor) : List Phi :=
  (if p.isParticipant then [.participant] else []) ++ (if p.number = .Plur then [.pl] else []) ++
    (if p.gender = some .masc then [.masc] else [])

/-- Gender impoverishment (63): `[masc]` is deleted next to `[pl]` and next to
`[participant]`, two paradigmatic rules on the shared engine. -/
def impoverishment : List (ImpoverishmentRule (List Phi) Phi) :=
  [.paradigmatic (·.contains .pl) .masc, .paradigmatic (·.contains .participant) .masc]

/-- The φ-bundle after (63). -/
def impoverish (φ : List Phi) : List Phi :=
  runChain (ImpoverishmentRule.apply List.erase) impoverishment (Neighborhood.ofBundle φ)

/-- The declarative marker's items (59): `decl[masc] ↔ ka`, `decl ↔ ke`. -/
def declarative : List (VocabularyItem Phi String) := [⟨[.masc], "ka"⟩, ⟨[], "ke"⟩]

/-- The declarative marker agreeing with a nominal of features `φ`. -/
def decl (φ : List Phi) : Option String := subsetPrinciple declarative (impoverish φ)

/-- Masculine singular takes *ka*, everything else *ke* ((54), (60)–(62)):
impoverishment bleeds the specific exponent. -/
theorem decl_masc_only :
    decl [.masc] = some "ka" ∧ decl [] = some "ke" ∧ decl [.participant] = some "ke" ∧
      decl [.masc, .pl] = some "ke" := by
  decide

/-- The possessed noun *mano* 'arm' (A7): *mano* for a marked feature —
`[participant]` or a surviving `[masc]` — and *mani* elsewhere. -/
def manV : List (VocabularyItem Phi String) :=
  [⟨[.participant], "mano"⟩, ⟨[.masc], "mano"⟩, ⟨[], "mani"⟩]

/-- The form of *mano* agreeing with possessor `p`. -/
def mano (p : Possessor) : Option String := subsetPrinciple manV (impoverish (possessorPhi p))

/-- The cells of Table 6. -/
def tableSix : List Possessor :=
  [⟨.first, .Sing, none⟩, ⟨.second, .Sing, none⟩, ⟨.first, .Plur, none⟩, ⟨.second, .Plur, none⟩,
    ⟨.third, .Sing, some .masc⟩, ⟨.third, .Sing, some .fem⟩, ⟨.third, .Plur, some .masc⟩,
    ⟨.third, .Plur, some .fem⟩]

/-- Impoverishment then insertion derives the Fragment's paradigm of Table 6:
the 3.m.pl *mani* is the one cell where (63) does the work. -/
theorem mano_eq_manoForm :
    ∀ p ∈ tableSix,
      mano p = some (match manoForm p with | .mascForm => "mano" | .femForm => "mani") := by
  decide

end Jarawara

/-! ### Number on n (§5.1) -/

namespace Italian

open _root_.Italian.NumberGender

/-- The *-a* plurals of (99) carry number on n, within the GLH's reach, and
change gender; regular plurals carry number on Num and do not. -/
theorem aPlural_changes_gender :
    (∀ n ∈ aPluralNouns, n.pluralClass.canAffectGender = true ∧ n.genderChanges = true) ∧
      ∀ n ∈ regularNouns, n.pluralClass.canAffectGender = false ∧ n.genderChanges = false := by
  decide

end Italian

end Adamson2024
