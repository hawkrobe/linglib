import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Linglib.Syntax.Agreement.Target
import Linglib.Features.Number.Basic
import Linglib.Fragments.Tamil.Gender
import Linglib.Fragments.Swahili.Nouns
import Linglib.Fragments.Afar.Gender
import Linglib.Fragments.Romanian.Gender
import Linglib.Fragments.Slavic.Russian.Gender
import Linglib.Fragments.Hausa.Gender
import Linglib.Data.Examples.Corbett1991

/-!
# Corbett's typology of gender

Gender is a property of nouns shown only in agreement, and a language's genders are the
classes of nouns that take the same agreements. Nouns are assigned to them by rules reading
their meaning or their form: semantic rules on the core of sex-differentiable or animate
nouns take precedence, formal rules, morphological or phonological, sort the semantic
residue, and no system is formal alone. Counting the genders starts from agreement classes,
the sets of nouns taking identical agreements in every form on every target, distinguishes
the controller genders into which nouns fall from the target genders marked on agreeing
elements, and reads Greenberg's universal that the plural never distinguishes more genders
than the singular off the map between the two numbers' target genders: parallel, convergent
or crossed. Nouns whose meaning and form conflict may be hybrid, taking semantic agreement on
some targets and syntactic agreement on others, and the Agreement Hierarchy, attributive
before predicate before relative pronoun before personal pronoun, orders the targets so that
the likelihood of semantic agreement never decreases along it. Conjoined controllers are
resolved by ordered rules of two shapes, one conjunct of a kind or all conjuncts of a kind,
reading the conjuncts' meaning, their gender, or both, a language's resolution never less
semantic than its assignment. The judgments the book reports are the rows of
`Data/Examples/Corbett1991.json`.

## Implementation notes

* An assignment system is typed by the meaning `σ` its semantic rules read and the form `φ`
  its formal rules read; the rules are total functions to an optional gender, ordered by
  construction so that precedence of the semantic rules is a theorem, and the residue gender
  catches what neither covers. Tamil, Russian, Swahili, Afar and Hausa instantiate it on
  their fragments, whose natural-gender flag stands in for the referent's sex. Corbett's
  irregular third declension of Russian is the study's refinement of the fragment's
  declension classes.
* Agreement classes are the kernel of the noun-level agreement map, and target genders the
  ranges of its restrictions to one target; the map between the singular and plural target
  genders is `Function.FactorsThrough`. Subgenders, inquorate genders and consistent
  agreement patterns are described in the book's prose and not formalised.
* The Agreement Hierarchy is the partial order on `Agreement.Target`, attributive at the
  top; a hybrid noun's profile assigns each position one of five availabilities of semantic
  agreement, the categories of the book's summary table, and respects the hierarchy when
  availability is antitone on the positions where it is defined.
* Resolution rules apply to a list of conjunct descriptors and return no form when no rule
  applies, the book's ineffable coordinations; the descriptors are genders, semantic
  features, or fragment nouns as each language requires. Optional rules are recorded as
  rows. The gender carriers of French, German, Lak, Slovene, Icelandic, Latin and Ojibwa
  are declared in the study, there being no fragments for them.
* Not modelled: the psycholinguistic evidence of chapter 4, the morphology of agreement and
  its limits in chapter 5, syncretism and neutral agreement in chapter 7, the diachrony of
  chapters 8 to 10, Russian acronyms and indeclinables, Chichewa's target-gender rule for
  plural conjuncts, the Polish optional resolution rules, and the case and distance effects
  within a position of the hierarchy (§8.1.2), which are rows only.

## TODO

* Subgenders as minimally different agreement classes, and consistent agreement patterns,
  want the full paradigm tables of the book's chapter 6 in the Russian fragment.
* The corpus-level reading of the hierarchy, proportions of semantic agreement per target,
  is recorded for *vrač* only.
* Attributive possessives are a finer division of the hierarchy (§8.3: Swahili *rafiki*,
  Kami), which `Agreement.Target` lacks; those examples are rows without a profile.
* The generalization of §9.8, that resolution is never less semantic than assignment, wants
  resolution rules tagged by what they read, meaning or gender.

## References

* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett, *The agreement hierarchy* (1979)][corbett-1979]
* [G. G. Corbett, *Hierarchies, Targets and Controllers* (1983)][corbett-1983]
* [A. A. Zaliznjak, *K voprosu o grammatičeskix kategorijax roda i oduševlennosti*
  (1964)][zaliznjak-1964]
* [J. H. Greenberg, *Some universals of grammar* (1963)][greenberg-1963]
* [C. F. Hockett, *A Course in Modern Linguistics* (1958)][hockett-1958]
* [B. Heine, *African noun class systems* (1982)][heine-1982]
* [T. Givón, *The resolution of gender conflicts in Bantu conjunction* (1970)][givon-1970]
* [R. M. W. Dixon, *The Dyirbal Language of North Queensland* (1972)][dixon-1972]
* [G. R. Tucker, W. E. Lambert, A. A. Rigault, *The French Speaker's Skill with Grammatical
  Gender* (1977)][tucker-lambert-rigault-1977]
-/

namespace Corbett1991

open Agreement

/-! ### Assignment systems -/

/-- A semantic opposition on which gender assignment can rest (§2.3): de la Grasserie's
types and the criteria the book adds. Sex is one opposition here, though the book separates
systems singling out females (Diyari, Dizi) from those singling out males (Kala Lagaw Ya). -/
inductive Criterion where
  | animacy
  | rationality
  | humanness
  | sex
  | strength
  | size
  | evaluation
  | insect
  | edibility
  | liquidity
  | abstractness
  | canine
  | huntingWeapon
  | lustre
  deriving DecidableEq, Repr, Fintype

/-- An assignment system: semantic rules reading a noun's meaning, formal rules reading its
form, and the residue gender. -/
structure AssignmentSystem (σ φ G : Type*) where
  /-- The semantic rules, as a partial function of the meaning. -/
  semantic : σ → Option G
  /-- The formal rules, morphological or phonological, as a partial function of the form. -/
  formal : φ → Option G
  /-- The gender of nouns no rule covers. -/
  residue : G

namespace AssignmentSystem

variable {N σ φ G : Type*} (A : AssignmentSystem σ φ G) (sem : N → σ) (form : N → φ)

/-- The gender of a noun: the semantic rules first, the formal rules on the semantic residue,
the residue gender last. -/
def assign (n : N) : G := ((A.semantic (sem n)).or (A.formal (form n))).getD A.residue

theorem assign_of_semantic {n : N} {g : G} (h : A.semantic (sem n) = some g) :
    A.assign sem form n = g := by
  simp [assign, h]

/-- Semantic rules take precedence: a formal rule decides only in the semantic residue. -/
theorem assign_of_formal {n : N} {g : G} (h₁ : A.semantic (sem n) = none)
    (h₂ : A.formal (form n) = some g) : A.assign sem form n = g := by
  simp [assign, h₁, h₂]

theorem assign_of_residue {n : N} (h₁ : A.semantic (sem n) = none)
    (h₂ : A.formal (form n) = none) : A.assign sem form n = A.residue := by
  simp [assign, h₁, h₂]

/-- A strict semantic system has no formal rules. -/
def IsStrictSemantic : Prop := ∀ x, A.formal x = none

/-- In a strict semantic system the gender is a function of the meaning. -/
theorem factorsThrough_of_isStrictSemantic (h : A.IsStrictSemantic) :
    Function.FactorsThrough (A.assign sem form) sem := λ a b hab => by
  simp [assign, hab, h (form a), h (form b)]

/-- Every system assigns by meaning on the nouns its semantic rules cover: the substrate's
semantic core, once one such noun exists. -/
theorem semanticCore_of_isSome (S : Gender.System G) {n₀ : N} (h : (A.semantic (sem n₀)).isSome) :
    ({ S with assign := A.assign sem form } : Gender.System.Assigned N G).SemanticCore
      {n | (A.semantic (sem n)).isSome} sem :=
  ⟨⟨n₀, h⟩, λ _ b _ hb hab => by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hb
    simp [assign, hab, hg]⟩

end AssignmentSystem

/-- The book's typology of assignment systems. -/
inductive AssignmentKind where
  | strictSemantic
  | predominantlySemantic
  | morphological
  | phonological
  deriving DecidableEq, Repr, Fintype

/-- A language of chapters 2 and 3 with the kind of its assignment system and the semantic
criteria its rules use, as this study reads the book's tables; the book draws up no such
list itself. -/
structure SurveyEntry where
  /-- The language, under the book's name. -/
  language : String
  glottocode : String
  /-- The kind of assignment system the book describes. -/
  kind : AssignmentKind
  /-- The semantic criteria the book's rules for the language use. -/
  criteria : List Criterion
  deriving DecidableEq, Repr

/-- The assignment systems of chapters 2 and 3 (Tables 2.1 to 2.8 and §3.1 to §3.2). -/
def survey : List SurveyEntry :=
  [⟨"Tamil", "tami1289", .strictSemantic, [.rationality, .sex]⟩,
    ⟨"Diyari", "dier1241", .strictSemantic, [.sex]⟩,
    ⟨"Dizi", "dizi1235", .strictSemantic, [.sex, .evaluation]⟩,
    ⟨"Halkomelem", "halk1245", .strictSemantic, [.sex, .evaluation]⟩,
    ⟨"Defaka", "defa1248", .strictSemantic, [.humanness, .sex]⟩,
    ⟨"English", "stan1293", .strictSemantic, [.humanness, .sex]⟩,
    ⟨"Zande", "zand1248", .predominantlySemantic, [.humanness, .sex, .animacy]⟩,
    ⟨"Dyirbal", "dyir1250", .predominantlySemantic, [.humanness, .sex, .animacy, .edibility]⟩,
    ⟨"Ket", "kett1243", .predominantlySemantic, [.animacy, .sex]⟩,
    ⟨"Ojibwa", "ojib1241", .predominantlySemantic, [.animacy]⟩,
    ⟨"Lak", "lakk1252", .predominantlySemantic, [.rationality, .sex, .animacy]⟩,
    ⟨"Archi", "arch1244", .predominantlySemantic,
      [.rationality, .sex, .animacy, .size, .abstractness, .insect]⟩,
    ⟨"Russian", "russ1263", .morphological, [.sex, .animacy]⟩,
    ⟨"Swahili", "swah1253", .morphological, [.animacy, .evaluation]⟩,
    ⟨"Afar", "afar1241", .phonological, [.sex]⟩,
    ⟨"Hausa", "haus1257", .phonological, [.sex]⟩,
    ⟨"Godié", "godi1239", .phonological, [.humanness, .size, .liquidity]⟩,
    ⟨"Yimas", "yima1243", .phonological, [.sex, .humanness, .animacy]⟩,
    ⟨"French", "stan1290", .phonological, [.sex]⟩]

/-! ### Tamil: a strict semantic system (§2.1.1) -/

namespace Tamil

open _root_.Tamil.Gender

/-- What the rules read: rationality, and the natural gender of a sex-differentiable noun. -/
def sem (n : Noun) : Bool × Option Value :=
  (n.rational, if n.isNaturalGender then some n.gender else none)

/-- Table 2.1: male rationals masculine, female rationals feminine, the residue neuter. -/
def system : AssignmentSystem (Bool × Option Value) Unit Value where
  semantic
    | (true, some .masc) => some .masc
    | (true, some .fem) => some .fem
    | _ => none
  formal _ := none
  residue := .neut

theorem isStrictSemantic_system : system.IsStrictSemantic := λ _ => rfl

/-- The rules assign every noun of the fragment its gender. -/
theorem assign_eq_gender : ∀ n ∈ allNouns, system.assign sem (λ _ => ()) n = n.gender := by
  decide

end Tamil

/-! ### Russian: a morphological system (§3.1.1) -/

namespace Russian

open _root_.Russian.Gender

/-- The declensional types of Figure 3.1: the four paradigms and the irregular third. -/
inductive Declension where
  | I
  | II
  | III
  | IV
  | irregularIII
  deriving DecidableEq, Repr, Fintype

/-- The fragment's declension classes under Corbett's typing: *znamja* and *put'* are of the
irregular third declension. -/
def declension (n : RussianNoun) : Option Declension :=
  if n = znamja ∨ n = put' then some .irregularIII else
    n.declClass.map λ
      | .I => .I
      | .II => .II
      | .III => .III
      | .IV => .IV

/-- The natural gender of a sex-differentiable noun. -/
def sem (n : RussianNoun) : Option Value :=
  if n.isNaturalGender then some n.controllerGender else none

/-- The rules of §3.1.1 for declinable nouns: males masculine and females feminine; then
declension I masculine, declensions II and III feminine, the rest neuter. The rules for
acronyms and indeclinables (Figure 3.4) are not modelled. -/
def system : AssignmentSystem (Option Value) (Option Declension) Value where
  semantic := id
  formal
    | some .I => some .masc
    | some .II | some .III => some .fem
    | _ => none
  residue := .neut

/-- The rules assign every noun of the fragment its gender, *put'* excepted, which the book
leaves as an isolated exception with an irregular lexical marker. -/
theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ≠ put' → system.assign sem declension n = n.controllerGender := by
  decide

/-- *djadja* 'uncle': the morphological rule would make it feminine, the semantic rule makes
it masculine, and the semantic rule takes precedence. -/
theorem djadja_precedence :
    system.formal (declension djadja) = some .fem ∧
      system.assign sem declension djadja = .masc := by
  decide

/-- *vrač* 'doctor' as a lexeme is not sex-differentiable, so the declension decides; the
conflict when it denotes a woman is the hybrid pattern of §8.1. -/
theorem vrac_by_declension : system.assign sem declension vrač = .masc := by decide

end Russian

/-! ### Swahili: morphological classes and animate concord (§3.1.2) -/

namespace Swahili

open _root_.Swahili

/-- What the semantic rules read: evaluative derivation and animacy. -/
def sem (n : Noun) : Option Evaluative × Bool := (n.evaluative, n.animate)

/-- The rules of §3.1.2: augmentatives to 5/6, diminutives to 7/8, remaining animates to
1/2; then each morphological class to its own gender, over the fragment's five genders (the
book's 11/10 and 15 are not among them). The residue gender is never reached. -/
def system :
    AssignmentSystem (Option Evaluative × Bool) _root_.Swahili.Gender _root_.Swahili.Gender where
  semantic
    | (some .augmentative, _) => some .genderC
    | (some .diminutive, _) => some .genderD
    | (none, true) => some .genderA
    | (none, false) => none
  formal := some
  residue := .genderE

/-- The rules assign every noun of the fragment its gender. -/
theorem assign_eq_gender : ∀ n ∈ allNouns, system.assign sem Noun.morphClass n = n.gender := by
  decide

/-- Gender 1/2 is a purely semantic gender: every noun assigned to it is assigned by a
semantic rule. -/
theorem genderA_semantic :
    ∀ n ∈ allNouns, system.assign sem Noun.morphClass n = .genderA →
      (system.semantic (sem n)).isSome := by
  decide

end Swahili

/-! ### Afar and Hausa: phonological systems (§3.2.1, §3.2.2) -/

namespace Afar

open _root_.Afar.Gender

/-- The natural gender of a sex-differentiable noun. -/
def sem (n : Noun) : Option Value := if n.isNaturalGender then some n.gender else none

/-- Sex first; then a citation form ending in an accented vowel is feminine, the rest
masculine. -/
def system : AssignmentSystem (Option Value) Bool Value where
  semantic := id
  formal acc := if acc then some .fem else none
  residue := .masc

/-- The rules assign every noun of the fragment its gender, the isolated exception *doònik*
'sail-boat' apart. -/
theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ≠ doonik → system.assign sem Noun.finalAccentedVowel n = n.gender := by
  decide

/-- *abbà* 'father' ends in an accented vowel yet is masculine: the semantic rule takes
precedence over the phonological one. -/
theorem abba_precedence :
    system.formal abba.finalAccentedVowel = some .fem ∧
      system.assign sem Noun.finalAccentedVowel abba = .masc := by
  decide

end Afar

namespace Hausa

open _root_.Hausa

/-- The natural gender of a sex-differentiable noun. -/
def sem (n : Noun) : Option Gender := if n.isNaturalGender then some n.gender else none

/-- Sex first; then a noun in *-ā* is feminine, the rest masculine. -/
def system : AssignmentSystem (Option Gender) Bool Gender where
  semantic := id
  formal aa := if aa then some .feminine else none
  residue := .masculine

/-- The rules assign every noun of the fragment its gender apart from *gidā* 'house' and
*kadā̀* 'crocodile', two of the *-ā* masculines of [newman-2000] that the fragment carries:
the book says only that the phonological rule has exceptions. -/
theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ∉ [gida, kada] →
      system.assign sem (λ n => decide n.EndsInAa) n = n.gender := by
  decide

end Hausa

/-! ### Agreement classes, controller genders and target genders (chapter 6) -/

section AgreementClasses

variable {N T F : Type*}

/-- Zaliznjak's agreement classes: two nouns are in one class when they take the same form
on every target in every morphosyntactic form. -/
abbrev agreementClasses (agr : N → T → F) : Setoid N := Setoid.ker agr

/-- The controller genders are the agreement classes: as many as the agreement map has
values. -/
theorem card_quotient_agreementClasses (agr : N → T → F) :
    Nat.card (Quotient (agreementClasses agr)) = Nat.card (Set.range agr) :=
  Nat.card_congr (Setoid.quotientKerEquivRange agr)

/-- The target genders of a target: the forms it shows. -/
abbrev targetGenders (agr : N → T → F) (t : T) : Set F := Set.range (agr · t)

/-- The controller genders are at most the product of the target genders over the targets:
Romanian's three controller genders over two target genders in each number. -/
theorem card_range_le_prod [Finite N] [Fintype T] (agr : N → T → F) :
    Nat.card (Set.range agr) ≤ ∏ t, Nat.card (targetGenders agr t) := by
  rw [← Nat.card_pi]
  exact Nat.card_le_card_of_injective (λ f t => ⟨f.1 t, f.2.imp λ n hn => congrFun hn t⟩)
    λ f g h => Subtype.ext (funext λ t => congrArg Subtype.val (congrFun h t))

variable {F' : Type*}

/-- The map between the target genders of two numbers (§6.3.1): parallel when each determines
the other. -/
def Parallel (sg : N → F) (pl : N → F') : Prop :=
  Function.FactorsThrough pl sg ∧ Function.FactorsThrough sg pl

/-- Convergent when the singular determines the plural but not conversely. -/
def Convergent (sg : N → F) (pl : N → F') : Prop :=
  Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl

/-- Crossed when neither determines the other. -/
def Crossed (sg : N → F) (pl : N → F') : Prop :=
  ¬ Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl

variable [Fintype N] [DecidableEq F] [DecidableEq F'] (sg : N → F) (pl : N → F')

instance : Decidable (Parallel sg pl) := by
  unfold Parallel Function.FactorsThrough; infer_instance

instance : Decidable (Convergent sg pl) := by
  unfold Convergent Function.FactorsThrough; infer_instance

instance : Decidable (Crossed sg pl) := by
  unfold Crossed Function.FactorsThrough; infer_instance

end AgreementClasses

namespace Romanian

open _root_.Romanian.Gender

/-- Figure 6.1: a crossed system. -/
theorem crossed : Crossed (Value.adjForm · false) (Value.adjForm · true) := by decide

/-- Three controller genders over two target genders in each number. -/
theorem card_range_adjForm :
    Fintype.card (Set.range Value.adjForm) = 3 ∧
      Fintype.card (targetGenders Value.adjForm false) = 2 ∧
        Fintype.card (targetGenders Value.adjForm true) = 2 := by
  decide

/-- Every fragment noun takes, in each number, the form of its gender: (5) to (10). -/
theorem rows : ∀ row ∈ Examples.all, row.language = "roma1327" →
    ∀ n ∈ row.parse? "noun" (allNouns.map λ n => (n.form, n)),
      ∀ pl ∈ row.parse? "number" [("singular", false), ("plural", true)],
        ∀ f ∈ row.parse? "form" [("zero", AdjForm.zero), ("ă", .ă), ("i", .i), ("e", .e)],
          (row.judgment = .acceptable ↔ n.gender.adjForm pl = f) := by
  decide +kernel

end Romanian

namespace French

/-- The two genders, with one form each in both numbers: Figure 6.6. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

theorem parallel : Parallel (id : Value → Value) id := by decide

end French

namespace German

/-- The three genders and the definite article, three forms in the singular, one in the
plural: Figure 6.7. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- The definite article. -/
inductive Article where
  | der
  | die
  | das
  deriving DecidableEq, Repr, Fintype

/-- The singular article of each gender. -/
def Value.sgArticle : Value → Article
  | .masc => .der
  | .fem => .die
  | .neut => .das

/-- The plural article, one form for all three. -/
def Value.plArticle : Value → Article := λ _ => .die

theorem convergent : Convergent Value.sgArticle Value.plArticle := by decide

end German

namespace Lak

/-- The four genders of Lak and the three sets of verbal agreement markers of Figure 6.5. -/
inductive Value where
  | I
  | II
  | III
  | IV
  deriving DecidableEq, Repr, Fintype

/-- The three sets of forms: prefixal `Ø`/`b`/`d`, internal or suffixal `w`/`w`/`r`. -/
inductive Marker where
  | zeroW
  | bW
  | dR
  deriving DecidableEq, Repr, Fintype

/-- The singular marker of each gender. -/
def Value.sgMarker : Value → Marker
  | .I => .zeroW
  | .II => .dR
  | .III => .bW
  | .IV => .dR

/-- The plural marker of each gender. -/
def Value.plMarker : Value → Marker
  | .I | .II | .III => .bW
  | .IV => .dR

/-- Figure 6.10: a crossed system, three target genders in the singular and two in the
plural. -/
theorem crossed : Crossed Value.sgMarker Value.plMarker := by decide

/-- Universal 37 holds though neither number determines the other. -/
theorem card_plMarker_le :
    Fintype.card (Set.range Value.plMarker) ≤ Fintype.card (Set.range Value.sgMarker) := by
  decide

end Lak

namespace Slovene

/-- The three genders and the endings of an agreeing predicate in the three numbers (Table
9.5): parallel between singular and plural, convergent with the dual, where feminine and
neuter share a form (Figure 6.11). -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- The endings of the past active participle. -/
inductive Ending where
  | zero
  | a
  | o
  | i
  | e
  deriving DecidableEq, Repr, Fintype

/-- The singular ending of each gender. -/
def Value.sgEnding : Value → Ending
  | .masc => .zero
  | .fem => .a
  | .neut => .o

/-- The dual ending of each gender. -/
def Value.duEnding : Value → Ending
  | .masc => .a
  | .fem | .neut => .i

/-- The plural ending of each gender. -/
def Value.plEnding : Value → Ending
  | .masc => .i
  | .fem => .e
  | .neut => .a

theorem parallel_sg_pl : Parallel Value.sgEnding Value.plEnding := by decide

theorem convergent_sg_du : Convergent Value.sgEnding Value.duEnding := by decide

theorem convergent_pl_du : Convergent Value.plEnding Value.duEnding := by decide

end Slovene

namespace Tamil

open _root_.Tamil.Gender

/-- Figure 6.8: three singular target genders converge on two in the plural. -/
theorem convergent : Convergent Value.sgConcord Value.plConcord := by decide

/-- Greenberg's Universal 37 in Tamil as a corollary of convergence: a number whose target
genders are determined by another's distinguishes no more of them. The book states the
universal over target genders because it holds of crossed systems too, Lak above. -/
theorem card_plConcord_le :
    Nat.card (Set.range Value.plConcord) ≤ Nat.card (Set.range Value.sgConcord) :=
  convergent.1.card_range_le

end Tamil

/-! ### Hybrid nouns and the Agreement Hierarchy (chapter 8) -/

/-- Whether an agreement form follows the semantic or the formal assignment rules. -/
inductive AgreementKind where
  | syntactic
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- The availability of semantic agreement at a target, the five categories of Table 8.1,
ordered by the likelihood of semantic agreement. -/
inductive Availability where
  | syntacticOnly
  | mostlySyntactic
  | both
  | mostlySemantic
  | semanticOnly
  deriving DecidableEq, Repr, Fintype

namespace Availability

/-- The position of an availability in the order of likelihood of semantic agreement. -/
def toNat : Availability → ℕ
  | .syntacticOnly => 0
  | .mostlySyntactic => 1
  | .both => 2
  | .mostlySemantic => 3
  | .semanticOnly => 4

theorem toNat_injective : Function.Injective toNat := by decide

instance : LinearOrder Availability := LinearOrder.lift' toNat toNat_injective

/-- Which agreement an availability admits. -/
def Allows : Availability → AgreementKind → Prop
  | .syntacticOnly, k => k = .syntactic
  | .semanticOnly, k => k = .semantic
  | _, _ => True

instance (a : Availability) (k : AgreementKind) : Decidable (a.Allows k) := by
  cases a <;> simp only [Allows] <;> infer_instance

end Availability

/-- A hybrid noun: for each position of the hierarchy where gender agreement applies, the
availability of semantic agreement. -/
structure Hybrid where
  /-- The noun or class of nouns, as the rows name it. -/
  name : String
  /-- The availability of semantic agreement at each position where gender agreement applies
  and the book has data. -/
  profile : Target → Option Availability

/-- The Agreement Hierarchy: moving rightwards, towards the personal pronoun, the likelihood
of semantic agreement never decreases. Positions where gender agreement does not apply, or
for which the book has no data, carry no availability and are skipped. -/
def Hybrid.RespectsHierarchy (h : Hybrid) : Prop :=
  ∀ t u : Target, t ≤ u → ∀ a ∈ h.profile t, ∀ b ∈ h.profile u, b ≤ a

instance (h : Hybrid) : Decidable h.RespectsHierarchy := by
  unfold Hybrid.RespectsHierarchy; infer_instance

/-- Table 8.1, with the English boat nouns of §6.4.5 and the Bantu hybrids of §8.3. -/
def frenchTitles : Hybrid := ⟨"frenchTitles", λ
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic
  | .verb => none⟩

def madchen : Hybrid := ⟨"mädchen", λ
  | .attributive | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | .predicate | .verb => none⟩

def lajdaki : Hybrid := ⟨"łajdaki", λ
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .semanticOnly
  | .verb => none⟩

def spanishTitles : Hybrid := ⟨"spanishTitles", λ
  | .attributive => some .syntacticOnly
  | .predicate | .relativePronoun | .personalPronoun => some .semanticOnly
  | .verb => none⟩

def konkani : Hybrid := ⟨"konkani", λ
  | .attributive => some .syntacticOnly
  | .predicate | .personalPronoun => some .semanticOnly
  | .relativePronoun | .verb => none⟩

def vrac : Hybrid := ⟨"vrač", λ
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun | .personalPronoun => some .mostlySemantic
  | .verb => none⟩

def gazde : Hybrid := ⟨"gazde", λ
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun => some .mostlySemantic
  | .personalPronoun => some .semanticOnly
  | .verb => none⟩

def boat : Hybrid := ⟨"boat", λ
  | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | _ => none⟩

/-- *kamwana*: gender 12/13 forms normally, gender 1/2 also possible for a personal pronoun
sufficiently removed from the controller. -/
def kamwana : Hybrid := ⟨"kamwana", λ
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic
  | .verb => none⟩

def kilumba : Hybrid := ⟨"kilumba", λ
  | .attributive => some .syntacticOnly
  | .predicate => some .both
  | _ => none⟩

def hybrids : List Hybrid :=
  [frenchTitles, madchen, lajdaki, spanishTitles, konkani, vrac, gazde, boat, kamwana, kilumba]

/-- Every hybrid of Table 8.1 respects the Agreement Hierarchy. -/
theorem hybrids_respectHierarchy : ∀ h ∈ hybrids, h.RespectsHierarchy := by decide

/-- The corpus-level claim on *vrač*: Panov's respondents favouring feminine agreement, 16.9
per cent of 3,835 for the attributive and 51.7 per cent of 3,806 for the predicate. -/
def vracFeminine : Target → Option ℚ
  | .attributive => some (169 / 1000)
  | .predicate => some (517 / 1000)
  | _ => none

theorem vracFeminine_attributive_le_predicate :
    ∀ p ∈ vracFeminine .predicate, ∀ a ∈ vracFeminine .attributive, a ≤ p := by
  norm_num [vracFeminine]

/-- The stacked-target constraint of §8.1.2: when stacked or parallel targets of one
controller differ, the further one shows semantic agreement. -/
def StackedAllowed (near far : AgreementKind) : Prop := near = .semantic → far = .semantic

instance (near far : AgreementKind) : Decidable (StackedAllowed near far) := by
  unfold StackedAllowed; infer_instance

/-! ### The judgments of chapter 8

A row with a `hybrid`, a `target` and an `agreement` feature is a use of a hybrid noun at a
position of the hierarchy, acceptable exactly when the hybrid's availability there admits
the agreement; a row with `near` and `far` features is a pair of stacked targets. -/

/-- The hybrids by the names the rows use. -/
def hybridNames : List (String × Hybrid) := hybrids.map λ h => (h.name, h)

/-- The positions of the hierarchy by the names the rows use. -/
def targetNames : List (String × Target) :=
  [("attributive", .attributive), ("predicate", .predicate),
    ("relativePronoun", .relativePronoun), ("personalPronoun", .personalPronoun)]

/-- The two agreements by the names the rows use. -/
def kindNames : List (String × AgreementKind) :=
  [("syntactic", .syntactic), ("semantic", .semantic)]

theorem hybrid_rows : ∀ row ∈ Examples.all, ∀ h ∈ row.parse? "hybrid" hybridNames,
    ∀ t ∈ row.parse? "target" targetNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ h.profile t, a.Allows k) := by
  decide +kernel

theorem stacked_rows : ∀ row ∈ Examples.all, ∀ near ∈ row.parse? "near" kindNames,
    ∀ far ∈ row.parse? "far" kindNames, (row.judgment = .acceptable ↔ StackedAllowed near far) := by
  decide +kernel

/-! ### Gender resolution (chapter 9) -/

/-- The two shapes of a resolution rule (§9.4): at least one conjunct of a kind, or all. -/
inductive Quantifier where
  | any
  | all
  deriving DecidableEq, Repr, Fintype

/-- A resolution rule: a condition on conjuncts, quantified one way or the other, and the
form it selects. -/
structure Rule (α G : Type*) where
  /-- Whether one conjunct or every conjunct must meet the condition. -/
  quant : Quantifier
  /-- The condition on a conjunct. -/
  pred : α → Prop
  [dec : DecidablePred pred]
  /-- The form the rule selects. -/
  out : G

attribute [instance] Rule.dec

namespace Rule

variable {α G : Type*}

/-- Whether the rule applies to a coordination. -/
def Applies (r : Rule α G) (cs : List α) : Prop :=
  match r.quant with
  | .any => ∃ c ∈ cs, r.pred c
  | .all => ∀ c ∈ cs, r.pred c

instance (r : Rule α G) (cs : List α) : Decidable (r.Applies cs) := by
  unfold Applies; cases r.quant <;> infer_instance

/-- The final "otherwise" rule. -/
def otherwise (g : G) : Rule α G := ⟨.all, λ _ => True, g⟩

theorem otherwise_applies (g : G) (cs : List α) : (otherwise g).Applies cs := λ _ _ => trivial

end Rule

/-- Apply ordered rules: the first that applies selects the form; none applying, the
coordination has no resolved form. -/
def resolve {α G : Type*} : List (Rule α G) → List α → Option G
  | [], _ => none
  | r :: rs, cs => if r.Applies cs then some r.out else resolve rs cs

section Resolve

variable {α G : Type*} (r : Rule α G) (rs : List (Rule α G)) (cs : List α)

@[simp] theorem resolve_nil : resolve ([] : List (Rule α G)) cs = none := rfl

theorem resolve_cons_of_applies (h : r.Applies cs) : resolve (r :: rs) cs = some r.out := by
  simp [resolve, h]

theorem resolve_cons_of_not_applies (h : ¬ r.Applies cs) :
    resolve (r :: rs) cs = resolve rs cs := by
  simp [resolve, h]

/-- An "otherwise" rule guarantees a resolved form. -/
theorem resolve_otherwise_isSome (g : G) :
    (resolve (rs ++ [Rule.otherwise g]) cs).isSome := by
  induction rs with
  | nil => simp [resolve, Rule.otherwise_applies]
  | cons r rs ih => by_cases h : r.Applies cs <;> simp [resolve, h, ih]

end Resolve

/-- The number resolution rules of §9.1.2: in a language with a dual, two singulars take
the dual; any other coordination with a non-plural conjunct takes the plural; all-plural
conjuncts resolve nothing. -/
def numberResolve (hasDual : Bool) (ns : List Number) : Option Number :=
  if hasDual ∧ ns = [.singular, .singular] then some .dual
  else if ∃ n ∈ ns, n ≠ .plural then some .plural else none

namespace Tamil

open _root_.Tamil.Gender

/-- Whether a gender is one of the rational genders. -/
def Rational : Value → Prop := (· ≠ .neut)

instance : DecidablePred Rational := λ _ => by unfold Rational; infer_instance

/-- §9.3: all rationals take the rational form, all non-rationals the neuter; a mixture
has no resolved form. -/
def rules : List (Rule Value PlConcord) :=
  [⟨.all, Rational, .rational⟩, ⟨.all, (¬ Rational ·), .neuter⟩]

/-- (16): masculine and feminine together resolve to the rational form. -/
theorem resolve_masc_fem : resolve rules [.masc, .fem] = some .rational := by decide

/-- (18): a rational and a non-rational cannot be resolved. -/
theorem resolve_masc_neut : resolve rules [.masc, .neut] = none := by decide

/-- A strict semantic assignment with a semantic resolution: the resolved form is a function
of the conjuncts' rationality. -/
theorem resolve_factorsThrough :
    Function.FactorsThrough (resolve rules) (List.map (decide <| Rational ·)) := λ cs ds h => by
  have h₁ : ∀ l : List Value,
      (∀ c ∈ l, Rational c) ↔ ∀ b ∈ l.map (decide <| Rational ·), b = true := λ l => by
    simp
  have h₂ : ∀ l : List Value,
      (∀ c ∈ l, ¬ Rational c) ↔ ∀ b ∈ l.map (decide <| Rational ·), b = false := λ l => by
    simp
  simp only [resolve, rules, Rule.Applies, h₁, h₂, h]

end Tamil

namespace Archi

/-- The plural target genders: I/II for rationals, III/IV for the rest (Figure 6.12). -/
inductive PlForm where
  | I_II
  | III_IV
  deriving DecidableEq, Repr, Fintype

/-- §9.3: a conjunct denoting a rational brings gender I/II, otherwise III/IV; the
descriptor is rationality, so *xalq'* 'people' resolves by what it denotes. -/
def rules : List (Rule Bool PlForm) := [⟨.any, (· = true), .I_II⟩, Rule.otherwise .III_IV]

theorem resolve_rational_nonrational : resolve rules [true, false] = some .I_II := by decide

end Archi

namespace Luganda

/-- The resolved forms: the class 2 and class 8 markers. -/
inductive PlForm where
  | cl2
  | cl8
  deriving DecidableEq, Repr, Fintype

/-- §9.3: all humans take class 2, no humans class 8, and a mixture class 8 if resolution is
forced at all. -/
def rules : List (Rule Bool PlForm) :=
  [⟨.all, (· = true), .cl2⟩, ⟨.all, (· = false), .cl8⟩, Rule.otherwise .cl8]

end Luganda

namespace French

/-- The type-A rules of §9.4: at least one masculine, masculine; otherwise feminine. -/
def rulesA : List (Rule Value Value) := [⟨.any, (· = .masc), .masc⟩, Rule.otherwise .fem]

/-- The type-B rules: all feminine, feminine; otherwise masculine. -/
def rulesB : List (Rule Value Value) := [⟨.all, (· = .fem), .fem⟩, Rule.otherwise .masc]

/-- With exactly two genders the two formulations agree on every coordination. -/
theorem resolve_rulesA_eq_rulesB (cs : List Value) : resolve rulesA cs = resolve rulesB cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp_all [rulesA, rulesB, resolve, Rule.Applies, Rule.otherwise]

end French

namespace Slovene

/-- §9.4: all feminine, feminine; otherwise masculine, a type-B system in which the neuter
never results from resolution. -/
def rules : List (Rule Value Value) := [⟨.all, (· = .fem), .fem⟩, Rule.otherwise .masc]

/-- (52): three neuter singulars take the masculine plural, gender resolution triggered by
number resolution. -/
theorem resolve_neuters :
    resolve rules [.neut, .neut, .neut] = some .masc ∧
      numberResolve true [.singular, .singular, .singular] = some .plural := by
  decide

/-- The neuter is excluded as a resolved form. -/
theorem resolve_ne_neut (cs : List Value) : resolve rules cs ≠ some .neut := by
  simp only [rules, resolve, Rule.otherwise, Rule.Applies]
  split_ifs <;> simp

end Slovene

namespace Icelandic

inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- §9.4: homogeneous masculines or feminines keep their gender, any mixture takes the
neuter, the semantically justified gender for beings of both sexes. -/
def rules : List (Rule Value Value) :=
  [⟨.all, (· = .masc), .masc⟩, ⟨.all, (· = .fem), .fem⟩, Rule.otherwise .neut]

end Icelandic

namespace Latin

inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- A conjunct: its gender and whether it denotes a human. -/
abbrev Conjunct := Value × Bool

/-- §9.5: two syntactic rules for homogeneous genders, a semantic rule for humans, the neuter
otherwise. -/
def rules : List (Rule Conjunct Value) :=
  [⟨.all, (·.1 = .masc), .masc⟩, ⟨.all, (·.1 = .fem), .fem⟩, ⟨.all, (·.2 = true), .masc⟩,
    Rule.otherwise .neut]

end Latin

namespace Polish

/-- The plural agreement forms. -/
inductive PlForm where
  | mascPers
  | nonMascPers
  deriving DecidableEq, Repr, Fintype

/-- The obligatory rules of §9.5: a masculine personal conjunct, masculine personal;
otherwise non-masculine personal. The optional rules of (60) to (62) are rows only. -/
def rules : List (Rule Bool PlForm) := [⟨.any, (· = true), .mascPers⟩, Rule.otherwise .nonMascPers]

end Polish

namespace Romanian

open _root_.Romanian.Gender

/-- Whether a noun denotes a male animate. -/
def MaleAnimate (n : Noun) : Prop := n.animate ∧ n.isNaturalGender ∧ n.gender = .masc

instance : DecidablePred MaleAnimate := λ _ => by unfold MaleAnimate; infer_instance

/-- §9.5, collapsed: a male animate, masculine; all masculine, masculine; otherwise
feminine, over the fragment's nouns. -/
def rules : List (Rule Noun Value) :=
  [⟨.any, MaleAnimate, .masc⟩, ⟨.all, (·.gender = .masc), .masc⟩, Rule.otherwise .fem]

/-- (69): a masculine and a neuter inanimate resolve to the feminine, the form the neuter
takes in the plural. -/
theorem resolve_perete_scaun : resolve rules [perete, scaun] = some .fem := by decide

end Romanian

namespace SerboCroat

/-- Stage 2 of §9.7, the alternative formulation, stage 1 being Slovene's rules: all
female, feminine; all feminine, optionally feminine; otherwise masculine. The optional rule
yields a second grammar. -/
def stage2 : List (List (Rule (Slovene.Value × Bool) Slovene.Value)) :=
  [[⟨.all, (λ c => c.1 = .fem ∧ c.2), .fem⟩, ⟨.all, (·.1 = .fem), .fem⟩, Rule.otherwise .masc],
    [⟨.all, (λ c => c.1 = .fem ∧ c.2), .fem⟩, Rule.otherwise .masc]]

/-- (77) and (78): feminine inanimates may take the masculine. -/
theorem feminine_inanimates_masc :
    ∃ g ∈ stage2, resolve g [(.fem, false), (.fem, false)] = some .masc := by
  decide

/-- Feminine nouns denoting females keep the feminine in both grammars. -/
theorem females_fem : ∀ g ∈ stage2, resolve g [(.fem, true), (.fem, true)] = some .fem := by
  decide

end SerboCroat

namespace Ojibwa

inductive Value where
  | animate
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- §9.7: homogeneous conjuncts keep their gender; animate and inanimate cannot be
conjoined. -/
def rules : List (Rule Value Value) :=
  [⟨.all, (· = .animate), .animate⟩, ⟨.all, (· = .inanimate), .inanimate⟩]

theorem resolve_mixed : resolve rules [.animate, .inanimate] = none := by decide

end Ojibwa

/-! ### The judgments of chapter 9

A row with a `conjuncts` and a `resolved` feature names its conjuncts and the form the
predicate shows; it is acceptable exactly when the language's rules select that form. -/

open _root_.Tamil.Gender in
theorem tamil_rows : ∀ row ∈ Examples.all, row.language = "tami1289" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+masc", [Value.masc, .masc]), ("fem+fem", [.fem, .fem]),
      ("fem+masc", [.fem, .masc]), ("neut+neut", [.neut, .neut]), ("masc+neut", [.masc, .neut])],
      ∀ g ∈ row.parse? "resolved" [("rational", PlConcord.rational), ("neuter", .neuter)],
        (row.judgment = .acceptable ↔ resolve Tamil.rules cs = some g) := by
  decide +kernel

theorem archi_rows : ∀ row ∈ Examples.all, row.language = "arch1244" →
    ∀ cs ∈ row.parse? "conjuncts" [("rational+rational", [true, true]),
      ("rational+nonrational", [true, false]), ("nonrational+nonrational", [false, false])],
      ∀ g ∈ row.parse? "resolved" [("I/II", Archi.PlForm.I_II), ("III/IV", .III_IV)],
        (row.judgment = .acceptable ↔ resolve Archi.rules cs = some g) := by
  decide +kernel

theorem luganda_rows : ∀ row ∈ Examples.all, row.language = "gand1255" →
    ∀ cs ∈ row.parse? "conjuncts" [("human+human+human", [true, true, true]),
      ("nonhuman+nonhuman+nonhuman+nonhuman", [false, false, false, false]),
      ("human+nonhuman", [true, false])],
      ∀ g ∈ row.parse? "resolved" [("2", Luganda.PlForm.cl2), ("8", .cl8)],
        (row.judgment = .acceptable ↔ resolve Luganda.rules cs = some g) := by
  decide +kernel

theorem french_rows : ∀ row ∈ Examples.all, row.language = "stan1290" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+masc", [French.Value.masc, .masc]),
      ("fem+fem", [.fem, .fem]), ("masc+fem", [.masc, .fem])],
      ∀ g ∈ row.parse? "resolved" [("masc", French.Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve French.rulesA cs = some g) := by
  decide +kernel

theorem slovene_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+fem", [Slovene.Value.masc, .fem]),
      ("masc+neut", [.masc, .neut]), ("fem+neut", [.fem, .neut]), ("neut+neut", [.neut, .neut]),
      ("fem+fem", [.fem, .fem]), ("neut+neut+neut", [.neut, .neut, .neut]),
      ("fem+fem+fem", [.fem, .fem, .fem])],
      ∀ g ∈ row.parse? "resolved" [("masc", Slovene.Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve Slovene.rules cs = some g) := by
  decide +kernel

theorem slovene_number_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ ns ∈ row.parse? "numbers" [("sg+sg", [Number.singular, .singular]),
      ("sg+sg+sg", [.singular, .singular, .singular]), ("sg+du", [.singular, .dual])],
      ∀ n ∈ row.parse? "number" [("dual", Number.dual), ("plural", .plural)],
        (row.judgment = .acceptable ↔ numberResolve true ns = some n) := by
  decide +kernel

theorem icelandic_rows : ∀ row ∈ Examples.all, row.language = "icel1247" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+fem", [Icelandic.Value.masc, .fem]),
      ("fem+neut", [.fem, .neut])],
      ∀ g ∈ row.parse? "resolved" [("neut", Icelandic.Value.neut)],
        (row.judgment = .acceptable ↔ resolve Icelandic.rules cs = some g) := by
  decide +kernel

theorem polish_rows : ∀ row ∈ Examples.all, row.language = "poli1260" →
    ∀ cs ∈ row.parse? "conjuncts" [("fem+fem", [false, false]),
      ("mascPers+fem+fem", [true, false, false])],
      ∀ g ∈ row.parse? "resolved" [("mascPers", Polish.PlForm.mascPers),
        ("nonMascPers", .nonMascPers)],
        (row.judgment = .acceptable ↔ resolve Polish.rules cs = some g) := by
  decide +kernel

theorem latin_rows : ∀ row ∈ Examples.all, row.language = "lati1261" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc.human+fem.human",
      [((Latin.Value.masc, true) : Latin.Conjunct), (.fem, true)]),
      ("masc.inanimate+fem.inanimate", [(.masc, false), (.fem, false)])],
      ∀ g ∈ row.parse? "resolved" [("masc", Latin.Value.masc), ("neut", .neut)],
        (row.judgment = .acceptable ↔ resolve Latin.rules cs = some g) := by
  decide +kernel

open _root_.Romanian.Gender in
theorem romanian_resolution_rows : ∀ row ∈ Examples.all, row.language = "roma1327" →
    ∀ cs ∈ row.parse? "conjuncts" [("fată+femeie", [fata, femeie]),
      ("băiat+bărbat", [baiat, barbat]), ("băiat+fată", [baiat, fata]),
      ("uşă+perete", [usa, perete]), ("perete+scaun", [perete, scaun]),
      ("scaun+masă", [scaun, masa]), ("nuc+prun", [nuc, prun]),
      ("frigider+televizor", [frigider, televizor]), ("uşă+masă", [usa, masa])],
      ∀ g ∈ row.parse? "resolved" [("masc", Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve Romanian.rules cs = some g) := by
  decide +kernel

theorem ojibwa_rows : ∀ row ∈ Examples.all, row.language = "ojib1241" →
    ∀ cs ∈ row.parse? "conjuncts" [("animate+animate", [Ojibwa.Value.animate, .animate]),
      ("inanimate+inanimate", [.inanimate, .inanimate]),
      ("animate+inanimate", [.animate, .inanimate])],
      ∀ g ∈ row.parse? "resolved" [("animate", Ojibwa.Value.animate), ("inanimate", .inanimate)],
        (row.judgment = .acceptable ↔ resolve Ojibwa.rules cs = some g) := by
  decide +kernel

/-! ### The judgments of chapter 3

A Swahili row with a `noun` and a `concord` feature is acceptable exactly when the concord
is the gender the assignment rules give the noun. -/

open _root_.Swahili in
theorem swahili_rows : ∀ row ∈ Examples.all, row.language = "swah1253" →
    ∀ n ∈ row.parse? "noun" (allNouns.map λ n => (n.form, n)),
      ∀ g ∈ row.parse? "concord" [("1/2", Gender.genderA), ("3/4", .genderB), ("7/8", .genderD)],
        (row.judgment = .acceptable ↔ Swahili.system.assign Swahili.sem Noun.morphClass n = g) := by
  decide +kernel

end Corbett1991
