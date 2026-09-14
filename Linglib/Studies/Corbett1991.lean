import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Agreement.Hierarchy
import Linglib.Syntax.Agreement.Resolution
import Linglib.Syntax.Agreement.Classes
import Linglib.Syntax.Gender.Assignment
import Linglib.Syntax.Number.Resolve
import Linglib.Syntax.Person.Resolve
import Linglib.Fragments.Tamil.Gender
import Linglib.Fragments.Swahili.Nouns
import Linglib.Fragments.Afar.Gender
import Linglib.Fragments.Romanian.Gender
import Linglib.Fragments.Slavic.Russian.Gender
import Linglib.Fragments.Hausa.Gender
import Linglib.Fragments.Latin.Gender
import Linglib.Data.Examples.Corbett1991

/-!
# Corbett (1991): Gender

This file formalizes the book's typology of gender. Gender is a property of nouns shown only
in agreement, and a language's genders are the classes of nouns that take the same
agreements. Nouns are assigned to them by rules reading their meaning or their form: the
semantic rules take precedence, the formal rules, morphological or phonological, sort the
semantic residue, and no system is formal alone (`Gender.AssignmentSystem`). Tamil, Russian,
Swahili, Afar and Hausa instantiate the schema on their fragments, and the assignment systems
of chapters 2 and 3 are surveyed by kind and by the semantic criteria their rules use
(`survey`).

Counting the genders starts from agreement classes, the sets of nouns taking identical
agreements in every form on every target, distinguishes the controller genders into which
nouns fall from the target genders marked on agreeing elements, and reads Greenberg's
universal that the plural never distinguishes more genders than the singular off the map
between the two numbers' target genders, parallel, convergent or crossed, exhibited here for
French, German, Tamil, Romanian, Lak and Slovene. Nouns whose meaning and form conflict may
be hybrid, taking semantic agreement on some targets and syntactic agreement on others, and
the hybrids of the book's summary table respect the Agreement Hierarchy
(`hybrids_respectHierarchy`); the Bantu data of §8.3 divide the attributive position into
the possessive and the other modifiers (`FinePosition`), and the corpus proportions of
feminine agreement with Russian *vrač* respect the hierarchy too.

Conjoined controllers are resolved by ordered rules of two shapes, one conjunct of a kind or
all conjuncts of a kind, reading the conjuncts' person, meaning or gender; the rules of
person, of number and of gender are stated for Czech, Tamil, Archi, Luganda, French, Slovene,
Icelandic, Latin, Polish, Romanian, Serbo-Croat and Ojibwa, and a language's resolution is
never less semantic than its assignment. The judgments the book reports are the rows of
`Data/Examples/Corbett1991.json`.

## Implementation notes

* The assignment systems are the substrate's, typed by the meaning their semantic rules read
  and the form their formal rules read; the fragments' natural-gender flag stands in for the
  referent's sex. Corbett's irregular third declension of Russian is the study's refinement
  of the fragment's declension classes.
* Agreement classes, target genders and the map between two numbers' target genders are the
  substrate's `Gender.agreementClasses`, `Gender.targetGenders` and `Gender.Parallel`,
  `Gender.Convergent` and `Gender.Crossed`. Subgenders, inquorate genders and consistent
  agreement patterns are described in the book's prose and not formalised.
* A hybrid noun is an `Agreement.Hybrid`, its availability profile over the positions of
  `Agreement.Target`, or over `FinePosition` where the book divides the attributive; it
  respects the hierarchy when the profile is antitone on the positions where it is recorded,
  and the same predicate serves the corpus proportions.
* Resolution rules are the substrate's `Agreement.ResolutionRule`, applied in order to a
  list of conjunct descriptors and returning no form when no rule applies, the book's
  ineffable coordinations; the descriptors are persons, genders, semantic features, or
  fragment nouns as each language requires. Optional rules are recorded as rows. Number
  resolution is `Number.resolveIn` folded over the conjuncts, except that a coordination of
  plurals alone resolves nothing, the book's restriction that keeps gender resolution from
  being triggered. The gender carriers of French, German, Lak, Slovene, Icelandic and Ojibwa
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

open Agreement Agreement.ResolutionRule

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
def sem (n : Tamil.Gender.Noun) : Bool × Option Value :=
  (n.rational, if n.isNaturalGender then some n.gender else none)

/-- Table 2.1: male rationals masculine, female rationals feminine, the residue neuter. -/
def system : Gender.AssignmentSystem (Bool × Option Value) Unit Value where
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
def declension (n : Russian.Gender.Noun) : Option Declension :=
  if n = znamja ∨ n = put' then some .irregularIII else
    n.declClass.map λ
      | .I => .I
      | .II => .II
      | .III => .III
      | .IV => .IV

/-- The natural gender of a sex-differentiable noun. -/
def sem (n : Russian.Gender.Noun) : Option Value :=
  if n.isNaturalGender then some n.gender else none

/-- The rules of §3.1.1 for declinable nouns: males masculine and females feminine; then
declension I masculine, declensions II and III feminine, the rest neuter. The rules for
acronyms and indeclinables (Figure 3.4) are not modelled. -/
def system : Gender.AssignmentSystem (Option Value) (Option Declension) Value where
  semantic := id
  formal
    | some .I => some .masc
    | some .II | some .III => some .fem
    | _ => none
  residue := .neut

/-- The rules assign every noun of the fragment its gender, *put'* excepted, which the book
leaves as an isolated exception with an irregular lexical marker. -/
theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ≠ put' → system.assign sem declension n = n.gender := by
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
def sem (n : Swahili.Noun) : Option Evaluative × Bool := (n.evaluative, n.animate)

/-- The rules of §3.1.2: augmentatives to 5/6, diminutives to 7/8, remaining animates to
1/2; then each morphological class to its own gender, over the fragment's five genders (the
book's 11/10 and 15 are not among them). The formal rule is total, so the residue gender is
never reached. -/
def system : Gender.AssignmentSystem (Option Evaluative × Bool) _root_.Swahili.Gender
    _root_.Swahili.Gender where
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
def sem (n : Afar.Gender.Noun) : Option Value := if n.isNaturalGender then some n.gender else none

/-- Sex first; then a citation form ending in an accented vowel is feminine, the rest
masculine. -/
def system : Gender.AssignmentSystem (Option Value) Bool Value where
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
def sem (n : Hausa.Noun) : Option Gender := if n.isNaturalGender then some n.gender else none

/-- Sex first; then a noun in *-ā* is feminine, the rest masculine. -/
def system : Gender.AssignmentSystem (Option Gender) Bool Gender where
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

/-! ### Controller and target genders (chapter 6) -/

namespace Romanian

open _root_.Romanian.Gender

/-- Figure 6.1: a crossed system. -/
theorem crossed : Gender.Crossed (Value.adjForm · false) (Value.adjForm · true) := by decide

/-- Three controller genders over two target genders in each number. -/
theorem card_range_adjForm :
    Fintype.card (Set.range Value.adjForm) = 3 ∧
      Fintype.card (Gender.targetGenders Value.adjForm false) = 2 ∧
        Fintype.card (Gender.targetGenders Value.adjForm true) = 2 := by
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

theorem parallel : Gender.Parallel (id : Value → Value) id := by decide

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

theorem convergent : Gender.Convergent Value.sgArticle Value.plArticle := by decide

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
theorem crossed : Gender.Crossed Value.sgMarker Value.plMarker := by decide

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

theorem parallel_sg_pl : Gender.Parallel Value.sgEnding Value.plEnding := by decide

theorem convergent_sg_du : Gender.Convergent Value.sgEnding Value.duEnding := by decide

theorem convergent_pl_du : Gender.Convergent Value.plEnding Value.duEnding := by decide

end Slovene

namespace Tamil

open _root_.Tamil.Gender

/-- Figure 6.8: three singular target genders converge on two in the plural. -/
theorem convergent : Gender.Convergent Value.sgConcord Value.plConcord := by decide

/-- Greenberg's Universal 37 in Tamil as a corollary of convergence: a number whose target
genders are determined by another's distinguishes no more of them. The book states the
universal over target genders because it holds of crossed systems too, Lak above. -/
theorem card_plConcord_le :
    Nat.card (Set.range Value.plConcord) ≤ Nat.card (Set.range Value.sgConcord) :=
  convergent.1.card_range_le

end Tamil

/-! ### Hybrid nouns and the Agreement Hierarchy (chapter 8) -/

/-- Table 8.1, with the English boat nouns of §6.4.5 and the Bantu hybrids of §8.3. -/
def frenchTitles : Hybrid Target := λ
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic
  | .verb => none

def madchen : Hybrid Target := λ
  | .attributive | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | .predicate | .verb => none

def lajdaki : Hybrid Target := λ
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .semanticOnly
  | .verb => none

def spanishTitles : Hybrid Target := λ
  | .attributive => some .syntacticOnly
  | .predicate | .relativePronoun | .personalPronoun => some .semanticOnly
  | .verb => none

def konkani : Hybrid Target := λ
  | .attributive => some .syntacticOnly
  | .predicate | .personalPronoun => some .semanticOnly
  | .relativePronoun | .verb => none

def vrac : Hybrid Target := λ
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun | .personalPronoun => some .mostlySemantic
  | .verb => none

def gazde : Hybrid Target := λ
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun => some .mostlySemantic
  | .personalPronoun => some .semanticOnly
  | .verb => none

def boat : Hybrid Target := λ
  | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | _ => none

/-- *kamwana*: gender 12/13 forms normally, gender 1/2 also possible for a personal pronoun
sufficiently removed from the controller. -/
def kamwana : Hybrid Target := λ
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic
  | .verb => none

def kilumba : Hybrid Target := λ
  | .attributive => some .syntacticOnly
  | .predicate => some .both
  | _ => none

/-- The hybrids of Table 8.1 by the names the rows use. -/
def hybridNames : List (String × Hybrid Target) :=
  [("frenchTitles", frenchTitles),
    ("mädchen", madchen),
    ("łajdaki", lajdaki),
    ("spanishTitles", spanishTitles),
    ("konkani", konkani),
    ("vrač", vrac),
    ("gazde", gazde),
    ("boat", boat),
    ("kamwana", kamwana),
    ("kilumba", kilumba)]

/-- Every hybrid of Table 8.1 respects the Agreement Hierarchy. -/
theorem hybrids_respectHierarchy : ∀ h ∈ hybridNames, RespectsHierarchy h.2 := by decide

/-- The corpus-level claim on *vrač*: Panov's respondents favouring feminine agreement, 16.9
per cent of 3,835 for the attributive and 51.7 per cent of 3,806 for the predicate. -/
def vracFeminine : Target → Option ℚ
  | .attributive => some (169 / 1000)
  | .predicate => some (517 / 1000)
  | _ => none

/-- The proportion of semantic agreement rises along the hierarchy. -/
theorem vracFeminine_respectsHierarchy : RespectsHierarchy vracFeminine := by decide +kernel

/-- The stacked-target constraint of §8.1.2: when stacked or parallel targets of one
controller differ, the further one shows semantic agreement. -/
def StackedAllowed (near far : Kind) : Prop := near = .semantic → far = .semantic

instance (near far : Kind) : Decidable (StackedAllowed near far) := by
  unfold StackedAllowed; infer_instance

/-! ### Attributive possessives (§8.3)

The last stages of the loss of syntactic agreement in coastal Bantu treat the attributive
possessive differently from the other attributive modifiers, a finer division of the
hierarchy. -/

/-- The positions of the hierarchy with the attributive divided into the possessive and the
other attributive modifiers, the possessive above them. -/
inductive FinePosition where
  | possessive
  | attributive
  | predicate
  | relativePronoun
  | personalPronoun
  deriving DecidableEq, Repr, Fintype

namespace FinePosition

/-- The rank of a fine position, the possessive on top. -/
def rank : FinePosition → ℕ
  | .possessive => 4
  | .attributive => 3
  | .predicate => 2
  | .relativePronoun => 1
  | .personalPronoun => 0

theorem rank_injective : Function.Injective rank := by decide

instance : LinearOrder FinePosition := LinearOrder.lift' rank rank_injective

/-- The position of the hierarchy a fine position divides. -/
def toTarget : FinePosition → Target
  | .possessive | .attributive => .attributive
  | .predicate => .predicate
  | .relativePronoun => .relativePronoun
  | .personalPronoun => .personalPronoun

/-- The finer division refines the hierarchy. -/
theorem toTarget_monotone : Monotone toTarget := by decide

end FinePosition

/-- Swahili *rafiki* 'friend', (47) to (49): an animate of morphological class 9/10 with
gender 1/2 agreement throughout, class 9/10 agreement remaining possible on an attributive
possessive alone. -/
def rafiki : Hybrid FinePosition := λ
  | .possessive => some .both
  | .attributive | .predicate => some .semanticOnly
  | _ => none

/-- Kami *ng'ombe* 'cows' and *mbudzi* 'goats', (54) and (55): syntactic agreement of the
predicate rejected, both forms accepted on attributives other than the possessive, which the
book reports with class 10 agreement only. -/
def ngombe : Hybrid FinePosition := λ
  | .possessive => some .syntacticOnly
  | .attributive => some .both
  | .predicate => some .semanticOnly
  | _ => none

/-- The Bantu hybrids of §8.3 by the names the rows use. -/
def fineHybridNames : List (String × Hybrid FinePosition) :=
  [("rafiki", rafiki),
    ("ng'ombe", ngombe)]

/-- The Bantu hybrids respect the finer hierarchy. -/
theorem fineHybrids_respectHierarchy : ∀ h ∈ fineHybridNames, RespectsHierarchy h.2 := by
  decide

/-! ### The judgments of chapter 8

A row with a `hybrid`, a `target` and an `agreement` feature is a use of a hybrid noun at a
position of the hierarchy, acceptable exactly when the hybrid's availability there admits
the agreement; a row with `near` and `far` features is a pair of stacked targets. The
hybrids are listed by the names the rows use. -/

/-- The positions of the hierarchy by the names the rows use. -/
def targetNames : List (String × Target) :=
  [("attributive", .attributive), ("predicate", .predicate),
    ("relativePronoun", .relativePronoun), ("personalPronoun", .personalPronoun)]

/-- The fine positions by the names the rows use. -/
def finePositionNames : List (String × FinePosition) :=
  [("attributivePossessive", .possessive), ("attributive", .attributive),
    ("predicate", .predicate), ("relativePronoun", .relativePronoun),
    ("personalPronoun", .personalPronoun)]

/-- The two agreements by the names the rows use. -/
def kindNames : List (String × Kind) := [("syntactic", .syntactic), ("semantic", .semantic)]

theorem hybrid_rows : ∀ row ∈ Examples.all, ∀ h ∈ hybridNames, row.feature? "hybrid" = some h.1 →
    ∀ t ∈ row.parse? "target" targetNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ h.2 t, a.Allows k) := by
  decide +kernel

theorem fine_rows : ∀ row ∈ Examples.all, ∀ h ∈ fineHybridNames, row.feature? "hybrid" = some h.1 →
    ∀ t ∈ row.parse? "target" finePositionNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ h.2 t, a.Allows k) := by
  decide +kernel

/-- Every row naming a hybrid names one of Table 8.1 or one of §8.3, at a position one of
the two theorems reads. -/
theorem hybrid_rows_covered : ∀ row ∈ Examples.all, ∀ n ∈ row.feature? "hybrid",
    (n ∈ hybridNames.map Prod.fst ∨ n ∈ fineHybridNames.map Prod.fst) ∧
      ∀ t ∈ row.feature? "target", t ∈ finePositionNames.map Prod.fst := by
  decide +kernel

theorem stacked_rows : ∀ row ∈ Examples.all, ∀ near ∈ row.parse? "near" kindNames,
    ∀ far ∈ row.parse? "far" kindNames, (row.judgment = .acceptable ↔ StackedAllowed near far) := by
  decide +kernel

/-! ### Resolution (chapter 9) -/

/-- The person resolution rules of §9.1.1, Czech's and claimed universal: a first person
conjunct, first person; a second, second; otherwise third. -/
def personRules : List (ResolutionRule Person Person) :=
  [⟨.any, (· = .first), .first⟩, ⟨.any, (· = .second), .second⟩, otherwise .third]

/-- On the three persons the rules are the substrate's resolution in a system of three
persons, the union of the conjuncts' discourse roles. -/
theorem resolve_personRules_pair :
    ∀ a ∈ [Person.first, .second, .third], ∀ b ∈ [Person.first, .second, .third],
      resolve personRules [a, b] = some (Person.resolveIn [.first, .second, .third] a b) := by
  decide

/-- The number resolution rules of §9.1.2 in a system with the given values: the conjuncts'
numbers resolved pairwise and coarsened to the system, except that a coordination of plurals
alone resolves nothing, so that gender resolution is not triggered. -/
def numberResolve (sys : List Number) : List Number → Option Number
  | [] => none
  | n :: ns =>
    if ∀ m ∈ n :: ns, m = .plural then none else some (ns.foldl (Number.resolveIn sys) n)

namespace Tamil

open _root_.Tamil.Gender

/-- Whether a gender is one of the rational genders. -/
def Rational : Value → Prop := (· ≠ .neut)

instance : DecidablePred Rational := λ _ => by unfold Rational; infer_instance

/-- §9.3: all rationals take the rational form, all non-rationals the neuter; a mixture
has no resolved form. -/
def rules : List (ResolutionRule Value PlConcord) :=
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
  simp only [resolve, rules, ResolutionRule.Applies, h₁, h₂, h]

end Tamil

namespace Archi

/-- The plural target genders: I/II for rationals, III/IV for the rest (Figure 6.12). -/
inductive PlForm where
  | I_II
  | III_IV
  deriving DecidableEq, Repr, Fintype

/-- §9.3: a conjunct denoting a rational brings gender I/II, otherwise III/IV; the
descriptor is rationality, so *xalq'* 'people' resolves by what it denotes. -/
def rules : List (ResolutionRule Bool PlForm) := [⟨.any, (· = true), .I_II⟩, otherwise .III_IV]

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
def rules : List (ResolutionRule Bool PlForm) :=
  [⟨.all, (· = true), .cl2⟩, ⟨.all, (· = false), .cl8⟩, otherwise .cl8]

end Luganda

namespace French

/-- The type-A rules of §9.4: at least one masculine, masculine; otherwise feminine. -/
def rulesA : List (ResolutionRule Value Value) := [⟨.any, (· = .masc), .masc⟩, otherwise .fem]

/-- The type-B rules: all feminine, feminine; otherwise masculine. -/
def rulesB : List (ResolutionRule Value Value) := [⟨.all, (· = .fem), .fem⟩, otherwise .masc]

/-- With exactly two genders the two formulations agree on every coordination. -/
theorem resolve_rulesA_eq_rulesB (cs : List Value) : resolve rulesA cs = resolve rulesB cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp_all [rulesA, rulesB, resolve, ResolutionRule.Applies, otherwise]

end French

namespace Slovene

/-- The numbers of Slovene. -/
def numbers : List Number := [.singular, .dual, .plural]

/-- §9.4: all feminine, feminine; otherwise masculine, a type-B system in which the neuter
never results from resolution. -/
def rules : List (ResolutionRule Value Value) := [⟨.all, (· = .fem), .fem⟩, otherwise .masc]

/-- (52): three neuter singulars take the masculine plural, gender resolution triggered by
number resolution. -/
theorem resolve_neuters :
    resolve rules [.neut, .neut, .neut] = some .masc ∧
      numberResolve numbers [.singular, .singular, .singular] = some .plural := by
  decide

/-- The neuter is excluded as a resolved form. -/
theorem resolve_ne_neut (cs : List Value) : resolve rules cs ≠ some .neut := by
  simp only [rules, resolve, otherwise, ResolutionRule.Applies]
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
def rules : List (ResolutionRule Value Value) :=
  [⟨.all, (· = .masc), .masc⟩, ⟨.all, (· = .fem), .fem⟩, otherwise .neut]

end Icelandic

namespace Latin

open _root_.Latin.Gender

/-- A conjunct: its gender and whether it denotes a human. -/
abbrev Conjunct := Value × Bool

/-- §9.5: two syntactic rules for homogeneous genders, a semantic rule for humans, the neuter
otherwise. -/
def rules : List (ResolutionRule Conjunct Value) :=
  [⟨.all, (·.1 = .masc), .masc⟩, ⟨.all, (·.1 = .fem), .fem⟩, ⟨.all, (·.2 = true), .masc⟩,
    otherwise .neut]

end Latin

namespace Polish

/-- The plural agreement forms. -/
inductive PlForm where
  | mascPers
  | nonMascPers
  deriving DecidableEq, Repr, Fintype

/-- The obligatory rules of §9.5: a masculine personal conjunct, masculine personal;
otherwise non-masculine personal. The optional rules of (60) to (62) are rows only. -/
def rules : List (ResolutionRule Bool PlForm) :=
  [⟨.any, (· = true), .mascPers⟩, otherwise .nonMascPers]

end Polish

namespace Romanian

open _root_.Romanian.Gender

/-- Whether a noun denotes a male animate. -/
def MaleAnimate (n : Romanian.Gender.Noun) : Prop :=
  n.animate ∧ n.isNaturalGender ∧ n.gender = .masc

instance : DecidablePred MaleAnimate := λ _ => by unfold MaleAnimate; infer_instance

/-- §9.5, collapsed: a male animate, masculine; all masculine, masculine; otherwise
feminine, over the fragment's nouns. -/
def rules : List (ResolutionRule Romanian.Gender.Noun Value) :=
  [⟨.any, MaleAnimate, .masc⟩, ⟨.all, (·.gender = .masc), .masc⟩, otherwise .fem]

/-- (69): a masculine and a neuter inanimate resolve to the feminine, the form the neuter
takes in the plural. -/
theorem resolve_perete_scaun : resolve rules [perete, scaun] = some .fem := by decide

end Romanian

namespace SerboCroat

/-- Stage 2 of §9.7, the alternative formulation, stage 1 being Slovene's rules: all
female, feminine; all feminine, optionally feminine; otherwise masculine. The optional rule
yields a second grammar. -/
def stage2 : List (List (ResolutionRule (Slovene.Value × Bool) Slovene.Value)) :=
  [[⟨.all, (λ c => c.1 = .fem ∧ c.2), .fem⟩, ⟨.all, (·.1 = .fem), .fem⟩, otherwise .masc],
    [⟨.all, (λ c => c.1 = .fem ∧ c.2), .fem⟩, otherwise .masc]]

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
def rules : List (ResolutionRule Value Value) :=
  [⟨.all, (· = .animate), .animate⟩, ⟨.all, (· = .inanimate), .inanimate⟩]

theorem resolve_mixed : resolve rules [.animate, .inanimate] = none := by decide

end Ojibwa

/-! ### The judgments of chapter 9

A row with a `conjuncts` and a `resolved` feature names its conjuncts and the form the
predicate shows; it is acceptable exactly when the language's rules select that form. -/

theorem czech_rows : ∀ row ∈ Examples.all, row.language = "czec1258" →
    ∀ cs ∈ row.parse? "conjuncts" [("1+2", [Person.first, .second]), ("3+1", [.third, .first]),
      ("3+2", [.third, .second])],
      ∀ p ∈ row.parse? "resolved" [("1", Person.first), ("2", .second)],
        (row.judgment = .acceptable ↔ resolve personRules cs = some p) := by
  decide +kernel

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
        (row.judgment = .acceptable ↔ numberResolve Slovene.numbers ns = some n) := by
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
      [((Latin.Gender.Value.masc, true) : Latin.Conjunct), (.fem, true)]),
      ("masc.inanimate+fem.inanimate", [(.masc, false), (.fem, false)])],
      ∀ g ∈ row.parse? "resolved" [("masc", Latin.Gender.Value.masc), ("neut", .neut)],
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
