import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Semantics.ArgumentStructure.LevinTheory
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Studies.Coon2019
import Linglib.Data.Examples.BeaversEtAl2021

/-!
# Beavers et al. (2021): States and Changes of State

Across an 88-language balanced sample, roots of deadjectival change-of-state
verbs (property-concept roots: *large*, *red*, *dry*) tend to have simple
stative forms and marked verbs, while roots of non-deadjectival ones (result
roots: *break*, *cook*, *kill*) lack simple statives and have unmarked verbs.
Semantic tests — change denial (10)–(11) and restitutive *again* (14)–(16) —
show that words built on result roots always entail change. The simplest
analysis is that result roots carry the change entailment themselves,
refuting the bifurcation thesis (2): templatic meaning can live in roots.
The default-realization rule (44) then derives the markedness mirror image
and the three attested language types.

## Main statements

* `bifurcation_fails`: result roots entail change
  (`Verb.Root.ChangeType.EntailsChange`), violating the bifurcation
  thesis (2).
* `grand_unification`: the root's change entailment alone determines the
  full package of morphosyntactic correlates ((44), §§3, 6–9).
* `markedness_complementarity`: verbal and stative markedness are mirror
  images, ruling out the unattested fourth language type (§8).

## References

* [beavers-etal-2021]: States and changes of state: A crosslinguistic study
  of the roots of verbal meaning. *Language* 97.
* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [embick-2004]: On the structure of resultative participles in English.
* [embick-2009]: Roots, states, and stative passives.
* [arad-2005]: Roots and Patterns: Hebrew Morpho-syntax.
* [dixon-1982]: Where Have All the Adjectives Gone?
* [haspelmath-1993]: More on the typology of inchoative/causative verb
  alternations.
* [coon-2019]: Building verbs in Chuj.
-/

namespace BeaversEtAl2021

open Verb Verb.Root ArgumentStructure ArgumentStructure.EventStructure Features

/-! ### Root meanings and subclasses ((5)–(6)) -/

/-- [dixon-1982]'s basic property types: the property-concept subclasses (5),
those most often lexicalized as adjectives across languages. -/
inductive PCSubclass where
  /-- *large*, *small*, *long*, *short*, *deep*, *wide*, *tall*. -/
  | dimension
  /-- *old*. -/
  | age
  /-- *bad*, *good*. -/
  | value
  /-- *white*, *black*, *red*, *green*, *blue*, *brown*. -/
  | color
  /-- *cool*, *warm*, *dry*, *soft*, *hard*, *smooth*. -/
  | physicalProperty
  /-- *fast*, *slow*. -/
  | speed
  deriving DecidableEq, Repr

/-- Result-root subclasses (6), chosen from [levin-1993] for having likely
translation equivalents across languages. -/
inductive ResultSubclass where
  /-- *burn*, *melt*, *freeze*, *decay*, *bloom*. -/
  | entitySpecificCoS
  /-- *cook*, *bake*, *fry*, *roast*, *boil*. -/
  | cooking
  /-- *break*, *crack*, *crush*, *shatter*, *tear*. -/
  | breaking
  /-- *bend*, *fold*, *wrinkle*. -/
  | bending
  /-- *kill*, *murder*, *drown*. -/
  | killing
  /-- *destroy*, *ruin*. -/
  | destroying
  /-- *rise*, *fall*, *increase*, *decrease*, *differ*. -/
  | calibratableCoS
  /-- *come*, *go*, *enter*, *exit*, *return*. -/
  | inherentlyDirectedMotion
  deriving DecidableEq, Repr

/-! ### The paradigm and relation codes ((40)–(41)) -/

/-- The five positions of a root's paradigm (40): every root meaning is
associated with up to five forms. -/
inductive ParadigmPosition where
  /-- Position 1: separate shared base morpheme, if any. -/
  | underlyingRoot
  /-- Position 2: basic stative form (adjective, verb, or noun). -/
  | simpleStative
  /-- Position 3: intransitive change-of-state form. -/
  | inchoative
  /-- Position 4: transitive causative form. -/
  | causative
  /-- Position 5: deverbal stative form. -/
  | resultStative
  deriving DecidableEq, Repr

/-- Morphological relationship codes between a form and each paradigm member
(41), generalizing [haspelmath-1993]'s classification. The `unrelated` code
covers what Haspelmath called suppletive pairs (*kill* ~ *die*); `identity`
marks a form's relation to its own paradigm slot. -/
inductive MorphRelation where
  /-- (i) input to a rule forming the other form. -/
  | input
  /-- (d) output of a rule on the other form. -/
  | derived
  /-- (t) transitively related via input/output pairs. -/
  | transitive
  /-- (l) labile: same surface stem. -/
  | labile
  /-- (e) equipollent: both derived from a shared base. -/
  | equipollent
  /-- (u) unrelated: no other relation applies. -/
  | unrelated
  /-- (n) the other form is unattested. -/
  | unattested
  /-- (s) the forms are the same item. -/
  | identity
  deriving DecidableEq, Repr

/-! ### Per-root crosslinguistic sample (Tables A1–A2)

Full-table medians (§6, §7): PC roots have simple statives in a median
95.67% of languages with data vs 1.59% for result roots (Mann-Whitney
U = 1266.5, n₁ = n₂ = 36, p < 0.001); PC verbal paradigms are marked in a
median 56.01% of languages vs 15.20% for result roots (U = 1291, p < 0.001).
The rows below are a sample of the 72 root meanings. -/

/-- A root meaning with its crosslinguistic attestation counts
(Tables A1–A2). -/
structure RootMeaning where
  /-- English gloss(es). -/
  gloss : String
  /-- Property-concept or result root. -/
  rootClass : ChangeType
  /-- Subclass per (5)–(6). -/
  subclass : Option (PCSubclass ⊕ ResultSubclass) := none
  /-- Languages with a simple stative for this root (Table A1). -/
  nSimpleStative : Nat
  /-- Languages with any data for this root (Table A1). -/
  nLanguages : Nat
  /-- Languages with a marked verbal paradigm (Table A2). -/
  nMarkedVerbal : Nat
  /-- Languages with sufficient verbal-paradigm data (Table A2). -/
  nVerbalLanguages : Nat
  deriving Repr

/-- Fraction of languages with a simple stative, as a percentage. -/
def RootMeaning.pctSimpleStative (r : RootMeaning) : ℚ :=
  if r.nLanguages = 0 then 0
  else (r.nSimpleStative : ℚ) * 100 / r.nLanguages

/-- Fraction of languages with a marked verbal paradigm, as a percentage. -/
def RootMeaning.pctMarkedVerbal (r : RootMeaning) : ℚ :=
  if r.nVerbalLanguages = 0 then 0
  else (r.nMarkedVerbal : ℚ) * 100 / r.nVerbalLanguages

def coldRoot : RootMeaning :=
  ⟨"cold/make cold", .propertyConcept, some (.inl .physicalProperty), 83, 83, 27, 45⟩
def largeRoot : RootMeaning :=
  ⟨"large/big/enlarge", .propertyConcept, some (.inl .dimension), 86, 87, 25, 47⟩
def redRoot : RootMeaning :=
  ⟨"red/redden", .propertyConcept, some (.inl .color), 77, 80, 31, 35⟩
def longRoot : RootMeaning :=
  ⟨"long/lengthen", .propertyConcept, some (.inl .dimension), 80, 82, 26, 37⟩
def goodRoot : RootMeaning :=
  ⟨"good/improved/improve", .propertyConcept, some (.inl .value), 83, 85, 30, 46⟩
def dryRoot : RootMeaning :=
  ⟨"dry/dry", .propertyConcept, some (.inl .physicalProperty), 72, 85, 32, 64⟩
/-- The one PC outlier: *old* was coded as a result stative on the grounds
that being old entails a prior young/new state (§6.1). -/
def oldRoot : RootMeaning :=
  ⟨"old/aged/age", .propertyConcept, some (.inl .age), 0, 81, 10, 36⟩
def whiteRoot : RootMeaning :=
  ⟨"white/whiten", .propertyConcept, some (.inl .color), 81, 84, 27, 35⟩

def brokenRoot : RootMeaning :=
  ⟨"broken/break", .result, some (.inr .breaking), 1, 85, 21, 80⟩
def cookedRoot : RootMeaning :=
  ⟨"cooked/cook", .result, some (.inr .cooking), 0, 86, 12, 79⟩
def deadRoot : RootMeaning :=
  ⟨"dead/killed/kill", .result, some (.inr .killing), 5, 87, 9, 86⟩
def meltedRoot : RootMeaning :=
  ⟨"melted/melt", .result, some (.inr .entitySpecificCoS), 3, 64, 16, 61⟩
def shatteredRoot : RootMeaning :=
  ⟨"shattered/shatter", .result, some (.inr .breaking), 1, 53, 7, 48⟩
def bentRoot : RootMeaning :=
  ⟨"bent/bend", .result, some (.inr .bending), 6, 73, 14, 57⟩
def burnedRoot : RootMeaning :=
  ⟨"burned/burn", .result, some (.inr .entitySpecificCoS), 3, 82, 11, 79⟩
def tornRoot : RootMeaning :=
  ⟨"torn/tear", .result, some (.inr .breaking), 0, 77, 16, 70⟩
def goneRoot : RootMeaning :=
  ⟨"gone/go", .result, some (.inr .inherentlyDirectedMotion), 0, 78, 4, 73⟩
def destroyedRoot : RootMeaning :=
  ⟨"destroyed/destroy", .result, some (.inr .destroying), 0, 70, 9, 64⟩

def pcRoots : List RootMeaning :=
  [coldRoot, largeRoot, redRoot, longRoot, goodRoot, dryRoot, oldRoot, whiteRoot]

def resultRoots : List RootMeaning :=
  [brokenRoot, cookedRoot, deadRoot, meltedRoot, shatteredRoot,
   bentRoot, burnedRoot, tornRoot, goneRoot, destroyedRoot]

/-- Every sampled PC root except the *old* outlier has a simple stative in
a majority of languages with data (Table A1, Fig. 2). -/
theorem pc_roots_majority_statives :
    ∀ r ∈ pcRoots, r.gloss ≠ oldRoot.gloss →
      r.nLanguages ≤ 2 * r.nSimpleStative := by decide

/-- No sampled result root has a simple stative in more than a tenth of
languages with data (Table A1, Fig. 2). -/
theorem result_roots_rare_statives :
    ∀ r ∈ resultRoots, 10 * r.nSimpleStative ≤ r.nLanguages := by decide

/-! ### Semantic diagnostics ((10)–(16)) -/

/-- Change denial (10)–(11): a stative form survives conjoined denial of
change (*the bright photo has never brightened*) iff its root does not
entail change; result-root statives are contradictory even in
prototypical-result contexts (*#the shattered vase has never shattered*). -/
def survivesChangeDenial : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- Change denial succeeds exactly when the root does not entail change. -/
theorem survivesChangeDenial_iff (ct : ChangeType) :
    survivesChangeDenial ct = true ↔ ¬ ct.EntailsChange := by
  cases ct <;> simp [survivesChangeDenial, ChangeType.EntailsChange]

/-! ### Sublexical *again* ((14)–(16)) -/

/-- Attachment sites for sublexical *again*: to the root (restitutive) or
over `v_become` (repetitive). -/
inductive AgainReading where
  /-- *again* scopes over the root's state only. -/
  | restitutive
  /-- *again* scopes over the change-introducing structure. -/
  | repetitive
  deriving DecidableEq, Repr

/-- Available *again* readings by root class: a result root's state itself
entails change, collapsing low attachment into the repetitive reading. -/
def againReadings : ChangeType → List AgainReading
  | .propertyConcept => [.restitutive, .repetitive]
  | .result => [.repetitive]

/-- Result roots lack the restitutive reading (16). -/
theorem result_no_restitutive :
    AgainReading.restitutive ∉ againReadings .result := by
  simp [againReadings]

/-- PC roots have the restitutive reading (15). -/
theorem pc_has_restitutive :
    AgainReading.restitutive ∈ againReadings .propertyConcept := by
  simp [againReadings]

/-- The change-denial and restitutive-*again* diagnostics ((10)–(11) vs
(14)–(16)) sort roots identically. -/
theorem diagnostics_agree (ct : ChangeType) :
    survivesChangeDenial ct = true ↔ AgainReading.restitutive ∈ againReadings ct := by
  cases ct <;> simp [survivesChangeDenial, againReadings]

/-! ### Morphosyntactic correlates (§§6–7) -/

/-- PC roots have simple (unmarked) stative forms; result roots lack them:
*bright* is a simple adjective while *shattered* requires the deverbal form.
Crosslinguistic tendency, not universal (§6, Fig. 1). -/
def hasSimpleStative : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- PC root verbs tend to be morphologically marked (*wid-en*, *flat-ten*);
result root verbs tend to be unmarked (*break*, *crack*). Crosslinguistic
tendency (§7, Fig. 5). -/
def verbalFormIsMarked : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- A root's change entailment determines its morphosyntactic profile in a
single biconditional: result roots lack simple statives (§6), have unmarked
verbal forms (§7), and lack restitutive *again* (§3.4); PC roots are the
reverse. -/
theorem semantic_determines_morphosyntax (ct : ChangeType) :
    ct.EntailsChange ↔
    (hasSimpleStative ct = false ∧
     verbalFormIsMarked ct = false ∧
     AgainReading.restitutive ∉ againReadings ct) := by
  cases ct <;> simp [ChangeType.EntailsChange, hasSimpleStative,
    verbalFormIsMarked, againReadings]

/-! ### The bifurcation thesis and its refutation ((2), §§3.6, 9) -/

/-- The bifurcation thesis for roots ([embick-2009], [arad-2005];
(2)): a component of meaning introduced by a templatic operator cannot be
part of a root's meaning — so no root should entail change. -/
def bifurcationThesis (rootEntailsChange : ChangeType → Prop) : Prop :=
  ∀ ct, ¬ rootEntailsChange ct

/-- The paper's main result: result roots entail change, so bifurcation
fails (§§3.3, 3.6, 9). -/
theorem bifurcation_fails :
    ¬ bifurcationThesis ChangeType.EntailsChange := fun h => h .result trivial

/-- PC roots on their own are consistent with bifurcation. -/
theorem pc_roots_consistent_with_bifurcation :
    ¬ ChangeType.EntailsChange .propertyConcept := id

/-- [beavers-koontz-garboden-2020] strengthen the refutation: roots can
entail change, causation, and manner simultaneously (√GUILLOTINE, √HAND) —
witnessed by `Root.Kinds.fullSpec`. -/
theorem bkg_bifurcation_fails_all_dimensions :
    Root.Kind.result ∈ Root.Kinds.fullSpec ∧
    Root.Kind.cause ∈ Root.Kinds.fullSpec ∧
    Root.Kind.manner ∈ Root.Kinds.fullSpec ∧
    Root.Kind.state ∈ Root.Kinds.fullSpec := by decide

/-- Multiple Levin classes witness the stronger bifurcation failure. -/
theorem bkg_bifurcation_multiple_witnesses :
    Root.Kind.result ∈ LevinClass.rootEntailments .cut ∧
    Root.Kind.manner ∈ LevinClass.rootEntailments .cut ∧
    Root.Kind.cause ∈ LevinClass.rootEntailments .give ∧
    Root.Kind.manner ∈ LevinClass.rootEntailments .give := by decide

/-! ### Default realization ((44), §8) -/

/-- Whether a form is morphologically marked relative to its paradigm. -/
inductive Markedness where
  /-- Basic form: only labile and unrelated relationships. -/
  | unmarked
  /-- Derived from or equipollent to another paradigm member. -/
  | marked
  deriving DecidableEq, Repr

/-- Default realization of `v_become` (44a): a root entailing change is
redundant with `v_become`, so its verb is unmarked; a PC root's verb carries
the change overtly and is marked. -/
def verbalMarkedness (ct : ChangeType) : Markedness :=
  if ct.EntailsChange then .unmarked else .marked

/-- Default realization of the stative head (44b): the mirror image — a PC
root's stative is basic, a result root's stative must strip nothing and is
built on the verb. -/
def stativeMarkedness (ct : ChangeType) : Markedness :=
  if ct.EntailsChange then .marked else .unmarked

/-- Verbal and stative markedness are mirror images, so the fourth logically
possible language type — result roots more marked than PC roots in both
columns — is predicted not to exist (§8). -/
theorem markedness_complementarity (ct : ChangeType) :
    verbalMarkedness ct ≠ stativeMarkedness ct := by
  cases ct <;> simp [verbalMarkedness, stativeMarkedness, ChangeType.EntailsChange]

/-- Verbal unmarkedness is exactly the change entailment. -/
theorem markedness_from_semantics (ct : ChangeType) :
    verbalMarkedness ct = .unmarked ↔ ct.EntailsChange := by
  cases ct <;> simp [verbalMarkedness, ChangeType.EntailsChange]

/-! ### Language types (§7.2, Table 1)

The (44) asymmetry surfaces only in languages with an overt markedness
contrast. Equipollent languages (Hebrew) mark nearly everything and labile
or unrelated-pair languages (Kakataibo, Kinyarwanda) mark nearly nothing,
neutralizing the contrast in opposite directions; the asymmetric type
(English, Greek) shows it directly. -/

/-- A language's verbal-markedness profile (Table 1). -/
structure LanguageProfile where
  language : String
  family : String
  /-- PC root verbal paradigms with determinable markedness. -/
  nPCParadigms : Nat
  /-- Result root verbal paradigms with determinable markedness. -/
  nResultParadigms : Nat
  /-- Percentage of PC verbal paradigms that are marked. -/
  pctPCMarked : ℚ
  /-- Percentage of result verbal paradigms that are marked. -/
  pctResultMarked : ℚ
  deriving Repr

def kakataibo : LanguageProfile :=
  ⟨"Kakataibo", "Panoan", 59, 64, 23.73, 31.25⟩
def kinyarwanda : LanguageProfile :=
  ⟨"Kinyarwanda", "Northeastern Bantu", 24, 33, 4.17, 9.09⟩
def hebrew : LanguageProfile :=
  ⟨"Hebrew (Modern)", "Semitic", 35, 42, 100, 97.62⟩
def greek : LanguageProfile :=
  ⟨"Greek (Modern)", "Indo-European", 22, 44, 59.09, 6.82⟩
def english : LanguageProfile :=
  ⟨"English", "Germanic", 43, 60, 46.51, 1.67⟩

/-- English and Greek show the overt asymmetry (44) predicts: marked PC
verbs, unmarked result verbs. -/
theorem asymmetric_type_shows_contrast :
    english.pctResultMarked < english.pctPCMarked ∧
    greek.pctResultMarked < greek.pctPCMarked := by
  refine ⟨?_, ?_⟩ <;> norm_num [english, greek]

/-- Hebrew neutralizes the contrast from above: its equipollent
root-and-template morphology marks both root classes near-categorically. -/
theorem hebrew_neutralizes_high :
    90 ≤ hebrew.pctPCMarked ∧ 90 ≤ hebrew.pctResultMarked := by
  refine ⟨?_, ?_⟩ <;> norm_num [hebrew]

/-- Kakataibo and Kinyarwanda neutralize from below: labile paradigms leave
both root classes largely unmarked (the paper's low-marking † criterion:
at most a third marked). -/
theorem labile_type_neutralizes_low :
    3 * kakataibo.pctPCMarked ≤ 100 ∧ 3 * kakataibo.pctResultMarked ≤ 100 ∧
    3 * kinyarwanda.pctPCMarked ≤ 100 ∧ 3 * kinyarwanda.pctResultMarked ≤ 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [kakataibo, kinyarwanda]

/-! ### Bridge to `EntailmentProfile.changeOfState` -/

/-- Dowty's P-Patient entailment "undergoes change of state" is the result
root entailment: profiles with `changeOfState` pattern as result roots. -/
def rootTypeFromChangeEntailment (p : EntailmentProfile) : ChangeType :=
  if p.changeOfState then .result else .propertyConcept

/-- Accomplishment objects pattern with result roots; contact-verb objects
(*kick*: no entailed change) fall on the PC side. -/
theorem result_object_has_changeOfState :
    rootTypeFromChangeEntailment accomplishmentObjectProfile = .result ∧
    rootTypeFromChangeEntailment ArgumentStructure.contactObject
      = .propertyConcept := by
  decide

/-- *die*'s subject undergoes change, so it patterns with result roots. -/
theorem die_result_pattern :
    rootTypeFromChangeEntailment
      ArgumentStructure.disappearance.subjectProfile = .result := by
  decide

/-! ### Bridge to templates and BECOME -/

/-- Result roots must combine with a template containing BECOME: the root's
change entailment is redundant with it. PC roots combine with any
template. -/
def requiresBECOME : ChangeType → Bool
  | .result => true
  | .propertyConcept => false

/-- Achievement and accomplishment templates contain BECOME; the state
template does not, so it is available only to PC roots. -/
def templateHasBECOME : Template → Bool
  | .achievement => true
  | .accomplishment => true
  | _ => false

/-- A root entailing change is associated with a BECOME template even
though the change comes from the root (§9). -/
theorem entails_change_implies_become_template (ct : ChangeType)
    (h : ct.EntailsChange) :
    requiresBECOME ct = true := by
  cases ct <;> simp_all [ChangeType.EntailsChange, requiresBECOME]

/-- A root not requiring BECOME does not entail change. -/
theorem no_become_implies_no_change (ct : ChangeType)
    (h : requiresBECOME ct = false) :
    ¬ ct.EntailsChange := by
  cases ct <;> simp_all [requiresBECOME, ChangeType.EntailsChange]

/-- BECOME templates map to the telic Vendler classes. -/
theorem become_templates_telic :
    Template.vendlerClass .achievement = .achievement ∧
    Template.vendlerClass .accomplishment = .accomplishment := ⟨rfl, rfl⟩

/-- Aspectual profile of a root's stative use: PC statives are states,
while even a result root's stative entails change. -/
def stativeAspectualProfile : ChangeType → AspectualProfile
  | .propertyConcept => stateProfile
  | .result => achievementProfile

/-- PC roots in stative use are states; result-root statives pattern as
achievements. -/
theorem root_stative_vendler :
    (stativeAspectualProfile .propertyConcept).toVendlerClass = .state ∧
    (stativeAspectualProfile .result).toVendlerClass = .achievement :=
  ⟨rfl, rfl⟩

/-! ### [embick-2004]'s adjectival structures ((8)) -/

/-- [embick-2004] posits basic statives (root with the stative head, (8a))
and result statives (root under `v_become`, (8b)); PC roots admit both,
result roots only the deverbal structure. -/
inductive AdjectivalStructure where
  /-- Simple adjective: stative head over the bare root (8a). -/
  | basicStative
  /-- Deverbal adjective: stative head over a `v_become` phrase (8b). -/
  | resultStative
  deriving DecidableEq, Repr

/-- Which roots admit the basic-stative structure (8a). -/
def admitsBasicStative : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- Admitting (8a) is equivalent to not entailing change. -/
theorem admitsBasicStative_iff_no_change (ct : ChangeType) :
    admitsBasicStative ct = true ↔ ¬ ct.EntailsChange := by
  cases ct <;> simp [admitsBasicStative, ChangeType.EntailsChange]

/-! ### Grand unification -/

/-- From the root's change entailment alone, all of the paper's
morphosyntactic predictions follow. -/
theorem grand_unification (ct : ChangeType) :
    (ct.EntailsChange →
      hasSimpleStative ct = false ∧
      verbalFormIsMarked ct = false ∧
      AgainReading.restitutive ∉ againReadings ct ∧
      requiresBECOME ct = true ∧
      admitsBasicStative ct = false ∧
      verbalMarkedness ct = .unmarked ∧
      stativeMarkedness ct = .marked) ∧
    (¬ ct.EntailsChange →
      hasSimpleStative ct = true ∧
      verbalFormIsMarked ct = true ∧
      AgainReading.restitutive ∈ againReadings ct ∧
      requiresBECOME ct = false ∧
      admitsBasicStative ct = true ∧
      verbalMarkedness ct = .marked ∧
      stativeMarkedness ct = .unmarked) := by
  cases ct <;> simp_all [
    ChangeType.EntailsChange, hasSimpleStative,
    verbalFormIsMarked, againReadings,
    requiresBECOME, admitsBasicStative,
    verbalMarkedness, stativeMarkedness]

/-- Change entailment determines markedness through the unified
`Classification`. -/
theorem root_markedness_from_change (r : Classification) :
    verbalMarkedness r.changeType = .unmarked ↔ r.changeType.EntailsChange :=
  markedness_from_semantics _

/-- Roots with the same change type behave identically regardless of
valency: markedness and statives are orthogonal to argument selection. -/
theorem same_change_same_morphosyntax (r₁ r₂ : Classification)
    (h : r₁.changeType = r₂.changeType) :
    verbalMarkedness r₁.changeType = verbalMarkedness r₂.changeType ∧
    stativeMarkedness r₁.changeType = stativeMarkedness r₂.changeType ∧
    (r₁.changeType.EntailsChange ↔ r₂.changeType.EntailsChange) := by
  rw [h]; exact ⟨rfl, rfl, Iff.rfl⟩

/-! ### Chuj root grounding ([coon-2019]) -/

open Chuj

/-- The result-root subdivision of [coon-2019]'s √TV class: shared
coordinates from `RootClass.toClassification`, with only the
change-entailment column added by the present paper. -/
def rootTV_res : Classification :=
  { RootClass.tv.toClassification with changeType := .result }

/-- The property-concept subdivision of √TV (no change entailment). -/
def rootTV_pc : Classification :=
  { RootClass.tv.toClassification with changeType := .propertyConcept }

/-- Coon's √ITV coordinates, reused unchanged. -/
def rootITV : Classification := RootClass.itv.toClassification

/-- Coon's √POS coordinates, reused unchanged. -/
def rootPOS : Classification := RootClass.pos.toClassification

/-- Chuj √TV result roots instantiate the result-root package: change
entailed, no simple stative, unmarked verb. -/
theorem chuj_tv_res_is_result_root :
    rootTV_res.changeType.EntailsChange ∧
    hasSimpleStative rootTV_res.changeType = false ∧
    verbalMarkedness rootTV_res.changeType = .unmarked :=
  ⟨trivial, rfl, rfl⟩

/-- Chuj √TV PC roots instantiate the PC package: no change entailment,
simple stative, marked verb. -/
theorem chuj_tv_pc_is_pc_root :
    ¬ rootTV_pc.changeType.EntailsChange ∧
    hasSimpleStative rootTV_pc.changeType = true ∧
    verbalMarkedness rootTV_pc.changeType = .marked :=
  ⟨id, rfl, rfl⟩

/-- The Chuj fragment witnesses cells of the valency × change-type matrix:
theme-taking roots with and without change entailment, and valency-free
property-concept roots. -/
theorem chuj_witnesses_orthogonality :
    rootTV_res.valency = {.internal} ∧ rootTV_res.changeType = .result ∧
    rootTV_pc.valency = {.internal} ∧ rootTV_pc.changeType = .propertyConcept ∧
    rootPOS.valency = ∅ ∧ rootPOS.changeType = .propertyConcept :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end BeaversEtAl2021
