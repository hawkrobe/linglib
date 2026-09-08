import Linglib.Data.Examples.DalrympleKaplan2000
import Linglib.Features.Gender.Resolve
import Linglib.Features.Person.Resolve
import Linglib.Fragments.Chichewa.Gender
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.German.Pronouns
import Linglib.Fragments.German.Verbs
import Linglib.Fragments.Slavic.Polish.Pronouns
import Linglib.Fragments.Xhosa.Basic
import Linglib.Morphology.Paradigm.Morphome
import Linglib.Studies.Shieber1986
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Bounds.Basic

/-!
# Dalrymple and Kaplan, feature indeterminacy and feature resolution (2000)

A syncretic form such as German *was* satisfies conflicting case requirements at once, and
a coordinate noun phrase has a person or gender of its own computed from those of its
conjuncts. Dalrymple and Kaplan represent both with set-valued features. An indeterminate
value is the set of atomic values the form can realize and a contextual requirement is
membership in it, so one value meets two requirements where equality against an atomic
value, whether disjoined or left unspecified, cannot; the same sets serve on the verb side,
where a syncretic agreement form imposes an indeterminate requirement that distributes to
the conjuncts of a coordinate subject. A resolving value is a set of markers, and the
person or gender of a coordination is the union of its conjuncts' sets, the least set the
two subset annotations of the coordination rule allow. Person values are subsets of {S, H},
which predicts the Fula inclusive/exclusive table and the collapsed English one and bounds
resolution at four persons; gender marker sets do the same for Hindi and Icelandic and, on
one of the paper's two accounts, for Slovene with the conjunction contributing a marker.
Resolving features are never indeterminate: they are checked by constraining equality
against a designated set, and an indeterminate one would have to be a set of sets.

We prove that an indeterminate value is a syncretism class of a paradigm, read off the
fragments for *was*, *kogo*, *set*, *kaufen* and the Xhosa and Chichewa subject prefixes;
that the two rejected alternatives fail as order theory, two atoms having no join in the
flat order, so that unification of the two verbs' requirements fails, while their join in
the set order is the union and the underspecified value is the universal set that
overgenerates; that union on marker sets is the substrate's person resolution because
profiles union, with the person hierarchy as the inclusion order of marker sets; and that
the gender generalizations follow from union, same-gender congruence from idempotence and
the need for a third gender from incomparability, with Slovene's violation located in the
conjunction's marker. Each construction is then checked against the paper's judgment.

## Implementation notes

* The syncretism class is the maximal indeterminate value a form can bear; §4.5 leaves it to
  the speaker's lexicon whether a form bears it or the disjunction of its singletons, and
  the file analyses the grammars that accept the paper's examples.
* The person of a marker set is total: the two markers give exactly the four values of the
  quadripartition, so resolution is derived from the substrate's profile grounding rather
  than checked by a table.
* The collapsed English system is stated as the tripartition's coarsened resolution, the
  study's bridge to the substrate; the paper frames §6.2 as a choice between two marker
  assignments.
* Each language's gender rules are a table over its own gender carrier, the shape of the
  substrate's `Gender.Strategy.res`, so that Slovene's same-gender clause is the failure of
  `Gender.Strategy.Congruent`.

## TODO

* The paper offers two accounts of Slovene and declines to choose; only the one on which the
  conjunction contributes `F` is formalized, and on the other coordinated neuters are neuter
  and the neuter plural verb form is what is restricted.

## References

* [M. Dalrymple and R. M. Kaplan, *Feature indeterminacy and feature resolution*
  (2000)][dalrymple-kaplan-2000]
* [A. Zaenen and L. Karttunen, *Morphological non-distinctiveness and coordination*
  (1984)][zaenen-karttunen-1984]
* [G. K. Pullum and A. M. Zwicky, *Phonological resolution of syntactic feature conflict*
  (1986)][pullum-zwicky-1986]
* [A. Groos and H. van Riemsdijk, *Matching effects in free relatives*
  (1981)][groos-van-riemsdijk-1981]
* [S. Dyła, *Across-the-board dependencies and case in Polish* (1984)][dyla-1984]
* [E. Voeltz, *Surface constraints and agreement resolution* (1971)][voeltz-1971]
* [G. G. Corbett, *Hierarchies, targets and controllers* (1983)][corbett-1983]
* [G. G. Corbett, *Resolution rules: Agreement in person, number, and gender*
  (1983)][corbett-1983b]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett and A. D. Mtenje, *Gender agreement in Chichewa* (1987)][corbett-mtenje-1987]
* [I. A. Sag, G. Gazdar, T. Wasow and S. Weisler, *Coordination and how to distinguish
  categories* (1985)][sag-gazdar-wasow-weisler-1985]
* [A. M. Zwicky, *Hierarchies of person* (1977)][zwicky-1977b]
* [R. M. Kaplan and J. Bresnan, *Lexical-functional grammar* (1982)][kaplan-bresnan-1982]
* [S. M. Shieber, *An introduction to unification-based approaches to grammar*
  (1986)][shieber-1986]
* [R. Noyer, *Features, positions, and affixes in autonomous morphological structure*
  (1992)][noyer-1992]
-/

namespace DalrympleKaplan2000

open Data.Examples Morphology

/-- The paper's judgment on `e` is the prediction `P`. -/
abbrev AcceptableIff (e : LinguisticExample) (P : Prop) : Prop := e.judgment = .acceptable ↔ P

/-- A distributive requirement on a coordinate structure holds of each conjunct ((44), (73)). -/
abbrev Distributes {α : Type*} (P : α → Prop) (s : Finset α) : Prop := ∀ f ∈ s, P f

/-- The union is the smallest set containing both, which is how the minimal model turns the
    two subset annotations of a coordination rule into union ((93), (94)). -/
theorem union_isLeast {α : Type*} [DecidableEq α] (x y : Finset α) :
    IsLeast {z | x ⊆ z ∧ y ⊆ z} (x ∪ y) :=
  ⟨⟨Finset.subset_union_left, Finset.subset_union_right⟩,
    λ _ ⟨hx, hy⟩ => Finset.union_subset hx hy⟩

/-- The intersection is the largest set contained in both, which is why an intersection
    analysis cannot be stated by minimal models (§6.5). -/
theorem inter_isGreatest {α : Type*} [DecidableEq α] (x y : Finset α) :
    IsGreatest {z | z ⊆ x ∧ z ⊆ y} (x ∩ y) :=
  ⟨⟨Finset.inter_subset_left, Finset.inter_subset_right⟩,
    λ _ ⟨hx, hy⟩ => Finset.subset_inter hx hy⟩

/-! ### Indeterminacy: set values and membership (§§3–4) -/

/-- Under equality checking no value meets two distinct requirements, whichever disjunct of
    (18) is chosen ((19)–(21)) and whatever the variable of (23) stands for ((24)). -/
theorem not_eq_and_eq_of_ne {α : Type*} {x a b : α} (h : a ≠ b) : ¬ (x = a ∧ x = b) :=
  λ ⟨ha, hb⟩ => h (ha ▸ hb)

/-- In the flat order two distinct atoms have no join, so the unification of an underspecified
    value with the two verbs' requirements fails, the transitivity argument of (24) as order
    theory. -/
theorem flat_no_join {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b) :
    Flat.unify (↑a : Flat α) ↑b = none :=
  Flat.unify_distinct_eq_none h

/-- On the UD bundle, the accusative and nominative requirements of the two verbs of (17) are
    not bounded above in the subsumption order, so Shieber's unification of them fails. -/
theorem requirements_not_compatible :
    ¬ UD.MorphFeatures.Compatible { case_ := ↑UD.Case.Acc } { case_ := ↑UD.Case.Nom } := by
  rw [← UD.MorphFeatures.compatible_iff_bddAbove]; decide

/-- Membership in a set designator is disjunction over its elements, and excludes every other
    atom ((35)). -/
theorem mem_pair_iff {α : Type*} [DecidableEq α] (x a b : α) :
    x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by simp

/-- A flat slot as a set value, a determinate commitment its singleton and no commitment, the
    underspecification of (22), the universal set; subsumption becomes reverse inclusion, so
    the flat order is the determinate fragment of the set order. -/
def toIndet : Flat Case → Finset Case
  | ⊥ => Finset.univ
  | (x : Case) => {x}

private theorem univ_ne_singleton (y : Case) : (Finset.univ : Finset Case) ≠ {y} := by
  intro h
  have hc : (Finset.univ : Finset Case).card = 1 := by rw [h, Finset.card_singleton]
  rw [Finset.card_univ] at hc
  exact absurd hc (by decide)

theorem le_iff_toIndet_superset (a b : Flat Case) : a ≤ b ↔ toIndet b ⊆ toIndet a := by
  cases a with
  | bot => exact iff_of_true bot_le (Finset.subset_univ _)
  | coe x =>
    cases b with
    | bot =>
      refine iff_of_false (Flat.not_coe_le_bot x) λ h => ?_
      exact univ_ne_singleton x (Finset.Subset.antisymm h (Finset.subset_univ _))
    | coe z => simp [toIndet, eq_comm]

open German.Pronouns in
/-- The case values of the German relative pronouns are the cells their forms realize, *wer*
    the nominative, *wem* the dative, *was* the nominative and the accusative ((26), (32)). -/
theorem german_cases :
    formCells wer (some "wer") = {Case.nom} ∧ formCells wer (some "wem") = {Case.dat} ∧
      formCells was (some "was") = {Case.nom, Case.acc} := by
  decide

open German.Pronouns in
/-- In the set order the two requirements do have a join, and it is the value of *was*, the
    minimal model of `ACC ∈ v` and `NOM ∈ v` ((28)–(31), (36)). -/
theorem was_isLeast :
    IsLeast {v | ({Case.acc} : Finset Case) ⊆ v ∧ {Case.nom} ⊆ v} (formCells was (some "was")) := by
  rw [german_cases.2.2,
    show ({Case.nom, Case.acc} : Finset Case) = {Case.acc} ∪ {Case.nom} by decide]
  exact union_isLeast _ _

open German.Pronouns in
/-- Underspecification overgenerates where the set value does not, *was* admitting no dative or
    genitive context and the universal set admitting every one (§3.2). -/
theorem underspecification_overgenerates :
    Case.dat ∈ toIndet ⊥ ∧ Case.dat ∉ formCells was (some "was") ∧
      Case.gen ∉ formCells was (some "was") := by
  decide

open German.Pronouns in
/-- *was* meets the accusative requirement of *gegessen* and the nominative one of *übrig war*
    ((28), (30)), and *wem* meets *vertraust* but not *muss* ((32), (33)). -/
theorem free_relatives :
    AcceptableIff Examples.ex_17
        (Case.acc ∈ formCells was (some "was") ∧ Case.nom ∈ formCells was (some "was")) ∧
      AcceptableIff Examples.ex_32
        (Case.dat ∈ formCells wer (some "wem") ∧ Case.nom ∈ formCells wer (some "wem")) := by
  decide

open Polish.Pronouns in
/-- Fronted *kogo* meets the accusative of *lubi* and the genitive of *nienawidzi* in both
    conjuncts ((40), (46)), and *co* does not ((41)). -/
theorem polish_coordination :
    AcceptableIff Examples.ex_40
        (Case.acc ∈ formCells kto (some "kogo") ∧ Case.gen ∈ formCells kto (some "kogo")) ∧
      AcceptableIff Examples.ex_41
        (Case.acc ∈ formCells co (some "co") ∧ Case.gen ∈ formCells co (some "co")) := by
  decide

open English.Predicates.Verbal in
/-- The cells *set* realizes are the base, the past and the past participle; the paper's VFORM
    value lists the two nonfinite ones, the past being a TENSE value ((50)). -/
theorem set_cells :
    formCells set_.realize "set" = {VerbEntry.Cell.base, .past, .pastParticiple} := by
  decide

open English.Predicates.Verbal in
/-- *will* requires the base form and *have* the past participle of the shared verb; *set*
    realizes both cells ((49), (50)) and neither form of *clarify* does ((47), (48)). -/
theorem will_and_have :
    AcceptableIff Examples.ex_49 (VerbEntry.Cell.base ∈ formCells set_.realize "set" ∧
        VerbEntry.Cell.pastParticiple ∈ formCells set_.realize "set") ∧
      AcceptableIff Examples.ex_47 (VerbEntry.Cell.base ∈ formCells clarify.realize "clarify" ∧
        VerbEntry.Cell.pastParticiple ∈ formCells clarify.realize "clarify") ∧
      AcceptableIff Examples.ex_48
        (VerbEntry.Cell.base ∈ formCells clarify.realize "clarified" ∧
          VerbEntry.Cell.pastParticiple ∈ formCells clarify.realize "clarified") := by
  decide

/-- The subject genders an indeterminate Xhosa verb such as *zibomvu* 'are red' agrees with are
    those whose plural class takes the prefix *zi-*, 7/8 and 9/10 ((54), (56)); the fragment's
    own account of *zi-* with non-human conjuncts is default agreement, a rival reading. -/
theorem zibomvu_genders :
    formCells Xhosa.Gender.plSubjPrefix "zi" = {Xhosa.Gender.genderD, .genderE} := by
  decide

/-- Distributed to the conjuncts, *zibomvu*'s requirement is met by *izandla* (7/8) and
    *iindlebe* (9/10) ((54)–(56)), while a determinate class-6 or class-8 requirement is not
    met by both *igqira* (5/6) and *isanuse* (7/8) ((53)). -/
theorem xhosa_coordination :
    AcceptableIff Examples.ex_54
        (Distributes (· ∈ formCells Xhosa.Gender.plSubjPrefix "zi")
          {Xhosa.Gender.genderD, .genderE}) ∧
      AcceptableIff Examples.ex_53a (Distributes (λ g : Xhosa.Gender => g.pluralClass = .cl6)
          {Xhosa.Gender.genderC, .genderD}) ∧
      AcceptableIff Examples.ex_53b (Distributes (λ g : Xhosa.Gender => g.pluralClass = .cl8)
          {Xhosa.Gender.genderC, .genderD}) := by
  decide

open Chichewa.Gender in
/-- The Chichewa plural prefix *a-* serves genders 1/2 and 5/6, so *a-kubvunda* and *a-li* agree
    with *ma-lalanje* and *ma-samba*, with *a-mphaka* and *a-galu*, and with their mixture
    ((57)–(59)). -/
theorem chichewa_coordination :
    AcceptableIff Examples.ex_57
        (Distributes (· ∈ formCells Value.plSubjPrefix .a) {lalanje.gender, samba.gender}) ∧
      AcceptableIff Examples.ex_58
        (Distributes (· ∈ formCells Value.plSubjPrefix .a) {mphaka.gender, galu.gender}) ∧
      AcceptableIff Examples.ex_59
        (Distributes (· ∈ formCells Value.plSubjPrefix .a) {mphaka.gender, lalanje.gender}) := by
  decide

open German.Verbs in
/-- *kaufen* is the first and the third plural and *kauft* the second plural and the third
    singular, so the persons *kaufen* agrees with are 1 and 3 ((62)) and *kauft* imposes the
    correlated requirement of (65). -/
theorem kaufen_cells :
    formCells kaufen (some "kaufen") = {(Person.first, Number.plural), (.third, .plural)} ∧
      formCells kaufen (some "kauft") = {(Person.second, Number.plural), (.third, .singular)} := by
  decide

open German.Verbs in
/-- Right-node-raised *kaufen* is satisfied by first-plural *wir* and third-plural *die Müllers*
    ((61), (63)), and *kauft* by second-plural *ihr* and third-singular *Franz* ((64)), the
    correlated features distributing as one cell each. -/
theorem right_node_raising :
    AcceptableIff Examples.ex_61 (Distributes (· ∈ formCells kaufen (some "kaufen"))
        {(Person.first, Number.plural), (.third, .plural)}) ∧
      AcceptableIff Examples.ex_64 (Distributes (· ∈ formCells kaufen (some "kauft"))
        {(Person.second, Number.plural), (.third, .singular)}) := by
  decide

/-! ### Person resolution (§6) -/

/-- The person markers, the paper's S and H ((77), §6.1). -/
inductive Marker where
  | speaker
  | hearer
  deriving DecidableEq, Repr, Fintype

/-- A person value as a set of markers. -/
abbrev PersonSet := Finset Marker

/-- The person of a marker set, first exclusive with the speaker alone, first inclusive with
    both, second with the hearer alone, third with neither ((87)). -/
def person (s : PersonSet) : Person :=
  if Marker.speaker ∈ s then (if Marker.hearer ∈ s then .firstInclusive else .firstExclusive)
  else if Marker.hearer ∈ s then .second else .third

/-- Two markers give exactly the four persons of the quadripartition, so no language resolves
    more than four (§6.3). -/
theorem person_injective : Function.Injective person := by decide

/-- Two markers give four values. -/
theorem card_personSet : Fintype.card PersonSet = 4 := by decide

theorem person_ne_zero (s : PersonSet) : person s ≠ .zero := by
  unfold person; split_ifs <;> simp

/-- A marker set is a discourse-role profile, the speaker marker speaker inclusion and the hearer
    marker addressee inclusion. -/
theorem toProfile_person (s : PersonSet) :
    (person s).toProfile =
      some ⟨decide (Marker.speaker ∈ s), some (decide (Marker.hearer ∈ s))⟩ := by
  unfold person; split_ifs with hS hH hH <;> simp [Person.toProfile, hS, hH]

private theorem resolve_ne_zero {a b : Person} (ha : a ≠ .zero) (hb : b ≠ .zero) :
    Person.resolve a b ≠ .zero := by
  revert a b; decide

/-- Resolution is union ((77)): the substrate resolves persons by the disjunction of their role
    profiles, the referential reading the paper starts from and weakens in §6.2, and the profile
    of a union of marker sets is that disjunction, so `Person.resolve` commutes with `∪`; the
    Fula table is the instance ((78), (88)). -/
theorem resolve_person (p q : PersonSet) :
    Person.resolve (person p) (person q) = person (p ∪ q) := by
  refine Person.toProfile_injOn _ _ (resolve_ne_zero (person_ne_zero p) (person_ne_zero q))
    (person_ne_zero _) ?_
  rw [Person.resolve_profile _ _ (person_ne_zero p) (person_ne_zero q), toProfile_person,
    toProfile_person, toProfile_person]
  by_cases hS : Marker.speaker ∈ p <;> by_cases hS' : Marker.speaker ∈ q <;>
    by_cases hH : Marker.hearer ∈ p <;> by_cases hH' : Marker.hearer ∈ q <;>
    simp [Person.Profile.or, hS, hS', hH, hH']

/-- The Fula examples, *you and Bill* second, *Bill and George* third, *you and I* and *you and
    Bill and I* first inclusive, *Bill and I* and *Bill and us* first exclusive ((81)–(86)). -/
theorem fula :
    AcceptableIff Examples.ex_81 (person ({.hearer} ∪ ∅) = .second) ∧
      AcceptableIff Examples.ex_82 (person (∅ ∪ ∅) = .third) ∧
      AcceptableIff Examples.ex_83 (person ({.hearer} ∪ {.speaker}) = .firstInclusive) ∧
      AcceptableIff Examples.ex_84 (person ({.hearer} ∪ ∅ ∪ {.speaker}) = .firstInclusive) ∧
      AcceptableIff Examples.ex_85 (person (∅ ∪ {.speaker}) = .firstExclusive) ∧
      AcceptableIff Examples.ex_86 (person (∅ ∪ {.speaker}) = .firstExclusive) := by
  decide

/-- The encoding of languages without the inclusive/exclusive contrast, every first person the
    inclusive's set, the second the hearer, the third empty ((91)). -/
def english : Person → PersonSet
  | .first => {.speaker, .hearer}
  | .second => {.hearer}
  | _ => ∅

/-- Union under this encoding is the tripartition's coarsened resolution ((92)). -/
theorem english_table :
    ∀ p q : Person, p ∈ Person.System.tripartition.values →
      q ∈ Person.System.tripartition.values →
      english (Person.System.tripartition.resolve p q) = english p ∪ english q := by
  decide

/-- Under this encoding the person hierarchy 1 < 2 < 3 is the reverse inclusion of marker sets,
    so union picks the lowest-ranked conjunct, the hierarchy of Zwicky and Corbett (fn. 12)
    as a corollary of union, as the substrate derives it from referent union. -/
theorem english_subset_iff_rank :
    ∀ p q : Person, p ∈ Person.System.tripartition.values →
      q ∈ Person.System.tripartition.values →
      (english q ⊆ english p ↔ p.hierarchyRank ≤ q.hierarchyRank) := by
  decide

/-- *José y yo* and *ja a ty* take first-plural agreement and *José y tú* second-plural, the
    minimal set above `{}` and `{H}` being `{H}`, so the second-plural verb's constraining
    equation holds and the first-plural one fails ((71), (76), (95)–(99)). -/
theorem spanish_slovak :
    AcceptableIff Examples.ex_71 (english .third ∪ english .first = {.speaker, .hearer}) ∧
      AcceptableIff Examples.ex_76 (english .first ∪ english .second = {.speaker, .hearer}) ∧
      AcceptableIff Examples.ex_95 (english .third ∪ english .second = {.hearer}) ∧
      english .third ∪ english .second ≠ {.speaker, .hearer} := by
  decide

/-- Sag, Gazdar, Wasow and Weisler's marker sets, combined by intersection ((100)). -/
def sag : Person → PersonSet
  | .first => ∅
  | .second => {.speaker}
  | .third => {.speaker, .hearer}
  | _ => ∅

/-- Their assignment is the De Morgan dual of (91), each set the complement of the union
    analysis's, so it succeeds on English exactly where union does ((101)–(103)). -/
theorem sag_eq_compl :
    ∀ p : Person, p ∈ Person.System.tripartition.values → sag p = (english p)ᶜ := by
  decide

/-- Intersection with the empty first-person set cannot tell *you and I* from *Bill and I*, so
    Fula's inclusive/exclusive contrast is underivable, where union keeps them apart ((101)
    against (88)). -/
theorem sag_intersection :
    sag .first ∩ sag .second = sag .first ∩ sag .third ∧
      person ({.speaker} ∪ {.hearer}) ≠ person ({.speaker} ∪ ∅) := by
  decide

/-- Any union analysis has an intersection dual over complements, markers read as absences
    ((102), (103)). -/
theorem compl_union (p q : PersonSet) : (p ∪ q)ᶜ = pᶜ ∩ qᶜ :=
  Finset.compl_union p q

/-! ### Gender resolution (§7) -/

/-- Gender markers; each language assigns its genders subsets of them. -/
inductive GenderMarker where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- A gender value as a set of markers. -/
abbrev GenderSet := Finset GenderMarker

/-- Whenever an injective marker assignment reproduces a language's resolution rules by union,
    same-gender coordination resolves to that gender, the generalization (105b), because union
    is idempotent. -/
theorem congruent_of_union {G : Type*} {mark : G → GenderSet} (hinj : Function.Injective mark)
    {rules : G → G → Option G} (h : ∀ a b, (rules a b).map mark = some (mark a ∪ mark b)) :
    Gender.Strategy.Congruent rules := by
  intro g
  have hg := h g g
  rw [Finset.union_self] at hg
  cases hr : rules g g with
  | none => simp [hr] at hg
  | some g' =>
    simp only [hr, Option.map_some, Option.some.injEq] at hg
    exact congrArg some (hinj hg)

/-- A mixed coordination resolves to one of its conjuncts' genders exactly when their marker
    sets are nested ((105c)); otherwise their join is a third gender's set. -/
theorem union_mem_pair_iff {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∪ t = s ∨ s ∪ t = t) ↔ (t ⊆ s ∨ s ⊆ t) := by
  rw [← Finset.sup_eq_union, sup_eq_left, sup_eq_right]

/-- The Hindi genders. -/
inductive HindiGender where
  | masculine
  | feminine
  deriving DecidableEq, Repr, Fintype

/-- Corbett's Hindi resolution, masculine if any conjunct is and feminine otherwise
    ((109), (110)). -/
def hindiRules : HindiGender → HindiGender → Option HindiGender
  | .feminine, .feminine => some .feminine
  | _, _ => some .masculine

/-- The marker assignment for Hindi ((111)). -/
def hindi : HindiGender → GenderSet
  | .masculine => {.masc}
  | .feminine => ∅

theorem hindi_injective : Function.Injective hindi := by decide

/-- Union of the assigned sets reproduces the Hindi rules ((112)). -/
theorem hindi_union : ∀ a b, (hindiRules a b).map hindi = some (hindi a ∪ hindi b) := by
  decide

theorem hindi_congruent : Gender.Strategy.Congruent hindiRules :=
  congruent_of_union hindi_injective hindi_union

/-- The feminine set is nested in the masculine, so the mixed coordination is masculine and
    Hindi needs no third gender ((105c), (110)). -/
theorem hindi_nested : hindi .feminine ⊆ hindi .masculine := by decide

/-- The Hindi examples, dog and cat masculine, girl and mother feminine ((107), (108),
    (113)). -/
theorem hindi_examples :
    AcceptableIff Examples.ex_107 (hindi .masculine ∪ hindi .feminine = hindi .masculine) ∧
      AcceptableIff Examples.ex_108 (hindi .feminine ∪ hindi .feminine = hindi .feminine) := by
  decide

/-- The Icelandic genders. -/
inductive IcelandicGender where
  | masculine
  | feminine
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- Corbett's Icelandic resolution, like genders preserved and any mixture neuter
    ((114), (118)). -/
def icelandicRules (a b : IcelandicGender) : Option IcelandicGender :=
  some (if a = b then a else .neuter)

/-- The marker assignment for Icelandic ((119)). -/
def icelandic : IcelandicGender → GenderSet
  | .masculine => {.masc}
  | .feminine => {.fem}
  | .neuter => {.masc, .fem}

theorem icelandic_injective : Function.Injective icelandic := by decide

/-- Union of the assigned sets reproduces the Icelandic rules ((120)). -/
theorem icelandic_union :
    ∀ a b, (icelandicRules a b).map icelandic = some (icelandic a ∪ icelandic b) := by
  decide

/-- Same-gender coordination resolves to that gender in Icelandic ((105b)). -/
theorem icelandic_congruent : Gender.Strategy.Congruent icelandicRules :=
  congruent_of_union icelandic_injective icelandic_union

/-- Masculine and feminine are incomparable, so their join is neither and a third gender must
    carry it, the neuter's set being that join ((105c), (119)). -/
theorem icelandic_needs_neuter :
    ¬ icelandic .masculine ⊆ icelandic .feminine ∧ ¬ icelandic .feminine ⊆ icelandic .masculine ∧
      icelandic .masculine ∪ icelandic .feminine = icelandic .neuter := by
  decide

/-- The Icelandic examples, boy and girl, man and baby, ewe and lamb all neuter
    ((115)–(117)). -/
theorem icelandic_examples :
    AcceptableIff Examples.ex_115 (icelandic .masculine ∪ icelandic .feminine = icelandic .neuter) ∧
      AcceptableIff Examples.ex_116 (icelandic .masculine ∪ icelandic .neuter = icelandic .neuter) ∧
      AcceptableIff Examples.ex_117
        (icelandic .feminine ∪ icelandic .neuter = icelandic .neuter) := by
  decide

/-- The Slovene genders. -/
inductive SloveneGender where
  | masculine
  | feminine
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- Corbett's Slovene agreement pattern, feminine if all conjuncts are and masculine otherwise,
    two neuters included ((121), (124)). -/
def sloveneRules : SloveneGender → SloveneGender → Option SloveneGender
  | .feminine, .feminine => some .feminine
  | _, _ => some .masculine

/-- The marker assignment for Slovene ((122)). -/
def slovene : SloveneGender → GenderSet
  | .masculine => {.fem, .neut}
  | .feminine => {.fem}
  | .neuter => {.neut}

/-- With the conjunction contributing the feminine marker ((126)), union of the assigned sets
    reproduces the Slovene pattern ((127)). -/
theorem slovene_union :
    ∀ a b, (sloveneRules a b).map slovene = some (slovene a ∪ slovene b ∪ {.fem}) := by
  decide

/-- The Slovene pattern violates the generalization (105b), two neuters resolving masculine
    ((123)), and the violation is the conjunction's marker, since without it the neuter's set
    is idempotent. -/
theorem slovene_not_congruent :
    ¬ Gender.Strategy.Congruent sloveneRules ∧
      slovene .neuter ∪ slovene .neuter ∪ {.fem} ≠ slovene .neuter ∧
      slovene .neuter ∪ slovene .neuter = slovene .neuter := by
  unfold Gender.Strategy.Congruent; decide

/-- The tree and the nest take masculine agreement ((123)). -/
theorem slovene_example :
    AcceptableIff Examples.ex_123
      (slovene .neuter ∪ slovene .neuter ∪ {.fem} = slovene .masculine) := by
  decide

/-! ### Resolving features are not indeterminate (§8) -/

/-- Hindi *wah* is masculine or feminine by a wide-scope disjunction of two determinate
    specifications ((140)); an indeterminate gender would instead be this set of sets, on
    which union does not resolve. -/
def wah : Finset GenderSet := {{.masc}, ∅}

/-- One disjunct serves each single agreement ((141)) and no disjunct serves both constraining
    equations at once ((128)), the equations checking the whole set ((113)). -/
theorem wah_examples :
    AcceptableIff Examples.ex_141a (∃ v ∈ wah, v = {GenderMarker.masc}) ∧
      AcceptableIff Examples.ex_141b (∃ v ∈ wah, v = ∅) ∧
      AcceptableIff Examples.ex_128 (∃ v ∈ wah, v = {GenderMarker.masc} ∧ v = ∅) := by
  decide

end DalrympleKaplan2000
