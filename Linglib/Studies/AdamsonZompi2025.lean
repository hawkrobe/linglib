import Linglib.Syntax.Agreement.PersonCaseConstraint
import Linglib.Features.Person.Resolve
import Linglib.Fragments.Italian.Pronouns
import Linglib.Fragments.Spanish.Pronouns
import Linglib.Fragments.German.Pronouns
import Linglib.Studies.Deal2024
import Linglib.Studies.CoonKeine2021
import Linglib.Data.Examples.AdamsonZompi2025

/-!
# Polite pronouns and the person-case constraint

The Italian polite pronoun LEI is formally the third person feminine singular — it takes third
person verbal agreement, binds the reflexive *si*, orders as a third person clitic and triggers
obligatory feminine participle agreement — yet it refers to the addressee, and in a ditransitive
clitic cluster it patterns with the second person: LEI as dative over a third person accusative is
fine, while a third person dative over accusative LEI is rejected exactly as a second person
accusative is. Adamson and Zompì give polite pronouns two person values, an uninterpretable one
read by agreement and an interpretable one read at LF, and argue that the person-case constraint
reads the interpretable one. The file states a person restriction over a person valuation of
pronoun entries (`Licit`); the agreement valuation `Morphosyntactic` and the LF valuation
`Syntacticosemantic` read the fragments' `person` and `interpretablePerson`. The two coincide on
ordinary pronouns (`morphosyntactic_iff_of_ordinary`), and every agreement-keyed restriction
treats LEI as *lei* while every interpretation-keyed one treats it as *tu*
(`morphosyntactic_lei_formal`, `syntacticosemantic_lei_formal`). On the Weak and Strong
P-Constraint grammars the interpretable valuation bans a third person dative over accusative LEI
where the agreement valuation licenses it (`lei_accusative`), as do the interaction–satisfaction
and feature-gluttony accounts run over agreement person (`deal_licenses_lei`,
`gluttony_licenses_lei`). The Fancy Constraint of *faire*-infinitive causatives gives the same
cells with the causee as applied argument (`fancy_constraint`); imposters, which carry no
interpretable second person, sit in the licit third-over-third cell; and coordination resolves LEI
to second person on its interpretable value and to third on its agreement value, as an imposter
resolves on both (`resolved_person`).

The prediction for other languages is that a third person addressee-referring pronoun in a
PCC language shows the effect, as Spanish USTED and German SIE do (`usted_accusative`,
`sie_accusative`); number is irrelevant, since `Licit` reads person alone. The German
assumed-identity restriction, which syncretism ameliorates, is instead an exponence effect on
agreement features, and there SIE behaves as third person plural: against a third plural subject it
does not glutton the person probe where second plural *ihr* does, and a singular subject gluttons
the number probe against it (`assumed_identity`). Left open, as in the paper, is the rejection by
some Weak-PCC speakers of a first person dative over accusative LEI, which the Weak grammar
licenses (`first_dative_lei`). The Person Licensing Condition, the clitic logophoric restriction,
and the rival representations of polite pronouns by impoverishment or by unmarked-value
recruitment are discussed by the paper without a formal counterpart here.

## References

* [adamson-zompi-2025]
* [pancheva-zubizarreta-2018]
* [deal-2024]
* [coon-keine-2021]
* [bejar-rezac-2003]
* [rezac-2011]
* [ackema-neeleman-2018]
* [wang-r-2023]
* [charnavel-mateu-2015]
* [adamson-anagnostopoulou-2025]
* [postal-1989]
-/

namespace AdamsonZompi2025

open PCC Italian.Pronouns

/-! ### Person restrictions over a person valuation -/

/-- `R` licenses the dative–accusative pair `dat`, `acc` under the person valuation `person`. -/
def Licit (R : Person → Person → Prop) (person : PersonalPronoun → Option Person)
    (dat acc : PersonalPronoun) : Prop :=
  ∃ p q, person dat = some p ∧ person acc = some q ∧ R p q

instance (R : Person → Person → Prop) [DecidableRel R]
    (person : PersonalPronoun → Option Person) (dat acc : PersonalPronoun) :
    Decidable (Licit R person dat acc) := by
  unfold Licit; infer_instance

/-- The morphosyntactic prediction: `R` reads agreement person. -/
abbrev Morphosyntactic (R : Person → Person → Prop) := Licit R (·.person)

/-- The syntacticosemantic prediction: `R` reads interpretable person. -/
abbrev Syntacticosemantic (R : Person → Person → Prop) :=
  Licit R PersonalPronoun.interpretablePerson

variable {R : Person → Person → Prop} {dat acc : PersonalPronoun}

/-- The two predictions coincide on pronouns whose referential person is not set. -/
theorem morphosyntactic_iff_of_ordinary (hd : dat.referentialPerson = none)
    (ha : acc.referentialPerson = none) :
    Morphosyntactic R dat acc ↔ Syntacticosemantic R dat acc := by
  simp [Licit, hd, ha]

/-- Every restriction reading agreement person treats LEI as *lei*. -/
theorem morphosyntactic_lei_formal :
    (Morphosyntactic R dat lei_formal ↔ Morphosyntactic R dat lei) ∧
      (Morphosyntactic R lei_formal acc ↔ Morphosyntactic R lei acc) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Every restriction reading interpretable person treats LEI as *tu*. -/
theorem syntacticosemantic_lei_formal :
    (Syntacticosemantic R dat lei_formal ↔ Syntacticosemantic R dat tu) ∧
      (Syntacticosemantic R lei_formal acc ↔ Syntacticosemantic R tu acc) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! ### Italian -/

/-- The Italian grammars: Weak for most speakers, Strong for those rejecting 1>2 and 2>1. -/
def grammars : List Grammar := [weakGrammar, strongGrammar]

/-- Second over third and third over third are licit and third over second is not, on either
valuation and either grammar. -/
theorem baseline : ∀ g ∈ grammars,
    Syntacticosemantic (IsLicit g) tu lei ∧ Syntacticosemantic (IsLicit g) lui lei ∧
      ¬ Syntacticosemantic (IsLicit g) lui tu := by
  decide

/-- LEI as dative over a third person accusative is licit on both valuations. -/
theorem lei_dative : ∀ g ∈ grammars,
    Morphosyntactic (IsLicit g) lei_formal lei ∧
      Syntacticosemantic (IsLicit g) lei_formal lei := by
  decide

/-- A third person dative over accusative LEI is licensed on agreement person and banned on
interpretable person. -/
theorem lei_accusative : ∀ g ∈ grammars,
    Morphosyntactic (IsLicit g) lui lei_formal ∧
      ¬ Syntacticosemantic (IsLicit g) lui lei_formal := by
  decide

/-- The interaction–satisfaction grammars, read over agreement person, license accusative LEI. -/
theorem deal_licenses_lei : ∀ g ∈ [Deal2024.weak, Deal2024.strong],
    Morphosyntactic (Deal2024.isLicit g · · = true) lui lei_formal := by
  decide

/-- Feature gluttony, read over agreement person, licenses accusative LEI: a third person dative
and a third person accusative do not glutton the Weak probe. -/
theorem gluttony_licenses_lei :
    Morphosyntactic (λ p q => ¬ CoonKeine2021.PCCViolation CoonKeine2021.weakProbe false p q)
      lui lei_formal := by
  decide

/-- The Fancy Constraint with a third person causee as applied argument: a third person
accusative is licit, second person and LEI are not. -/
theorem fancy_constraint :
    Syntacticosemantic (IsLicit weakGrammar) lui lei ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) lui tu ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) lui lei_formal := by
  decide

/-- Coordinated with a third person, LEI resolves to second person on its interpretable value and
to third on its agreement value. -/
theorem resolved_person :
    lei_formal.interpretablePerson.map (Person.resolve · .third) = some .second ∧
      lei_formal.person.map (Person.resolve · .third) = some .third :=
  ⟨rfl, rfl⟩

/-- A first person dative over accusative LEI is licit on the Weak grammar and banned on the Strong
one, exactly as over *ti*; some Weak speakers nonetheless reject it. -/
theorem first_dative_lei :
    Syntacticosemantic (IsLicit weakGrammar) io lei_formal ∧
      ¬ Syntacticosemantic (IsLicit strongGrammar) io lei_formal := by
  decide

/-! ### Spanish and German -/

/-- USTED as dative over a third person accusative is licit; a third person dative over
accusative USTED is not. -/
theorem usted_accusative :
    Syntacticosemantic (IsLicit weakGrammar) Spanish.Pronouns.usted Spanish.Pronouns.el ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) Spanish.Pronouns.el Spanish.Pronouns.usted := by
  decide

/-- A third person dative over accusative SIE is banned where over third plural *sie* it is
licit. -/
theorem sie_accusative :
    Syntacticosemantic (IsLicit weakGrammar) German.Pronouns.er German.Pronouns.sie_pl ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) German.Pronouns.er
          German.Pronouns.sie_polite := by
  decide

open CoonKeine2021 in
/-- Assumed identity under a third plural subject: SIE, entering with its agreement person, does
not glutton the person probe where second plural *ihr* does; a singular subject gluttons the
number probe against plural SIE. -/
theorem assumed_identity :
    (∀ p ∈ German.Pronouns.sie_polite.person,
      ¬ Gluttonous Goal.personSegments weakProbe [dpPl .third, dpPl p]) ∧
      (∀ p ∈ German.Pronouns.ihr.person,
        Gluttonous Goal.personSegments weakProbe [dpPl .third, dpPl p]) ∧
      Gluttonous Goal.numberSegments (numberProbe weakProbe) [dp .third, dpPl .third] := by
  decide

end AdamsonZompi2025
