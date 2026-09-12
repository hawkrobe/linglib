import Linglib.Syntax.Agreement.PersonCaseConstraint
import Linglib.Syntax.Minimalist.Phi.Geometry
import Linglib.Features.Logophoricity
import Linglib.Features.Person.Decomposition
import Linglib.Fragments.Italian.Pronouns
import Linglib.Fragments.Spanish.Clitics

/-!
# Pancheva and Zubizarreta (2018): The Person Case Constraint

This file formalizes the predictions of the P-Constraint of [pancheva-zubizarreta-2018], the
proposal that Person Case Constraint effects are the syntactic encoding of perspective: an
interpretable person feature on the applicative head marks the indirect object as the
point-of-view center of its domain, and a clitic combination is licit exactly when selecting
the indirect object as that center satisfies the constraint (`ApplDomain`,
`PConstraintSatisfied`, `isLicit_iff_pConstraint`). The Person Hierarchy 1 > 2 > 3 is derived
from the count of positive person features rather than stipulated
(`personHierarchy_from_features`). The constraint's four parameters, the prominence
threshold, the domain of application, P-Uniqueness, and P-Primacy, generate the five attested
varieties, strong, ultra-strong, weak, super-strong, and me-first, together with three
predicted ones, each checked against the paper's examples (`strong_predictions` and its
siblings, `french_strong_examples` and its siblings), and the attested varieties are ordered
by containment of their licit sets (`strong_le_ultra`, `ultra_le_weak`, `super_le_strong`).
The three prominence values correspond to the logophoric roles pivot, self, and source of
[sells-1987] (`prominenceToSellsRole`).

## Implementation notes

The grammars and the licitness predicate live in `Syntax/Agreement/PersonCaseConstraint`.
The Italian and Spanish clitic combinations are read off the Fragments, the French, Catalan,
Kambera, and Bulgarian ones off the parameter settings, since no clitic Fragment exists for
those languages. The paper's separation of the Clitic Logophoric Restriction from the PCC,
against the unification proposed by [charnavel-mateu-2015], the two phenomena sharing only
the point-of-view marking on the applicative head, is not represented: the restriction is a
semantic constraint outside this model.

## TODO

The substrate's P-Primacy checks only the indirect object's [+author], so the ultra-strong
grammar licenses the ⟨1, 1⟩ combination that the descriptive statement (14d) bans
(`ultra_one_one_licensed`); the paper does not walk the mechanism through that cell.

## References

* [pancheva-zubizarreta-2018]
* [sells-1987]
* [charnavel-mateu-2015]
-/

namespace PanchevaZubizarreta2018

open PCC

/-! ### The applicative domain -/

/-- The applicative phase: the indirect object introduced by Appl, the direct object inside
VP, and the argument selected as point-of-view center. -/
structure ApplDomain where
  io : Person
  do_ : Person
  povCenter : Person
  deriving DecidableEq

/-- The P-Constraint over an Appl domain: either the domain is exempt, or the indirect object
is the point-of-view center, satisfies the prominence threshold, and P-Uniqueness holds or
P-Primacy rescues it. -/
def PConstraintSatisfied (g : Grammar) (a : ApplDomain) : Prop :=
  DomainExempt g a.io a.do_ ∨
    (a.povCenter = a.io ∧ IOSatisfiesProminence g a.io a.do_ ∧
      (g.uniqueness → UniquenessSatisfied g a.do_ ∨ PrimacyRescues g a.io))

instance (g : Grammar) (a : ApplDomain) : Decidable (PConstraintSatisfied g a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A clitic combination is licit exactly when the domain with the indirect object as
point-of-view center satisfies the P-Constraint: the parametric clauses are the conditions on
that selection, the only felicitous derivation being the one in which Appl agrees with the
argument it introduces (§4.5). -/
theorem isLicit_iff_pConstraint (g : Grammar) (io do_ : Person) :
    IsLicit g io do_ ↔ PConstraintSatisfied g ⟨io, do_, io⟩ := by
  constructor
  · rintro (h | ⟨hp, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hp, hr⟩
  · rintro (h | ⟨_, hp, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hp, hr⟩

/-! ### The Person Hierarchy -/

/-- The number of positive features in a person decomposition: first person bears proximate,
participant, and author, second person two of them, third person none (11). -/
def positiveFeatureCount (dp : Minimalist.DecomposedPerson) : ℕ :=
  (if dp.hasProximate then 1 else 0) + (if dp.hasParticipant then 1 else 0) +
    (if dp.hasAuthor then 1 else 0)

/-- The Person Hierarchy is derived: the prominence order coincides with the order by count of
positive features (§2.1). -/
theorem personHierarchy_from_features (p q : Person) :
    p.prominence ≤ q.prominence ↔
      positiveFeatureCount (Minimalist.decomposePerson p) ≤
        positiveFeatureCount (Minimalist.decomposePerson q) := by
  cases p <;> cases q <;> decide

/-! ### The varieties (§4) -/

/-- Strong PCC (14a): the direct object must be third person. -/
theorem strong_predictions :
    licitFinset strongGrammar = {(.first, .third), (.second, .third), (.third, .third)} := by
  decide

/-- Ultra-strong PCC (14d): P-Primacy lets a first-person indirect object rescue a local
direct object, so ⟨1, 2⟩ is licit and ⟨2, 1⟩ is not. -/
theorem ultra_predictions :
    licitFinset ultraStrongGrammar =
      {(.first, .first), (.first, .second), (.first, .third), (.second, .third),
        (.third, .third)} := by
  decide

/-- Weak PCC (14b): without P-Uniqueness any local indirect object licenses any direct object;
only a third-person indirect object with a local direct object is banned. -/
theorem weak_predictions :
    licitFinset weakGrammar =
      {(.first, .first), (.first, .second), (.first, .third), (.second, .first),
        (.second, .second), (.second, .third), (.third, .third)} := by
  decide

/-- Super-strong PCC (14e): the indirect object must be local and the direct object third
person. -/
theorem super_predictions :
    licitFinset superStrongGrammar = {(.first, .third), (.second, .third)} := by decide

/-- Me-first PCC (14c): a first-person direct object needs a first-person indirect object,
and the restricted domain exempts every combination without a first-person argument;
⟨1, 1⟩ falls to P-Uniqueness. -/
theorem mefirst_predictions :
    licitFinset meFirstGrammar =
      {(.first, .second), (.first, .third), (.second, .second), (.second, .third),
        (.third, .second), (.third, .third)} := by
  decide

/-- The first predicted variety (32a): [+participant] prominence with P-Primacy. -/
theorem pg1_predictions :
    licitFinset pg1Grammar =
      {(.first, .first), (.first, .second), (.first, .third), (.second, .third)} := by
  decide

/-- The second predicted variety (32b): [+participant] prominence without P-Uniqueness. -/
theorem pg2_predictions :
    licitFinset pg2Grammar =
      {(.first, .first), (.first, .second), (.first, .third), (.second, .first),
        (.second, .second), (.second, .third)} := by
  decide

/-- The third predicted variety (33): [+author] prominence over an unrestricted domain, so
only a first-person indirect object licenses, and P-Uniqueness then excludes ⟨1, 1⟩. -/
theorem pg3_predictions :
    licitFinset pg3Grammar = {(.first, .second), (.first, .third)} := by decide

/-- Restricting the domain to applicatives with a participant argument while setting the
threshold to [+participant] yields a grammar whose licit set is the strong PCC's (§4.5); the
paper locates the residual difference in Clitic Logophoric Restriction effects on
third-person combinations, outside this model. -/
theorem restricted_participant_surfaces_as_strong :
    licitFinset { prominence := .participant, restrictedDomain := true } =
      licitFinset strongGrammar := by
  decide

/-! ### Containment among the attested varieties (§4.5) -/

/-- Activating P-Primacy only enlarges the licit region. -/
theorem strong_le_ultra : strongGrammar ≤ ultraStrongGrammar := by decide

/-- Dropping P-Uniqueness enlarges it further. -/
theorem ultra_le_weak : ultraStrongGrammar ≤ weakGrammar := by decide

theorem strong_le_weak : strongGrammar ≤ weakGrammar := strong_le_ultra.trans ultra_le_weak

/-- The [+participant] threshold of the super-strong variety is stricter than the
[+proximate] threshold of the strong one. -/
theorem super_le_strong : superStrongGrammar ≤ strongGrammar := by decide

/-! ### Logophoric roles (§6.2) -/

/-- The prominence values as the logophoric roles of [sells-1987]: proximate arguments are
pivots, participants selves, and authors sources. -/
def prominenceToSellsRole : ProminenceThreshold → Features.Logophoricity.LogophoricRole
  | .proximate => .pivot
  | .participant => .self
  | .author => .source

/-- The attested varieties and the [+author] predicted variety on the role hierarchy: the
strong family requires a pivot, the super-strong a self, and me-first a source. -/
theorem family_logophoric_assignments :
    prominenceToSellsRole strongGrammar.prominence = .pivot ∧
      prominenceToSellsRole ultraStrongGrammar.prominence = .pivot ∧
      prominenceToSellsRole weakGrammar.prominence = .pivot ∧
      prominenceToSellsRole superStrongGrammar.prominence = .self ∧
      prominenceToSellsRole meFirstGrammar.prominence = .source ∧
      prominenceToSellsRole pg3Grammar.prominence = .source := by
  decide

/-! ### The paper's examples (§4) -/

/-- The person of a clitic entry, undefined only for the impersonal value that object clitics
never bear. -/
private def cliticLevel? : UD.Person → Option Person
  | .zero => none
  | p => some (Person.fromUD p)

/-- Italian dative *gli* is third person and accusative *ti* second, so the weak PCC bans the
pair. -/
theorem italian_weak_glidat_tiacc :
    cliticLevel? Italian.Pronouns.gli_dat.person = some .third ∧
      cliticLevel? Italian.Pronouns.ti_acc.person = some .second ∧
      ¬ IsLicit weakGrammar .third .second :=
  ⟨rfl, rfl, by decide⟩

/-- Italian *ti la*, second-person dative over third-person accusative, is licit. -/
theorem italian_weak_tidat_lacl :
    cliticLevel? Italian.Pronouns.ti_dat.person = some .second ∧
      cliticLevel? Italian.Pronouns.la_cl.person = some .third ∧
      IsLicit weakGrammar .second .third :=
  ⟨rfl, rfl, by decide⟩

/-- Spanish *te me* (23), second-person dative over first-person accusative, is licit in the
weak variety. -/
theorem spanish_weak_tedat_meacc :
    cliticLevel? Spanish.Clitics.te_dat.person = some .second ∧
      cliticLevel? Spanish.Clitics.me_acc.person = some .first ∧
      IsLicit weakGrammar .second .first :=
  ⟨rfl, rfl, by decide⟩

/-- Spanish *me te*, first-person dative over second-person accusative, is licit as well. -/
theorem spanish_weak_medat_teacc :
    cliticLevel? Spanish.Clitics.me_dat.person = some .first ∧
      cliticLevel? Spanish.Clitics.te_acc.person = some .second ∧
      IsLicit weakGrammar .first .second :=
  ⟨rfl, rfl, by decide⟩

/-- Spanish *me le* (24), third-person dative over first-person accusative, is banned. -/
theorem spanish_weak_ledat_meacc_banned :
    cliticLevel? Spanish.Clitics.le_dat.person = some .third ∧
      cliticLevel? Spanish.Clitics.me_acc.person = some .first ∧
      ¬ IsLicit weakGrammar .third .first :=
  ⟨rfl, rfl, by decide⟩

/-- French (16), strong PCC: a third-person dative with a first-person accusative is out,
a second-person dative with a third-person accusative and two third persons are in. -/
theorem french_strong_examples :
    ¬ IsLicit strongGrammar .third .first ∧ IsLicit strongGrammar .second .third ∧
      IsLicit strongGrammar .third .third := by
  decide

/-- Catalan (20), ultra-strong PCC: the ⟨1, 2⟩ against ⟨2, 1⟩ asymmetry that separates the
ultra-strong from the strong variety. -/
theorem catalan_ultra_strong_examples :
    IsLicit ultraStrongGrammar .first .second ∧ ¬ IsLicit ultraStrongGrammar .second .first := by
  decide

/-- Kambera (27), super-strong PCC: the indirect object must be local and the direct object
third person, so ⟨3, 3⟩ is banned as well. -/
theorem kambera_super_strong_examples :
    IsLicit superStrongGrammar .first .third ∧ IsLicit superStrongGrammar .second .third ∧
      ¬ IsLicit superStrongGrammar .third .third ∧
      ¬ IsLicit superStrongGrammar .first .second := by
  decide

/-- Bulgarian (29), me-first PCC: ⟨3, 2⟩ is licit, where every [+proximate] variety bans it,
and ⟨2, 1⟩ is not. -/
theorem bulgarian_me_first_examples :
    IsLicit meFirstGrammar .third .second ∧ ¬ IsLicit meFirstGrammar .second .first := by
  decide

/-! ### The ⟨1, 1⟩ corner -/

/-- Me-first bans two first-person arguments by P-Uniqueness on [+author]: neither is uniquely
the perspectival source (§4.5). -/
theorem mefirst_one_one_excluded : ¬ IsLicit meFirstGrammar .first .first := by decide

/-- The substrate's P-Primacy checks only the indirect object's [+author], so the ultra-strong
grammar licenses ⟨1, 1⟩ where the descriptive statement (14d) bans it. -/
theorem ultra_one_one_licensed : IsLicit ultraStrongGrammar .first .first := by decide

/-- Me-first shows no ⟨3, 3⟩ effect: without a first-person argument the domain is exempt, so
the spurious-*se* restriction of the [+proximate] varieties is unavailable (§4.4). -/
theorem mefirst_three_three_exempt : IsLicit meFirstGrammar .third .third := by decide

end PanchevaZubizarreta2018
