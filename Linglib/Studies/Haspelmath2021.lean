import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.Examples.Haspelmath2021
import Linglib.Discourse.Givenness
import Linglib.Semantics.Reference.Definiteness
import Linglib.Semantics.Reference.Prominence
import Linglib.Studies.BejarRezac2009
import Linglib.Syntax.Clause.ArgumentRole
import Linglib.Syntax.Clause.Scenario
import Linglib.Syntax.Person.Basic
import Linglib.Syntax.Person.Class

/-!
# Haspelmath (2021): Role-reference associations and the explanation of argument coding splits

This file formalizes the role-reference association universal of [haspelmath-2021]
(Universal 1, (5)): deviations from the usual associations of role rank and referential
prominence are coded by longer grammatical forms. `RoleReferenceUniversal` states it for
any usualness relation on situations; `ArgumentRole.MoreUsualFor` (the single-argument
tendencies (9)) and `Scenario.MoreUsual` (the scenario tendencies (10), (11), over
`Clause.Scenario`) instantiate it as the
single-argument flagging universal `SingleArgumentUniversal` (Universal 3, whose role
instances are Universals 4, 6, 7 and 8) and the scenario universal `ScenarioUniversal`
(Universal 5, which yields the person-role universal 9b, the relative scenario universal
10 and the inverse universal 11). Universal 12 is Universal 1 read with the usage rate of
the longer alternant of an alternation as its coding, and the givenness alternation
universals 13 and 14 are its scenario instances. `roleReferenceUniversal_of_formFrequency`
is the explanation of §11.2: Universal 2 (the usual association is the frequent one) and
the form-frequency correspondence universal (68) of [haspelmath-2021b] entail Universal 1.

The coding splits the paper cites are stated as coding-length functions on the
prominence scales of (8), checked against the universals and against the paper's own
examples (`Reproduces`), together with the anti-efficient language of §11.3 that the
universals exclude.

## Implementation notes

* The scales are the binary versions of (8), which are the two-element bounded orders
  (`IsSimpleOrder`); `ScenarioUniversal.top_bot_le` and `scenarioUniversal_comp_high` are
  the facts about them that the paper uses tacitly. The binary scales are load-bearing: on
  a scale with three levels a monadic scenario split (fn. 18) obeys Universal 5 only if it
  is constant (`ScenarioUniversal.comp_high_le`), since a balanced scenario of two low
  values is coded no longer than an upstream one and no shorter than a downstream one. The
  ternary scales appear only where the paper's rule refers to them: `PersonRank` for
  Kashmiri, `AnimacyLevel` for Sardinian, Spanish, Fore and Awtuw, `NominalType` for Baule;
  Kolyma Yukaghir's and Greek's rules on the ternary person scale violate Universal 5
  (`yukaghirP_ternary_violates`, `greekT_ternary_violates`).
* Universal 1's qualification to asymmetric coding is dropped: with coding lengths as the
  coding, a symmetric split has equal lengths and satisfies the universal vacuously, as
  Samoan's equal-length ergative alternants do (fn. 14). Its "tends to" is read as
  exceptionless, an idealization the paper itself qualifies. Universal 3's restriction to
  flagging (fn. 6) is not encoded, and the paper applies "longer coding" to Georgian (34)
  and Makassarese (56) itself; the index-based person-role constraint 9a (41) is omitted.
* `BinaryGivenness` is read as the discourse-given ~ discourse-new scale of (8b), which the
  paper also calls topicality; Persian's topical indefinite P (19c) counts as given.
* Coding length is an `ℕ` count of special coding elements in the cited systems; the
  universals are stated over any preorder, and Universal 12 is Universal 5 read with the
  usage rate of the longer alternant as the coding.
* Universal 2 is a claim about discourse frequencies and enters as the hypothesis
  `UsualIsFrequent` of the reduction rather than as data. It is read within a role, across
  prominence values (a definite P is rarer than an indefinite P), which is what (68) opposes
  and what the reduction needs; (6) and the Appendix compare across roles at a fixed value (a
  definite A is commoner than a definite P), a weaker claim.
* The example rows carry the coding an example shows (`codingShown`), so a strict split
  reproduces a row when the coding shown is acceptable exactly when it is the coding the
  split requires, and a splitting alternation when the construction shown is available in
  the row's scenario.

## TODO

* Makassarese (56c), the applicative on a person-form T, is the nominality projection of a
  rule over definiteness and nominality together; the two projections are checked
  separately.
* `lummiPassive`'s availability whenever A is a full nominal is inferred from (64c) and
  (65b); the paper states only that the passive is obligatory in upstream scenarios and
  optional in `N > N`. UNVERIFIED against the source grammar.
* The product-order alternative to Universal 5, antitone in the higher-ranked argument's
  prominence and monotone in the lower-ranked one's, admits monadic splits on ternary
  scales; which cited systems separate it from Universal 5 is open.

## References

* [haspelmath-2021]
* [haspelmath-2021b]
* [bejar-rezac-2009]
-/

namespace Haspelmath2021

open Discourse Reference Reference.Prominence

/-! ### Referential prominence scales (8)

Each scale is a linear order whose greater element is the more prominent. The person scale
of (8a), locuphoric above aliophoric, is `Person.Class`; the definiteness scale of (8b)
without its optional specific-indefinite level is `Reference.Definiteness`, with Eastern
Khanty's specific P (37) read at the definite end; and the givenness scale is
`BinaryGivenness`. -/


/-- The ternary person scale of (47a), first > second > third: the ranks of
`Person.prominence`, read off by `ofPerson`; `Person.Class` is its coarsening at the
locuphoric cut. -/
inductive PersonRank where
  | third
  | second
  | first
  deriving DecidableEq, Fintype, Repr

namespace PersonRank

/-- Rank on the ternary person scale. -/
def rank : PersonRank → ℕ
  | .third => 0
  | .second => 1
  | .first => 2

instance : LinearOrder PersonRank := LinearOrder.lift' rank (by decide)

/-- The rank of a person: the clusivity-marked firsts rank first and the impersonal
third. -/
def ofPerson (p : Person) : PersonRank :=
  match p.prominence with
  | 0 => .third
  | 1 => .second
  | _ => .first

theorem rank_ofPerson (p : Person) : (ofPerson p).rank = p.prominence := by cases p <;> rfl

end PersonRank

/-- The nominality scale of (8a): person forms (independent or index) above full
nominals. -/
inductive Nominality where
  | fullNominal
  | personForm
  deriving DecidableEq, Fintype, Repr

/-- Rank on the nominality scale. -/
def Nominality.rank : Nominality → ℕ
  | .fullNominal => 0
  | .personForm => 1

instance : LinearOrder Nominality := LinearOrder.lift' Nominality.rank (by decide)

/-- `⊥ = fullNominal`, `⊤ = personForm`. -/
instance : BoundedOrder Nominality where
  top := .personForm
  le_top := by decide
  bot := .fullNominal
  bot_le := by decide

instance : IsSimpleOrder Nominality where
  exists_pair_ne := ⟨.fullNominal, .personForm, by decide⟩
  eq_bot_or_eq_top := by decide

/-- The animacy scale of (8a) without its optional animal level; the ternary version is
`AnimacyLevel`. -/
inductive Animacy where
  | inanimate
  | animate
  deriving DecidableEq, Fintype, Repr

/-- Rank on the binary animacy scale. -/
def Animacy.rank : Animacy → ℕ
  | .inanimate => 0
  | .animate => 1

instance : LinearOrder Animacy := LinearOrder.lift' Animacy.rank (by decide)

/-- `⊥ = inanimate`, `⊤ = animate`. -/
instance : BoundedOrder Animacy where
  top := .animate
  le_top := by decide
  bot := .inanimate
  bot_le := by decide

instance : IsSimpleOrder Animacy where
  exists_pair_ne := ⟨.inanimate, .animate, by decide⟩
  eq_bot_or_eq_top := by decide

/-- The focus scale of (8b): background above focus. -/
inductive FocusStatus where
  | focus
  | background
  deriving DecidableEq, Fintype, Repr

/-- Rank on the focus scale. -/
def FocusStatus.rank : FocusStatus → ℕ
  | .focus => 0
  | .background => 1

instance : LinearOrder FocusStatus := LinearOrder.lift' FocusStatus.rank (by decide)

/-- The scale of (49a) conditioning Baule's ditransitive construction: personal pronoun
> proper name > common noun. -/
inductive NominalType where
  | commonNoun
  | properName
  | pronoun
  deriving DecidableEq, Fintype, Repr

/-- Rank on the scale of (49a). -/
def NominalType.rank : NominalType → ℕ
  | .commonNoun => 0
  | .properName => 1
  | .pronoun => 2

instance : LinearOrder NominalType := LinearOrder.lift' NominalType.rank (by decide)

/-! ### Scenarios (10), (11) -/

open Clause (Scenario)

/-- (11): `s` is a more usual scenario than `t`. -/
def Scenario.MoreUsual {α : Type*} [LinearOrder α] (s t : Scenario α) : Prop :=
  t.kind < s.kind

/-! ### Universal 1 and its instances -/

section Universals

variable {S L F : Type*} [Preorder L] [Preorder F]

/-- (5) Universal 1, for situations `S` with usualness relation `r` and coding `c`: a more
usual situation is never coded longer. -/
def RoleReferenceUniversal (r : S → S → Prop) (c : S → L) : Prop :=
  ∀ ⦃s t⦄, r s t → c s ≤ c t

instance (r : S → S → Prop) (c : S → L) [i : Decidable (∀ s t, r s t → c s ≤ c t)] :
    Decidable (RoleReferenceUniversal r c) := i

/-- Universal 1 for a usualness relation holds for every relation it contains. -/
theorem RoleReferenceUniversal.mono {r r' : S → S → Prop} {c : S → L} (hr : r ≤ r')
    (h : RoleReferenceUniversal r' c) : RoleReferenceUniversal r c :=
  fun _ _ hst ↦ h (hr _ _ hst)

/-- (68) The grammatical form-frequency correspondence universal, for frequencies `freq`
and coding `c`: a more frequent pattern is never coded longer. -/
def FormFrequencyCorrespondence (freq : S → F) (c : S → L) : Prop :=
  ∀ ⦃s t⦄, freq t < freq s → c s ≤ c t

/-- (6) Universal 2, relative to a usualness relation: the more usual association is the
more frequent one in language use. -/
def UsualIsFrequent (r : S → S → Prop) (freq : S → F) : Prop :=
  ∀ ⦃s t⦄, r s t → freq t < freq s

/-- §11.2: Universal 1 follows from Universal 2 and the form-frequency correspondence
universal (68), which is Universal 1 for the relation of being more frequent. -/
theorem roleReferenceUniversal_of_formFrequency {r : S → S → Prop} {freq : S → F}
    {c : S → L} (hu : UsualIsFrequent r freq) (h : FormFrequencyCorrespondence freq c) :
    RoleReferenceUniversal r c :=
  RoleReferenceUniversal.mono hu h

variable {α : Type*} [LinearOrder α]

/-- (13) Universal 3, the single-argument flagging universal, for a split on role `r`
coded by `c`: Universal 1 for the role's usual associations `ArgumentRole.MoreUsualFor`
of (9), which are vacuous for S. -/
def SingleArgumentUniversal (r : ArgumentRole) (c : α → L) : Prop :=
  RoleReferenceUniversal r.MoreUsualFor c

instance (r : ArgumentRole) (c : α → L)
    [i : Decidable (∀ x y, r.MoreUsualFor x y → c x ≤ c y)] :
    Decidable (SingleArgumentUniversal r c) := i

/-- (21) Universal 6 and (26) Universal 7: for A and R, Universal 3 says the coding is
longer for the less prominent argument. -/
theorem singleArgumentUniversal_iff_antitone {r : ArgumentRole} (h : r.IsHighDefault)
    {c : α → L} : SingleArgumentUniversal r c ↔ Antitone c :=
  ⟨fun H ↦ antitone_iff_forall_lt.2 fun _ _ hab ↦ H (.inl ⟨h, hab⟩),
    fun H _ _ hst ↦ hst.elim (fun h ↦ H h.2.le) fun h' ↦ (h.not_isLowDefault h'.1).elim⟩

/-- (14) Universal 4 and (27) Universal 8: for P and T, Universal 3 says the coding is
longer for the more prominent argument. -/
theorem singleArgumentUniversal_iff_monotone {r : ArgumentRole} (h : r.IsLowDefault)
    {c : α → L} : SingleArgumentUniversal r c ↔ Monotone c :=
  ⟨fun H ↦ monotone_iff_forall_lt.2 fun _ _ hab ↦ H (.inr ⟨h, hab⟩),
    fun H _ _ hst ↦ hst.elim (fun h' ↦ (h.not_isHighDefault h'.1).elim) fun h ↦ H h.2.le⟩

/-- (16) Universal 5, the scenario universal: coding is longest for upstream, shortest for
downstream and intermediate for balanced scenarios. Universal 10 (54) is its restriction
to `Relative` splits, with the same prediction. -/
def ScenarioUniversal (c : Scenario α → L) : Prop :=
  RoleReferenceUniversal Scenario.MoreUsual c

instance (c : Scenario α → L) [i : Decidable (∀ s t, t.kind < s.kind → c s ≤ c t)] :
    Decidable (ScenarioUniversal c) := i

/-- Under Universal 5 a downstream scenario is coded no longer than any scenario that is
not downstream. -/
theorem ScenarioUniversal.downstream_le {c : Scenario α → L} (h : ScenarioUniversal c)
    {s t : Scenario α} (hs : s.kind = .downstream) (ht : t.kind ≠ .downstream) :
    c s ≤ c t :=
  h (show t.kind < s.kind by rw [hs]; exact lt_top_iff_ne_top.2 ht)

/-- On a binary scale, under Universal 5 the scenario `⟨⊤, ⊥⟩`, the only downstream one, is
coded no longer than any other. -/
theorem ScenarioUniversal.top_bot_le [BoundedOrder α] [IsSimpleOrder α] {c : Scenario α → L}
    (h : ScenarioUniversal c) (s : Scenario α) : c ⟨⊤, ⊥⟩ ≤ c s := by
  by_cases hs : s.kind = .downstream
  · rw [Scenario.kind_eq_downstream_iff_eq.1 hs]
  · exact h.downstream_le (Scenario.kind_eq_downstream_iff_eq.2 rfl) hs

/-- fn. 18: a monadic scenario split, in which only the prominence `coargument s` of the
coargument decides the coding; a dyadic split is one that is monadic in neither
argument. -/
abbrev Monadic (coargument : Scenario α → α) (c : Scenario α → L) : Prop :=
  c.FactorsThrough coargument

instance (coargument : Scenario α → α) (c : Scenario α → L)
    [i : Decidable (∀ s t, coargument s = coargument t → c s = c t)] :
    Decidable (Monadic coargument c) := i

/-- On a binary scale, a split monadic in the higher-ranked argument and antitone in its
prominence obeys Universal 5: the split is coded longest at `⟨⊥, ⊤⟩`, the upstream
scenario, and shortest at `⟨⊤, ⊥⟩`, the downstream one. -/
theorem scenarioUniversal_comp_high [BoundedOrder α] [IsSimpleOrder α] {f : α → L}
    (hf : Antitone f) : ScenarioUniversal (f ∘ Scenario.high) := by
  intro s t hst
  rcases eq_bot_or_eq_top s.high with hs | hs
  · rcases eq_bot_or_eq_top t.high with ht | ht
    · exact (congr_arg f (hs.trans ht.symm)).le
    · exact absurd hst (Scenario.not_kind_lt_kind (.inl hs) (.inl ht))
  · exact hf (hs ▸ le_top)

/-- On a scale with three levels, a split monadic in the higher-ranked argument obeys
Universal 5 only if it is constant: a balanced scenario is coded no longer than an
upstream one at the middle level and no shorter than a downstream one there. -/
theorem ScenarioUniversal.comp_high_le {f : α → L} (h : ScenarioUniversal (f ∘ Scenario.high))
    {a b c : α} (hab : a < b) (hbc : b < c) (x y : α) : f x ≤ f y :=
  (h (s := ⟨x, x⟩) (t := ⟨b, c⟩) (show Scenario.kind _ < Scenario.kind _ by
    rw [Scenario.kind_eq_upstream_iff.2 hbc, Scenario.kind_eq_balanced_iff.2 rfl]; decide)).trans
    (h (s := ⟨b, a⟩) (t := ⟨y, y⟩) (show Scenario.kind _ < Scenario.kind _ by
      rw [Scenario.kind_eq_balanced_iff.2 rfl, Scenario.kind_eq_downstream_iff.2 hab]; decide))

/-- On a scale with three levels, a split monadic in the lower-ranked argument obeys
Universal 5 only if it is constant. -/
theorem ScenarioUniversal.comp_low_le {g : α → L} (h : ScenarioUniversal (g ∘ Scenario.low))
    {a b c : α} (hab : a < b) (hbc : b < c) (x y : α) : g x ≤ g y :=
  (h (s := ⟨x, x⟩) (t := ⟨a, b⟩) (show Scenario.kind _ < Scenario.kind _ by
    rw [Scenario.kind_eq_upstream_iff.2 hab, Scenario.kind_eq_balanced_iff.2 rfl]; decide)).trans
    (h (s := ⟨c, b⟩) (t := ⟨y, y⟩) (show Scenario.kind _ < Scenario.kind _ by
      rw [Scenario.kind_eq_balanced_iff.2 rfl, Scenario.kind_eq_downstream_iff.2 hbc]; decide))

/-- On a binary scale, a split monadic in the lower-ranked argument and monotone in its
prominence obeys Universal 5. -/
theorem scenarioUniversal_comp_low [BoundedOrder α] [IsSimpleOrder α] {g : α → L}
    (hg : Monotone g) : ScenarioUniversal (g ∘ Scenario.low) := by
  intro s t hst
  rcases eq_bot_or_eq_top s.low with hs | hs
  · exact hg (hs ▸ bot_le)
  · rcases eq_bot_or_eq_top t.low with ht | ht
    · exact absurd hst (Scenario.not_kind_lt_kind (.inr hs) (.inr ht))
    · exact (congr_arg g (hs.trans ht.symm)).le

/-- §8: a relative scenario split, in which the coding is determined by the relation
between the prominence levels of the two arguments. On a binary scale this admits the
dyadic splits of Yurok's type, which fn. 20 allows are "just like" Kashmiri's. -/
abbrev Relative (c : Scenario α → L) : Prop :=
  c.FactorsThrough Scenario.kind

instance (c : Scenario α → L) [i : Decidable (∀ s t, s.kind = t.kind → c s = c t)] :
    Decidable (Relative c) := i

/-- (42) Universal 9b, the ditransitive person-role universal: the scenario with a
locuphoric R and an aliophoric T is coded no longer than any other. -/
def PersonRoleUniversal (c : Scenario Person.Class → L) : Prop :=
  ∀ s, c ⟨.participant, .nonParticipant⟩ ≤ c s

/-- §7.1: Universal 9b is a special case of Universal 5. -/
theorem personRoleUniversal_of_scenarioUniversal {c : Scenario Person.Class → L}
    (h : ScenarioUniversal c) : PersonRoleUniversal c :=
  h.top_bot_le

/-- (57) Universal 11, the inverse universal, for verb coding `v`: the inverse form of an
upstream scenario is no shorter than the direct form of a downstream one. -/
def InverseUniversal (v : Scenario α → L) : Prop :=
  ∀ ⦃s t⦄, s.kind = .downstream → t.kind = .upstream → v s ≤ v t

/-- Verb coding that obeys the scenario universal obeys the inverse universal. -/
theorem inverseUniversal_of_scenarioUniversal {v : Scenario α → L} (h : ScenarioUniversal v) :
    InverseUniversal v :=
  fun _ _ hs ht ↦ h (show _ < _ by rw [hs, ht]; exact bot_lt_top)

/-- (62) Universal 13 and (63) Universal 14, for the usage rate `rate` of the passive or
of the dative alternant across the givenness scenarios of A and P or of R and T: the
longer alternant is used least when the higher-ranked argument is given and the
lower-ranked one new. -/
def GivennessAlternationUniversal (rate : Scenario BinaryGivenness → F) : Prop :=
  ∀ s, rate ⟨.given, .new⟩ ≤ rate s

/-- §10.1: Universals 13 and 14 are special cases of the alternation universal (61),
Universal 5 read with the usage rate of the longer alternant as its coding. -/
theorem givennessAlternationUniversal_of_scenarioUniversal
    {rate : Scenario BinaryGivenness → F} (h : ScenarioUniversal rate) :
    GivennessAlternationUniversal rate :=
  h.top_bot_le

/-- §10.2: a splitting alternation between a shorter and a longer construction, which
alternate in some scenarios and are in complementary distribution in others. -/
def SplittingAlternation (short long : Scenario α → Prop) : Prop :=
  (∃ s, short s ∧ long s) ∧ ∃ s, Xor (short s) (long s)

instance (short long : Scenario α → Prop)
    [i : Decidable ((∃ s, short s ∧ long s) ∧ ∃ s, Xor (short s) (long s))] :
    Decidable (SplittingAlternation short long) := i

/-- The shortest coding available in a scenario: `0` where the shorter construction is
available, `1` otherwise. -/
def minimalCoding (short : Scenario α → Prop) [DecidablePred short] (s : Scenario α) : ℕ :=
  if short s then 0 else 1

/-! #### Cutoff splits

The cited splits are cutoffs on a scale (`atLeast x`, `below x`); a scenario split is a
cutoff on one argument's prominence or on the kind. -/

/-- Universals 4 and 8: a P or T split from a cutoff up obeys Universal 3. -/
theorem singleArgumentUniversal_atLeast {r : ArgumentRole} (h : r.IsLowDefault) (x : α) :
    SingleArgumentUniversal r (atLeast x) :=
  (singleArgumentUniversal_iff_monotone h).2 (atLeast_monotone x)

/-- Universals 6 and 7: an A or R split below a cutoff obeys Universal 3. -/
theorem singleArgumentUniversal_below {r : ArgumentRole} (h : r.IsHighDefault) (x : α) :
    SingleArgumentUniversal r (below x) :=
  (singleArgumentUniversal_iff_antitone h).2 (below_antitone x)

omit [Preorder L] in
/-- A split that is a function of the kind is relative. -/
theorem relative_comp_kind (g : Scenario.Kind → L) :
    Relative (g ∘ Scenario.kind : Scenario α → L) :=
  fun _ _ h ↦ congrArg g h

/-- Universal 10: a relative split antitone in usualness obeys Universal 5. -/
theorem scenarioUniversal_comp_kind {g : Scenario.Kind → L} (hg : Antitone g) :
    ScenarioUniversal (g ∘ Scenario.kind : Scenario α → L) :=
  fun _ _ hst ↦ hg hst.le

end Universals

/-! ### Single-argument splits (§4, §5) -/

/-- (2): Sakha flags a definite P with the accusative; Punjabi's `nũũ` (18) is alike. -/
def sakhaP : Definiteness → ℕ := atLeast .definite

/-- (17): Nuorese Sardinian flags a human P with `a`. -/
def sardinianP : AnimacyLevel → ℕ := atLeast .human

/-- (19): Persian flags a topical P with `-râ`. -/
def persianP : BinaryGivenness → ℕ := atLeast .given

/-- (20): Abruzzese flags a locuphoric P with `a`. -/
def abruzzeseP : Person.Class → ℕ := atLeast .participant

/-- §4.1.3: English distinguishes P from A only on person forms (*he* ~ *him*), a split in
indexes rather than flags, which fn. 12 allows may have a different explanation. -/
def englishP : Nominality → ℕ := atLeast .personForm

/-- (22): Godoberi has an ergative form only for aliophoric A; Kham (1) is alike. -/
def godoberiA : Person.Class → ℕ := below .participant

/-- (23): Warrgamay flags a full-nominal A with the ergative. -/
def warrgamayA : Nominality → ℕ := below .personForm

/-- (24): Mangarrayi flags an inanimate (neuter) A with the ergative. -/
def mangarrayiA : Animacy → ℕ := below .animate

/-- (25): Central Tibetan flags a focused A with the ergative `-ki'`. -/
def tibetanA : FocusStatus → ℕ := below .background

/-- (28): French dative clitics are longer than accusative ones only for aliophoric R
(`lui` ~ `le`, `leur` ~ `les`); they are person indexes, so fn. 17 keeps the case outside
split flagging proper. -/
def frenchR : Person.Class → ℕ := below .participant

/-- (29): Telkepe Neo-Aramaic flags a full-nominal R with `ta`. -/
def neoAramaicR : Nominality → ℕ := below .personForm

/-- (30): Yakkha puts an inanimate R in the locative. -/
def yakkhaR : Animacy → ℕ := below .animate

/-- (31): Wolof flags an indefinite R with `ci`. -/
def wolofR : Definiteness → ℕ := below .definite

/-- (32): Ewe flags a person-form T with the serial verb `tsɔ́`. -/
def eweT : Nominality → ℕ := atLeast .personForm

/-- (33): Akan flags a definite T with the serial verb `de`. -/
def akanT : Definiteness → ℕ := atLeast .definite

/-- (34): Georgian requires the reinforced form (`šeni tavi`) for a locuphoric T. -/
def georgianT : Person.Class → ℕ := atLeast .participant

/-- §4.1: the split P flagging systems obey Universal 4. -/
theorem universal4_splitP :
    SingleArgumentUniversal .P sakhaP ∧ SingleArgumentUniversal .P sardinianP ∧
      SingleArgumentUniversal .P persianP ∧ SingleArgumentUniversal .P abruzzeseP ∧
      SingleArgumentUniversal .P englishP :=
  ⟨singleArgumentUniversal_atLeast (.inl rfl) _, singleArgumentUniversal_atLeast (.inl rfl) _,
    singleArgumentUniversal_atLeast (.inl rfl) _, singleArgumentUniversal_atLeast (.inl rfl) _,
    singleArgumentUniversal_atLeast (.inl rfl) _⟩

/-- §4.2: the split A flagging systems obey Universal 6. -/
theorem universal6_splitA :
    SingleArgumentUniversal .A godoberiA ∧ SingleArgumentUniversal .A warrgamayA ∧
      SingleArgumentUniversal .A mangarrayiA ∧ SingleArgumentUniversal .A tibetanA :=
  ⟨singleArgumentUniversal_below (.inl rfl) _, singleArgumentUniversal_below (.inl rfl) _,
    singleArgumentUniversal_below (.inl rfl) _, singleArgumentUniversal_below (.inl rfl) _⟩

/-- §5.1: the split R flagging systems obey Universal 7. -/
theorem universal7_splitR :
    SingleArgumentUniversal .R frenchR ∧ SingleArgumentUniversal .R neoAramaicR ∧
      SingleArgumentUniversal .R yakkhaR ∧ SingleArgumentUniversal .R wolofR :=
  ⟨singleArgumentUniversal_below (.inr rfl) _, singleArgumentUniversal_below (.inr rfl) _,
    singleArgumentUniversal_below (.inr rfl) _, singleArgumentUniversal_below (.inr rfl) _⟩

/-- §5.2: the split T flagging systems obey Universal 8. -/
theorem universal8_splitT :
    SingleArgumentUniversal .T eweT ∧ SingleArgumentUniversal .T akanT ∧
      SingleArgumentUniversal .T georgianT :=
  ⟨singleArgumentUniversal_atLeast (.inr rfl) _, singleArgumentUniversal_atLeast (.inr rfl) _,
    singleArgumentUniversal_atLeast (.inr rfl) _⟩

/-! ### Scenario splits (§6, §7) -/

/-- (35): Kolyma Yukaghir flags P with the accusative when A is aliophoric; Teop's object
marker `ben-` (3) is alike. -/
def yukaghirP : Scenario Person.Class → ℕ := below .participant ∘ Scenario.high

/-- §6.1: Yurok flags P with the accusative when A is aliophoric and P locuphoric. -/
def yurokP (s : Scenario Person.Class) : ℕ :=
  if s.high = .nonParticipant ∧ s.low = .participant then 1 else 0

/-- (36): Sahaptin flags A with the ergative when P is locuphoric. -/
def sahaptinA : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- (37): Eastern Khanty flags A with the ergative when P is specific. -/
def khantyA : Scenario Definiteness → ℕ := atLeast .definite ∘ Scenario.low

/-- (38): Spanish flags P with `a` when the construction is not animacy-downstream, which
subsumes the human P of §4.1.1. -/
def spanishP : Scenario AnimacyLevel → ℕ := below .downstream ∘ Scenario.kind

/-- (39): Bulgarian flags R with `na` when T is a locuphoric clitic. -/
def bulgarianR : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- (40): Shambala flags R with `kwa` when T is locuphoric. -/
def shambalaR : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- (4): English requires `to` on R in the N > pers scenario. -/
def englishR (s : Scenario Nominality) : ℕ := if s = ⟨.fullNominal, .personForm⟩ then 1 else 0

/-- (44): the American varieties of English require `to` on R whenever T is a person
form. -/
def americanEnglishR : Scenario Nominality → ℕ := atLeast .personForm ∘ Scenario.low

/-- (45): Modern Greek has the T proclitic in downstream and aliophoric balanced scenarios
and the independent pronoun otherwise, so whenever T is locuphoric. -/
def greekT : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- (46): Icelandic flags R with `fyrir` when T is animate. -/
def icelandicR : Scenario Animacy → ℕ := atLeast .animate ∘ Scenario.low

/-- §6: the monotransitive scenario splits obey Universal 5; the monadic ones by fn. 18 on
a binary scale, Spanish as a relative split, the dyadic Yurok by inspection. -/
theorem universal5_monotransitive :
    ScenarioUniversal yukaghirP ∧ ScenarioUniversal yurokP ∧
      ScenarioUniversal sahaptinA ∧ ScenarioUniversal khantyA ∧ ScenarioUniversal spanishP :=
  ⟨scenarioUniversal_comp_high (below_antitone _), by decide,
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_kind (below_antitone _)⟩

/-- §7: the ditransitive scenario splits obey Universal 5. -/
theorem universal5_ditransitive :
    ScenarioUniversal bulgarianR ∧ ScenarioUniversal shambalaR ∧ ScenarioUniversal englishR ∧
      ScenarioUniversal americanEnglishR ∧ ScenarioUniversal greekT ∧
      ScenarioUniversal icelandicR :=
  ⟨scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _), by decide,
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _)⟩

/-- (39): Bulgarian obeys Universal 9b. -/
theorem universal9b_bulgarian : PersonRoleUniversal bulgarianR :=
  personRoleUniversal_of_scenarioUniversal (scenarioUniversal_comp_low (atLeast_monotone _))

/-- fn. 18: Kolyma Yukaghir's split is monadic and Yurok's dyadic. -/
theorem yukaghir_monadic_yurok_dyadic :
    Monadic Scenario.high yukaghirP ∧
      ¬ Monadic Scenario.high yurokP ∧ ¬ Monadic Scenario.low yurokP :=
  ⟨fun _ _ h ↦ congrArg (below _) h, by decide, by decide⟩

/-- Kolyma Yukaghir's rule on the ternary person scale, P flagged whenever A is third
person, violates Universal 5, as every non-constant monadic split on a ternary scale does
(`ScenarioUniversal.comp_high_le`). -/
theorem yukaghirP_ternary_violates :
    ¬ ScenarioUniversal (below PersonRank.second ∘ Scenario.high) :=
  fun h ↦ absurd
    (h.comp_high_le (by decide : PersonRank.third < PersonRank.second)
      (by decide : PersonRank.second < PersonRank.first) .third .first) (by decide)

/-- Modern Greek's rule on the ternary person scale (47a) violates Universal 5 likewise:
the downstream `1 > 2` is coded longer than the balanced `3 > 3`. -/
theorem greekT_ternary_violates :
    ¬ ScenarioUniversal (atLeast PersonRank.second ∘ Scenario.low) :=
  fun h ↦ absurd
    (h.comp_low_le (by decide : PersonRank.third < PersonRank.second)
      (by decide : PersonRank.second < PersonRank.first) .first .third) (by decide)

/-! ### Relative scenario splits (§8) -/

/-- (47): Kashmiri puts P in the dative unless A outranks P on the ternary person
scale. -/
def kashmiriP : Scenario PersonRank → ℕ := below .downstream ∘ Scenario.kind

/-- §8: Fore flags A with the ergative only when P outranks A in animacy. -/
def foreA : Scenario AnimacyLevel → ℕ := below .balanced ∘ Scenario.kind

/-- §8: Awtuw flags P with the accusative only when P is not lower than A in animacy. -/
def awtuwP : Scenario AnimacyLevel → ℕ := below .downstream ∘ Scenario.kind

/-- (49): Baule flags T with the serial verb `fà` unless R outranks T on the scale of
(49a). -/
def bauleT : Scenario NominalType → ℕ := below .downstream ∘ Scenario.kind

/-- (47) against [bejar-rezac-2009]'s Table 11: Kashmiri's dative P is the R-Case of their
attested cells, which their `repair_iff_inverse` places exactly at the inverse contexts of
cyclic Agree, so the relative split and the failed EA licensing pick out the same
scenarios. -/
theorem kashmiriP_eq_kashmiriRCase :
    ∀ c ∈ BejarRezac2009.attestedCells,
      kashmiriP ((Scenario.mk c.1 c.2).map PersonRank.ofPerson) = 1 ↔
        BejarRezac2009.kashmiriRCase c = true := by
  decide

/-- §8: the relative scenario splits are relative and obey Universal 10. -/
theorem universal10_relative :
    (Relative kashmiriP ∧ ScenarioUniversal kashmiriP) ∧
      (Relative foreA ∧ ScenarioUniversal foreA) ∧
      (Relative awtuwP ∧ ScenarioUniversal awtuwP) ∧
      (Relative bauleT ∧ ScenarioUniversal bauleT) :=
  ⟨⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩,
    ⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩,
    ⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩,
    ⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩⟩

/-- §8: Kolyma Yukaghir's monadic split is not relative, since the two balanced person
scenarios are coded differently. -/
theorem yukaghir_not_relative : ¬ Relative yukaghirP := by decide

/-! ### Verbal voice coding (§9) -/

/-- (55): Itonama's inverse prefix `k'i-` appears in upstream scenarios. -/
def itonamaV : Scenario Person.Class → ℕ := below .balanced ∘ Scenario.kind

/-- (55): Itonama obeys the inverse universal. -/
theorem universal11_itonama : InverseUniversal itonamaV :=
  inverseUniversal_of_scenarioUniversal (scenarioUniversal_comp_kind (below_antitone _))

/-- (56): Makassarese requires the applicative `-ang` on the verb for a definite T. -/
def makassarV : Definiteness → ℕ := atLeast .definite

/-- (56c): Makassarese requires the applicative `-ang` on the verb for a person-form T. -/
def makassarVNominality : Nominality → ℕ := atLeast .personForm

/-- §9: Makassarese's verb coding is shaped like a split obeying Universal 8. -/
theorem makassar_universal8 :
    SingleArgumentUniversal .T makassarV ∧ SingleArgumentUniversal .T makassarVNominality :=
  ⟨singleArgumentUniversal_atLeast (.inr rfl) _, singleArgumentUniversal_atLeast (.inr rfl) _⟩

/-! ### Splitting alternations (§10.2) -/

/-- (64), (65): Lummi's active construction is available unless the scenario is
upstream. -/
def lummiActive (s : Scenario Nominality) : Prop := s.kind ≠ .upstream

instance : DecidablePred lummiActive := fun s ↦ inferInstanceAs (Decidable (s.kind ≠ _))

/-- (64), (65): Lummi's passive construction is available when A is a full nominal, the
common condition of the obligatory (64c) and optional (65b) passives. -/
def lummiPassive (s : Scenario Nominality) : Prop := s.high = .fullNominal

instance : DecidablePred lummiPassive := fun s ↦ inferInstanceAs (Decidable (s.high = _))

/-- (66), (67): Koyra Chiini's double object construction is available only in downstream
scenarios; the postpositional dative construction is always available. -/
def koyraChiiniDoubleObject (s : Scenario Nominality) : Prop := s.kind = .downstream

instance : DecidablePred koyraChiiniDoubleObject :=
  fun s ↦ inferInstanceAs (Decidable (s.kind = _))

/-- (4), (60): the English double object construction is available except in the
N > pers scenario; the prepositional dative construction is always available. -/
def englishDoubleObject (s : Scenario Nominality) : Prop := s ≠ ⟨.fullNominal, .personForm⟩

instance : DecidablePred englishDoubleObject := fun s ↦ inferInstanceAs (Decidable (s ≠ _))

/-- §10.2: Lummi, Koyra Chiini and English have splitting alternations whose shortest
available coding obeys Universal 5. -/
theorem splittingAlternations_universal5 :
    (SplittingAlternation lummiActive lummiPassive ∧
        ScenarioUniversal (minimalCoding lummiActive)) ∧
      (SplittingAlternation koyraChiiniDoubleObject (fun _ ↦ True) ∧
        ScenarioUniversal (minimalCoding koyraChiiniDoubleObject)) ∧
      (SplittingAlternation englishDoubleObject (fun _ ↦ True) ∧
        ScenarioUniversal (minimalCoding englishDoubleObject)) := by
  decide

/-! ### The anti-efficient language (§11.3)

The hypothetical language flags the usual associations and leaves the rare ones bare, so it
has less potential ambiguity than the attested mirror image; its non-existence is the paper's
argument that efficient coding, not ambiguity avoidance, explains the splits. -/

/-- §11.3's hypothetical language: the ergative on every topical A and zero coding on a
focused A. -/
def antiEfficientA : FocusStatus → ℕ := atLeast .background

/-- §11.3's hypothetical language: the accusative on every indefinite P and zero coding
on a definite P. -/
def antiEfficientP : Definiteness → ℕ := below .definite

/-- §11.3: the unattested anti-efficient language violates Universals 6 and 4. -/
theorem antiEfficient_violates :
    ¬ SingleArgumentUniversal .A antiEfficientA ∧
      ¬ SingleArgumentUniversal .P antiEfficientP := by
  decide

/-! ### The paper's examples

Each cited system is checked against the rows of its language: every row reads to a
prominence value or scenario on the system's scale, and the coding the row shows is
acceptable exactly when it is the coding the system requires, or, for a splitting
alternation, when the construction shown is available in the row's scenario. -/

section Examples

open Data.Examples (LinguisticExample)

variable {α : Type*}

/-- The coding an example shows: `0` for zero coding, `1` for the special coding. -/
def codingShown (e : LinguisticExample) : Option ℕ :=
  e.parse? "coding" [("zero", 0), ("special", 1)]

/-- The rows on the split of role `role` on scale `scale` in the language with glottocode
`lang`. -/
def rows (lang role scale : String) : List LinguisticExample :=
  Examples.all.filter fun e ↦
    e.language = lang ∧ e.feature? "role" = some role ∧ e.feature? "scale" = some scale

/-- The prominence value of a single-argument row, read through `table`. -/
def prominence? (table : List (String × α)) (e : LinguisticExample) : Option α :=
  e.parse? "prominence" table

/-- The two sides of `X > Y`, by a structural scan so that `decide` can evaluate it. -/
private def splitGt : List Char → Option (List Char × List Char)
  | [] => none
  | ' ' :: '>' :: ' ' :: rest => some ([], rest)
  | c :: rest => (splitGt rest).map fun p ↦ (c :: p.1, p.2)

/-- The scenario `X > Y` of a scenario row, its sides read through `table`. -/
def scenario? (table : List (String × α)) (e : LinguisticExample) : Option (Scenario α) :=
  (e.feature? "scenario").bind fun s ↦ (splitGt s.toList).bind fun (x, y) ↦
    (table.lookup (String.ofList x)).bind fun h ↦
      (table.lookup (String.ofList y)).map (⟨h, ·⟩)

/-- The rows `rs` reproduce the split `c` on the values `x?` reads off them: each row reads
to a value at which the coding it shows is acceptable exactly when it is the coding `c`
requires. -/
def Reproduces (rs : List LinguisticExample) (x? : LinguisticExample → Option α)
    (c : α → ℕ) : Prop :=
  rs ≠ [] ∧ ∀ e ∈ rs, ∃ x ∈ x? e, ∃ k ∈ codingShown e,
    (e.judgment = .acceptable ↔ c x = k)

instance (rs : List LinguisticExample) (x? : LinguisticExample → Option α) (c : α → ℕ) :
    Decidable (Reproduces rs x? c) := by
  unfold Reproduces; infer_instance

/-- The rows `rs` reproduce the alternation between `short` and `long`: a row showing zero
coding is acceptable exactly when the shorter construction is available in its scenario,
one showing the special coding exactly when the longer one is. -/
def ReproducesAlternation (rs : List LinguisticExample)
    (s? : LinguisticExample → Option (Scenario α)) (short long : Scenario α → Prop)
    [DecidablePred short] [DecidablePred long] : Prop :=
  rs ≠ [] ∧ ∀ e ∈ rs, ∃ s ∈ s? e, ∃ k ∈ codingShown e,
    (e.judgment = .acceptable ↔ if k = 0 then short s else long s)

instance (rs : List LinguisticExample) (s? : LinguisticExample → Option (Scenario α))
    (short long : Scenario α → Prop) [DecidablePred short] [DecidablePred long] :
    Decidable (ReproducesAlternation rs s? short long) := by
  unfold ReproducesAlternation; infer_instance

/-- The person tags of the rows, as the binary scale. -/
def Person.Class.table : List (String × Person.Class) :=
  [("locuphoric", .participant), ("aliophoric", .nonParticipant),
    ("1", .participant), ("2", .participant), ("3", .nonParticipant)]

/-- The person tags of the rows, as the ternary scale. -/
def PersonRank.table : List (String × PersonRank) := [("1", .first), ("2", .second), ("3", .third)]

/-- The nominality tags of the rows. -/
def Nominality.table : List (String × Nominality) :=
  [("personForm", .personForm), ("fullNominal", .fullNominal), ("pers", .personForm),
    ("N", .fullNominal)]

/-- The animacy tags of the rows, as the binary scale. -/
def Animacy.table : List (String × Animacy) := [("animate", .animate), ("inanimate", .inanimate)]

/-- The animacy tags of the rows, as the ternary scale. -/
def AnimacyLevel.table : List (String × AnimacyLevel) :=
  [("human", .human), ("animate", .animate), ("inanimate", .inanimate)]

/-- The definiteness tags of the rows. -/
def Definiteness.table : List (String × Definiteness) :=
  [("definite", .definite), ("indefinite", .indefinite), ("def", .definite), ("indef", .indefinite)]

/-- The givenness tags of the rows. -/
def BinaryGivenness.table : List (String × BinaryGivenness) := [("given", .given), ("new", .new)]

/-- The focus tags of the rows. -/
def FocusStatus.table : List (String × FocusStatus) :=
  [("background", .background), ("focus", .focus)]

/-- The nominal-type tags of the rows. -/
def NominalType.table : List (String × NominalType) :=
  [("pers", .pronoun), ("prop", .properName), ("common", .commonNoun)]

/-- §4.1, §4.2: the single-argument P and A splits reproduce the paper's examples, the
Punjabi and Kham rows those of the Sakha and Godoberi rules they share. -/
theorem rows_splitP_splitA :
    Reproduces (rows "yaku1245" "P" "definiteness") (prominence? Definiteness.table) sakhaP ∧
      Reproduces (rows "nuor1238" "P" "animacy") (prominence? AnimacyLevel.table) sardinianP ∧
      Reproduces (rows "panj1256" "P" "definiteness") (prominence? Definiteness.table) sakhaP ∧
      Reproduces (rows "west2369" "P" "givenness") (prominence? BinaryGivenness.table) persianP ∧
      Reproduces (rows "neap1235" "P" "person") (prominence? Person.Class.table) abruzzeseP ∧
      Reproduces (rows "taka1261" "A" "person") (prominence? Person.Class.table) godoberiA ∧
      Reproduces (rows "warr1255" "A" "nominality") (prominence? Nominality.table) warrgamayA ∧
      Reproduces (rows "mang1381" "A" "animacy") (prominence? Animacy.table) mangarrayiA ∧
      Reproduces (rows "cent2346" "A" "focus") (prominence? FocusStatus.table) tibetanA := by
  decide

/-- §5, §9: the single-argument R and T splits and Makassarese's verb coding reproduce the
paper's examples. -/
theorem rows_splitR_splitT :
    Reproduces (rows "telk1238" "R" "nominality") (prominence? Nominality.table) neoAramaicR ∧
      Reproduces (rows "yakk1236" "R" "animacy") (prominence? Animacy.table) yakkhaR ∧
      Reproduces (rows "nucl1347" "R" "definiteness") (prominence? Definiteness.table) wolofR ∧
      Reproduces (rows "ewee1241" "T" "nominality") (prominence? Nominality.table) eweT ∧
      Reproduces (rows "akan1250" "T" "definiteness") (prominence? Definiteness.table) akanT ∧
      Reproduces (rows "nucl1302" "T" "person") (prominence? Person.Class.table) georgianT ∧
      Reproduces (rows "maka1311" "T" "definiteness") (prominence? Definiteness.table) makassarV ∧
      Reproduces (rows "maka1311" "T" "nominality") (prominence? Nominality.table)
        makassarVNominality := by
  decide

/-- §6, §7, §9: the scenario splits and Itonama's inverse reproduce the paper's examples;
the Teop rows those of the Yukaghir rule, and the rows of (43) and (44) are the American
varieties'. -/
theorem rows_scenario :
    Reproduces (rows "teop1238" "P" "person") (scenario? Person.Class.table) yukaghirP ∧
      Reproduces (rows "sout2750" "P" "person") (scenario? Person.Class.table) yukaghirP ∧
      Reproduces (rows "saha1240" "A" "person") (scenario? Person.Class.table) sahaptinA ∧
      Reproduces (rows "east2774" "A" "definiteness") (scenario? Definiteness.table) khantyA ∧
      Reproduces (rows "stan1288" "P" "animacy") (scenario? AnimacyLevel.table) spanishP ∧
      Reproduces (rows "bulg1262" "R" "person") (scenario? Person.Class.table) bulgarianR ∧
      Reproduces (rows "sham1280" "R" "person") (scenario? Person.Class.table) shambalaR ∧
      Reproduces ((rows "stan1293" "R" "nominality").filter (·.feature? "variety" = none))
        (scenario? Nominality.table) englishR ∧
      Reproduces ((rows "stan1293" "R" "nominality").filter
          (·.feature? "variety" = some "American"))
        (scenario? Nominality.table) americanEnglishR ∧
      Reproduces (rows "mode1248" "T" "person") (scenario? Person.Class.table) greekT ∧
      Reproduces (rows "icel1247" "R" "animacy") (scenario? Animacy.table) icelandicR ∧
      Reproduces (rows "kash1277" "P" "person") (scenario? PersonRank.table) kashmiriP ∧
      Reproduces (rows "baou1238" "T" "nominal type") (scenario? NominalType.table) bauleT ∧
      Reproduces (rows "iton1250" "verb" "person") (scenario? Person.Class.table) itonamaV := by
  decide

/-- §10.2, (4): the splitting alternations reproduce the paper's examples. -/
theorem rows_alternations :
    ReproducesAlternation (rows "lumm1243" "A" "nominality") (scenario? Nominality.table)
        lummiActive lummiPassive ∧
      ReproducesAlternation (rows "koyr1240" "R" "nominality") (scenario? Nominality.table)
        koyraChiiniDoubleObject (fun _ ↦ True) ∧
      ReproducesAlternation ((rows "stan1293" "R" "nominality").filter
          (·.feature? "variety" = none))
        (scenario? Nominality.table) englishDoubleObject (fun _ ↦ True) := by
  decide

end Examples

end Haspelmath2021
