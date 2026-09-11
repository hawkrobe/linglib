import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Givenness
import Linglib.Features.Prominence
import Linglib.Syntax.Clause.ArgumentRole

/-!
# Haspelmath (2021): Role-reference associations and the explanation of argument coding splits

This file formalizes the role-reference association universal of [haspelmath-2021]
(Universal 1, (5)): deviations from the usual associations of role rank and referential
prominence are coded by longer grammatical forms. `RoleReferenceUniversal` states it for
any usualness relation on situations; `MoreUsualFor` (the single-argument tendencies (9))
and `Scenario.MoreUsual` (the scenario tendencies (10), (11)) instantiate it as the
single-argument flagging universal `SingleArgumentUniversal` (Universal 3, whose role
instances are Universals 4, 6, 7 and 8) and the scenario universal `ScenarioUniversal`
(Universal 5, which yields the person-role universal 9b, the relative scenario universal
10, the inverse universal 11 and the givenness alternation universals 13 and 14).
`roleReferenceUniversal_of_formFrequency` is the explanation of §11.2: Universal 2 (the
usual association is the frequent one) and the form-frequency correspondence universal
(68) entail Universal 1.

The coding splits the paper cites are stated as coding-length functions on the
prominence scales of (8) and checked against the universals, together with the
anti-efficient language of §11.3 that the universals exclude.

## Implementation notes

* The scales are the binary versions of (8). A monadic scenario split (fn. 18) such as
  Kolyma Yukaghir's, which flags P whenever A is aliophoric, obeys Universal 5 only on a
  binary scale, since on a finer scale a balanced scenario of two low values would be
  coded longer than an upstream one. The ternary scales appear only where the paper's
  rule refers to them: `PersonRank` for Kashmiri, `AnimacyLevel` for Sardinian, Spanish,
  Fore and Awtuw, `NominalType` for Baule.
* Coding length is an `ℕ` count of special coding elements in the cited systems; the
  universals are stated over any preorder, and Universal 12 is Universal 5 read with the
  usage rate of the longer alternant as the coding.
* Universal 2 is a claim about discourse frequencies and enters as the hypothesis
  `UsualIsFrequent` of the reduction rather than as data.

## References

* [haspelmath-2021]
-/

namespace Haspelmath2021

open Features (BinaryGivenness)
open Features.Prominence (AnimacyLevel)

/-! ### Referential prominence scales (8)

Each scale is a linear order whose greater element is the more prominent. -/

/-- The person scale of (8a): locuphoric (first and second person) above aliophoric
(third person). -/
inductive PersonClass where
  | aliophoric
  | locuphoric
  deriving DecidableEq, Fintype, Repr

/-- Rank on the person scale. -/
def PersonClass.rank : PersonClass → ℕ
  | .aliophoric => 0
  | .locuphoric => 1

instance : LinearOrder PersonClass := LinearOrder.lift' PersonClass.rank (by decide)

/-- The ternary person scale of (47a), first > second > third, the ranks of
`Person.prominence`. -/
inductive PersonRank where
  | third
  | second
  | first
  deriving DecidableEq, Fintype, Repr

/-- Rank on the ternary person scale. -/
def PersonRank.rank : PersonRank → ℕ
  | .third => 0
  | .second => 1
  | .first => 2

instance : LinearOrder PersonRank := LinearOrder.lift' PersonRank.rank (by decide)

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

/-- The definiteness scale of (8b) without its optional specific-indefinite level;
Eastern Khanty's specific P (37) is read at the definite end. -/
inductive Definiteness where
  | indefinite
  | definite
  deriving DecidableEq, Fintype, Repr

/-- Rank on the definiteness scale. -/
def Definiteness.rank : Definiteness → ℕ
  | .indefinite => 0
  | .definite => 1

instance : LinearOrder Definiteness := LinearOrder.lift' Definiteness.rank (by decide)

/-- The focus scale of (8b): background above focus. The givenness scale of (8b) is
`BinaryGivenness`. -/
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

/-- A scenario (fn. 4): the prominence values of the two arguments of a monotransitive
or ditransitive construction. The paper writes `X > Y` for `⟨X, Y⟩`. -/
structure Scenario (α : Type*) where
  /-- The prominence of the higher-ranked argument, A or R. -/
  high : α
  /-- The prominence of the lower-ranked argument, P or T. -/
  low : α
  deriving DecidableEq

instance {α : Type*} [Fintype α] : Fintype (Scenario α) :=
  Fintype.ofEquiv (α × α)
    ⟨λ p => ⟨p.1, p.2⟩, λ s => (s.high, s.low), λ _ => rfl, λ _ => rfl⟩

namespace Scenario

/-- The kinds of scenario of (11), in order of usualness. -/
inductive Kind where
  | upstream
  | balanced
  | downstream
  deriving DecidableEq, Fintype, Repr

/-- Usualness of a kind: downstream scenarios are the most usual, upstream the least. -/
def Kind.usualness : Kind → ℕ
  | .upstream => 0
  | .balanced => 1
  | .downstream => 2

instance : LinearOrder Kind := LinearOrder.lift' Kind.usualness (by decide)

theorem Kind.lt_downstream_iff {k : Kind} : k < .downstream ↔ k ≠ .downstream := by
  cases k <;> decide

theorem Kind.upstream_lt_downstream {k l : Kind} (hk : k = .upstream) (hl : l = .downstream) :
    k < l := by
  subst hk hl; decide

variable {α : Type*} [LinearOrder α]

/-- (11): a scenario is downstream when the higher-ranked argument is the more
prominent, upstream when it is the less prominent, and balanced otherwise. -/
def kind (s : Scenario α) : Kind :=
  if s.low < s.high then .downstream else if s.high < s.low then .upstream else .balanced

theorem kind_eq_downstream_iff {s : Scenario α} : s.kind = .downstream ↔ s.low < s.high := by
  unfold kind
  split_ifs with h₁ h₂
  · exact iff_of_true rfl h₁
  · exact iff_of_false (by decide) h₁
  · exact iff_of_false (by decide) h₁

theorem kind_eq_upstream_iff {s : Scenario α} : s.kind = .upstream ↔ s.high < s.low := by
  unfold kind
  split_ifs with h₁ h₂
  · exact iff_of_false (by decide) (lt_asymm h₁)
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by decide) h₂

theorem kind_eq_balanced_iff {s : Scenario α} : s.kind = .balanced ↔ s.high = s.low := by
  unfold kind
  split_ifs with h₁ h₂
  · exact iff_of_false (by decide) h₁.ne'
  · exact iff_of_false (by decide) h₂.ne
  · exact iff_of_true rfl (le_antisymm (not_lt.1 h₁) (not_lt.1 h₂))

/-- (11): `s` is a more usual scenario than `t`. -/
def MoreUsual (s t : Scenario α) : Prop := t.kind < s.kind

end Scenario

/-! ### Universal 1 and its instances -/

section Universals

variable {S L F : Type*} [Preorder L] [Preorder F]

/-- (5) Universal 1, for situations `S` with usualness relation `MoreUsual` and coding
`c`: a more usual situation is never coded longer. -/
def RoleReferenceUniversal (MoreUsual : S → S → Prop) (c : S → L) : Prop :=
  ∀ ⦃s t⦄, MoreUsual s t → c s ≤ c t

/-- (68) The grammatical form-frequency correspondence universal, for frequencies `freq`
and coding `c`: a more frequent pattern is never coded longer. -/
def FormFrequencyCorrespondence (freq : S → F) (c : S → L) : Prop :=
  ∀ ⦃s t⦄, freq t < freq s → c s ≤ c t

/-- (6) Universal 2, relative to a usualness relation: the more usual association is the
more frequent one in language use. -/
def UsualIsFrequent (MoreUsual : S → S → Prop) (freq : S → F) : Prop :=
  ∀ ⦃s t⦄, MoreUsual s t → freq t < freq s

/-- §11.2: Universal 1 follows from Universal 2 and the form-frequency correspondence
universal (68). -/
theorem roleReferenceUniversal_of_formFrequency {MoreUsual : S → S → Prop} {freq : S → F}
    {c : S → L} (h₂ : UsualIsFrequent MoreUsual freq) (h : FormFrequencyCorrespondence freq c) :
    RoleReferenceUniversal MoreUsual c :=
  λ _ _ hst => h (h₂ hst)

variable {α : Type*} [LinearOrder α]

/-- (9): prominence `x` is a more usual association for role `r` than `y`: A and R tend to
be prominent, P and T non-prominent. -/
def MoreUsualFor (r : ArgumentRole) (x y : α) : Prop :=
  (r.IsHighDefault → y < x) ∧ (r.IsLowDefault → x < y)

/-- (13) Universal 3, the single-argument flagging universal, for a split on role `r`
coded by `c`. -/
def SingleArgumentUniversal (r : ArgumentRole) (c : α → L) : Prop :=
  RoleReferenceUniversal (MoreUsualFor r) c

instance (r : ArgumentRole) (c : α → L) [Fintype α] [DecidableRel (α := L) (· ≤ ·)] :
    Decidable (SingleArgumentUniversal r c) := by
  unfold SingleArgumentUniversal RoleReferenceUniversal MoreUsualFor; infer_instance

/-- (21) Universal 6 and (26) Universal 7: for A and R, Universal 3 says the coding is
longer for the less prominent argument. -/
theorem singleArgumentUniversal_iff_antitone {r : ArgumentRole} (h : r.IsHighDefault)
    {c : α → L} : SingleArgumentUniversal r c ↔ Antitone c := by
  have h' : ¬ r.IsLowDefault := by rcases h with rfl | rfl <;> decide
  simp only [SingleArgumentUniversal, RoleReferenceUniversal, MoreUsualFor, h, h',
    true_implies, false_implies, and_true, antitone_iff_forall_lt]
  exact ⟨λ H _ _ hab => H hab, λ H _ _ hts => H hts⟩

/-- (14) Universal 4 and (27) Universal 8: for P and T, Universal 3 says the coding is
longer for the more prominent argument. -/
theorem singleArgumentUniversal_iff_monotone {r : ArgumentRole} (h : r.IsLowDefault)
    {c : α → L} : SingleArgumentUniversal r c ↔ Monotone c := by
  have h' : ¬ r.IsHighDefault := by rcases h with rfl | rfl <;> decide
  simp only [SingleArgumentUniversal, RoleReferenceUniversal, MoreUsualFor, h, h',
    true_implies, false_implies, true_and, monotone_iff_forall_lt]

/-- (16) Universal 5, the scenario universal: coding is longest for upstream, shortest for
downstream and intermediate for balanced scenarios. Universal 10 (54) is its restriction
to `Relative` splits, with the same prediction. -/
def ScenarioUniversal (c : Scenario α → L) : Prop :=
  RoleReferenceUniversal Scenario.MoreUsual c

instance (c : Scenario α → L) [Fintype α] [DecidableRel (α := L) (· ≤ ·)] :
    Decidable (ScenarioUniversal c) := by
  unfold ScenarioUniversal RoleReferenceUniversal Scenario.MoreUsual; infer_instance

/-- Under Universal 5 a downstream scenario is coded no longer than any scenario that is
not downstream. -/
theorem ScenarioUniversal.downstream_le {c : Scenario α → L} (h : ScenarioUniversal c)
    {s t : Scenario α} (hs : s.kind = .downstream) (ht : t.kind ≠ .downstream) :
    c s ≤ c t :=
  h (show t.kind < s.kind by rw [hs, Scenario.Kind.lt_downstream_iff]; exact ht)

/-- fn. 18: a monadic scenario split, in which only the prominence `coargument s` of the
coargument decides the coding; a dyadic split is one that is monadic in neither
argument. -/
def Monadic (coargument : Scenario α → α) (c : Scenario α → L) : Prop :=
  ∀ s t, coargument s = coargument t → c s = c t

instance (coargument : Scenario α → α) (c : Scenario α → L) [Fintype α] [DecidableEq L] :
    Decidable (Monadic coargument c) := by
  unfold Monadic; infer_instance

/-- §8: a relative scenario split, in which the coding is determined by the relation
between the prominence levels of the two arguments. -/
def Relative (c : Scenario α → L) : Prop :=
  ∀ s t, s.kind = t.kind → c s = c t

instance (c : Scenario α → L) [Fintype α] [DecidableEq L] : Decidable (Relative c) := by
  unfold Relative; infer_instance

/-- (42) Universal 9b, the ditransitive person-role universal: the scenario with a
locuphoric R and an aliophoric T is coded no longer than any other. -/
def PersonRoleUniversal (c : Scenario PersonClass → L) : Prop :=
  ∀ s, c ⟨.locuphoric, .aliophoric⟩ ≤ c s

/-- §7.1: Universal 9b is a special case of Universal 5. -/
theorem personRoleUniversal_of_scenarioUniversal {c : Scenario PersonClass → L}
    (h : ScenarioUniversal c) : PersonRoleUniversal c := by
  rintro ⟨_ | _, _ | _⟩ <;> first | exact le_rfl | exact h.downstream_le (by decide) (by decide)

/-- (57) Universal 11, the inverse universal, for verb coding `v`: the inverse form of an
upstream scenario is no shorter than the direct form of a downstream one. -/
def InverseUniversal (v : Scenario α → L) : Prop :=
  ∀ ⦃s t⦄, s.kind = .downstream → t.kind = .upstream → v s ≤ v t

/-- Verb coding that obeys the scenario universal obeys the inverse universal. -/
theorem inverseUniversal_of_scenarioUniversal {v : Scenario α → L} (h : ScenarioUniversal v) :
    InverseUniversal v :=
  λ _ _ hs ht => h (Scenario.Kind.upstream_lt_downstream ht hs)

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
    GivennessAlternationUniversal rate := by
  rintro ⟨_ | _, _ | _⟩ <;> first | exact le_rfl | exact h.downstream_le (by decide) (by decide)

/-- §10.2: a splitting alternation between a shorter and a longer construction, which
alternate in some scenarios and are in complementary distribution in others. -/
def SplittingAlternation (short long : Scenario α → Prop) : Prop :=
  (∃ s, short s ∧ long s) ∧ ∃ s, Xor (short s) (long s)

instance (short long : Scenario α → Prop) [Fintype α] [DecidablePred short]
    [DecidablePred long] : Decidable (SplittingAlternation short long) := by
  unfold SplittingAlternation; infer_instance

/-- The shortest coding available in a scenario: `0` where the shorter construction is
available, `1` otherwise. -/
def minimalCoding (short : Scenario α → Prop) [DecidablePred short] (s : Scenario α) : ℕ :=
  if short s then 0 else 1

end Universals

/-! ### Single-argument splits (§4, §5) -/

/-- (2): Sakha flags a definite P with the accusative. -/
def sakhaP : Definiteness → ℕ
  | .definite => 1
  | .indefinite => 0

/-- (17): Nuorese Sardinian flags a human P with `a`. -/
def sardinianP : AnimacyLevel → ℕ
  | .human => 1
  | .animate | .inanimate => 0

/-- (19): Persian flags a topical P with `-râ`. -/
def persianP : BinaryGivenness → ℕ
  | .given => 1
  | .new => 0

/-- (20): Abruzzese flags a locuphoric P with `a`. -/
def abruzzeseP : PersonClass → ℕ
  | .locuphoric => 1
  | .aliophoric => 0

/-- §4.1.3: English distinguishes P from A only on person forms (*he* ~ *him*). -/
def englishP : Nominality → ℕ
  | .personForm => 1
  | .fullNominal => 0

/-- (22): Godoberi has an ergative form only for aliophoric A; Kham (1) is alike. -/
def godoberiA : PersonClass → ℕ
  | .aliophoric => 1
  | .locuphoric => 0

/-- (23): Warrgamay flags a full-nominal A with the ergative. -/
def warrgamayA : Nominality → ℕ
  | .fullNominal => 1
  | .personForm => 0

/-- (24): Mangarrayi flags an inanimate (neuter) A with the ergative. -/
def mangarrayiA : Animacy → ℕ
  | .inanimate => 1
  | .animate => 0

/-- (25): Central Tibetan flags a focused A with the ergative `-ki'`. -/
def tibetanA : FocusStatus → ℕ
  | .focus => 1
  | .background => 0

/-- (28): French dative clitics are longer than accusative ones only for aliophoric R
(`lui` ~ `le`, `leur` ~ `les`). -/
def frenchR : PersonClass → ℕ
  | .aliophoric => 1
  | .locuphoric => 0

/-- (29): Telkepe Neo-Aramaic flags a full-nominal R with `ta`. -/
def neoAramaicR : Nominality → ℕ
  | .fullNominal => 1
  | .personForm => 0

/-- (30): Yakkha puts an inanimate R in the locative. -/
def yakkhaR : Animacy → ℕ
  | .inanimate => 1
  | .animate => 0

/-- (31): Wolof flags an indefinite R with `ci`. -/
def wolofR : Definiteness → ℕ
  | .indefinite => 1
  | .definite => 0

/-- (32): Ewe flags a person-form T with the serial verb `tsɔ́`. -/
def eweT : Nominality → ℕ
  | .personForm => 1
  | .fullNominal => 0

/-- (33): Akan flags a definite T with the serial verb `de`. -/
def akanT : Definiteness → ℕ
  | .definite => 1
  | .indefinite => 0

/-- (34): Georgian requires the reinforced form (`šeni tavi`) for a locuphoric T. -/
def georgianT : PersonClass → ℕ
  | .locuphoric => 1
  | .aliophoric => 0

/-- §4.1: the split P flagging systems obey Universal 4. -/
theorem universal4_splitP :
    SingleArgumentUniversal .P sakhaP ∧ SingleArgumentUniversal .P sardinianP ∧
      SingleArgumentUniversal .P persianP ∧ SingleArgumentUniversal .P abruzzeseP ∧
      SingleArgumentUniversal .P englishP := by
  decide

/-- §4.2: the split A flagging systems obey Universal 6. -/
theorem universal6_splitA :
    SingleArgumentUniversal .A godoberiA ∧ SingleArgumentUniversal .A warrgamayA ∧
      SingleArgumentUniversal .A mangarrayiA ∧ SingleArgumentUniversal .A tibetanA := by
  decide

/-- §5.1: the split R flagging systems obey Universal 7. -/
theorem universal7_splitR :
    SingleArgumentUniversal .R frenchR ∧ SingleArgumentUniversal .R neoAramaicR ∧
      SingleArgumentUniversal .R yakkhaR ∧ SingleArgumentUniversal .R wolofR := by
  decide

/-- §5.2: the split T flagging systems obey Universal 8. -/
theorem universal8_splitT :
    SingleArgumentUniversal .T eweT ∧ SingleArgumentUniversal .T akanT ∧
      SingleArgumentUniversal .T georgianT := by
  decide

/-! ### Scenario splits (§6, §7) -/

/-- (35): Kolyma Yukaghir flags P with the accusative when A is aliophoric; Teop (3) is
alike. -/
def yukaghirP (s : Scenario PersonClass) : ℕ := if s.high = .aliophoric then 1 else 0

/-- §6.1: Yurok flags P with the accusative when A is aliophoric and P locuphoric. -/
def yurokP (s : Scenario PersonClass) : ℕ :=
  if s.high = .aliophoric ∧ s.low = .locuphoric then 1 else 0

/-- (36): Sahaptin flags A with the ergative when P is locuphoric. -/
def sahaptinA (s : Scenario PersonClass) : ℕ := if s.low = .locuphoric then 1 else 0

/-- (37): Eastern Khanty flags A with the ergative when P is specific. -/
def khantyA (s : Scenario Definiteness) : ℕ := if s.low = .definite then 1 else 0

/-- (38) with §4.1.1: Spanish flags P with `a` when P is human or A is inanimate. -/
def spanishP (s : Scenario AnimacyLevel) : ℕ :=
  if s.low = .human ∨ s.high = .inanimate then 1 else 0

/-- (39): Bulgarian flags R with `na` when T is a locuphoric clitic. -/
def bulgarianR (s : Scenario PersonClass) : ℕ := if s.low = .locuphoric then 1 else 0

/-- (4): English requires `to` on R in the N > pers scenario. -/
def englishR (s : Scenario Nominality) : ℕ := if s = ⟨.fullNominal, .personForm⟩ then 1 else 0

/-- (44): the American varieties of English require `to` on R whenever T is a person
form. -/
def americanEnglishR (s : Scenario Nominality) : ℕ := if s.low = .personForm then 1 else 0

/-- (45): Modern Greek replaces the T proclitic by the independent pronoun in upstream
scenarios. -/
def greekT (s : Scenario PersonClass) : ℕ := if s.kind = .upstream then 1 else 0

/-- (46): Icelandic flags R with `fyrir` when T is animate. -/
def icelandicR (s : Scenario Animacy) : ℕ := if s.low = .animate then 1 else 0

/-- §6: the monotransitive scenario splits obey Universal 5. -/
theorem universal5_monotransitive :
    ScenarioUniversal yukaghirP ∧ ScenarioUniversal yurokP ∧ ScenarioUniversal sahaptinA ∧
      ScenarioUniversal khantyA ∧ ScenarioUniversal spanishP := by
  decide

/-- §7: the ditransitive scenario splits obey Universal 5. -/
theorem universal5_ditransitive :
    ScenarioUniversal bulgarianR ∧ ScenarioUniversal englishR ∧
      ScenarioUniversal americanEnglishR ∧ ScenarioUniversal greekT ∧
      ScenarioUniversal icelandicR := by
  decide

/-- (39): Bulgarian obeys Universal 9b. -/
theorem universal9b_bulgarian : PersonRoleUniversal bulgarianR :=
  personRoleUniversal_of_scenarioUniversal universal5_ditransitive.1

/-- fn. 18: Kolyma Yukaghir's split is monadic and Yurok's dyadic. -/
theorem yukaghir_monadic_yurok_dyadic :
    Monadic Scenario.high yukaghirP ∧
      ¬ Monadic Scenario.high yurokP ∧ ¬ Monadic Scenario.low yurokP := by
  decide

/-! ### Relative scenario splits (§8) -/

/-- (47): Kashmiri puts P in the dative unless A outranks P on the ternary person
scale. -/
def kashmiriP (s : Scenario PersonRank) : ℕ := if s.kind = .downstream then 0 else 1

/-- §8: Fore flags A with the ergative only when P outranks A in animacy. -/
def foreA (s : Scenario AnimacyLevel) : ℕ := if s.kind = .upstream then 1 else 0

/-- §8: Awtuw flags P with the accusative only when P is not lower than A in animacy. -/
def awtuwP (s : Scenario AnimacyLevel) : ℕ := if s.kind = .downstream then 0 else 1

/-- (49): Baule flags T with the serial verb `fà` unless R outranks T on the scale of
(49a). -/
def bauleT (s : Scenario NominalType) : ℕ := if s.kind = .downstream then 0 else 1

/-- §8: the relative scenario splits are relative and obey Universal 10. -/
theorem universal10_relative :
    (Relative kashmiriP ∧ ScenarioUniversal kashmiriP) ∧
      (Relative foreA ∧ ScenarioUniversal foreA) ∧
      (Relative awtuwP ∧ ScenarioUniversal awtuwP) ∧
      (Relative bauleT ∧ ScenarioUniversal bauleT) := by
  decide

/-- §8: Kolyma Yukaghir's monadic split is not relative, since the two balanced person
scenarios are coded differently. -/
theorem yukaghir_not_relative : ¬ Relative yukaghirP := by decide

/-! ### Verbal voice coding (§9) -/

/-- (55): Itonama's inverse prefix `k'i-` appears in upstream scenarios. -/
def itonamaV (s : Scenario PersonClass) : ℕ := if s.kind = .upstream then 1 else 0

/-- (55): Itonama obeys the inverse universal. -/
theorem universal11_itonama : InverseUniversal itonamaV :=
  inverseUniversal_of_scenarioUniversal (by decide)

/-! ### Splitting alternations (§10.2) -/

/-- (64), (65): Lummi's active construction is available unless the scenario is
upstream. -/
def lummiActive (s : Scenario Nominality) : Prop := s.kind ≠ .upstream

instance : DecidablePred lummiActive := λ s => inferInstanceAs (Decidable (s.kind ≠ _))

/-- (64), (65): Lummi's passive construction is available when A is a full nominal. -/
def lummiPassive (s : Scenario Nominality) : Prop := s.high = .fullNominal

instance : DecidablePred lummiPassive := λ s => inferInstanceAs (Decidable (s.high = _))

/-- (66), (67): Koyra Chiini's double object construction is available only in downstream
scenarios; the postpositional dative construction is always available. -/
def koyraChiiniDoubleObject (s : Scenario Nominality) : Prop := s.kind = .downstream

instance : DecidablePred koyraChiiniDoubleObject :=
  λ s => inferInstanceAs (Decidable (s.kind = _))

/-- (4), (60): the English double object construction is available except in the
N > pers scenario; the prepositional dative construction is always available. -/
def englishDoubleObject (s : Scenario Nominality) : Prop := s ≠ ⟨.fullNominal, .personForm⟩

instance : DecidablePred englishDoubleObject := λ s => inferInstanceAs (Decidable (s ≠ _))

/-- §10.2: Lummi, Koyra Chiini and English have splitting alternations whose shortest
available coding obeys Universal 5. -/
theorem splittingAlternations :
    (SplittingAlternation lummiActive lummiPassive ∧
        ScenarioUniversal (minimalCoding lummiActive)) ∧
      (SplittingAlternation koyraChiiniDoubleObject (λ _ => True) ∧
        ScenarioUniversal (minimalCoding koyraChiiniDoubleObject)) ∧
      (SplittingAlternation englishDoubleObject (λ _ => True) ∧
        ScenarioUniversal (minimalCoding englishDoubleObject)) := by
  decide

/-! ### The anti-efficient language (§11.3) -/

/-- §11.3's hypothetical language: the ergative on every topical A and zero coding on a
focused A. -/
def antiEfficientA : FocusStatus → ℕ
  | .background => 1
  | .focus => 0

/-- §11.3's hypothetical language: the accusative on every indefinite P and zero coding
on a definite P. -/
def antiEfficientP : Definiteness → ℕ
  | .indefinite => 1
  | .definite => 0

/-- §11.3: the unattested anti-efficient language violates Universals 6 and 4. -/
theorem antiEfficient_violates :
    ¬ SingleArgumentUniversal .A antiEfficientA ∧
      ¬ SingleArgumentUniversal .P antiEfficientP := by
  decide

end Haspelmath2021
