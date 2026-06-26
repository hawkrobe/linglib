import Mathlib.Data.Fintype.Card
import Linglib.Features.ContainmentPair
import Linglib.Features.Gender.Basic

/-!
# Gender — feature decompositions of the labels
[smith-2015] [smith-2021] [kramer-2015] [adamson-anagnostopoulou-2025]
[hammerly-2019]

Rival feature analyses of gender values. None is baked into `Gender.System`
— the carrier is analysis-neutral, and each scheme here is a presentation a
study can adopt or refute.

* **The split-feature architecture** ([smith-2015]; book version
  [smith-2021]): a grammatical feature has two halves — `uF` legible to
  morphology, `iF` legible to semantics — which "in general match up" but
  "can be distinct or one can be missing altogether". `SplitFeature V`
  encodes this for any value vocabulary. [kramer-2015]'s interpretability
  classification falls out as the special cases (`IsNatural`,
  `IsArbitrary`), and *hybrid* values (`IsHybrid` — [smith-2021]'s
  mismatch zoo: committee-type collectives for number, Russian
  profession nouns for gender, Hebrew be'alim, Chichewa heroes) are
  exactly what the special cases cannot represent.
* **Kramer's gender calculus** ([kramer-2015]): gender features on the
  nominalizing head n, drawn from `KramerN` = {plain, i[±FEM], u[±FEM]}.
  Natural and arbitrary gender differ only in interpretability and receive
  the same exponence at PF (`KramerN.exponence`), which yields the
  calculus's signature limit, here a theorem
  (`KramerN.card_image_exponence_le_three`): **no inventory of
  gender-relevant ns distinguishes more than three agreement classes** —
  Kramer's own argument that >3-gender systems need per-class identity
  features, i.e. a language-particular carrier (`Gender.System`).

## Implementation notes

* `SplitFeature` is φ-generic (its motivating mismatch, *committee*
  uF:SG × iF:PL, is a number value): it lives here until a second feature
  module consumes it, then hoists to a shared file.
* The bivalent [±feminine, ±neuter] presentation ([sauerland-2003]):
  `Gender.Features`, a `ContainmentPairLike` label scheme for sex-based
  three-gender systems — one edge of the φ-feature iso-web
  (`phiKernelEquiv, Studies/Harbour2016.lean`), parallel to `Person.Features` and
  `Number.Features`. Its `no_fourth_gender` is a claim about this scheme,
  not about gender writ large (Fula has 20 controller genders).
* [hammerly-2019] rejects both interpretability schemes (masculine = bare
  GENDER node, no masculine feature; natural/arbitrary derived at LF, not
  represented) — a single-paper analysis, so it belongs in
  `Studies/Hammerly2019.lean`, stated over the same `Gender.System`
  carriers as its rivals.
-/

set_option autoImplicit false

open Features (ContainmentPair ContainmentPairLike)

namespace Gender

/-! ### The split-feature architecture -/

/-- A feature split into a morphology-legible half `uF` and a
    semantics-legible half `iF` ([smith-2015]). The halves usually match,
    but may differ (hybrid values) or be singly absent. -/
structure SplitFeature (V : Type*) where
  /-- The half legible to morphology (agreement, exponence). -/
  uF : Option V
  /-- The half legible to semantics (interpretation). -/
  iF : Option V
  deriving DecidableEq, Repr

namespace SplitFeature

variable {V : Type*} (s : SplitFeature V)

/-- Natural (conceptual) value: both halves present and matched —
    [kramer-2015]'s interpretable gender in split-feature terms. -/
def IsNatural : Prop := ∃ v, s.uF = some v ∧ s.iF = some v

/-- Arbitrary value: morphological half only — [kramer-2015]'s
    uninterpretable gender in split-feature terms. -/
def IsArbitrary : Prop := (∃ v, s.uF = some v) ∧ s.iF = none

/-- Semantic-only value: interpreted but morphologically inert
    (the half [smith-2015] allows to go missing on the uF side). -/
def IsSemanticOnly : Prop := s.uF = none ∧ ∃ v, s.iF = some v

/-- Hybrid value: both halves present and mismatched — committee-type
    nouns ([smith-2015]); unrepresentable in an interpretability
    classification of single feature tokens. -/
def IsHybrid : Prop := ∃ u i, s.uF = some u ∧ s.iF = some i ∧ u ≠ i

/-- Featureless: both halves absent. -/
def IsAbsent : Prop := s.uF = none ∧ s.iF = none

/-- The five cases are exhaustive: every split feature is natural, hybrid,
    arbitrary, semantic-only, or absent. -/
theorem classify (s : SplitFeature V) :
    s.IsNatural ∨ s.IsHybrid ∨ s.IsArbitrary ∨ s.IsSemanticOnly ∨ s.IsAbsent := by
  obtain ⟨_ | u, _ | i⟩ := s
  · exact .inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  · exact .inr (.inr (.inr (.inl ⟨rfl, i, rfl⟩)))
  · exact .inr (.inr (.inl ⟨⟨u, rfl⟩, rfl⟩))
  · rcases eq_or_ne u i with rfl | h
    · exact .inl ⟨u, rfl, rfl⟩
    · exact .inr (.inl ⟨u, i, rfl, rfl, h⟩)

/-- A hybrid value is not natural: the mismatch is real. -/
theorem IsHybrid.not_isNatural {s : SplitFeature V} (h : s.IsHybrid) :
    ¬ s.IsNatural := by
  rintro ⟨v, hu, hi⟩
  obtain ⟨u, i, hu', hi', hne⟩ := h
  rw [hu] at hu'
  rw [hi] at hi'
  exact hne ((Option.some.inj hu').symm.trans (Option.some.inj hi'))

end SplitFeature

/-! ### The bivalent presentation: [±feminine, ±neuter]

[sauerland-2003]'s decomposition of sex-based gender:
**[±feminine]** (feminine and neuter are [+feminine]) and **[±neuter]**
(only neuter is [+neuter]), with the containment [+neuter] → [+feminine]:
neuter is the most specified gender (like singular for number, 1st for
person) and masculine the least. The three well-formed combinations are the
three genders of a sex-based system; the scheme parallels person
[±author] ⊂ [±participant] and number [±atomic] ⊂ [±minimal] — all three are
`ContainmentPairLike` presentations of the same skeleton
(`Features/ContainmentPair.lean`). -/

/-- Bivalent gender features: [±feminine, ±neuter] ([sauerland-2003]).

    The three well-formed combinations yield the three sex-based genders:
    neuter [+feminine, +neuter], feminine [+feminine, −neuter],
    masculine [−feminine, −neuter]. -/
structure Features where
  /-- [+feminine]: referent triggers feminine (or neuter) agreement. -/
  isFeminine : Bool
  /-- [+neuter]: referent triggers neuter agreement. -/
  isNeuter : Bool
  deriving DecidableEq, Repr, Fintype

/-- Neuter features: [+feminine, +neuter]. -/
def neuterF : Features := ⟨true, true⟩

/-- Feminine features: [+feminine, −neuter]. -/
def feminineF : Features := ⟨true, false⟩

/-- Masculine features: [−feminine, −neuter]. -/
def masculineF : Features := ⟨false, false⟩

/-- The `[±feminine, ±neuter]` decomposition is carrier-equivalent to the
    containment pair: `outer` = feminine, `inner` = neuter — one edge of the
    φ-feature iso-web (`phiKernelEquiv, Studies/Harbour2016.lean`). -/
def featuresEquiv : Features ≃ ContainmentPair where
  toFun f := ⟨f.isFeminine, f.isNeuter⟩
  invFun p := ⟨p.outer, p.inner⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three canonical gender values land on the three well-formed cells. -/
@[simp] theorem neuter_is_maximal :
    ContainmentPairLike.toPair neuterF = .maximal := rfl
@[simp] theorem feminine_is_intermediate :
    ContainmentPairLike.toPair feminineF = .intermediate := rfl
@[simp] theorem masculine_is_minimal :
    ContainmentPairLike.toPair masculineF = .minimal := rfl

/-- Well-formedness: [+neuter] → [+feminine] — neuter entails feminine in
    the feature geometry, inherited from `ContainmentPair.WellFormed`. -/
abbrev Features.WellFormed (gf : Features) : Prop :=
  ContainmentPairLike.WellFormed gf

/-- No 4-way distinction *within this scheme* (inherited from
    `ContainmentPairLike.no_four_way`) — a claim about the sex-based
    bivalent presentation, not about gender systems writ large. -/
theorem no_fourth_gender :
    ∀ (a b c d : Features),
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    ContainmentPairLike.no_four_way a b c d ha hb hc hd

@[simp] theorem neuter_wellFormed : neuterF.WellFormed := by decide
@[simp] theorem feminine_wellFormed : feminineF.WellFormed := by decide
@[simp] theorem masculine_wellFormed : masculineF.WellFormed := by decide

/-- The filtered combination [−feminine, +neuter] is the only one that
    violates containment. -/
theorem illFormed_only : ¬ (⟨false, true⟩ : Features).WellFormed := by decide

/-- Exactly 3 well-formed feature combinations (= 3 genders) — the carrier
    count of the containment chain (`ContainmentPair.card_wellFormed`). -/
theorem card_wellFormed :
    Fintype.card {gf : Features // gf.WellFormed} = 3 := by decide

/-- Containment: [+neuter] → [+feminine] for all well-formed features. -/
theorem neuter_implies_feminine :
    ∀ f : Features, f.WellFormed → f.isNeuter = true → f.isFeminine = true := by
  decide

/-- Map gender features to the comparative labels. -/
def Features.toGender : Features → Option Gender
  | ⟨true, true⟩   => some .neuter
  | ⟨true, false⟩  => some .feminine
  | ⟨false, false⟩ => some .masculine
  | ⟨false, true⟩  => none  -- ill-formed

/-- Map comparative labels to gender features (partial — only sex-based
    labels have feature equivalents). -/
def Features.fromGender : Gender → Option Features
  | .neuter    => some neuterF
  | .feminine  => some feminineF
  | .masculine => some masculineF
  | _          => none

/-- Round-trip: `fromGender ∘ toGender = some` for all well-formed
    features. -/
theorem roundtrip_fromGender_toGender :
    [neuterF, feminineF, masculineF].all
      (λ f => f.toGender.bind Features.fromGender == some f) = true := by
  decide

/-! ### Kramer's gender calculus and its three-gender bound -/

/-- A gender-relevant nominalizing head in [kramer-2015]'s calculus:
    plain n, or n bearing an interpretable or uninterpretable [±FEM]. -/
inductive KramerN where
  /-- n with no gender features (Romanian default-gender nouns). -/
  | plain
  /-- n i[+FEM]: interpretable feminine (natural gender). -/
  | iFem
  /-- n i[−FEM]: interpretable masculine (natural gender). -/
  | iMasc
  /-- n u[+FEM]: uninterpretable feminine (arbitrary gender). -/
  | uFem
  /-- n u[−FEM]: uninterpretable masculine (arbitrary gender). -/
  | uMasc
  deriving DecidableEq, Repr, Fintype

namespace KramerN

/-- What agreement exponence sees: the feature value, not its
    interpretability — natural and arbitrary gender receive the same
    Vocabulary Item ([kramer-2015]). `none` = no gender features. -/
def exponence : KramerN → Option Bool
  | .plain => none
  | .iFem  => some true
  | .uFem  => some true
  | .iMasc => some false
  | .uMasc => some false

/-- Each Kramer head reads as a split feature: interpretable heads value
    both halves, uninterpretable heads only the morphological half. -/
def toSplitFeature : KramerN → SplitFeature Bool
  | .plain => ⟨none, none⟩
  | .iFem  => ⟨some true, some true⟩
  | .iMasc => ⟨some false, some false⟩
  | .uFem  => ⟨some true, none⟩
  | .uMasc => ⟨some false, none⟩

/-- The calculus generates no hybrids: every Kramer head is natural,
    arbitrary, or absent in split-feature terms — the representational gap
    [smith-2015]'s architecture closes. -/
theorem toSplitFeature_not_isHybrid (n : KramerN) :
    ¬ n.toSplitFeature.IsHybrid := by
  cases n <;> rintro ⟨u, i, hu, hi, hne⟩ <;> simp_all [toSplitFeature]

/-- [kramer-2015]'s three-gender bound, as a theorem: any inventory of
    gender-relevant ns distinguishes at most three agreement classes
    ([+FEM], [−FEM], bare). More than three genders therefore requires
    machinery beyond the calculus — per-class identity features, i.e. a
    language-particular `Gender.System` carrier. -/
theorem card_image_exponence_le_three (inv : Finset KramerN) :
    (inv.image exponence).card ≤ 3 :=
  le_trans (Finset.card_le_univ _) (by decide)

end KramerN

end Gender
