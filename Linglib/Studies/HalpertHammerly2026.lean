import Linglib.Features.ContainmentPair
import Linglib.Features.Person.Decomposition
import Linglib.Fragments.Xhosa.Nouns
import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Data.Examples.HalpertHammerly2026
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Halpert and Hammerly (2026): Reconciling Animacy and Noun Class in Bantu

This file formalizes the Core Noun Class Hypothesis of [halpert-hammerly-2026]: every Bantu
noun is specified for [±Animate, ±Human] on its nominalizing head, so falls into one of the
core classes HUMAN, ANIMATE, and INANIMATE, canonically classes 1/2, 9/10, and 7/8 (19),
whatever class its prefix shows. The features are [hammerly-2023]'s sets of ontological
primitives, author, addressee, human, animal, force, concrete, and abstract, ranked by
prominence (1): a feature is the primitives at least as prominent as a cutoff, so features nest
(3), and a bivalent specification denotes the intersection of features and their complements,
`category`. Every such category is order-convex, `category_ordConnected`, which is the paper's
prediction that no conflation in the sense of [mcginnis-2005] groups humans with natural forces
to the exclusion of animals (section 2); at the limit each primitive is its own category, the
contrastive hierarchy (4); the incoherent combination [−Animate, +Human] of footnote 10 denotes
the empty set; and local persons are a more highly specified subset of HUMAN, the containment
behind Lubukusu alternative agreement (8) and Zulu person reduction (10). Core class is spelled
out by the nominalizing final vowel, -i for [+Human] and -o otherwise (22), and class prefixes
are secondary n heads stacked over the core as in [fuchs-van-der-wal-2022]'s diminutives (26):
a noun whose prefix class disagrees with its core carries a secondary n with a class feature of
its own (28), `Nominal.ofEntry`, built from the Xhosa nouns fragment. Agreement then depends on
the probe (29): a flat probe finds the secondary n, so
agrees with the prefix class as in Zulu, `agreement_flat`, while a probe relativized to
[+Animate] searches past it to the core, the animacy override of Chiyao (11) and Swahili (13)
and the animate-only object marking of Nyaturu (14), `agreement_animateProbe`. That Swahili
overrides to class 1/2 for humans and animals alike, and that Xhosa's class 8 and 10 markers are
syncretic, are exponents conditioned on [±Animate] or on [±Human] alone. The proposal converges
with [carstens-2026]'s stacking of genders over a core, [kramer-2015]'s gendered n, but grounds
the core in the containment features Carstens rejects (footnote 12). The examples are the rows
of `Data.Examples.HalpertHammerly2026`.

## Implementation notes

The feature-bearing heads of a nominal are the core n and, when the prefix class is one of the
three core classes and differs from the core, a secondary n bearing that class's features; the
paper leaves the features of classes 3/4 and 5/6 open (section 6), so `Nominal.ofEntry` is
undefined for them, and the fragment's semantic animacy stands in for the grammatical core,
which the paper allows to be idiosyncratic. Agreement with conjoined subjects, (15) to (18), is
recorded as data only, since the paper assigns its resolution to a separate mechanism.

## References

* [halpert-hammerly-2026]
* [hammerly-2023]
* [mcginnis-2005]
* [fuchs-van-der-wal-2022]
* [taraldsen-et-al-2018]
* [carstens-2026]
* [kramer-2015]
-/

namespace HalpertHammerly2026

open Bantu Minimalist

/-! ### Containment features, section 2 -/

/-- The ontological primitives of (1) and (3), most prominent first: the author I, the
addressee U, other humans O, animals A, natural forces F, concrete things R, and abstract
things S. -/
inductive Primitive where
  | author | addressee | human | animal | force | concrete | abstract
  deriving DecidableEq, Repr, Fintype

namespace Primitive

/-- Prominence rank, the author highest. -/
def rank : Primitive → ℕ
  | .author => 0 | .addressee => 1 | .human => 2 | .animal => 3
  | .force => 4 | .concrete => 5 | .abstract => 6

/-- The prominence order (1): `author < addressee < human < animal < force < concrete <
abstract`. -/
instance : LinearOrder Primitive :=
  LinearOrder.lift' rank (λ a b h => by cases a <;> cases b <;> simp_all [rank])

end Primitive

/-- A feature of (3), the primitives at least as prominent as its cutoff: [Author] is
`feature .author`, [Participant] `feature .addressee`, [Human] `feature .human`, [Animate]
`feature .animal`, [Agent] `feature .force`, [Individuated] `feature .concrete`, and ɸ
`feature .abstract`, each contained in the next. -/
abbrev feature (p : Primitive) : Set Primitive := Set.Iic p

/-- A bivalent value of a feature: the feature itself or its complement. -/
def value (p : Primitive) : Bool → Set Primitive
  | true => feature p
  | false => (feature p)ᶜ

theorem value_ordConnected (p : Primitive) (b : Bool) : (value p b).OrdConnected := by
  cases b
  · rw [value, feature, Set.compl_Iic]; exact Set.ordConnected_Ioi
  · exact Set.ordConnected_Iic

/-- A specification: the value, if any, of each feature. -/
abbrev Spec := Primitive → Option Bool

/-- The category a specification defines, the intersection of the values it specifies ((4),
(5)); a feature left unspecified is conflated. -/
def category (s : Spec) : Set Primitive := ⋂ p, ⋂ b ∈ s p, value p b

theorem mem_category {s : Spec} {x : Primitive} :
    x ∈ category s ↔ ∀ p b, s p = some b → (x ≤ p ↔ b = true) := by
  simp only [category, Set.mem_iInter, Option.mem_def]
  refine forall₂_congr λ p b => imp_congr_right λ _ => ?_
  cases b <;> simp [value, feature]

/-- Feature-definable categories are order-convex. -/
theorem category_ordConnected (s : Spec) : (category s).OrdConnected :=
  Set.ordConnected_iInter λ p => Set.ordConnected_biInter λ b _ => value_ordConnected p b

/-- The impossible conflation (section 2): no category encompasses non-interlocutor humans and
natural forces to the exclusion of animals. -/
theorem animal_mem_category {s : Spec} (h₁ : .human ∈ category s)
    (h₂ : .force ∈ category s) : .animal ∈ category s :=
  (category_ordConnected s).out h₁ h₂ ⟨by decide, by decide⟩

/-- The full specification singling out a primitive (4): positive on every feature at or
above it, negative on every feature below it. -/
def contrast (p : Primitive) : Spec := λ q => some (decide (p ≤ q))

/-- At the limit each primitive defines its own category, the leaves of the contrastive
hierarchy (4). -/
theorem category_contrast (p : Primitive) : category (contrast p) = {p} := by
  ext x
  simp only [mem_category, contrast, Option.some.injEq, Set.mem_singleton_iff]
  revert x p
  decide

/-! ### Core noun classes, (19) and (22) -/

/-- The bivalent features [±Animate, ±Human] of a Bantu nominalizing head (19). -/
structure AnimacyFeatures where
  isAnimate : Bool
  isHuman : Bool
  deriving DecidableEq, Repr, Fintype

namespace AnimacyFeatures

/-- The features as a containment pair, [+Human] the inner feature entailing [+Animate]. -/
def featuresEquiv : AnimacyFeatures ≃ Features.ContainmentPair where
  toFun af := ⟨af.isAnimate, af.isHuman⟩
  invFun p := ⟨p.outer, p.inner⟩
  left_inv := λ ⟨_, _⟩ => rfl
  right_inv := λ ⟨_, _⟩ => rfl

instance : Features.ContainmentPairLike AnimacyFeatures := .ofEquiv featuresEquiv

/-- Coherence: [+Human] entails [+Animate] (footnote 10). -/
abbrev WellFormed (af : AnimacyFeatures) : Prop := Features.ContainmentPairLike.WellFormed af

/-- The features as a specification of the [Animate] and [Human] features of (3). -/
def spec (af : AnimacyFeatures) : Spec := λ q =>
  if q = .animal then some af.isAnimate else if q = .human then some af.isHuman else none

/-- The incoherent combination is the one denoting no primitive at all. -/
theorem category_spec_eq_empty_iff (af : AnimacyFeatures) :
    category af.spec = ∅ ↔ ¬ af.WellFormed := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_category]
  revert af
  decide

end AnimacyFeatures

/-- A core noun class (19): a coherent specification of [±Animate, ±Human]. -/
abbrev Core := {af : AnimacyFeatures // af.WellFormed}

namespace Core

/-- HUMAN, [+Animate, +Human]. -/
def human : Core := ⟨⟨true, true⟩, by decide⟩

/-- ANIMATE, [+Animate, −Human]. -/
def animal : Core := ⟨⟨true, false⟩, by decide⟩

/-- INANIMATE, [−Animate, −Human]. -/
def inanimate : Core := ⟨⟨false, false⟩, by decide⟩

/-- HUMAN denotes every primitive down to the local persons: the class contains the speech-act
participants, the containment behind their reduction to class 1/2 ((8), (10)). -/
theorem category_spec_human : category human.1.spec = Set.Iic .human := by
  ext x
  simp only [mem_category, Set.mem_Iic]
  revert x
  decide

/-- INANIMATE is the conflation of natural forces, concrete things, and abstract things, the
GENERIC INANIMATE of (5). -/
theorem category_spec_inanimate : category inanimate.1.spec = Set.Ioi .animal := by
  ext x
  simp only [mem_category, Set.mem_Ioi]
  revert x
  decide

/-- The core class of a referent of a given animacy. -/
def ofAnimacyLevel : Features.Prominence.AnimacyLevel → Core
  | .human => human
  | .animate => animal
  | .inanimate => inanimate

/-- (19) in Xhosa: HUMAN is class 1/2, ANIMATE class 9/10, and INANIMATE class 7/8. -/
def gender : Core → Xhosa.Gender
  | ⟨⟨true, true⟩, _⟩ => .genderA
  | ⟨⟨true, false⟩, _⟩ => .genderE
  | ⟨⟨false, false⟩, _⟩ => .genderD
  | ⟨⟨false, true⟩, h⟩ => absurd h (by decide)

/-- The core class of a gender, read off the semantic core the fragment records for it; none
for a purely formal gender. -/
def ofGender (g : Xhosa.Gender) : Option Core :=
  match g.status with
  | .interpretable .human => some human
  | .interpretable .animal => some animal
  | .interpretable .inanimate => some inanimate
  | _ => none

/-- (19) agrees with the fragment's semantic cores: the gender a core class is spelled out in
bears that core. -/
theorem ofGender_gender : ∀ c : Core, ofGender c.gender = some c := by decide

theorem gender_eq_of_ofGender {g : Xhosa.Gender} {c : Core} (h : ofGender g = some c) :
    c.gender = g := by
  revert h; revert c; revert g; decide

/-- The nominalizing final vowels (22). -/
inductive FinalVowel where
  | i | o
  deriving DecidableEq, Repr

/-- (22): the core n is spelled out as -i when [+Human] and as -o otherwise. -/
def finalVowel (c : Core) : FinalVowel := if c.1.isHuman then .i else .o

/-- At the core, -i is exactly class 1/2: the 73% of Chichewa -i nouns in class 1 reported in
section 4.1 are the aligned nominals, the rest stacked. -/
theorem finalVowel_eq_i_iff (c : Core) : c.finalVowel = .i ↔ c.gender = .genderA := by
  revert c; decide

/-- An exponent conditioned on [±Animate] alone, as Swahili's class 1/2 agreement under animacy
override (13), treats humans and animals alike: the GENERIC ANIMATE conflation of (5). -/
theorem eq_of_factorsThrough_isAnimate {β : Type*} {f : Core → β}
    (hf : Function.FactorsThrough f (·.1.isAnimate)) : f human = f animal :=
  hf (a := human) (b := animal) rfl

/-- Xhosa's core genders distinguish [±Human] within [+Animate]. -/
theorem not_factorsThrough_gender : ¬ Function.FactorsThrough gender (·.1.isAnimate) :=
  λ h => absurd (h (a := human) (b := animal) rfl) (by decide)

/-- The plural subject marker of a core class's gender. -/
def pluralSubjPrefix (c : Core) : String := c.gender.pluralClass.subjPrefix

/-- Xhosa's class 8 and class 10 subject markers are both *zi-* (footnote 7): the plural marker
is conditioned on [±Human] alone, so ANIMATE and INANIMATE share it. -/
theorem pluralSubjPrefix_factorsThrough :
    Function.FactorsThrough pluralSubjPrefix (·.1.isHuman) := by
  intro a b; revert a b; decide

end Core

/-! ### Local persons -/

/-- The person features [±Participant, ±Author] as a specification of (3). -/
def personSpec (pf : Person.Features) : Spec := λ q =>
  if q = .addressee then some pf.hasParticipant
  else if q = .author then some pf.hasAuthor else none

/-- Local persons are a more highly specified subset of HUMAN (section 3.2): a participant's
category lies inside the core class, so a probe for class 1/2 finds them, as Lubukusu
alternative agreement (8) and Zulu person reduction (10) show. -/
theorem category_personSpec_subset {pf : Person.Features} (h : pf.hasParticipant = true) :
    category (personSpec pf) ⊆ category Core.human.1.spec := by
  rw [Core.category_spec_human]
  intro x hx
  have hx' := mem_category.mp hx .addressee pf.hasParticipant (by simp [personSpec])
  rw [h] at hx'
  exact le_trans (hx'.mpr rfl) (by decide)

/-! ### Stacked nominals, (26) to (29) -/

/-- The feature-bearing heads of a nominal (26): the core n beneath an optional secondary n
with a class feature of its own ((27), (28)); an aligned noun's secondary n bears none and is
spelled out by the core. -/
structure Nominal where
  core : Core
  secondary : Option Core
  deriving DecidableEq, Repr

namespace Nominal

/-- The goals a probe on the nominal meets, outermost first. -/
def heads (n : Nominal) : List Core := n.secondary.toList ++ [n.core]

/-- The class prefix: the allomorph of the outermost n, chosen by the core when the secondary n
bears no feature (27). -/
def prefixGender (n : Nominal) : Xhosa.Gender := (n.secondary.getD n.core).gender

/-- A nominal from a Xhosa noun (28): the core from the entity denoted, and a secondary n
bearing the prefix class's features when that class is a core class other than the core's;
undefined for the classes whose features the paper leaves open. -/
def ofEntry (e : Xhosa.NounEntry) : Option Nominal :=
  (Xhosa.Gender.ofSingular e.cls).bind λ g =>
    let core := Core.ofAnimacyLevel e.animacy
    if g = core.gender then some ⟨core, none⟩
    else (Core.ofGender g).map λ s => ⟨core, some s⟩

/-- The prefix class of a nominal is the noun's class. -/
theorem ofSingular_prefixGender {e : Xhosa.NounEntry} {n : Nominal} (h : ofEntry e = some n) :
    Xhosa.Gender.ofSingular e.cls = some n.prefixGender := by
  unfold ofEntry at h
  rcases hg : Xhosa.Gender.ofSingular e.cls with _ | g
  · simp [hg] at h
  · simp only [hg, Option.bind_some] at h
    split at h
    · obtain rfl := Option.some.inj h
      simp_all [prefixGender]
    · rcases hs : Core.ofGender g with _ | s
      · simp [hs] at h
      · simp only [hs, Option.map_some, Option.some.injEq] at h
        subst h
        rw [prefixGender, Option.getD_some, Core.gender_eq_of_ofGender hs]

/-- (28): *isikhohleli* 'coughing person' is a human core under a class 7 secondary n, its final
vowel the animate -i and its prefix class 7. -/
theorem ofEntry_isikhohleli :
    ofEntry Xhosa.Nouns.isikhohleli = some ⟨Core.human, some Core.inanimate⟩ := by decide

/-- (27a) and (27c): *umkhohleli* 'coughing person' and *isikhohlela* 'phlegm' are aligned, the
prefix class the core's own. -/
theorem ofEntry_aligned :
    ofEntry Xhosa.Nouns.umkhohleli = some ⟨Core.human, none⟩ ∧
      ofEntry Xhosa.Nouns.isikhohlela = some ⟨Core.inanimate, none⟩ := by decide

end Nominal

/-- (29a): the flat ɸ probe, to which any n is visible. -/
def flat : Probe Core := Probe.indiscriminate

/-- (29b): the ɸ probe relativized to [+Animate]. -/
def animateProbe : Probe Core := Probe.ofVis (·.1.isAnimate)

/-- The gender a probe agrees in: the allomorph of the n it finds. -/
def agreement (p : Probe Core) (n : Nominal) : Option Xhosa.Gender :=
  (p.search n.heads).map Core.gender

/-- Zulu: a flat probe finds the outermost n, so agreement tracks the prefix class (29a). -/
theorem agreement_flat (n : Nominal) : agreement flat n = some n.prefixGender := by
  rcases n with ⟨c, _ | s⟩ <;> rfl

/-- Swahili: with an inanimate secondary n over an animate core, as in (28), the relativized
probe searches past the secondary n to the core (29b). -/
theorem animateProbe_search {n : Nominal} (hc : n.core.1.isAnimate = true)
    (hs : ∀ s ∈ n.secondary, s.1.isAnimate = false) :
    animateProbe.search n.heads = some n.core := by
  rcases n with ⟨c, _ | s⟩ <;> simp only at hc hs
  · simp [animateProbe, Probe.search, Nominal.heads, Probe.ofVis, hc]
  · simp [animateProbe, Probe.search, Nominal.heads, Probe.ofVis, hc, hs s rfl]

/-- Animacy override ((11), (13)): the relativized probe agrees with the core class. -/
theorem agreement_animateProbe {n : Nominal} (hc : n.core.1.isAnimate = true)
    (hs : ∀ s ∈ n.secondary, s.1.isAnimate = false) :
    agreement animateProbe n = some n.core.gender := by
  rw [agreement, animateProbe_search hc hs, Option.map_some]

/-- Nyaturu object doubling (14): an object probe relativized to [+Animate] is valued by an
aligned noun iff its core is animate, so an inanimate object leaves it unvalued and no object
marker surfaces. -/
theorem animateProbe_outcome (c : Core) :
    animateProbe.outcome (Nominal.mk c none).heads = .valued ↔ c.1.isAnimate = true := by
  simp [Probe.outcome_eq_valued_iff, Nominal.heads, animateProbe, Probe.ofVis]

/-- (28) through (29): *isikhohleli* agrees in class 7 with a flat probe and in class 1 with the
relativized one. -/
theorem isikhohleli_agreement :
    (Nominal.ofEntry Xhosa.Nouns.isikhohleli).bind (agreement flat) = some .genderD ∧
      (Nominal.ofEntry Xhosa.Nouns.isikhohleli).bind (agreement animateProbe) = some .genderA := by
  decide

end HalpertHammerly2026
