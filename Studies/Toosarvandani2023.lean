module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Minimalist.Phi.Lattice
public import Linglib.Data.Examples.Toosarvandani2023

/-!
# Toosarvandani (2023): The Interpretation and Grammatical Representation of Animacy

The third person plural pronouns of Southeastern Sierra Zapotec distinguish elders, other humans,
animals and inanimates, refer to heterogeneous groups, and give a mixed group the most marked
pronoun (14). Toosarvandani composes animacy features as Harbour and Kratzer compose person
features: a feature denotes the lattice of groups of its atoms (48), (58), features combine by the
pairwise join `⊕` (50), mathlib's `⊻`, and Lexical Complementarity (52) restricts a pronoun to
what no more specified pronoun denotes. Because person and animacy features share one head, the
condition on Agree behind the person-case constraint (86) compares them together.

## Main results

* `specification_eq_containing`: along an entailment chain, a specification denotes the groups
  containing an atom of its most specific feature (53), (62).
* `mixed_group_marked`, `mem_elder_lexComp_iff`: a mixed group takes the most marked pronoun, and
  the local persons take the speaker and addressee away from the elder pronoun.
* `singular_containing`, `exists_plural_sups_singular`: number composes by intersection after
  person and animacy and cannot precede them (57), (63).
* `gender_incomparable`: disjoint feature denotations give pronouns neither of which is the more
  specified (71).
* `agrees_iff`, `AgreesUnder.mono`: Agree holds iff the subject is at least as high on the
  hierarchy (77)–(81), and a probe relativized to fewer animacy features, as in Laxopa and
  Zoogocho, collapses the distinctions it does not see.

## Implementation notes

Individuals are a finite type and a group a nonempty finite set of atoms, the join being
union, as in `Syntax/Minimalist/Phi/Lattice.lean`, where the composition and complementarity
lemmas live; a feature's atoms are a `Finset`, with the speaker and addressee among the
elders, (58a). Context-dependence, (54), is not modelled: the associate relation is left to
the context. The person-based constraint is absolute in Zapotec while (86) derives a relative
one, a difference the paper attributes to the probe's relativization, and the same-category
pairings that (86) licenses are not in the data. The Agree-based theory generalizes
Deal's, with the probe's features sequenced after Coon and Keine so that only the
features of the highest head, person and animacy, enter the comparison. The Yalálag clitic
data of (77)–(81) and the English context-dependence examples of (16)–(18) are the rows of
`Data.Examples.Toosarvandani2023`.

## References

* [toosarvandani-2023]
* [harbour-2016]
* [kratzer-2009]
* [link-1983]
* [deal-2024]
* [coon-keine-2021]
-/

@[expose] public section

namespace Toosarvandani2023

open Minimalist.Phi.Lattice Finset
open scoped FinsetFamily

/-! ### Features and their composition (section 3) -/

variable {Ind : Type*} [DecidableEq Ind] [Fintype Ind]

/-- The denotation of π holds every singular or plural individual (48c). -/
def piDen : Finset (Finset Ind) := nePowerset univ

/-- A feature specification adds the features' lattices by `⊻` over π, the last listed
innermost (51), (61). -/
def specification (fs : List (Finset Ind)) : Finset (Finset Ind) :=
  fs.foldr (fun X acc ↦ nePowerset X ⊻ acc) piDen

@[simp] theorem specification_nil : specification ([] : List (Finset Ind)) = piDen := rfl

@[simp] theorem specification_cons (X : Finset Ind) (fs : List (Finset Ind)) :
    specification (X :: fs) = nePowerset X ⊻ specification fs := rfl

/-- Along an entailment chain of features, a specification denotes the groups containing an atom
of its most specific feature (53), (62). -/
theorem specification_eq_containing : ∀ {fs : List (Finset Ind)} {X : Finset Ind},
    (X :: fs).Pairwise (· ⊆ ·) → specification (X :: fs) = containing X univ
  | [], X, _ => nePowerset_sups_nePowerset (subset_univ X)
  | Y :: fs, X, h => by
    have h' := List.pairwise_cons.1 h
    rw [specification_cons, specification_eq_containing h'.2,
      nePowerset_sups_containing (h'.1 Y (by simp)) (subset_univ _)]

/-- A group of an elder and a nonelder human lies in the elder and the human specifications, and
lexical complementarity removes it from the human pronoun, marked reference (62). -/
theorem mixed_group_marked {E H : Finset Ind} {e h : Ind} (he : e ∈ E) (hh : h ∈ H) :
    {e, h} ∈ containing E univ ∧ {e, h} ∈ containing H univ ∧
      {e, h} ∉ containing H univ \ containing E univ :=
  ⟨mem_containing_iff.2 ⟨subset_univ _, e, by simp [he]⟩,
    mem_containing_iff.2 ⟨subset_univ _, h, by simp [hh]⟩,
    fun hm ↦ (mem_containing_sdiff_containing_iff.1 hm).2.2 ⟨e, by simp [he]⟩⟩

/-- Against the local persons, whose most specific features have the speaker and the addressee as
atoms, the elder pronoun refers to the groups with an elder and no conversational participant
(62a). -/
theorem mem_elder_lexComp_iff {E : Finset Ind} {i u : Ind} {s : Finset Ind} :
    s ∈ containing E univ \ containing {i, u} univ ↔
      (s ∩ E).Nonempty ∧ i ∉ s ∧ u ∉ s := by
  rw [mem_containing_sdiff_containing_iff, not_nonempty_iff_eq_empty, eq_empty_iff_forall_notMem]
  simp only [subset_univ, true_and, mem_inter, mem_insert, mem_singleton, not_and, not_or]
  constructor
  · rintro ⟨hE, h⟩
    exact ⟨hE, fun hi ↦ (h i hi).1 rfl, fun hu ↦ (h u hu).2 rfl⟩
  · rintro ⟨hE, hi, hu⟩
    exact ⟨hE, fun x hx ↦ ⟨fun h ↦ hi (h ▸ hx), fun h ↦ hu (h ▸ hx)⟩⟩

/-! ### Number (section 3.2) -/

/-- *Singular* keeps the atomic individuals, composing by intersection (56a). -/
def singular (L : Finset (Finset Ind)) : Finset (Finset Ind) := L.filter fun s ↦ s.card = 1

/-- Composed after person and animacy, *singular* leaves a specification's atoms (57). -/
theorem singular_containing (X : Finset Ind) : singular (containing X univ) = X.image ({·}) := by
  ext s
  simp only [singular, mem_filter, mem_containing_iff, subset_univ, true_and, card_eq_one,
    mem_image]
  constructor
  · rintro ⟨hX, a, rfl⟩
    obtain ⟨b, hb⟩ := hX
    rw [mem_inter, mem_singleton] at hb
    exact ⟨a, hb.1 ▸ hb.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, by simp [ha]⟩, a, rfl⟩

/-- A feature composed by `⊻` after *singular* restores pluralities (63). -/
theorem pair_mem_sups_singular {X : Finset Ind} {x : Ind} (hx : x ∈ X) (y : Ind) :
    ({x, y} : Finset Ind) ∈ nePowerset X ⊻ singular piDen := by
  rw [insert_eq]
  exact sup_mem_sups
    (mem_nePowerset_iff.2 ⟨singleton_nonempty x, singleton_subset_iff.2 hx⟩)
    (mem_filter.2
      ⟨mem_nePowerset_iff.2 ⟨singleton_nonempty y, subset_univ _⟩, card_singleton y⟩)

/-- So person and animacy must compose before number. -/
theorem exists_plural_sups_singular {X : Finset Ind} {x y : Ind} (hx : x ∈ X) (hxy : x ≠ y) :
    ∃ s ∈ nePowerset X ⊻ singular piDen, s.card ≠ 1 :=
  ⟨{x, y}, pair_mem_sups_singular hx y, by rw [card_pair hxy]; decide⟩

/-! ### Social gender (section 3.5) -/

/-- Feminine and masculine atoms are disjoint, so the pronouns their features would compose by
`⊻` are incomparable and lexical complementarity cannot restrict either (71). -/
theorem gender_incomparable {F M : Finset Ind} (hd : Disjoint F M) (hF : F.Nonempty)
    (hM : M.Nonempty) :
    ¬ containing F univ ⊆ containing M univ ∧ ¬ containing M univ ⊆ containing F univ :=
  ⟨containing_not_subset_of_disjoint hd hF (subset_univ _),
    containing_not_subset_of_disjoint hd.symm hM (subset_univ _)⟩

/-! ### The person-case constraint (section 4) -/

/-- The features of the highest nominal head in Zapotec form a chain, each entailing the next
(60). -/
inductive Feature where
  | speaker
  | participant
  | elder
  | human
  | animate
  | pi
  deriving DecidableEq, Fintype, Repr

/-- Position in the chain, from the most specific. -/
def Feature.rank : Feature → ℕ
  | .speaker => 0
  | .participant => 1
  | .elder => 2
  | .human => 3
  | .animate => 4
  | .pi => 5

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

/-- The pronoun categories of Table 1, clusivity set aside. -/
inductive Pronoun where
  | first
  | second
  | thirdElder
  | thirdHuman
  | thirdAnimal
  | thirdInanimate
  deriving DecidableEq, Fintype, Repr

/-- The most specific feature of a category's specification, (60)–(61). -/
def Pronoun.top : Pronoun → Feature
  | .first => .speaker
  | .second => .participant
  | .thirdElder => .elder
  | .thirdHuman => .human
  | .thirdAnimal => .animate
  | .thirdInanimate => .pi

/-- A category's feature specification is its most specific feature and all it entails. -/
def Pronoun.features (p : Pronoun) : Finset Feature := univ.filter (p.top ≤ ·)

/-- Specifications are nested as the hierarchy orders the categories. -/
theorem features_subset_iff {p q : Pronoun} : p.features ⊆ q.features ↔ q.top ≤ p.top :=
  ⟨fun h ↦ (mem_filter.1 (h (mem_filter.2 ⟨mem_univ _, le_refl _⟩))).2,
    fun h _ hf ↦ mem_filter.2 ⟨mem_univ _, h.trans (mem_filter.1 hf).2⟩⟩

/-- A head Agrees with a subject and an object pronoun, and both cliticize, iff the subject has
all of the object's features (86). -/
def Agrees (subj obj : Pronoun) : Prop := obj.features ⊆ subj.features

instance (subj obj : Pronoun) : Decidable (Agrees subj obj) :=
  inferInstanceAs (Decidable (obj.features ⊆ subj.features))

/-- The specifications form a chain, so Agree holds iff the subject is at least as high on the
hierarchy: the object clitic is blocked exactly when the object outranks the subject,
(77)–(81). -/
theorem agrees_iff {subj obj : Pronoun} : Agrees subj obj ↔ subj.top ≤ obj.top :=
  features_subset_iff

/-- A probe relativized to the features `R` compares only those. -/
def AgreesUnder (R : Finset Feature) (subj obj : Pronoun) : Prop :=
  obj.features ∩ R ⊆ subj.features ∩ R

instance (R : Finset Feature) (subj obj : Pronoun) : Decidable (AgreesUnder R subj obj) :=
  inferInstanceAs (Decidable (obj.features ∩ R ⊆ subj.features ∩ R))

theorem agreesUnder_univ {subj obj : Pronoun} : AgreesUnder univ subj obj ↔ Agrees subj obj := by
  simp [AgreesUnder, Agrees]

/-- The fewer features a probe sees, the weaker the constraint. -/
theorem AgreesUnder.mono {R R' : Finset Feature} {subj obj : Pronoun} (h : R ⊆ R')
    (ha : AgreesUnder R' subj obj) : AgreesUnder R subj obj := fun _ hf ↦
  mem_inter.2 ⟨(mem_inter.1 (ha (mem_inter.2 ⟨(mem_inter.1 hf).1, h (mem_inter.1 hf).2⟩))).1,
    (mem_inter.1 hf).2⟩

/-- The Laxopa probe does not see *elder*, so elder and nonelder human clitics combine
freely, where Yalálag's full relativization blocks (79b). -/
theorem laxopa_human_elder :
    AgreesUnder {.speaker, .participant, .human, .animate, .pi} .thirdHuman .thirdElder ∧
      ¬ Agrees .thirdHuman .thirdElder := by
  decide

/-- The Zoogocho probe sees only *animate* among the animacy features, so any animate
clitics combine. -/
theorem zoogocho_animal_elder :
    AgreesUnder {.speaker, .participant, .animate, .pi} .thirdAnimal .thirdElder := by
  decide

end Toosarvandani2023
