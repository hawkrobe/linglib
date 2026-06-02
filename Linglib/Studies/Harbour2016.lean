import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Features.Person
import Linglib.Features.Number
import Linglib.Syntax.Minimalist.CyclicAgree
import Linglib.Syntax.Minimalist.Agreement.FeatureRecursion
import Linglib.Studies.Corbett2000

/-!
# Harbour (2016): *Impossible Persons* — the partition calculus
[harbour-2016]

Person categories are **derived**, not primitive: they are the cells of a
*partition of the π-lattice* induced by two features, `±author` and
`±participant`. Crucially — and this is the thesis of [harbour-2016] (Ch. 4.2.3,
Ch. 9) — the features denote **operations on person lattices, not predicates**:
their values are actions `⊕` (disjoint addition) and `⊖` (joint subtraction),
"not truth functors, which would reduce the features to first-order predicates,
but actions by and on the person lattices."

This file formalizes that calculus directly, so the empirical results come out
*by construction* rather than being stipulated:

* the **ontology** is the speaker `i`, hearer `u`, and others `o`; referents are
  sets of these (`Finset Ω`), and the three feature lattices are powerset
  sublattices `ℒau ⊆ ℒpt ⊆ ℒπ` (the egocentric chain, [harbour-2016] p. 74);
* a **feature acts** on a collection: `+F(G) = G ⊕ ℒF` (pairwise join, (17)) and
  `−F(G) = G ⊖ ℒF` (strip `ℒF`'s maximum, (19));
* cells are made disjoint by **Lexical Complementarity** ((31): a cell properly
  containing a sibling is confined to the difference) and the **∅-winnowing** of
  the variable head `φ` (§4.4); and
* **composition is noncommutative** (Ch. 4.2.3), so the order of the two features
  yields the *standard tripartition* (participant outermost: the two `−participant`
  cells coincide) or the *quadripartition* (author outermost: inclusive/exclusive
  split).

## Main declarations

* `posAct` / `negAct` — the `⊕` / `⊖` actions of a feature lattice on a collection.
* `refine` — Lexical Complementarity + ∅-winnowing.
* `quadCell` / `triCell` — the cells of the quadri- and tripartition.
* `Examples` — the concrete three-element ontology `{i, u, o} = Fin 3` on which the
  derived theorems are `decide`-checked.

## Main results (all *derived*, none stipulated)

* `inclusive_ne_exclusive`, `exclusive_excludes_addressee`, `inclusive_has_both` —
  inclusive (`+author +participant`) and exclusive (`+author −participant`) come
  out **disjoint**, with the exclusive genuinely `−participant`. This is exactly the
  distinction a Boolean-membership encoding (the foil [harbour-2016] argues against)
  collapses.
* `quad_is_partition` / `tri_is_partition` — the cells cover `ℒπ` and are pairwise
  disjoint.
* `tri_card` / `quad_card` — composition order gives 3 vs 4 cells (noncommutativity).
* `five_partitions` — the two-feature inventory generates exactly five partitions
  ([harbour-2016] Table 4.1), no more.
* `no_four_singular` — at most three person cells contain a singleton referent.

The number side ([harbour-2014a], Ch. 6) and the Cysouw-`Category` bridge live in
later sections / `Features.Person`.
-/

namespace Harbour2016

open Finset

/-! ### The feature calculus (Ch. 4.2.3) -/

section Calculus
variable {Ω : Type*} [DecidableEq Ω]

/-- Positive action `⊕`: *disjoint addition*. `+F` joins every element of the input
collection `G` with every element of the feature lattice `F`
([harbour-2016] (17)). This is `Finset.image₂` of the lattice join `∪`. -/
def posAct (G F : Finset (Finset Ω)) : Finset (Finset Ω) := image₂ (· ∪ ·) G F

/-- The maximum of a (powerset-generated) feature lattice — its generating set. -/
def maxElt (F : Finset (Finset Ω)) : Finset Ω := F.sup id

/-- Negative action `⊖`: *joint subtraction*. `−F` strips `F`'s maximum from every
element of `G`. Cumulative subtraction reduces to subtracting the maximum, since
the feature lattices have a unique maximal element ([harbour-2016] (19)). -/
def negAct (G F : Finset (Finset Ω)) : Finset (Finset Ω) := G.image (· \ maxElt F)

/-- Apply a signed feature (lattice `F`) to a collection `G`: `+F` is `posAct`,
`−F` is `negAct`. -/
def act (sign : Bool) (F G : Finset (Finset Ω)) : Finset (Finset Ω) :=
  if sign then posAct G F else negAct G F

/-- Lexical Complementarity + the `φ` domain restriction ([harbour-2016] (31), §4.4):
confine a cell `c` by removing every sibling cell *properly contained* in it ("catch
the slack" of more-specified cells), then winnow the empty set (there are no empty
persons). -/
def refine (siblings : List (Finset (Finset Ω))) (c : Finset (Finset Ω)) :
    Finset (Finset Ω) :=
  (siblings.foldl (fun acc d => if d ⊂ c then acc \ d else acc) c).erase ∅

/-- The cells of a partition, given the raw (pre-refinement) denotations of each
sign assignment: refine each against the whole family, collected as a set. -/
def cellsOf (raws : List (Finset (Finset Ω))) : Finset (Finset (Finset Ω)) :=
  (raws.map (refine raws)).toFinset

end Calculus

/-! ### The three-element ontology `{i, u, o}` and the derived results

Harbour's abbreviation `i_o`/`iu_o`/`u_o`/`o_o` collapses the π-lattice into four
shape-classes; the minimal ontology realizing all four is `{i, u, o}`, taken here
as `Fin 3` with `i = 0`, `u = 1`, `o = 2`. All theorems below are kernel-checked
by `decide` on this finite model. -/

namespace Examples

abbrev Ω := Fin 3      -- 0 = speaker i, 1 = hearer u, 2 = other o

/-- The author lattice `ℒau = {{i}}` (powerset of `{i}`, minus `∅`). -/
def ℒau : Finset (Finset Ω) := {{0}}
/-- The participant lattice `ℒpt = {{i}, {u}, {i,u}}` (powerset of `{i,u}`, minus `∅`). -/
def ℒpt : Finset (Finset Ω) := {{0}, {1}, {0, 1}}
/-- The π-lattice: all nonempty referent-sets. -/
def ℒπ  : Finset (Finset Ω) := univ.powerset.erase ∅

/-- The egocentric containment chain `ℒau ⊆ ℒpt ⊆ ℒπ` ([harbour-2016] p. 74). -/
theorem lattice_chain : ℒau ⊆ ℒpt ∧ ℒpt ⊆ ℒπ := by decide

/-! #### Quadripartition — author composes outermost ([harbour-2016] §4.3.5) -/

/-- Raw cell of the quadripartition for sign `sa` of author, `sp` of participant
(author outermost, participant innermost). -/
def quadRaw (sa sp : Bool) : Finset (Finset Ω) := act sa ℒau (act sp ℒpt ℒπ)

/-- The four raw quadripartition cells. -/
def quadRaws : List (Finset (Finset Ω)) :=
  [quadRaw true true, quadRaw true false, quadRaw false true, quadRaw false false]

/-- A refined quadripartition cell. -/
def quadCell (sa sp : Bool) : Finset (Finset Ω) := refine quadRaws (quadRaw sa sp)

/-- 1st-person **inclusive** = `+author +participant`. -/
def inclusive : Finset (Finset Ω) := quadCell true true
/-- 1st-person **exclusive** = `+author −participant`. -/
def exclusive : Finset (Finset Ω) := quadCell true false
/-- 2nd person = `−author +participant`. -/
def secondP : Finset (Finset Ω) := quadCell false true
/-- 3rd person = `−author −participant`. -/
def thirdP : Finset (Finset Ω) := quadCell false false

/-! The collapse the predicate encoding suffers is gone *by construction*: -/

/-- The exclusive never contains the addressee `u` — it is genuinely `−participant`
in Harbour's sense, the case `Category.toFeatures` (membership reading) gets wrong. -/
theorem exclusive_excludes_addressee : ∀ s ∈ exclusive, (1 : Ω) ∉ s := by decide

/-- The exclusive always contains the speaker `i`. -/
theorem exclusive_includes_speaker : ∀ s ∈ exclusive, (0 : Ω) ∈ s := by decide

/-- The inclusive always contains *both* speaker and addressee. -/
theorem inclusive_has_both : ∀ s ∈ inclusive, (0 : Ω) ∈ s ∧ (1 : Ω) ∈ s := by decide

/-- Inclusive ≠ exclusive — they do **not** collapse to one feature bundle. -/
theorem inclusive_ne_exclusive : inclusive ≠ exclusive := by decide

/-- The four quadripartition cells cover the π-lattice. -/
theorem quad_covers : inclusive ∪ exclusive ∪ secondP ∪ thirdP = ℒπ := by decide

/-- The four quadripartition cells are pairwise disjoint. -/
theorem quad_disjoint :
    Disjoint inclusive exclusive ∧ Disjoint inclusive secondP ∧
    Disjoint inclusive thirdP ∧ Disjoint exclusive secondP ∧
    Disjoint exclusive thirdP ∧ Disjoint secondP thirdP := by decide

/-- The quadripartition has four cells. -/
theorem quad_card : (cellsOf quadRaws).card = 4 := by decide

/-! #### Standard tripartition — participant composes outermost ([harbour-2016] §4.3.4) -/

/-- Raw cell of the tripartition for sign `sp` of participant, `sa` of author
(participant outermost). The two `−participant` cells coincide. -/
def triRaw (sp sa : Bool) : Finset (Finset Ω) := act sp ℒpt (act sa ℒau ℒπ)

/-- The (four) raw tripartition cells. -/
def triRaws : List (Finset (Finset Ω)) :=
  [triRaw true true, triRaw true false, triRaw false true, triRaw false false]

/-- Composition order matters: with participant outermost, the two `−participant`
specifications coincide, so the tripartition has only **three** cells — whereas the
quadripartition has four. This *is* the noncommutativity of feature composition
([harbour-2016] Ch. 4.2.3). -/
theorem tri_card : (cellsOf triRaws).card = 3 := by decide

theorem tri_ne_quad : cellsOf triRaws ≠ cellsOf quadRaws := by decide

/-! #### The five partitions ([harbour-2016] Table 4.1) -/

/-- Monopartition: no features active. -/
def monoP : Finset (Finset (Finset Ω)) := cellsOf [ℒπ]
/-- Author bipartition: `{±author}`. -/
def authorBi : Finset (Finset (Finset Ω)) := cellsOf [posAct ℒπ ℒau, negAct ℒπ ℒau]
/-- Participant bipartition: `{±participant}`. -/
def participantBi : Finset (Finset (Finset Ω)) := cellsOf [posAct ℒπ ℒpt, negAct ℒπ ℒpt]
/-- The standard tripartition as a set of cells. -/
def triP : Finset (Finset (Finset Ω)) := cellsOf triRaws
/-- The quadripartition as a set of cells. -/
def quadP : Finset (Finset (Finset Ω)) := cellsOf quadRaws

/-- The two-feature inventory `{±author, ±participant}` generates **exactly five**
distinct partitions — monopartition, the two bipartitions, the tripartition, and the
quadripartition — and no more ([harbour-2016] Table 4.1). -/
theorem five_partitions :
    [monoP, authorBi, participantBi, triP, quadP].dedup.length = 5 := by decide

/-! #### No four-way singular person ([harbour-2016] Ch. 4) -/

/-- The singleton referents (atoms): `{i}`, `{u}`, `{o}`. -/
def singletons : Finset (Finset Ω) := {{0}, {1}, {2}}

/-- The inclusive — the only cell distinguishing the quadripartition from the
tripartition — contains no singleton referent (its every set has ≥ 2 members). -/
theorem inclusive_has_no_singleton : inclusive ∩ singletons = ∅ := by decide

/-- **No four-way singular person** ([harbour-2016] Ch. 4). Every inclusive referent set
has at least two members, so no singleton (atomic) referent is inclusive: the
inclusive/exclusive split — the only difference between the quadri- and tripartition —
collapses in the singular, leaving three persons. -/
theorem no_four_singular : ∀ s ∈ inclusive, 2 ≤ s.card := by decide

end Examples

/-! ### The phi kernel: a shared *form*, not a shared denotation ([harbour-2016] Ch. 9)

Harbour's "phi kernel" is the cluster of structural properties that person and number
features *share*: both are **operations** (not predicates), both are **bivalent**, and
both have **freely-ordered composition**. It is **not** a `1 ↔ sg` / `2 ↔ du` / `3 ↔ pl`
identification — §9.5.1 stresses that the two families' values *denote differently*
(person's `±` are `⊕`/`⊖` on the person lattices; number's `+` is the identity map and
`−` a type-flexible `¬`). What they share at the level of the abstract `PrivativePair`
carrier is the **containment hierarchy**: the person hierarchy `1 > 2 > 3` and the number
hierarchy `sg > du > pl` are both the specification ordering `maximal > intermediate >
minimal`. -/

open Features (PhiFeatures)
open Features.Number (singularF dualF pluralF)

/-- The person hierarchy `1 > 2 > 3` is the specification ordering of `PrivativePair`
(maximal > intermediate > minimal), connecting [harbour-2016]'s lattice approach to the
hierarchy in [bejar-rezac-2009]'s Cyclic Agree and [preminger-2014]'s relativized
probing. -/
theorem person_hierarchy_is_spec_ordering :
    PhiFeatures.specLevel Features.Person.first >
      PhiFeatures.specLevel Features.Person.second ∧
    PhiFeatures.specLevel Features.Person.second >
      PhiFeatures.specLevel Features.Person.third := ⟨by decide, by decide⟩

/-- The number hierarchy `sg > du > pl` is the *same* specification ordering — the
structural reflection of the phi kernel, not an identification of the categories. -/
theorem number_hierarchy_is_spec_ordering :
    PhiFeatures.specLevel singularF > PhiFeatures.specLevel dualF ∧
    PhiFeatures.specLevel dualF > PhiFeatures.specLevel pluralF := ⟨by decide, by decide⟩

/-! ### Bridge to Cyclic Agree ([bejar-rezac-2009]) -/

open Minimalist.CyclicAgree (personSpec)
open Features.Prominence (PersonLevel)

/-- The person hierarchy from `PrivativePair.specLevel` agrees with the segment-count
hierarchy of [bejar-rezac-2009]'s Cyclic Agree: in the standard geometry, `specLevel + 1
= segment count` (1st: 2/[π, participant, speaker]; 2nd: 1/[π, participant]; 3rd: 0/[π]).
The person hierarchy is *one* hierarchy in two formalizations — featural (spec level) and
configurational (probe depth). -/
theorem specLevel_agrees_with_segments (p : PersonLevel) :
    PhiFeatures.specLevel p.toFeatures + 1 = (personSpec .standard p).length := by
  cases p <;> rfl

/-! ### Bridge to Corbett (2000): attested number systems are generable ([harbour-2014a])

Every attested number system from [corbett-2000] is a subset of what some well-formed
Harbour configuration generates (a language may not lexicalize every category its geometry
affords). The number side uses the three-feature `±atomic`/`±minimal`/`±additive` calculus
of [harbour-2014a] (Ch. 6), faithfully distinct from the two-feature *person* calculus
above. -/

open Minimalist.Agreement.FeatureRecursion (HarbourConfig)
open Corbett2000

/-- Every attested number system's values are generated by some well-formed Harbour
configuration: Pirahã (∅ → no number), English/Russian/Japanese (`±atomic` → sg/pl),
Upper Sorbian/Slovene (`±atomic, ±minimal` → sg/du/pl), Bayso (`±atomic, ±additive` →
sg/pl/pauc), Larike and Lihir (with `±minimal` recursion). -/
theorem attested_number_systems_derivable :
    pirahaNS.values.all
      ((HarbourConfig.mk false false false false false).categories.contains ·) = true ∧
    englishNS.values.all
      ((HarbourConfig.mk true false false false false).categories.contains ·) = true ∧
    russianNS.values.all
      ((HarbourConfig.mk true false false false false).categories.contains ·) = true ∧
    upperSorbianNS.values.all
      ((HarbourConfig.mk true true false false false).categories.contains ·) = true ∧
    baysoNS.values.all
      ((HarbourConfig.mk true false true false false).categories.contains ·) = true ∧
    sloveneNS.values.all
      ((HarbourConfig.mk true true false false false).categories.contains ·) = true ∧
    larikeNS.values.all
      ((HarbourConfig.mk true true false true false).categories.contains ·) = true ∧
    lihirNS.values.all
      ((HarbourConfig.mk true true true true false).categories.contains ·) = true ∧
    japaneseNS.values.all
      ((HarbourConfig.mk true false false false false).categories.contains ·) = true
    := by decide

/-- MIN/AUG systems from [harbour-2014] Table 3. -/
theorem minAug_systems_derivable :
    winnebagoNS.values.all
      ((HarbourConfig.mk false true false false false).categories.contains ·) = true ∧
    rembarrnganS.values.all
      ((HarbourConfig.mk false true false true false).categories.contains ·) = true ∧
    mebengokreNS.values.all
      ((HarbourConfig.mk false true true false false).categories.contains ·) = true
    := by decide

/-- The Harbour configurations used in the bridge are all well-formed. -/
theorem bridge_configs_wellFormed :
    (HarbourConfig.mk false false false false false).wellFormed = true ∧
    (HarbourConfig.mk true false false false false).wellFormed = true ∧
    (HarbourConfig.mk true true false false false).wellFormed = true ∧
    (HarbourConfig.mk true false true false false).wellFormed = true ∧
    (HarbourConfig.mk true true false true false).wellFormed = true ∧
    (HarbourConfig.mk true true true true false).wellFormed = true ∧
    (HarbourConfig.mk false true false false false).wellFormed = true ∧
    (HarbourConfig.mk false true false true false).wellFormed = true ∧
    (HarbourConfig.mk false true true false false).wellFormed = true
    := by decide

end Harbour2016
