import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Features.Person.Decomposition
import Linglib.Features.Person.Interp
import Linglib.Features.Number.Decomposition
import Linglib.Syntax.Minimalist.Agree.Cyclic
import Linglib.Syntax.Minimalist.Phi.Recursion
import Linglib.Syntax.Minimalist.Phi.Lattice
import Linglib.Studies.Corbett2000
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Fragments.Tamil.Pronouns

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

The operators themselves (`⊕`/`⊖`/`lexComp`/`nePowerset`) are reusable substrate in
`Syntax.Minimalist.Phi.Lattice`; this file builds the partition *construction* on
top and checks the empirical results, which come out *by construction* rather than
being stipulated:

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

* `refine` / `cellsOf` — Lexical Complementarity over a sibling family + ∅-winnowing,
  the partition construction over `Phi.Lattice`'s `⊕`/`⊖`/`act` operators.
* `Examples` — the concrete three-element ontology `{i, u, o} = Fin 3`, where the
  partition cells live and the derived theorems are `decide`-checked.
* `signOf` — Harbour's `±author`/`±participant` *signs* for a Cysouw `Category`
  (theory-laden; cf. the neutral `Person.Category.toFeatures`).

## Main results (all *derived*, none stipulated)

* `inclusive_ne_exclusive`, `exclusive_excludes_addressee`, `inclusive_has_both` —
  inclusive (`+author +participant`) and exclusive (`+author −participant`) come
  out **disjoint**, with the exclusive genuinely `−participant`. This is exactly the
  distinction a Boolean-membership encoding (the foil [harbour-2016] argues against)
  collapses.
* `quad_covers` / `quad_disjoint` — the cells cover `ℒπ` and are pairwise disjoint.
* `tri_card` / `quad_card` — composition order gives 3 vs 4 cells (noncommutativity).
* `five_partitions` — the two-feature inventory's five parameter settings yield five
  distinct partitions ([harbour-2016] Table 4.1).
* `inclusive_has_no_singleton` — the inclusive holds no singleton, so the singular
  realizes only three persons (no four-way singular).

The number side ([harbour-2014]; [harbour-2016] Ch. 6) is the `Phi.Recursion`/`Corbett2000`
bridge.
-/

namespace Harbour2016

open Finset
open Minimalist.Phi.Lattice (act nePowerset)

/-! ### The partition construction (over `Phi.Lattice`'s operators) -/

section Construction
variable {Ω : Type*} [DecidableEq Ω]

/-- Lexical Complementarity over a sibling family + the `φ` domain restriction
([harbour-2016] (31), §4.4): confine a cell `c` by removing every sibling cell
*properly contained* in it (`Phi.Lattice.lexComp` across the family), then winnow the
empty set (there are no empty persons). -/
def refine (siblings : List (Finset (Finset Ω))) (c : Finset (Finset Ω)) :
    Finset (Finset Ω) :=
  (siblings.foldl (fun acc d => if d ⊂ c then acc \ d else acc) c).erase ∅

/-- The cells of a partition, given the raw (pre-refinement) denotations of each sign
assignment: refine each against the whole family, collected as a set. -/
def cellsOf (raws : List (Finset (Finset Ω))) : Finset (Finset (Finset Ω)) :=
  (raws.map (refine raws)).toFinset

end Construction

/-! ### The three-element ontology `{i, u, o}` and the derived results

Harbour's abbreviation `i_o`/`iu_o`/`u_o`/`o_o` collapses the π-lattice into four
shape-classes; the minimal ontology realizing all four is `{i, u, o}`, taken here
as `Fin 3` with `i = 0`, `u = 1`, `o = 2`. A single `o` suffices for the *person*
partition (the four cells are fixed by `has i?`/`has u?`, not the others' count); the
3rd-person *group* `{o, o'}` is not modelled, and no result below depends on it. All
theorems are kernel-checked by `decide` on this finite model. -/

namespace Examples

abbrev Ω := Fin 3      -- 0 = speaker i, 1 = hearer u, 2 = other o

/-- The author lattice `ℒau = {{i}}` (powerset of `{i}`, minus `∅`). -/
def ℒau : Finset (Finset Ω) := {{0}}
/-- The participant lattice `ℒpt = {{i}, {u}, {i,u}}` (powerset of `{i,u}`, minus `∅`). -/
def ℒpt : Finset (Finset Ω) := {{0}, {1}, {0, 1}}
/-- The π-lattice: all nonempty referent-sets. -/
def ℒπ  : Finset (Finset Ω) := nePowerset univ

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

/-! Inclusive and exclusive come out as distinct, disjoint cells *by construction*: -/

/-- The exclusive never contains the addressee `u` — it is genuinely `−participant`
in Harbour's sense, the case a Boolean-membership decomposition collapses. -/
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

/-- **The calculus certifies the canonical inventory**: over the
    referent lattice, the four quadripartition cells are exactly the
    regions `Person.interp` assigns to the four quadripartition values
    (speaker `0`, addressee `1`). The generative system and the
    analytical inventory (`Features/Person/Basic.lean`) agree cell by
    cell. -/
theorem quad_cells_are_interp_regions :
    ∀ s ∈ ℒπ,
      (s ∈ inclusive ↔ Person.region (0 : Ω) 1 .firstInclusive s) ∧
      (s ∈ exclusive ↔ Person.region (0 : Ω) 1 .firstExclusive s) ∧
      (s ∈ secondP ↔ Person.region (0 : Ω) 1 .second s) ∧
      (s ∈ thirdP ↔ Person.region (0 : Ω) 1 .third s) := by decide

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
def authorBi : Finset (Finset (Finset Ω)) := cellsOf [act true ℒau ℒπ, act false ℒau ℒπ]
/-- Participant bipartition: `{±participant}`. -/
def participantBi : Finset (Finset (Finset Ω)) := cellsOf [act true ℒpt ℒπ, act false ℒpt ℒπ]
/-- The standard tripartition as a set of cells. -/
def triP : Finset (Finset (Finset Ω)) := cellsOf triRaws
/-- The quadripartition as a set of cells. -/
def quadP : Finset (Finset (Finset Ω)) := cellsOf quadRaws

/-- The five parameter settings of [harbour-2016] Table 4.1 — `∅`, `{±author}`,
`{±participant}`, and the two composition orders of `{±author, ±participant}` — yield five
**distinct** partitions (monopartition, the two bipartitions, the tripartition, the
quadripartition). This theorem checks the distinctness; that these five settings *exhaust*
the two-feature parameter space is the enumeration of Table 4.1 itself. -/
theorem five_partitions :
    [monoP, authorBi, participantBi, triP, quadP].dedup.length = 5 := by decide

/-! #### No four-way singular person ([harbour-2016] Ch. 4) -/

/-- The singleton referents (atoms): `{i}`, `{u}`, `{o}`. -/
def singletons : Finset (Finset Ω) := {{0}, {1}, {2}}

/-- **No four-way singular person** ([harbour-2016] Ch. 4): the inclusive — the only cell
distinguishing the quadripartition from the tripartition — contains no singleton referent,
so the singular realizes only three persons (the inclusive/exclusive split collapses). -/
theorem inclusive_has_no_singleton : inclusive ∩ singletons = ∅ := by decide

/-- Every inclusive referent set has ≥ 2 members (it contains both speaker and addressee) —
the elementwise form of `inclusive_has_no_singleton`. -/
theorem inclusive_card_ge_two : ∀ s ∈ inclusive, 2 ≤ s.card := by decide

end Examples

/-! ### The phi kernel: a shared *form*, not a shared denotation ([harbour-2016] Ch. 9)

Harbour's "phi kernel" is the cluster of structural properties that person and number
features *share*: both are **operations** (not predicates), both are **bivalent**, and
both have **freely-ordered composition**. It is **not** a `1 ↔ sg` / `2 ↔ du` / `3 ↔ pl`
identification — §9.5.1 stresses that the two families' values *denote differently*
(person's `±` are `⊕`/`⊖` on the person lattices; number's `+` is the identity map and
`−` a type-flexible `¬`). What they share at the level of the abstract `ContainmentPair`
carrier is the **containment hierarchy**: the person hierarchy `1 > 2 > 3` and the number
hierarchy `sg > du > pl` are both the specification ordering `maximal > intermediate >
minimal`. -/

open Features (ContainmentPairLike)
open Number (singularF dualF pluralF)

/-- The person hierarchy `1 > 2 > 3` is the specification ordering of `ContainmentPair`
(maximal > intermediate > minimal), connecting [harbour-2016]'s lattice approach to the
hierarchy in [bejar-rezac-2009]'s Cyclic Agree and [preminger-2014]'s relativized
probing. -/
theorem person_hierarchy_is_spec_ordering :
    ContainmentPairLike.specLevel Person.firstF >
      ContainmentPairLike.specLevel Person.secondF ∧
    ContainmentPairLike.specLevel Person.secondF >
      ContainmentPairLike.specLevel Person.thirdF :=
  ContainmentPairLike.specLevel_strict_order Person.firstF_is_maximal
    Person.secondF_is_intermediate Person.thirdF_is_minimal

/-- The number hierarchy `sg > du > pl` is the *same* specification ordering — the
structural reflection of the phi kernel, not an identification of the categories. -/
theorem number_hierarchy_is_spec_ordering :
    ContainmentPairLike.specLevel singularF > ContainmentPairLike.specLevel dualF ∧
    ContainmentPairLike.specLevel dualF > ContainmentPairLike.specLevel pluralF :=
  ContainmentPairLike.specLevel_strict_order Number.singular_is_maximal
    Number.dual_is_intermediate Number.plural_is_minimal

/-! ### Bridge to Cyclic Agree ([bejar-rezac-2009]) -/

open Minimalist.CyclicAgree (personSpec)

/-- The person hierarchy from `ContainmentPair.specLevel` agrees with the segment-count
hierarchy of [bejar-rezac-2009]'s Cyclic Agree: in the standard geometry, `specLevel + 1
= segment count` (1st: 2/[π, participant, speaker]; 2nd: 1/[π, participant]; 3rd: 0/[π]).
The person hierarchy is *one* hierarchy in two formalizations — featural (spec level) and
configurational (probe depth). -/
theorem specLevel_agrees_with_segments (p : Person) :
    ∀ f, p.toFeatures = some f →
      ContainmentPairLike.specLevel f + 1 = (personSpec .standard p).length := by
  cases p <;> intro f hf <;>
    simp only [Person.toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> rfl

/-! ### Bridge to Corbett (2000): attested number systems are generable ([harbour-2014])

Every attested number system from [corbett-2000] is a subset of what some well-formed
Harbour configuration generates (a language may not lexicalize every category its geometry
affords). The number side uses the three-feature `±atomic`/`±minimal`/`±additive` calculus
of [harbour-2014] (developed at chapter length in [harbour-2016] Ch. 6), faithfully distinct
from the two-feature *person* calculus above. -/

open Minimalist.Phi.Recursion (HarbourConfig)
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

/-! ### Harbour's sign decomposition of the Cysouw categories ([harbour-2016] Table 4.3)

The neutral `Person.Category.toFeatures` underdetermines the group categories
(`excl`/`minIncl`/`augIncl` all `⟨true,true⟩`). Harbour's **operational signs** distinguish
them; that distinction is *this theory's* commitment, derived from the partition above. A
dedicated `Sign` carrier is used rather than `Person.Features`, because the
exclusive's `+author −participant` is exactly the combination the neutral type's `wellFormed`
invariant (SAP containment: author ⟹ participant) rejects — for operations, not SAP-membership
predicates, that invariant does not apply ([harbour-2016] Ch. 9). -/

open Person (Category)

/-- A Harbour `±author`/`±participant` sign — bivalent feature *values* ([harbour-2016]
Ch. 9), distinct from the SAP-membership `Person.Features`. -/
structure Sign where
  author : Bool
  participant : Bool
  deriving DecidableEq, Repr

/-- Harbour's signs for a Cysouw `Category` ([harbour-2016] Table 4.3). The 1st-person
*exclusive* — and the singular speaker `.s1`, which Harbour's quadripartition lumps into
the exclusive cell `i_o` (p. 96) — is `+author −participant`, so it does *not* collapse
with the *inclusive* `+author +participant`, unlike the neutral `Category.toFeatures`. -/
def signOf : Category → Sign
  | .minIncl | .augIncl => ⟨true, true⟩    -- +author +participant (inclusive)
  | .s1 | .excl         => ⟨true, false⟩   -- +author −participant (exclusive / sg speaker)
  | .s2 | .secondGrp    => ⟨false, true⟩   -- −author +participant
  | .s3 | .thirdGrp     => ⟨false, false⟩  -- −author −participant

/-- Harbour's signs distinguish exclusive from inclusive, where the neutral membership
decomposition (`Category.toFeatures`) collapses them (cf. `Examples.inclusive_ne_exclusive`). -/
theorem signOf_excl_ne_incl : signOf .excl ≠ signOf .minIncl := by decide

/-! ### Application: the Tamil clusivity contrast through the Pronoun API

A lexical pronoun entry feeds Harbour's signs by composing `Pronoun.category` — the
[cysouw-2009] category a `person`/`number`/`clusivity` triple realizes — with `signOf`. Tamil's
clusivity-marked 1pl forms *naam* (inclusive) and *naangaL* (exclusive) land on distinct signs,
where the neutral `Category.toFeatures` collapses both 1pl categories to `⟨true, true⟩`: the
distinction [harbour-2016]'s decomposition exists to draw, here discharged on real Fragment
entries rather than a stipulated example. -/

open Tamil.Pronouns (naam naangaL)

/-- The Harbour sign a pronoun realizes: its [cysouw-2009] `Category` (via the Pronoun API's
`Pronoun.category`) decomposed by `signOf`. `none` when the φ-features underdetermine a
category. The bridge from a lexical pronoun entry to [harbour-2016]'s `±author/±participant`
operations. -/
def harbourSign (p : Pronoun) : Option Sign := p.category.map signOf

/-- *naam* (1pl inclusive) realizes the inclusive sign `+author +participant`. -/
theorem naam_sign : harbourSign naam.toPronoun = some ⟨true, true⟩ := by decide

/-- *naangaL* (1pl exclusive) realizes the exclusive sign `+author −participant`. -/
theorem naangaL_sign : harbourSign naangaL.toPronoun = some ⟨true, false⟩ := by decide

/-- Harbour's signs distinguish *naam* from *naangaL* through the Pronoun API. -/
theorem tamil_clusivity_distinguished :
    harbourSign naam.toPronoun ≠ harbourSign naangaL.toPronoun := by decide

/-- The neutral membership decomposition collapses them: both 1pl categories map to the same
`Category.toFeatures`, so only Harbour's operational signs keep *naam* and *naangaL* apart. -/
theorem tamil_clusivity_collapsed_by_toFeatures :
    naam.toPronoun.category.map Category.toFeatures
      = naangaL.toPronoun.category.map Category.toFeatures := by decide

/-- Person and number feature carriers are the same containment-pair
skeleton, composed through the `ContainmentPair` hub: `1st ↔ singular`,
`2nd ↔ dual`, `3rd ↔ plural`. One edge of the φ-feature iso-web; equates
carriers, not denotations ([harbour-2016] §9.5.1 — the two domains'
feature values denote differently). -/
def phiKernelEquiv : Person.Features ≃ Number.Features :=
  Person.featuresEquiv.trans Number.featuresEquiv.symm

end Harbour2016
