import Mathlib.Data.Fintype.Powerset
import Linglib.Features.Individuation
import Linglib.Features.MassCount
import Linglib.Core.Order.Mereology

/-!
# Sutton & Filip (2021) — The Count/Mass Distinction for Granular Nouns
[sutton-filip-2021]

Formalizes the core of:

  Sutton, P. R. & Filip, H. (2021). The count/mass distinction for granular
  nouns. In H. Filip (ed.), *Countability in Natural Language*, 252–291.
  Cambridge University Press.

## The account

Lexical entries are tripartite (their (33)): a basic predicate (`baspred`,
number-neutral conceptual content), a counting base (`cbase`), and an
extension. Two mechanisms mediate between them: the **object identifying
function** 𝒪 (their (30)), which selects the perceptually/functionally
salient units if the concept specifies any, and **individuation schemas**
𝒮ᵢ, which select a maximally disjoint subset of those units; the **null
schema** 𝒮₀ (their (32)) instead unions *all* maximally disjoint subsets.
Grammatical counting requires a disjoint counting base, so:

* count = `[+O, +S]` (a specific schema over identified objects — *cat*,
  *lentil*, Finnish *huonekalut* 'items of furniture');
* mass = `[−S]` (null schema): either `[+O, −S]` (*furniture* — objects
  identified but overlapping, so cardinality comparison is available) or
  `[−O, −S]` (*rice*, Czech *čočka* 'lentil', *mud* — no object function
  in the counting base at all).

The **accessibility puzzle**: *rice* denotes stuff made of perceptually
salient, *disjoint* grains, yet `#three rices` cannot mean 'three grains of
rice' (only container/subkind readings). On this account the grains live in
`baspred` but are not passed to `cbase` — and an *implicit* unit-extracting
shift would be a generalized `[−O,−S] → [+O,+S]` operation, incompatible
with a lexicalized mass/count distinction (their §9.5.4; Yudja, which
lacks one, counts everything — cf. `Grimm2018.yudjaClassify`).

## Main declarations

* `OverlapPred`/`IsMaxDisjointIn`/`nullSchema` — the schema machinery over
  an arbitrary overlap relation. The disjoint-counting-base thesis and the
  multiple-perspectives ("variants") idea this packages originate with
  [landman-2011] and [landman-2016]; the chapter's own contribution is the
  null schema `𝒮₀` and the unified `𝒪`/`𝒮ᵢ` mechanism. The machinery is a
  graduation candidate when a Landman-anchored study lands.
* `overlapPred_union_of_maxDisjoint_ne` — the load-bearing generic fact:
  the union of two *distinct* maximal disjoint subsets overlaps. Hence
  `nullSchema`-saturated entries are mass whenever individuation is
  perspectival (`overlapPred_nullSchema`), and stable for prototypical
  objects (`nullSchema_eq_of_disjoint`).
* `Categorization` (`[±O, ±S]`) and Table 9.1 (`table91`) over the
  graduated individuation scale (`Features/Individuation.lean`), with the
  junction theorems: the count option *ascends* the scale
  (`count_option_monotone`) and the mass option *descends* it
  (`mass_option_antitone`). Ordering Table 9.1 by [grimm-2018]'s scale is
  this study's bridge, not the chapter's (it cites [grimm-2012] and Grimm &
  Levin 2017, not [grimm-2018]); the theorems show the two frameworks'
  landscapes coincide.
* A concrete furniture/rice model on nonempty `Finset`s: *furniture*'s
  identified units overlap (table vs. vanity), *rice*'s grains are disjoint
  in `baspred` yet its counting base overlaps — the accessibility puzzle's
  two halves (`furniture_units_overlap`, `rice_accessibility`).

## Connections

* Second consumer of the individuation scale — the graduation that moved
  `IndividuationType` to `Features/Individuation.lean` (with [grimm-2018]).
* `MassCount` records the *outcome* of categorization
  (`Categorization.massCount`); the `[±O, ±S]` features are its analysis.
* The cluster/MSSC content of granular `baspred` frames is [grimm-2012]'s
  mereotopology ([casati-varzi-1999] self-connection), not formalized
  here.
* Their counting condition (cardinality only over disjoint bases, their
  (A1), after [landman-2011]'s overlap thesis) is the semantic ground for why
  countability classes, not `Number` values, carry the count/mass
  distinction (`Features/Number/Basic.lean`).
-/

set_option autoImplicit false

namespace SuttonFilip2021

/-! ### Overlap, disjointness, and individuation schemas

Their (16)–(18): the schema machinery (`Mereology.OverlapPred`,
`Mereology.IsMaxDisjointIn`, `Mereology.nullSchema` for `𝒮₀`, their (32))
lives in `Core/Order/Mereology.lean`, shared with [landman-2020]
(`Studies/Landman2020.lean`), whose disjointness thesis it packages.
A predicate is *overlapping* if two distinct members overlap (their (17)
omits the distinctness, under which any inhabited predicate self-overlaps
via `x ∘ x`; the substrate states the intended reading). -/

open Mereology (OverlapPred DisjointPred IsMaxDisjointIn nullSchema
  overlapPred_nullSchema)

/-! ### The `[±O, ±S]` categorization and Table 9.1

`[+O]`: the counting base contains the object identifying function 𝒪;
`[+S]`: it is interpreted under a specific schema `𝒮ᵢ` rather than `𝒮₀`.
Count nouns are `[+O, +S]`; mass nouns are `[−S]`. -/

/-- The two binary features classifying counting bases (their §9.4.4). -/
structure Categorization where
  /-- The counting base contains the object identifying function 𝒪. -/
  hasObjectFn : Bool
  /-- The counting base is interpreted under a specific schema `𝒮ᵢ`
      (rather than the null schema `𝒮₀`). -/
  hasSpecificSchema : Bool
  deriving DecidableEq, Repr

/-- Count iff `[+O, +S]`; everything `[−S]` is mass (Table 9.1's
    generalizations). -/
def Categorization.massCount : Categorization → MassCount
  | ⟨true, true⟩ => .count
  | _ => .mass

/-- Table 9.1: the categorization options available to each notional
    class, stated over the graduated individuation scale. Substances are
    `[−O, −S]` only (*mud*); granulars lexicalize either way (*lentil* vs
    *rice*/*čočka*); collective artifacts are `[+O, ±S]` (*huonekalut* vs
    *furniture*); prototypical objects are `[+O, +S]` (*cat*). -/
def table91 : IndividuationType → List Categorization
  | .substance => [⟨false, false⟩]
  | .granularAggregate => [⟨true, true⟩, ⟨false, false⟩]
  | .collectiveAggregate => [⟨true, true⟩, ⟨true, false⟩]
  | .individualEntity => [⟨true, true⟩]

/-- A count lexicalization is available from granular aggregates upward —
    availability of `[+O, +S]` is monotone on the individuation scale. -/
theorem count_option_monotone :
    Monotone (fun i =>
      (table91 i).any (fun c => c.hasObjectFn && c.hasSpecificSchema)) := by
  decide

/-- A mass lexicalization is available from collective aggregates
    downward — availability of `[−S]` is antitone on the scale. Together
    with `count_option_monotone`, this is [grimm-2018]'s Table 20
    landscape derived from the `[±O, ±S]` analysis: the count/mass
    boundary can only fall *across* the scale, never gerrymander it. -/
theorem mass_option_antitone :
    Antitone (fun i => (table91 i).any (fun c => !c.hasSpecificSchema)) := by
  decide

/-- Every notional class has at least one lexicalization, and the
    cross-linguistically variable classes (granular, collective artifact)
    are exactly those with two ([sutton-filip-2021] §9.3.1: *lentil* vs
    *čočka*, *furniture* vs *huonekalut*). -/
theorem variable_classes :
    (∀ i, (table91 i) ≠ []) ∧
    (∀ i, (table91 i).length = 2 ↔
      (i = .granularAggregate ∨ i = .collectiveAggregate)) := by
  constructor
  · decide
  · decide

/-! ### A concrete model: furniture and rice

Carrier: nonempty subsets of a small atom domain, overlap = nonempty
intersection. *Furniture* (their §9.4.2–9.4.3): a table `t`, a mirror `m`,
and the vanity `t ⊔ m` are all functional units, so `𝒪(furniture)`
overlaps — two individuation perspectives exist (count the vanity as one,
or the table and mirror as two). *Rice*: the basic predicate knows the
grains (disjoint!) and their aggregates, but the `[−O, −S]` counting base
is the null schema over the whole predicate — overlapping. The grains are
real and inaccessible: the accessibility puzzle. -/

/-- Mereological overlap on `Finset` parts: nonempty intersection. -/
def fovl (s t : Finset (Fin 3)) : Prop := (s ∩ t).Nonempty

instance : ∀ s t, Decidable (fovl s t) := fun s t =>
  inferInstanceAs (Decidable (s ∩ t).Nonempty)

instance {a : Finset (Fin 3)} {P : Set (Finset (Fin 3))}
    [DecidablePred (· ∈ P)] : DecidablePred (· ∈ insert a P) := fun x =>
  decidable_of_iff (x = a ∨ x ∈ P) (by simp [Set.mem_insert_iff])

instance {P : Set (Finset (Fin 3))} [DecidablePred (· ∈ P)] :
    Decidable (OverlapPred fovl P) := by
  unfold OverlapPred; infer_instance

instance {P : Set (Finset (Fin 3))} [DecidablePred (· ∈ P)] :
    Decidable (DisjointPred fovl P) :=
  decidable_of_iff (¬ OverlapPred fovl P) Iff.rfl

instance {P Q : Set (Finset (Fin 3))} [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ Q)] : Decidable (P ⊆ Q) :=
  decidable_of_iff (∀ x, x ∈ P → x ∈ Q) Iff.rfl

instance {D P : Set (Finset (Fin 3))} [DecidablePred (· ∈ D)]
    [DecidablePred (· ∈ P)] : Decidable (IsMaxDisjointIn fovl D P) :=
  decidable_of_iff
    ((∀ x, x ∈ D → x ∈ P) ∧ DisjointPred fovl D ∧
      ∀ x, x ∈ P → x ∉ D → OverlapPred fovl (insert x D)) Iff.rfl

/-- The identified units of *furniture* on a two-atom domain: table `{0}`,
    mirror `{1}`, and the vanity `{0, 1}` they jointly compose. -/
def furnitureUnits : Set (Finset (Fin 3)) :=
  {s | s = {0} ∨ s = {1} ∨ s = {0, 1}}

instance : DecidablePred (· ∈ furnitureUnits) := fun s =>
  decidable_of_iff (s = {0} ∨ s = {1} ∨ s = {0, 1}) Iff.rfl

/-- The piece perspective: count the table and the mirror. -/
def piecePerspective : Set (Finset (Fin 3)) := {s | s = {0} ∨ s = {1}}

instance : DecidablePred (· ∈ piecePerspective) := fun s =>
  decidable_of_iff (s = {0} ∨ s = {1}) Iff.rfl

/-- The vanity perspective: count the composed unit. -/
def vanityPerspective : Set (Finset (Fin 3)) := {s | s = {0, 1}}

instance : DecidablePred (· ∈ vanityPerspective) := fun s =>
  decidable_of_iff (s = {0, 1}) Iff.rfl

/-- `𝒪(furniture)` is overlapping: the vanity shares parts with the table.
    Hence *furniture* is `[+O, −S]`: object units exist (cardinality
    comparisons are licensed) but the null schema's base overlaps — mass. -/
theorem furniture_units_overlap : OverlapPred fovl furnitureUnits := by
  decide

/-- The two individuation perspectives on the furniture units — count the
    pieces, or count the vanity — are both maximally disjoint, and differ;
    by `overlapPred_nullSchema` the null-schema counting base is
    overlapping, which is *why* `#three furnitures` fails. -/
theorem furniture_two_perspectives :
    IsMaxDisjointIn fovl piecePerspective furnitureUnits ∧
    IsMaxDisjointIn fovl vanityPerspective furnitureUnits ∧
    OverlapPred fovl (nullSchema fovl furnitureUnits) := by
  refine ⟨by decide, by decide,
    overlapPred_nullSchema fovl (D₁ := piecePerspective)
      (D₂ := vanityPerspective) (by decide) (by decide) ?_⟩
  intro h
  have h0 : ({0} : Finset (Fin 3)) ∈ vanityPerspective := by
    rw [← h]; exact Or.inl rfl
  exact absurd h0 (by decide)

/-- *Rice* on a three-grain domain: the basic predicate contains the
    grains and their aggregates (its `extension = unit ∨ collection`,
    their (29)). -/
def riceBaspred : Set (Finset (Fin 3)) := {s | s.Nonempty}

instance : DecidablePred (· ∈ riceBaspred) := fun s =>
  inferInstanceAs (Decidable s.Nonempty)

/-- The grains of rice: the atoms. -/
def riceGrains : Set (Finset (Fin 3)) :=
  {s | s = {0} ∨ s = {1} ∨ s = {2}}

instance : DecidablePred (· ∈ riceGrains) := fun s =>
  decidable_of_iff (s = {0} ∨ s = {1} ∨ s = {2}) Iff.rfl

/-- The heap perspective on rice: one three-grain aggregate. -/
def heapPerspective : Set (Finset (Fin 3)) := {s | s = {0, 1, 2}}

instance : DecidablePred (· ∈ heapPerspective) := fun s =>
  decidable_of_iff (s = {0, 1, 2}) Iff.rfl

/-- **The accessibility puzzle, both halves** ((Q2), §9.5.3): the grains
    are part of *rice*'s basic predicate and are perfectly disjoint — they
    intuitively count as one — yet the `[−O, −S]` counting base (the null
    schema over the whole basic predicate) is overlapping, because grain
    and heap perspectives are both maximal. Grammatical counting is
    blocked: salience without accessibility. -/
theorem rice_accessibility :
    riceGrains ⊆ riceBaspred ∧
    DisjointPred fovl riceGrains ∧
    OverlapPred fovl (nullSchema fovl riceBaspred) := by
  refine ⟨by decide, by decide,
    overlapPred_nullSchema fovl
      (D₁ := riceGrains) (D₂ := heapPerspective)
      (by decide) (by decide) ?_⟩
  intro h
  have h0 : ({0} : Finset (Fin 3)) ∈ heapPerspective := by
    rw [← h]; exact Or.inl rfl
  exact absurd h0 (by decide)

/-! ### Cross-linguistic variation as a schema substitution

Finnish *huonekalut* 'items of furniture' is the count counterpart of
*furniture*: identical basic predicate, with the null schema replaced by a
contextually specified one — `⟦huonekalut⟧^𝒮ᵢ = ⟦furniture⟧^{𝒮₀ ↦ 𝒮ᵢ}`
(their p. 278). On the model: each *specific* perspective on the furniture
units is disjoint, hence countable. The same substitution relates Czech
*čočka* to English *lentil(s)* among granulars. -/

/-- Each specific individuation perspective on the furniture units is a
    disjoint counting base — `[+O, +S]` is count (*huonekalut*), even
    though the `[+O, −S]` null-schema base overlaps (*furniture*). -/
theorem huonekalut_count :
    DisjointPred fovl piecePerspective ∧
    DisjointPred fovl vanityPerspective := by
  exact ⟨by decide, by decide⟩

end SuttonFilip2021
