import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Semantics.Mereology
import Linglib.Features.Individuation

/-!
# Grimm & Dočekal (2021) — Counting Aggregates, Groups and Kinds
[grimm-docekal-2021]

Formalizes the formal core of:

  Grimm, S. & Dočekal, M. (2021). Counting aggregates, groups and kinds:
  Countability from the perspective of a morphologically complex
  language. In H. Filip (ed.), *Countability in Natural Language*,
  85–120. Cambridge University Press.

## The data

Czech makes the individuation scale *morphologically visible*. Beyond
the count/non-count contrast, its derivational morphology targets entity
types English leaves undifferentiated:

* **Derived aggregates** (suffix *-í*, Table 3.1): countable roots yield
  strongly non-countable collection nouns — *list* 'leaf' → *listí*
  'foliage', *strom* 'tree' → *stromoví* 'clump of trees' — requiring
  coherence (spatial proximity, functional interdependence) of the
  members, with no pluralization, no cardinals ((10)–(11)), and no
  packaging shifts ((12)).
* **Group numerals** (*-ice*, §3.2.2.1): *troj-ice námořníků* 'a group
  of three sailors' — animate-only, collective-only interpretation, and
  the output is *fully countable* (*dvě trojice* 'two groups of three',
  (54)) via [landman-1989]-style group formation.
* **Aggregate numerals** (*-oje*/*-ery*, §3.2.2.2): *dv-oje klíče* 'two
  sets of keys' — select connected-entity nouns ((21)–(23)), and the
  output **cannot be recounted** (*\*tři dvoje klíče*, (27)).
* **Taxonomic numerals** (*-ojí*/*-ero*, §3.2.2.3): *dvojí víno* 'two
  kinds of wine' — licensed in both episodic and non-episodic contexts,
  unlike bare-plural taxonomic readings ((40)).
* **Restricted flexibility** (§3.2.3): no grinding ((34)–(35)),
  conventional-only packaging ((8)), episodic-restricted sorting — the
  inverse of what flexibility-foundational theories predict (§3.3:
  against Borer's mass-to-count trajectory, since *-í* manufactures
  non-countables *from* countables; against single-source vagueness
  accounts, since *listí*'s parts are non-vaguely atomic).

## The formalization

Their §3.5 extends [krifka-1995b]'s kind-based semantics with
[grimm-2012] mereotopology ([casati-varzi-1999] connection axioms
(56)–(59)). This file formalizes that extension:

* `ChainIn`/`IsCluster`/`IsMaxCluster` — transitive connection (60),
  cluster individuals (61), maximal clusters (63), over an arbitrary
  connection relation (their proximate vs external varieties).
* `isCluster_sup` — joining clusters across a connection yields a
  cluster: the honest version of their cumulativity remark for *-í*
  nouns (sums of *connected* clusters, not arbitrary sums).
* **`maxClusters_disjointPred`** — distinct maximal clusters never
  overlap: the *-oje* counting base is disjoint, so aggregate counting
  is certified by exactly the disjointness that [landman-2020]'s
  counting theorems require (`Mereology.DisjointPred`; cf.
  `Studies/Landman2020.lean`).
* **`ojeSem_determinate`** — the (64) semantics fixes the cardinality of
  maximal clusters uniquely: the formal content of *\*tři dvoje klíče*
  ((27)) and *\*všechny dvoje* ((26)) — an aggregate-numeral output has
  determinate cardinality that no outer numeral can re-specify.
* `ojiSem` and `oji_needs_subkinds` — the taxonomic numeral (50) is
  empty on kind-less arguments (proper names, (52b)).
* The individuation-scale junction (third consumer of
  `Features/Individuation.lean`): *-í* is a morphological *descent* of
  the scale (`isuffix_descends`), and the Czech countability map is
  monotone on it (`czech_monotone`), the [grimm-2018] order-preservation
  thesis in a language where the boundary is drawn by derivation rather
  than lexical class alone.
-/

set_option autoImplicit false

namespace GrimmDocekal2021

open Mereology (OverlapPred DisjointPred)

/-! ### Cluster mereotopology (their §3.5.2)

[casati-varzi-1999] connection: a reflexive, symmetric relation `C`
((56)–(57)); the varieties relevant to aggregates are external and
proximate connectedness. Clusters are sums of property-bearers pairwise
connected *through the cluster* ((60)–(61)); maximal clusters absorb
every overlapping cluster ((63)). -/

variable {α : Type*} [SemilatticeSup α]
variable (C ov : α → α → Prop)

/-- (60): connected through a chain of members of `Z`. -/
def ChainIn (Z : Finset α) : α → α → Prop :=
  Relation.ReflTransGen fun a b => a ∈ Z ∧ b ∈ Z ∧ C a b

/-- (61): a cluster individual — the sum of a nonempty set of
    `P`-entities, pairwise transitively connected through the set. -/
def IsCluster (P : α → Prop) (x : α) : Prop :=
  ∃ (Z : Finset α) (hZ : Z.Nonempty),
    (∀ z ∈ Z, P z) ∧ x = Z.sup' hZ id ∧
    ∀ z ∈ Z, ∀ z' ∈ Z, ChainIn C Z z z'

/-- (63): a maximal cluster absorbs every overlapping cluster. -/
def IsMaxCluster (P : α → Prop) (x : α) : Prop :=
  IsCluster C P x ∧ ∀ y, IsCluster C P y → ov y x → y ≤ x

/-- **Maximal clusters are pairwise disjoint** (their remark after
    (63)): two distinct maximal clusters cannot overlap — each would
    absorb the other. This is what makes the `-oje` counting base a
    disjoint set, the precondition the [landman-2020] counting theorems
    certify as sufficient for counting. -/
theorem maxClusters_disjointPred {P : α → Prop}
    (hsym : ∀ a b, ov a b → ov b a) :
    DisjointPred ov {x | IsMaxCluster C ov P x} := by
  rintro ⟨x, hx, y, hy, hne, hov⟩
  exact hne (le_antisymm (hy.2 x hx.1 hov) (hx.2 y hy.1 (hsym x y hov)))

/-- Joining two clusters connected at some pair of members yields a
    cluster: the honest form of their cumulativity remark for `-í`
    nouns — sums of *connected* clusters are clusters (arbitrary sums
    are not, which is exactly why `-oje` counts maximal clusters).
    Uses connection symmetry ((57)). -/
theorem isCluster_sup {P : α → Prop} {Z₁ Z₂ : Finset α}
    (hsymC : ∀ a b, C a b → C b a)
    (h₁ : Z₁.Nonempty) (h₂ : Z₂.Nonempty)
    (hP₁ : ∀ z ∈ Z₁, P z) (hP₂ : ∀ z ∈ Z₂, P z)
    (hc₁ : ∀ z ∈ Z₁, ∀ z' ∈ Z₁, ChainIn C Z₁ z z')
    (hc₂ : ∀ z ∈ Z₂, ∀ z' ∈ Z₂, ChainIn C Z₂ z z')
    {z₁ z₂ : α} (hz₁ : z₁ ∈ Z₁) (hz₂ : z₂ ∈ Z₂) (hlink : C z₁ z₂) :
    IsCluster C P (Z₁.sup' h₁ id ⊔ Z₂.sup' h₂ id) := by
  classical
  have hsub₁ : Z₁ ⊆ Z₁ ∪ Z₂ := Finset.subset_union_left
  have hsub₂ : Z₂ ⊆ Z₁ ∪ Z₂ := Finset.subset_union_right
  have hrel₁ : (fun a b : α => a ∈ Z₁ ∧ b ∈ Z₁ ∧ C a b) ≤
      (fun a b : α => a ∈ Z₁ ∪ Z₂ ∧ b ∈ Z₁ ∪ Z₂ ∧ C a b) :=
    fun _ _ ⟨hu, hv, hC⟩ => ⟨hsub₁ hu, hsub₁ hv, hC⟩
  have hrel₂ : (fun a b : α => a ∈ Z₂ ∧ b ∈ Z₂ ∧ C a b) ≤
      (fun a b : α => a ∈ Z₁ ∪ Z₂ ∧ b ∈ Z₁ ∪ Z₂ ∧ C a b) :=
    fun _ _ ⟨hu, hv, hC⟩ => ⟨hsub₂ hu, hsub₂ hv, hC⟩
  have hmono₁ : ∀ a b, ChainIn C Z₁ a b → ChainIn C (Z₁ ∪ Z₂) a b := Relation.ReflTransGen.mono hrel₁
  have hmono₂ : ∀ a b, ChainIn C Z₂ a b → ChainIn C (Z₁ ∪ Z₂) a b := Relation.ReflTransGen.mono hrel₂
  have hstep : ChainIn C (Z₁ ∪ Z₂) z₁ z₂ :=
    Relation.ReflTransGen.single ⟨hsub₁ hz₁, hsub₂ hz₂, hlink⟩
  have hstep' : ChainIn C (Z₁ ∪ Z₂) z₂ z₁ :=
    Relation.ReflTransGen.single ⟨hsub₂ hz₂, hsub₁ hz₁, hsymC _ _ hlink⟩
  refine ⟨Z₁ ∪ Z₂, h₁.mono hsub₁, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact hP₁ z h
    · exact hP₂ z h
  · rw [Finset.sup'_union h₁ h₂ id]
  · intro z hz z' hz'
    rcases Finset.mem_union.mp hz with h | h <;>
      rcases Finset.mem_union.mp hz' with h' | h'
    · exact hmono₁ _ _ (hc₁ z h z' h')
    · exact ((hmono₁ _ _ (hc₁ z h z₁ hz₁)).trans hstep).trans
        (hmono₂ _ _ (hc₂ z₂ hz₂ z' h'))
    · exact ((hmono₂ _ _ (hc₂ z h z₂ hz₂)).trans hstep').trans
        (hmono₁ _ _ (hc₁ z₁ hz₁ z' h'))
    · exact hmono₂ _ _ (hc₂ z h z' h')

/-! ### The aggregate numeral `-oje` (their (64)) -/

/-- (64): `n`-oje `P` holds of `x` iff the maximal `P`-clusters properly
    below `x` number exactly `n`. -/
def ojeSem (n : ℕ) (P : α → Prop) (x : α) : Prop :=
  ∃ Y : Finset α,
    (∀ z, (z < x ∧ IsMaxCluster C ov P z) ↔ z ∈ Y) ∧ Y.card = n

/-- **Aggregate-numeral cardinality is determinate**: the witnessing set
    of (64) is the set of maximal clusters below `x`, so its cardinality
    is unique. This is the formal content of `*tři dvoje klíče` ((27))
    and `*všechny dvoje` ((26)): the output of an aggregate numeral
    cannot be re-specified by an outer cardinal — unlike the `-ice`
    group numerals, whose [landman-1989]-style group atoms are freely
    recountable (*dvě trojice*, (54)). -/
theorem ojeSem_determinate {n m : ℕ} {P : α → Prop} {x : α}
    (hn : ojeSem C ov n P x) (hm : ojeSem C ov m P x) : n = m := by
  obtain ⟨Y, hY, rfl⟩ := hn
  obtain ⟨Y', hY', rfl⟩ := hm
  have : Y = Y' := Finset.ext fun z => (hY z).symm.trans (hY' z)
  rw [this]

/-! ### The taxonomic numeral `-ojí` (their (50)) -/

/-- (50), extensionalized over a subkind relation `T`: `n`-ojí `k` holds
    of a set of kinds all of which are subkinds of `k`, numbering `n`. -/
def ojiSem {κ : Type*} (T : κ → κ → Prop) (n : ℕ) (k : κ)
    (X : Finset κ) : Prop :=
  (∀ z ∈ X, T z k) ∧ X.card = n

/-- Kind-less arguments defeat the taxonomic numeral ((52): `#dvojí Petr
    Novák` — proper names supply no subkinds). -/
theorem oji_needs_subkinds {κ : Type*} {T : κ → κ → Prop} {k : κ}
    (hk : ∀ z, ¬T z k) {n : ℕ} (hn : n ≠ 0) :
    ¬∃ X : Finset κ, ojiSem T n k X := by
  rintro ⟨X, hX, hcard⟩
  rcases Finset.eq_empty_or_nonempty X with rfl | ⟨z, hz⟩
  · exact hn (hcard ▸ rfl)
  · exact hk z (hX z hz)

/-! ### The individuation-scale junction (their Table 3.1, §3.2.1)

Third consumer of `Features/Individuation.lean`. The suffix `-í` maps
individuated roots to coherent-collection denotations — a morphological
*descent* of the scale ([grimm-2018]'s types) — and Czech's countability
boundary is monotone on the scale, with the twist that the
collective-aggregate region is populated *derivationally*. -/

/-- A Table 3.1 row: root, derived aggregate, glosses. -/
structure DerivedAggregate where
  root : String
  rootGloss : String
  derived : String
  derivedGloss : String
  deriving DecidableEq, Repr

/-- A sample of Table 3.1 (trees, plants, complex objects, nautical
    terms). Roots are countable individual nouns (their fn. 5: 21 of
    the 22 listed roots are purely countable; *dřevo* 'wood' is the
    ambiguous exception). -/
def table31 : List DerivedAggregate :=
  [⟨"strom", "tree", "stromoví", "clump of trees"⟩,
   ⟨"list", "leaf", "listí", "foliage"⟩,
   ⟨"trn", "thorn", "trní", "thorns, brambles"⟩,
   ⟨"cihla", "brick", "cihloví", "brickwork"⟩,
   ⟨"krajka", "lace", "krajkoví", "lacework"⟩,
   ⟨"lano", "rope", "lanoví", "rigging/ropes"⟩,
   ⟨"kámen", "rock", "kamení", "rocks"⟩]

/-- The scale position of `-í` inputs (countable individual roots) and
    outputs (coherent collections — spatial proximity or functional
    interdependence, their §3.2.1). -/
def rootType : IndividuationType := .individualEntity

def derivedType : IndividuationType := .collectiveAggregate

/-- `-í` descends the individuation scale: derivational morphology moves
    a noun from the individual region into the collective-aggregate
    region — the inverse of the mass-to-count trajectory
    flexibility-foundational theories predict (their §3.3 against
    Borer). -/
theorem isuffix_descends : derivedType < rootType := by decide

/-- Czech grammatical countability (combination with simple cardinals,
    pluralization, *mnozí*): individuals are count (*pes*, (4));
    substances (*bláto*, (5)), granulars (*písek*, (8b)), and derived
    aggregates (*listí*, (9)–(11)) are non-count. -/
inductive CzechClass where
  | nonCount
  | count
  deriving DecidableEq, Repr

def CzechClass.toNat : CzechClass → Nat
  | .nonCount => 0
  | .count => 1

instance : LinearOrder CzechClass :=
  LinearOrder.lift' CzechClass.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [CzechClass.toNat])

/-- The Czech countability map on the individuation scale. -/
def czechClassify : IndividuationType → CzechClass
  | .substance => .nonCount
  | .granularAggregate => .nonCount
  | .collectiveAggregate => .nonCount
  | .individualEntity => .count

/-- Czech draws its countability boundary monotonically on the
    individuation scale — the [grimm-2018] order-preservation thesis,
    holding in a language where the collective-aggregate region is
    reached by derivation (`-í`) rather than only by lexical class. -/
theorem czech_monotone : Monotone czechClassify := by decide

/-- The derivational route: `-í` carries a count root to a non-count
    output — countability change without coercion, the data point
    against derive-count-from-mass architectures (their §3.3). -/
theorem isuffix_decountabilizes :
    czechClassify rootType = .count ∧
    czechClassify derivedType = .nonCount := ⟨rfl, rfl⟩

end GrimmDocekal2021
