import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Semantics.Mereology
import Linglib.Semantics.Plurality.Groups
import Linglib.Data.Examples.GrimmDocekal2021

/-!
# Grimm and Dočekal (2021): Counting Aggregates, Groups and Kinds

This file formalizes [grimm-docekal-2021]'s account of the Czech morphology that counts
aggregates, groups, and kinds. The suffix *-í* derives strongly non-countable nouns from
countable roots, *listí* 'foliage' from *list* 'leaf', which take no plural, no cardinal, and no
packaging (`derived_aggregates_noncountable`); the group numeral *-ice* yields a countable group,
*dvě trojice námořníků* 'two groups of three sailors', whereas the aggregate numeral *-oje* and
the taxonomic numeral *-ojí* yield phrases that no outer cardinal or universal quantifier can
take (`complex_numerals_uncounted`); *-oje* selects nouns whose referents come in connected
sets (`aggregate_numeral_selects`); and Czech nouns are inflexible, with no grinding and a
taxonomic plural confined to non-episodic contexts where the taxonomic numeral is free
(`taxonomic_plural_nonepisodic`). Section 5 extends [krifka-1995b]'s nominal semantics with
[landman-1989]'s groups for *-ice* and with [grimm-2012]'s mereotopology for *-í* and *-oje*:
a cluster is a sum of entities transitively connected through it, a maximal cluster absorbs every
cluster it overlaps, maximal clusters are disjoint (`maxClusters_disjointPred`), *-oje* counts
the maximal clusters below its argument, whose number is therefore determinate
(`ojeSem_determinate`), and *-ojí* counts subkinds and so fails on a kind-less argument
(`oji_needs_subkinds`).

## Implementation notes

The connection relation is a parameter, the paper's proximate or external connectedness; the
cluster of (61) uses a finite set of members and its supremum. The group numeral is stated over
the library's `Plurality.GroupStructure`, whose `up` packs a sum into an atom, which is why a
group can be counted again. The paper's Table 1, the twenty-two nouns derived by *-í*, is
lexical data for the Czech Fragment and is not retyped here.

## References

* [grimm-docekal-2021]
* [krifka-1995b]
* [landman-1989]
* [grimm-2012]
* [casati-varzi-1999]

## TODO

Table 1's derived aggregates belong in `Fragments/Slavic/Czech/`; [krifka-1995b]'s kind and
object unit operators of section 4 are not formalized.
-/

namespace GrimmDocekal2021

open Mereology Data.Examples Features

/-! ### The judged noun phrases, section 2 -/

/-- The class of the noun a numeral or operation applies to. -/
inductive Noun where
  | ordinary
  | animate
  /-- A noun derived by *-í*. -/
  | derivedAggregate
  | pluraleTantum
  /-- A countable noun whose referents typically come together in multiples, *klíče* 'keys'. -/
  | multiple
  | substance
  | abstract
  /-- A uniquely referring phrase, *noha tohoto stolu* 'this table's leg'. -/
  | unique
  | proper
  deriving DecidableEq, Repr

/-- The numeral of the phrase. -/
inductive Numeral where
  | none
  | simple
  /-- *-ice*. -/
  | group
  /-- *-oje*, *-ery*. -/
  | aggregate
  /-- *-ojí*, *-ero*. -/
  | taxonomic
  deriving DecidableEq, Repr

/-- The operation the phrase tests. -/
inductive Operation where
  | none
  | pluralization
  | simpleCardinal
  /-- *mnohé* 'many'. -/
  | vagueQuantifier
  /-- *všechny* 'all'. -/
  | universal
  /-- A simple cardinal over a complex numeral. -/
  | outerCardinal
  | packaging
  | grinding
  /-- Deriving an aggregate with *-í*. -/
  | derivation
  deriving DecidableEq, Repr

/-- The context a reading is judged in. -/
inductive Context where
  | episodic
  | generic
  /-- A fast-food order, section 2.2.2. -/
  | portion
  deriving DecidableEq, Repr

/-- A judged noun phrase. -/
structure Row where
  noun : Noun
  numeral : Numeral
  operation : Operation
  context : Option Context
  taxonomic : Bool
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let noun ← ex.parse? "noun"
    [("ordinary", Noun.ordinary), ("animate", .animate), ("derivedAggregate", .derivedAggregate),
      ("pluraleTantum", .pluraleTantum), ("multiple", .multiple), ("substance", .substance),
      ("abstract", .abstract), ("unique", .unique), ("proper", .proper)]
  let numeral ← ex.parse? "numeral"
    [("none", Numeral.none), ("simple", .simple), ("group", .group), ("aggregate", .aggregate),
      ("taxonomic", .taxonomic)]
  let operation ← ex.parse? "operation"
    [("none", Operation.none), ("pluralization", .pluralization),
      ("simpleCardinal", .simpleCardinal), ("vagueQuantifier", .vagueQuantifier),
      ("universal", .universal), ("outerCardinal", .outerCardinal), ("packaging", .packaging),
      ("grinding", .grinding), ("derivation", .derivation)]
  pure ⟨noun, numeral, operation,
    ex.parse? "context"
      [("episodic", Context.episodic), ("generic", .generic), ("portion", .portion)],
    ex.feature? "reading" = some "taxonomic", ex.judgment⟩

/-- The judged phrases of sections 2, 4, and 5. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Nouns derived by *-í* take neither plural, nor simple cardinal, nor a vague quantifier, nor a
packaging reading, (9) to (12). -/
theorem derived_aggregates_noncountable :
    ∀ r ∈ rows, r.noun = .derivedAggregate → r.numeral ≠ .aggregate →
      r.operation ≠ .none → r.judgment ≠ .acceptable := by
  decide

/-- *-í* does not apply to an arbitrary countable noun, (13). -/
theorem derivation_restricted :
    ∀ r ∈ rows, r.operation = .derivation → r.judgment = .ungrammatical := by
  decide

/-- A group numeral phrase is counted again and quantified by *mnohé*, (17) and (18), but not
by *všechna*, (19). -/
theorem group_numeral_countable :
    (∃ r ∈ rows, r.numeral = .group ∧ r.operation = .outerCardinal ∧ r.judgment = .acceptable) ∧
      (∃ r ∈ rows, r.numeral = .group ∧ r.operation = .vagueQuantifier ∧
        r.judgment = .acceptable) ∧
      ∀ r ∈ rows, r.numeral = .group → r.operation = .universal → r.judgment ≠ .acceptable := by
  decide

/-- Aggregate and taxonomic numeral phrases take no outer cardinal and no universal quantifier,
(26), (27), (32), (33). -/
theorem complex_numerals_uncounted :
    ∀ r ∈ rows, (r.numeral = .aggregate ∨ r.numeral = .taxonomic) →
      (r.operation = .outerCardinal ∨ r.operation = .universal) → r.judgment ≠ .acceptable := by
  decide

/-- *-oje* takes nouns derived by *-í*, pluralia tantum, and nouns of entities that come in
multiples, (20) to (24), and rejects ordinary countable nouns, (25) and (68). -/
theorem aggregate_numeral_selects :
    (∀ r ∈ rows, r.numeral = .aggregate → r.operation = .none →
      (r.noun = .derivedAggregate ∨ r.noun = .pluraleTantum ∨ r.noun = .multiple) →
        r.judgment = .acceptable) ∧
      ∀ r ∈ rows, r.numeral = .aggregate → r.noun = .ordinary → r.judgment ≠ .acceptable := by
  decide

/-- Section 2.3: grinding is rejected, (34) and (35); the taxonomic reading of a plural or a
simple cardinal phrase needs a non-episodic context, (36) to (40), while the taxonomic numeral
is free in both. -/
theorem taxonomic_plural_nonepisodic :
    (∀ r ∈ rows, r.operation = .grinding → r.judgment ≠ .acceptable) ∧
      (∀ r ∈ rows, r.taxonomic = true → r.numeral ≠ .taxonomic →
        (r.judgment = .acceptable ↔ r.context = some .generic)) ∧
      ∀ r ∈ rows, r.taxonomic = true → r.numeral = .taxonomic → r.judgment = .acceptable := by
  decide

/-- The taxonomic numeral fails on a uniquely referring or proper argument, (52). -/
theorem taxonomic_needs_kind :
    ∀ r ∈ rows, r.numeral = .taxonomic → (r.noun = .unique ∨ r.noun = .proper) →
      r.judgment ≠ .acceptable := by
  decide

/-! ### Cluster mereotopology, section 5.2

Connection is reflexive and symmetric ((56), (57)) and parthood entails it (58). A cluster is
the sum of a set of entities of a property, any two of which are connected through the set
((60), (61)); a maximal cluster absorbs every cluster it overlaps (63). -/

variable {α : Type*} [SemilatticeSup α] (C ov : α → α → Prop)

/-- (60): connected through a chain of members of `Z`. -/
def ChainIn (Z : Finset α) : α → α → Prop :=
  Relation.ReflTransGen λ a b => a ∈ Z ∧ b ∈ Z ∧ C a b

/-- (61): a cluster individual, the sum of a nonempty set of `P`-entities pairwise transitively
connected through the set. -/
def IsCluster (P : α → Prop) (x : α) : Prop :=
  ∃ (Z : Finset α) (hZ : Z.Nonempty),
    (∀ z ∈ Z, P z) ∧ x = Z.sup' hZ id ∧ ∀ z ∈ Z, ∀ z' ∈ Z, ChainIn C Z z z'

/-- (63): a maximal cluster absorbs every cluster overlapping it. -/
def IsMaxCluster (P : α → Prop) (x : α) : Prop :=
  IsCluster C P x ∧ ∀ y, IsCluster C P y → ov y x → y ≤ x

/-- Maximal clusters are pairwise disjoint, the paper's remark after (63): two overlapping
maximal clusters would each absorb the other. -/
theorem maxClusters_disjointPred {P : α → Prop} (hsym : ∀ a b, ov a b → ov b a) :
    DisjointPred ov {x | IsMaxCluster C ov P x} := by
  rintro ⟨x, hx, y, hy, hne, hov⟩
  exact hne (le_antisymm (hy.2 x hx.1 hov) (hx.2 y hy.1 (hsym x y hov)))

/-- Two clusters connected at some pair of members sum to a cluster: the cumulativity of *-í*
nouns, *listí* and *listí* making *listí*, for connected sums. -/
theorem isCluster_sup {P : α → Prop} {Z₁ Z₂ : Finset α} (hsymC : ∀ a b, C a b → C b a)
    (h₁ : Z₁.Nonempty) (h₂ : Z₂.Nonempty) (hP₁ : ∀ z ∈ Z₁, P z) (hP₂ : ∀ z ∈ Z₂, P z)
    (hc₁ : ∀ z ∈ Z₁, ∀ z' ∈ Z₁, ChainIn C Z₁ z z') (hc₂ : ∀ z ∈ Z₂, ∀ z' ∈ Z₂, ChainIn C Z₂ z z')
    {z₁ z₂ : α} (hz₁ : z₁ ∈ Z₁) (hz₂ : z₂ ∈ Z₂) (hlink : C z₁ z₂) :
    IsCluster C P (Z₁.sup' h₁ id ⊔ Z₂.sup' h₂ id) := by
  classical
  have hsub₁ : Z₁ ⊆ Z₁ ∪ Z₂ := Finset.subset_union_left
  have hsub₂ : Z₂ ⊆ Z₁ ∪ Z₂ := Finset.subset_union_right
  have hmono₁ : ∀ a b, ChainIn C Z₁ a b → ChainIn C (Z₁ ∪ Z₂) a b :=
    Relation.ReflTransGen.mono λ _ _ ⟨hu, hv, hC⟩ => ⟨hsub₁ hu, hsub₁ hv, hC⟩
  have hmono₂ : ∀ a b, ChainIn C Z₂ a b → ChainIn C (Z₁ ∪ Z₂) a b :=
    Relation.ReflTransGen.mono λ _ _ ⟨hu, hv, hC⟩ => ⟨hsub₂ hu, hsub₂ hv, hC⟩
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
    rcases Finset.mem_union.mp hz with h | h <;> rcases Finset.mem_union.mp hz' with h' | h'
    · exact hmono₁ _ _ (hc₁ z h z' h')
    · exact ((hmono₁ _ _ (hc₁ z h z₁ hz₁)).trans hstep).trans (hmono₂ _ _ (hc₂ z₂ hz₂ z' h'))
    · exact ((hmono₂ _ _ (hc₂ z h z₂ hz₂)).trans hstep').trans (hmono₁ _ _ (hc₁ z₁ hz₁ z' h'))
    · exact hmono₂ _ _ (hc₂ z h z' h')

/-! ### The three numerals, sections 4.2 and 5 -/

/-- (55): the group numeral packs a sum of `n` members of `P` into a group atom. -/
def iceSem (G : Plurality.GroupStructure α) (n : ℕ) (P : α → ℕ → Prop) (x : α) : Prop :=
  ∃ y, x = G.up y ∧ P y n

/-- A group numeral phrase denotes an atom, which is why it is counted again, (17) and (54). -/
theorem iceSem_atom {G : Plurality.GroupStructure α} {n : ℕ} {P : α → ℕ → Prop} {x : α}
    (h : iceSem G n P x) : Mereology.Atom x :=
  let ⟨_, hx, _⟩ := h
  hx ▸ G.atom_up _

/-- (64): `n`-*oje* `P` holds of `x` when the maximal `P`-clusters properly below `x` number
`n`. -/
def ojeSem (n : ℕ) (P : α → Prop) (x : α) : Prop :=
  ∃ Y : Finset α, (∀ z, (z < x ∧ IsMaxCluster C ov P z) ↔ z ∈ Y) ∧ Y.card = n

/-- The cardinality an aggregate numeral asserts is determinate, the witnessing set being the
maximal clusters below the argument: no outer cardinal can re-specify it, (27) and (26). -/
theorem ojeSem_determinate {n m : ℕ} {P : α → Prop} {x : α} (hn : ojeSem C ov n P x)
    (hm : ojeSem C ov m P x) : n = m := by
  obtain ⟨Y, hY, rfl⟩ := hn
  obtain ⟨Y', hY', rfl⟩ := hm
  rw [Finset.ext λ z => (hY z).symm.trans (hY' z)]

/-- (50), over a subkind relation `T`: `n`-*ojí* `k` holds of a set of subkinds of `k` numbering
`n`. -/
def ojiSem {κ : Type*} (T : κ → κ → Prop) (n : ℕ) (k : κ) (X : Finset κ) : Prop :=
  (∀ z ∈ X, T z k) ∧ X.card = n

/-- A kind-less argument defeats the taxonomic numeral, (52): a proper name has no subkinds. -/
theorem oji_needs_subkinds {κ : Type*} {T : κ → κ → Prop} {k : κ} (hk : ∀ z, ¬ T z k) {n : ℕ}
    (hn : n ≠ 0) : ¬ ∃ X : Finset κ, ojiSem T n k X := by
  rintro ⟨X, hX, hcard⟩
  rcases Finset.eq_empty_or_nonempty X with rfl | ⟨z, hz⟩
  · exact hn (hcard ▸ rfl)
  · exact hk z (hX z hz)

end GrimmDocekal2021
