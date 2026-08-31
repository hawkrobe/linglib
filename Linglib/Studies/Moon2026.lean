import Linglib.Features.Number.Interp
import Linglib.Studies.Filip2012
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Moon (2026): countability and measured parts in mixed drink nouns

Mixed drink nouns (*martini*, *cappuccino*) are count nouns that denote liquids.
[moon-2026] derives their countability from their part structure: a mixed drink is a
mereological sum of ingredient parts standing in a fixed ratio of measures (`Recipe`,
`RatioHolds`), one of which — the shot of liquor or espresso, the MEASURED PART — supplies
the unit of individuation, and the whole is a connected liquid in the mereotopological
sense of [casati-varzi-1999] (`ConnectedLiquid`, with spatial structure a
`TopologicalSpace` independent of parthood). The denotation `mixedDrinkDen` packages
Moon's final formula as the existence of a `MixedDrinkWitness`.

Two consequences carry the countability argument. The sum of two spatially separate drinks
is not a connected liquid, so the denotation is not cumulative
(`not_mixedDrinkDen_of_not_selfConnected`) — a topological route to non-cumulativity that
a bare semilattice lacks, where it comes only from quantization (`connectivity_breaks_cum`).
And a mixed drink has proper parts, so it is not a mereological atom (`mixedDrink_not_atom`)
and [borer-2005]'s individuation operator excludes it (`div_excludes_mixed_drinks`), while
half a drink with its ratios preserved is still a drink, so the denotation is not quantized
either (`mixedDrink_not_qua`). Mixed drinks thus occupy the ¬CUM ∧ ¬QUA middle ground of
[filip-2012] (`mixedDrink_middle_ground`), and the gap propagates to drinking VPs through
`Filip2012.middle_ground_stable` (`mixedDrink_VP_propagation_gap`). Multipliers such as
*double* rescale the measured part's ratio constant rather than the whole (`doubleRecipe`,
[wagiel-2021]'s subatomic quantification), and *dry* rescales another ingredient's
(`modifyRatio`).

Moon's corpus and judgment data stay in prose: in her COCA counts (Appendix A) cocktail
nouns pattern with count nouns on bare plurals and numerals while non-count drink nouns
take bare singulars and containers; countability survives coercion contexts such as
*pitcher of martinis*; and *who drank more americanos?* is ambiguous between volume,
portions, and measured parts.

## References

* [moon-2026]
* [borer-2005], [casati-varzi-1999], [filip-2012], [krifka-2021], [wagiel-2021]
-/

namespace Moon2026

open Mereology
open Semantics.Aspect.Incremental (IsSincVerb)
open Semantics.Aspect.Cumulativity (VP)

/-! ### Mereotopology -/

section Mereotopology

variable {α : Type*} [TopologicalSpace α]

/-- Self-connected ([casati-varzi-1999]): the parts of `x`, the principal downset
`Set.Iic x`, form a connected set. -/
def SelfConnected [Preorder α] (x : α) : Prop := IsConnected (Set.Iic x)

/-- Phase of matter ([krifka-2021]): solids retain shape, granulars are aggregates of
discrete pieces, liquids have parts in constant internal motion. -/
inductive Phase where
  | solid
  | granular
  | liquid
  deriving DecidableEq, Repr

/-- Connected liquid (Moon's definition (23), without its temporal parameter):
self-connected with every part liquid. -/
def ConnectedLiquid [PartialOrder α] (phase : α → Phase) (x : α) : Prop :=
  SelfConnected x ∧ ∀ y ≤ x, phase y = .liquid

theorem ConnectedLiquid.selfConnected [PartialOrder α] {phase : α → Phase} {x : α}
    (h : ConnectedLiquid phase x) : SelfConnected x :=
  h.1

variable [SemilatticeSup α] {P : α → Prop}

/-- A predicate entailing self-connection is not cumulative once two instances have a
disconnected sum: non-cumulativity from topology rather than from quantization
(`qua_cum_incompatible`). -/
theorem connectivity_breaks_cum (hConn : ∀ x, P x → SelfConnected x) {x y : α} (hx : P x)
    (hy : P y) (hDisc : ¬ SelfConnected (x ⊔ y)) : ¬ CUM P :=
  fun hCum => hDisc (hConn _ (hCum hx hy))

/-- With a proper part that is also an instance, such a predicate is neither cumulative
nor quantized. -/
theorem connectivity_middle_ground (hConn : ∀ x, P x → SelfConnected x) {a b : α} (ha : P a)
    (hb : P b) (hDisc : ¬ SelfConnected (a ⊔ b)) {x y : α} (hx : P x) (hy : P y)
    (hlt : y < x) : ¬ CUM P ∧ ¬ QUA P :=
  ⟨connectivity_breaks_cum hConn ha hb hDisc, fun hQ => hQ hy hx hlt.ne hlt.le⟩

end Mereotopology

/-! ### Recipes and the mixed-drink denotation -/

/-- A mixed drink recipe: ingredient predicates, positive ratio constants, and the index of
the measured part. -/
structure Recipe (α K : Type*) [Zero K] [LT K] (n : ℕ) where
  /-- The ingredient predicates. -/
  ingredients : Fin n → α → Prop
  /-- The ratio constants. -/
  ratios : Fin n → K
  ratios_pos : ∀ i, 0 < ratios i
  /-- The index of the measured part, the ingredient that supplies the unit. -/
  measuredPart : Fin n

variable {α K : Type*} [SemilatticeSup α] [TopologicalSpace α] [Field K] [LinearOrder K] {n : ℕ}

/-- Moon's ratio constraint, `μ yᵢ / rᵢ = μ yⱼ / rⱼ` for all ingredient parts, in
cross-multiplied form. -/
def RatioHolds (μ : α → K) (recipe : Recipe α K n) (parts : Fin n → α) : Prop :=
  ∀ i j, μ (parts i) * recipe.ratios j = μ (parts j) * recipe.ratios i

/-- A witness that `x` is a mixed drink under `recipe`: non-null, pairwise non-overlapping
ingredient parts of `x` that exhaust it, satisfy their ingredient predicates and the ratio
constraint, with `x` a connected liquid. -/
structure MixedDrinkWitness (recipe : Recipe α K n) (μ : α → K) (phase : α → Phase)
    (x : α) where
  /-- The entity filling each ingredient slot. -/
  assign : Fin n → α
  part_le : ∀ i, assign i ≤ x
  present : ∀ i, ¬ IsBot (assign i)
  satisfies : ∀ i, recipe.ingredients i (assign i)
  ratio : RatioHolds μ recipe assign
  disjoint : ∀ i j, i ≠ j → ¬ Overlap (assign i) (assign j)
  covers : ∀ z, z ≤ x → ∃ i, Overlap z (assign i)
  connected : ConnectedLiquid phase x

/-- The denotation of a mixed drink noun, Moon's final formula: ratio-related ingredient
parts forming a connected liquid. The MEASURED PART conjunct, which Moon leaves informal,
is recorded only as the recipe's `measuredPart` index and not imposed as a truth
condition, so this is her ratio formula (19) plus CONNECTED LIQUID; she notes that (19)
alone also covers ratio-structured non-count drinks such as *lemonade*. -/
def mixedDrinkDen (recipe : Recipe α K n) (μ : α → K) (phase : α → Phase) (x : α) : Prop :=
  Nonempty (MixedDrinkWitness recipe μ phase x)

variable {recipe : Recipe α K n} {μ : α → K} {phase : α → Phase}

theorem selfConnected_of_mixedDrinkDen {x : α} (hx : mixedDrinkDen recipe μ phase x) :
    SelfConnected x :=
  hx.some.connected.selfConnected

/-- Two margaritas in separate glasses do not sum to a margarita: the sum is not a
connected liquid. -/
theorem not_mixedDrinkDen_of_not_selfConnected {x : α} (hDisc : ¬ SelfConnected x) :
    ¬ mixedDrinkDen recipe μ phase x :=
  fun hx => hDisc (selfConnected_of_mixedDrinkDen hx)

/-- A single ingredient is not the drink: with at least two ingredients whose extensions
are exclusive of one another's parts, an entity all of whose parts are ingredient `i`
fills no other slot. -/
theorem not_mixedDrinkDen_of_exclusive {recipe : Recipe α K (n + 2)} {y : α} (i : Fin (n + 2))
    (hExcl : ∀ j ≠ i, ∀ z ≤ y, ¬ recipe.ingredients j z) :
    ¬ mixedDrinkDen recipe μ phase y :=
  fun ⟨w⟩ => let ⟨j, hj⟩ := exists_ne i; hExcl j hj _ (w.part_le j) (w.satisfies j)

/-- A mixed drink has at least two disjoint non-null parts, so it is not an atom. -/
theorem mixedDrink_not_atom {recipe : Recipe α K (n + 2)} {x : α}
    (hx : mixedDrinkDen recipe μ phase x) : ¬ Atom x := by
  intro hAtom
  obtain ⟨w⟩ := hx
  have h0 : w.assign 0 = x := Atom.eq hAtom (w.part_le 0) (w.present 0)
  have h1 : w.assign 1 = x := Atom.eq hAtom (w.part_le 1) (w.present 1)
  have hDisj := w.disjoint 0 1 Fin.zero_ne_one
  rw [h0, h1] at hDisj
  exact hDisj (Overlap.refl hAtom.not_isBot)

/-- The atoms-restriction — individuation as atom-based count theories construe it — excludes
mixed drinks: their unit of individuation is not atomicity but the measured part. -/
theorem atomsOf_excludes_mixed_drinks {recipe : Recipe α K (n + 2)} (DRINK : α → Prop) {x : α}
    (hx : mixedDrinkDen recipe μ phase x) : ¬ Number.atomsOf DRINK x :=
  fun ⟨_, hAtom⟩ => mixedDrink_not_atom hx hAtom

/-- Half a margarita with its ratios and connectivity preserved is a margarita, so the
denotation is not quantized. -/
theorem mixedDrink_not_qua {x y : α} (hx : mixedDrinkDen recipe μ phase x)
    (hy : mixedDrinkDen recipe μ phase y) (hlt : y < x) : ¬ QUA (mixedDrinkDen recipe μ phase) :=
  fun hQ => hQ hy hx hlt.ne hlt.le

/-- Mixed drinks occupy [filip-2012]'s middle ground, neither cumulative nor quantized,
as an instance of `connectivity_middle_ground`. -/
theorem mixedDrink_middle_ground {a b : α} (ha : mixedDrinkDen recipe μ phase a)
    (hb : mixedDrinkDen recipe μ phase b) (hDisc : ¬ SelfConnected (a ⊔ b)) {x y : α}
    (hx : mixedDrinkDen recipe μ phase x) (hy : mixedDrinkDen recipe μ phase y) (hlt : y < x) :
    ¬ CUM (mixedDrinkDen recipe μ phase) ∧ ¬ QUA (mixedDrinkDen recipe μ phase) :=
  connectivity_middle_ground (fun _ => selfConnected_of_mixedDrinkDen) ha hb hDisc hx hy hlt

/-- The middle ground propagates to VPs: a strictly incremental drinking verb with a
mixed-drink object is neither cumulative nor quantized (`Filip2012.middle_ground_stable`). -/
theorem mixedDrink_VP_propagation_gap {β : Type*} [SemilatticeSup β] (drinkTheme : α → β → Prop)
    [IsSincVerb drinkTheme] {a b : α} {e_a e_b : β} (ha : mixedDrinkDen recipe μ phase a)
    (hb : mixedDrinkDen recipe μ phase b) (hθ_a : drinkTheme a e_a) (hθ_b : drinkTheme b e_b)
    (hSum : ¬ mixedDrinkDen recipe μ phase (a ⊔ b)) {x y : α} {e_x : β}
    (hx : mixedDrinkDen recipe μ phase x) (hy : mixedDrinkDen recipe μ phase y) (hlt : y < x)
    (hθ_x : drinkTheme x e_x) :
    ¬ CUM (VP drinkTheme (mixedDrinkDen recipe μ phase)) ∧
      ¬ QUA (VP drinkTheme (mixedDrinkDen recipe μ phase)) :=
  Filip2012.middle_ground_stable ha hb hθ_a hθ_b hSum hx hy hlt hθ_x

/-! ### Modifying the ratios -/

variable [IsStrictOrderedRing K]

/-- Rescaling one ingredient's ratio constant: *dry martini* (Moon's (27b)) lowers the
vermouth relative to the gin. -/
def modifyRatio (recipe : Recipe α K n) (target : Fin n) (factor : K) (hPos : 0 < factor) :
    Recipe α K n where
  ingredients := recipe.ingredients
  ratios i := if i = target then factor * recipe.ratios i else recipe.ratios i
  ratios_pos i := by
    split_ifs
    exacts [mul_pos hPos (recipe.ratios_pos i), recipe.ratios_pos i]
  measuredPart := recipe.measuredPart

/-- The multiplier *double* targets the measured part ([wagiel-2021]): a double americano
has twice the espresso, not twice the volume. -/
def doubleRecipe (recipe : Recipe α K n) : Recipe α K n :=
  modifyRatio recipe recipe.measuredPart 2 two_pos

/-- A margarita: tequila, triple sec and lime juice in ratio `5 : 2 : 3/2`, with the tequila
as measured part. -/
def margaritaRecipe (α K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (tequila tripleSec limeJuice : α → Prop) : Recipe α K 3 where
  ingredients := ![tequila, tripleSec, limeJuice]
  ratios := ![5, 2, 3 / 2]
  ratios_pos i := by fin_cases i <;> norm_num
  measuredPart := 0

end Moon2026
