import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Linglib.Features.Number.Decomposition
import Linglib.Syntax.Minimalist.Phi.Recursion

/-!
# Harbour (2014): Paucity, Abundance, and the Theory of Number

This file formalizes [harbour-2014]'s account of the approximative numbers, paucal and greater
plural, by a feature [±additive] of additive closure, over the library's [±atomic, ±minimal]
decomposition and its activation and recursion parameters (`Features/Number/Decomposition.lean`,
`Syntax/Minimalist/Phi/Recursion.lean`). The convexity condition (32) asks basic meanings to be
convex regions of the number lattice, and its definition of convexity (33) is `Set.OrdConnected`,
`ordConnected_iff_convexity_def`; on the first-person lattice the [+additive] region is not
convex, since between the speaker atom and any [+additive] plurality lies a [−additive] paucity
(section 4.5, Figure 8), `firstPerson_additive_not_ordConnected`, which is why [±additive] alone
is never a language's number feature while [±atomic] or [±minimal] alone can be. Feature bundles
being sets (27), a doubly negative specification of a feature is its maximal one, so there is no
dyad augmented (25) or quadral (26), `axiom_of_extension`. The Greenberg-style implications of
Table 1 hold across the well-formed parameter space, `table1_implications_generated`, every
attested system of Table 3 satisfies them, and the unattested setting {±additive, ±minimal*}
would violate the implication from unit augmented to augmented, so the universals are contingent
on the typology's gaps (section 5.1). In Mele-Fila (Table 4) the plural is [+additive] relative
to the lower of two conventionalized cuts and [−additive] relative to the upper, so it belongs
both to the class the article *a* realizes and to the class the pronoun *raateu* realizes
(section 5.2).

## Implementation notes

The first-person lattice is modeled on a four-element carrier, the speaker and three others,
with the conventional cut at triads. The critique of privative geometries (section 6) is the
argument behind the containment filter of `Features/ContainmentPair.lean`, which Harbour
rejects. Table 1 (p. 186), Table 3 (p. 214), Table 4 (p. 216), (27), (32), (33), and Figure 8
were verified against the publication.

## References

* [harbour-2014]
* [gardenfors-2004]
* [grimm-2018]
* [corbett-2000]
-/

namespace Harbour2014

open Minimalist.Phi.Recursion

/-! ### Convexity (§4.5): (33) is `Set.OrdConnected` -/

/-- [harbour-2014] (33): "a lattice region L is convex if and only if
    `c ∈ L` whenever `a, b ∈ L` and `a ⊑ c ⊑ b`" — definitionally
    mathlib's `Set.OrdConnected`, hence the same predicate as
    [grimm-2018]'s no-discontinuous-class condition and the fixed points of
    `ordConnectedHull`. -/
theorem ordConnected_iff_convexity_def {α : Type*} [Preorder α] (L : Set α) :
    L.OrdConnected ↔ ∀ a ∈ L, ∀ b ∈ L, ∀ c, a ≤ c → c ≤ b → c ∈ L := by
  constructor
  · intro h a ha b hb c hac hcb
    exact h.out ha hb ⟨hac, hcb⟩
  · intro h
    exact ⟨λ a ha b hb c hc => h a ha b hb c hc.1 hc.2⟩

/-- The first-person(-exclusive) lattice over the ontology
    {i, o, o′, o″} (`0` = the speaker atom i): every element contains i
    ([harbour-2014] Figure 8, modeled on a four-element carrier). -/
def firstPerson : Set (Finset (Fin 4)) := {s | 0 ∈ s}

/-- The [+additive] value region of `{±additive}` on the first-person
    lattice, with the conventional cut at triads: the join-complete upper
    region *and* the speaker atom {i}, which — being the unique member of
    its equivalence class — is its own join-complete region defined by a
    single horizontal cut ([harbour-2014] p. 211, Figure 8). -/
def firstPersonAdditive : Set (Finset (Fin 4)) :=
  {s | 0 ∈ s ∧ (s.card = 1 ∨ 3 ≤ s.card)}

instance : DecidablePred (· ∈ firstPersonAdditive) := λ s =>
  decidable_of_iff (0 ∈ s ∧ (s.card = 1 ∨ 3 ≤ s.card)) Iff.rfl

/-- Both parts of the [+additive] region are genuinely join-complete
    ((7): the sum of any two elements stays within): the upper region is
    closed under union, and the atom trivially so. -/
theorem firstPersonAdditive_parts_joinComplete :
    (∀ s t : Finset (Fin 4), 0 ∈ s ∧ 3 ≤ s.card → 0 ∈ t ∧ 3 ≤ t.card →
      0 ∈ s ∪ t ∧ 3 ≤ (s ∪ t).card) ∧
    ({0} : Finset (Fin 4)) ∪ {0} = {0} := by
  constructor
  · decide
  · decide

/-- **The §4.5 disparity, as a theorem** (previously prose): the
    [+additive] value region of the first-person lattice is *nonconvex* —
    "between the [+additive] first-person atom and any [+additive]
    first-person plural, there must lie a [−additive] first-person paucal"
    (p. 212). Witness: i ⊑ io ⊑ ioo′, with the dyad io in the paucal gap.
    By the convexity condition (32) — basic meanings must be convex
    ([gardenfors-2004]) — `{±additive}` cannot be a language's sole
    number feature, while `{±atomic}` and `{±minimal}` (whose cuts are
    single horizontal lines) can. -/
theorem firstPerson_additive_not_ordConnected :
    ¬ firstPersonAdditive.OrdConnected := by
  intro h
  have h01 : ({0, 1} : Finset (Fin 4)) ∈ firstPersonAdditive :=
    h.out (x := {0}) (by decide) (y := {0, 1, 2}) (by decide)
      ⟨by decide, by decide⟩
  exact absurd h01 (by decide)

/-! ### The axiom of extension (§4.2)

Feature bundles are sets, so (27) {a, a} = {a}: `[+F −F]` is the maximal
specification a single feature admits. This rules out the dyad augmented
(25) `*[+minimal −minimal −minimal]` and the quadral (26)
`*[+minimal −minimal −minimal −atomic]` — they are not richer bundles at
all — and caps exact numbers at trial and unit augmented. -/

/-- (27) in bundle form: a third occurrence of a feature value adds
    nothing — the putative quadral bundle *is* the trial bundle. -/
theorem axiom_of_extension :
    ({true, false, false} : Finset Bool) = {true, false} := by decide

/-- A single bivalent feature's value set has at most two elements —
    `[+F −F]` is maximal complexity. -/
theorem feature_set_card_le_two : ∀ s : Finset Bool, s.card ≤ 2 := by decide

/-! ### Typology (§5.1): Table 1 universals as corollaries

(34) Typological implication schema: if category A must cooccur with
category B, then the parameter setting for A generates B. The named
Table 1 implications hold across the entire well-formed parameter space,
and every attested Table 3 system satisfies the full universal set through
`HarbourConfig.toSystem`. -/

open Minimalist.Phi.Recursion in
/-- TR → DU, DU → SG, SG → PL, PC → PL, and GR.PC → PC ([harbour-2014]
    Table 1) hold for every well-formed parameter setting — Greenberg-style
    universals as corollaries of the feature geometry, not stipulations. -/
theorem table1_implications_generated :
    ∀ c : HarbourConfig, c.wellFormed →
      (.trial ∈ c.surfaceCategories → .dual ∈ c.surfaceCategories) ∧
      (.dual ∈ c.surfaceCategories → .singular ∈ c.surfaceCategories) ∧
      (.singular ∈ c.surfaceCategories → .plural ∈ c.surfaceCategories) ∧
      (.paucal ∈ c.surfaceCategories → .plural ∈ c.surfaceCategories) ∧
      (.greaterPaucal ∈ c.surfaceCategories →
        .paucal ∈ c.surfaceCategories) := by
  decide

/-- Every attested Table 3 system, read as a `Number.System` through the
    `HarbourConfig.toSystem` bridge, satisfies all Table 1 universals
    (`Number.System.WellFormed`). The generative inventory and the
    descriptive inventory agree. -/
theorem table3_systems_wellFormed :
    ∀ e ∈ harbour2014Table3, (e.config.toSystem).WellFormed := by decide

/-! ### The lacunae (§5.1, pp. 214–215)

Four parameter settings are well-formed but unattested:
`{±additive, ±minimal*}`, `{±additive*, ±minimal}`,
`{±additive*, ±minimal*}`, and `{±additive*, ±minimal*, ±atomic}`.
Harbour argues the gaps are contingent (unit augmentation and multiple
approximative numbers are independently rare). The first lacuna shows the
universals are claims about *attested* systems: its generated system
violates U.AUG → AUG. -/

/-- The unattested setting `{±additive, ±minimal*}` (Table 3's first
    lacuna row): minimal, unit augmented, paucal, plural. -/
def uaugLacuna : HarbourConfig :=
  ⟨false, true, true, true, false⟩

/-- The lacuna's system has unit augmented without augmented — Table 1's
    U.AUG → AUG would fail were it attested. The universal is protected by
    the (contingent) typological gap, exactly as the paper's discussion of
    the lacunae implies. -/
theorem lacuna_violates_uaug :
    uaugLacuna.wellFormed = true ∧
    ¬ (uaugLacuna.toSystem).WellFormed := by
  constructor
  · decide
  · decide

/-! ### Composed number (§5.2): Mele-Fila, Table 4

Mele-Fila (singular–dual–paucal–plural–greater plural) crosscuts two
syncretism patterns: the definite article *a* covers plural and greater
plural — exactly the values carrying (+additive) — while the pronoun
*raateu* covers paucal and plural — exactly the values carrying
(−additive). Plural belongs to both natural classes because, with two
conventionalized cuts, it is [−additive] relative to the high cut and
[+additive] relative to the low one. -/

/-- Mele-Fila's five values ([harbour-2014] Table 4). -/
def meleFilaValues : List Number :=
  [.singular, .dual, .paucal, .plural, .greaterPlural]

/-- The position of a value on Mele-Fila's scale. -/
def rank (v : Number) : ℕ := meleFilaValues.idxOf v

/-- [+additive] relative to a cut of the scale: the values at the cut and above it. -/
def Additive (cut : ℕ) (v : Number) : Prop := cut ≤ rank v

instance (cut : ℕ) : DecidablePred (Additive cut) := λ _ => Nat.decLe _ _

/-- The two conventionalized cuts of [±additive] (Table 4): the lower between paucal and
plural, the upper between plural and greater plural. -/
def lowerCut : ℕ := 3

def upperCut : ℕ := 4

/-- The plural is [+additive] relative to the lower cut and [−additive] relative to the upper:
the two signs of Table 4's bottom row. -/
theorem plural_additive_lower_not_upper :
    Additive lowerCut .plural ∧ ¬ Additive upperCut .plural := by decide

/-- The article *a* realizes the values [+additive] relative to the lower cut, plural and
greater plural; the pronoun *raateu* the non-minimal values [−additive] relative to the upper
cut, paucal and plural; plural is in both classes. -/
theorem meleFila_syncretism_classes :
    meleFilaValues.filter (λ v => decide (Additive lowerCut v)) = [.plural, .greaterPlural] ∧
      meleFilaValues.filter (λ v => decide (2 ≤ rank v ∧ ¬ Additive upperCut v)) =
        [.paucal, .plural] := by
  decide

/-- Mele-Fila's inventory satisfies the Table 1 universals. -/
theorem meleFila_wellFormed :
    Number.System.WellFormed
      { name := "Mele-Fila", values := meleFilaValues } := by decide

end Harbour2014
