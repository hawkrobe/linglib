import Linglib.Core.Logic.ModalLogic
import Linglib.Theories.Semantics.Modality.Kratzer.Flavor

/-!
# Modal Semantic Universals

Formalizes the Independence of Force and Flavor (IFF) universal and the
Single Axis of Variability (SAV) universal from cross-linguistic modal typology.

## Key Definitions

* `satisfiesIFF`: A modal meaning ⟦m⟧ satisfies IFF iff ⟦m⟧ = fo(m) × fl(m)
* `satisfiesSAV`: A modal meaning satisfies SAV iff it varies on at most one axis
* `iffDegree`: Fraction of modals in a language satisfying IFF

## Key Theorems

* `sav_implies_iff`: SAV is strictly stronger than IFF
* `cartesianProduct_satisfies_iff`: Kratzer's independent parameterization → IFF

-/

namespace Semantics.Modality.Typology

open Core.Modality (ModalForce ModalFlavor ForceFlavor)

/-! ## Modal Meaning Projections -/

/-- The set of forces expressed by a modal meaning. -/
def forces (m : List ForceFlavor) : List ModalForce :=
  (m.map (·.force)).eraseDups

/-- The set of flavors expressed by a modal meaning. -/
def flavors (m : List ForceFlavor) : List ModalFlavor :=
  (m.map (·.flavor)).eraseDups

/-! ## Semantic Universals -/

/-- **Independence of Force and Flavor (IFF).**

A modal meaning satisfies IFF iff for any two pairs (fo₁, fl₁) and (fo₂, fl₂)
in the meaning, the pair (fo₁, fl₂) is also in the meaning.
Equivalently: ⟦m⟧ = fo(m) × fl(m) (Cartesian closure).

Alternative formulation: a modal m satisfies IFF just in case ⟦m⟧ = fo(m) × fl(m),
where × is the Cartesian product.

@cite{steinert-threlkeld-imel-guo-2023}. -/
def satisfiesIFF (m : List ForceFlavor) : Bool :=
  m.all fun ⟨fo₁, _⟩ =>
    m.all fun ⟨_, fl₂⟩ =>
      m.any fun ff => ff.force == fo₁ && ff.flavor == fl₂

/-- **Single Axis of Variability (SAV).**

A modal meaning satisfies SAV iff it exhibits variation along at most one axis
of the force-flavor space: either all pairs share the same force, or all pairs
share the same flavor.

[Alternative formulation: |fo(m)| = 1 or |fl(m)| = 1.]

@cite{nauze-2008}. -/
def satisfiesSAV (m : List ForceFlavor) : Bool :=
  m.all (fun ff₁ => m.all (fun ff₂ => ff₁.force == ff₂.force)) ||
  m.all (fun ff₁ => m.all (fun ff₂ => ff₁.flavor == ff₂.flavor))

/-! ## Relationship Between Universals -/

/-- SAV is strictly stronger than IFF: every SAV meaning is IFF.

**Proof sketch**: If all forces are equal to fo₀ (SAV left disjunct), then for any
(fo₁, fl₁) ∈ m and (_, fl₂) ∈ m, fo₁ = fo₀ and the pair (fo₂, fl₂) with
flavor fl₂ already has force fo₀ = fo₁, so (fo₁, fl₂) ∈ m.
Symmetric for the right disjunct. -/
theorem sav_implies_iff (m : List ForceFlavor) (h : satisfiesSAV m = true) :
    satisfiesIFF m = true := by
  unfold satisfiesSAV at h
  unfold satisfiesIFF
  simp only [Bool.or_eq_true] at h
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂
  rcases h with hForce | hFlavor
  · -- All forces equal: fo₁ = fo₂, so witness is (fo₂, fl₂) itself
    have hfo : (fo₂ == fo₁) = true := by
      have h₂₁ := List.all_eq_true.mp (List.all_eq_true.mp hForce ⟨fo₂, fl₂⟩ h₂) ⟨fo₁, fl₁⟩ h₁
      simp only [BEq.beq] at h₂₁ ⊢
      exact h₂₁
    exact ⟨⟨fo₂, fl₂⟩, h₂, hfo, beq_self_eq_true fl₂⟩
  · -- All flavors equal: fl₁ = fl₂, so witness is (fo₁, fl₁) itself
    have hfl : (fl₁ == fl₂) = true := by
      have h₁₂ := List.all_eq_true.mp (List.all_eq_true.mp hFlavor ⟨fo₁, fl₁⟩ h₁) ⟨fo₂, fl₂⟩ h₂
      simp only [BEq.beq] at h₁₂ ⊢
      exact h₁₂
    exact ⟨⟨fo₁, fl₁⟩, h₁, beq_self_eq_true fo₁, hfl⟩

/-- IFF does NOT imply SAV: a meaning can vary on both axes while satisfying IFF.
    E.g., {(nec,e),(nec,d),(poss,e),(poss,d)} is IFF but not SAV. -/
theorem iff_not_implies_sav :
    ∃ m : List ForceFlavor,
      satisfiesIFF m = true ∧ satisfiesSAV m = false := by
  exact ⟨[⟨.necessity, .epistemic⟩, ⟨.necessity, .deontic⟩,
          ⟨.possibility, .epistemic⟩, ⟨.possibility, .deontic⟩],
         by decide, by decide⟩

/-! ## Cartesian Products in the Force-Flavor Space -/

/-- Local abbreviation for the Core infrastructure, for readability. -/
abbrev cartesianProduct := ForceFlavor.cartesianProduct

/-- Membership in a Cartesian product: `⟨fo, fl⟩ ∈ fos × fls` iff `fo ∈ fos ∧ fl ∈ fls`. -/
theorem mem_cartesianProduct (ff : ForceFlavor) (fos : List ModalForce)
    (fls : List ModalFlavor) :
    ff ∈ cartesianProduct fos fls ↔ ff.force ∈ fos ∧ ff.flavor ∈ fls := by
  unfold cartesianProduct ForceFlavor.cartesianProduct
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨fo, hfo, fl, hfl, rfl⟩; exact ⟨hfo, hfl⟩
  · rintro ⟨hfo, hfl⟩; exact ⟨ff.force, hfo, ff.flavor, hfl, rfl⟩

/-- Any Cartesian product of forces and flavors satisfies IFF.

    This is the formal content of @cite{kratzer-1981}'s insight that force
    (quantificational) and flavor (contextual) are **independent** parameters
    in the semantics of modals. -/
theorem cartesianProduct_satisfies_iff
    (fos : List ModalForce) (fls : List ModalFlavor) :
    satisfiesIFF (cartesianProduct fos fls) = true := by
  unfold satisfiesIFF cartesianProduct ForceFlavor.cartesianProduct
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro ⟨fo₁, _⟩ h₁ ⟨_, fl₂⟩ h₂
  simp only [List.mem_flatMap, List.mem_map, ForceFlavor.mk.injEq] at h₁ h₂
  obtain ⟨fo₁', hfo₁, fl₁', _, rfl, _⟩ := h₁
  obtain ⟨fo₂', _, fl₂', hfl₂, _, rfl⟩ := h₂
  exact ⟨⟨fo₁', fl₂'⟩,
         List.mem_flatMap.mpr ⟨fo₁', hfo₁, List.mem_map.mpr ⟨fl₂', hfl₂, rfl⟩⟩,
         beq_self_eq_true fo₁', beq_self_eq_true fl₂'⟩

/-- A Cartesian product with a singleton force axis satisfies SAV.
    Covers fixed-force Kratzer modals (e.g., English "must", "can"). -/
theorem cartesianProduct_singleton_force_satisfies_sav
    (fo : ModalForce) (fls : List ModalFlavor) :
    satisfiesSAV (cartesianProduct [fo] fls) = true := by
  unfold satisfiesSAV
  simp only [Bool.or_eq_true]
  left
  simp only [List.all_eq_true]
  intro ff₁ h₁ ff₂ h₂
  have hfo₁ : ff₁.force = fo :=
    ((mem_cartesianProduct ff₁ [fo] fls).mp h₁).1 |> List.mem_singleton.mp
  have hfo₂ : ff₂.force = fo :=
    ((mem_cartesianProduct ff₂ [fo] fls).mp h₂).1 |> List.mem_singleton.mp
  rw [hfo₁, hfo₂]
  exact beq_self_eq_true fo

/-- A Cartesian product with a singleton flavor axis satisfies SAV.
    Covers variable-force Kratzer modals (e.g., Gitksan ima'a). -/
theorem cartesianProduct_singleton_flavor_satisfies_sav
    (fos : List ModalForce) (fl : ModalFlavor) :
    satisfiesSAV (cartesianProduct fos [fl]) = true := by
  unfold satisfiesSAV
  simp only [Bool.or_eq_true]
  right
  simp only [List.all_eq_true]
  intro ff₁ h₁ ff₂ h₂
  have hfl₁ : ff₁.flavor = fl :=
    ((mem_cartesianProduct ff₁ fos [fl]).mp h₁).2 |> List.mem_singleton.mp
  have hfl₂ : ff₂.flavor = fl :=
    ((mem_cartesianProduct ff₂ fos [fl]).mp h₂).2 |> List.mem_singleton.mp
  rw [hfl₁, hfl₂]
  exact beq_self_eq_true fl

/-- Singleton meanings trivially satisfy IFF. -/
theorem singleton_satisfies_iff (ff : ForceFlavor) :
    satisfiesIFF [ff] = true := by
  unfold satisfiesIFF
  simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    Bool.and_true, Bool.or_false]
  cases ff with | mk fo fl => cases fo <;> cases fl <;> decide

/-- Empty meanings trivially satisfy IFF. -/
theorem empty_satisfies_iff : satisfiesIFF [] = true := by
  unfold satisfiesIFF; simp [List.all_nil]

/-! ## Convexity Characterization

IFF is equivalent to convexity in the grid betweenness relation on the
force-flavor space (@cite{steinert-threlkeld-imel-guo-2023} §4.2).

Betweenness on a 2D grid: (fo_b, fl_b) lies between (fo_a, fl_a) and
(fo_c, fl_c) iff one can reach (fo_b, fl_b) by first changing force,
then flavor (or vice versa) on the path from a to c.

Following @cite{chemla-buccola-dautriche-2019}: a set S is convex iff
for any a, c ∈ S, every point between a and c is also in S. -/

/-- Grid betweenness: `b` lies between `a` and `c` iff each coordinate
    of `b` matches one of the corresponding coordinates of `a` or `c`. -/
def isBetween (b a c : ForceFlavor) : Bool :=
  (b.force == a.force || b.force == c.force) &&
  (b.flavor == a.flavor || b.flavor == c.flavor)

/-- A set of force-flavor pairs is convex iff it is closed under grid
    betweenness: for any two members, all points between them are members. -/
def isConvex (S : List ForceFlavor) : Bool :=
  S.all fun a => S.all fun c =>
    ForceFlavor.universe.all fun b =>
      if isBetween b a c then S.any (· == b) else true

/-- **IFF ≡ Convexity.** A modal meaning satisfies IFF iff it is convex
    in the grid betweenness relation.

    The proof reduces both sides to Cartesian closure: IFF checks that
    every force-flavor recombination is present, while convexity checks
    that every grid-between point is present. On the 2D grid, these
    coincide because the points between (fo₁, fl₁) and (fo₂, fl₂) are
    exactly {fo₁, fo₂} × {fl₁, fl₂}.

    @cite{steinert-threlkeld-imel-guo-2023} §4.2. -/
private theorem bool_ite_true (b x : Bool) :
    (if b then x else true) = true ↔ (b = true → x = true) := by
  cases b <;> simp

private theorem forceFlavor_ext {a b : ForceFlavor}
    (hf : a.force = b.force) (hfl : a.flavor = b.flavor) : a = b := by
  cases a; cases b; simp_all

private theorem mem_universe (ff : ForceFlavor) : ff ∈ ForceFlavor.universe := by
  cases ff with | mk f fl => cases f <;> cases fl <;> decide

set_option maxHeartbeats 800000 in
theorem iff_eq_convex (m : List ForceFlavor) :
    satisfiesIFF m = isConvex m := by
  apply Bool.eq_iff_iff.mpr; constructor
  · -- IFF → Convex: 4-way case split on betweenness coordinates
    intro hIFF
    unfold satisfiesIFF at hIFF
    unfold isConvex
    simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at hIFF
    simp only [List.all_eq_true]
    intro a ha c hc b _
    rw [bool_ite_true]; intro hBet
    unfold isBetween at hBet
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hBet
    obtain ⟨hfo, hfl⟩ := hBet
    rw [List.any_eq_true]
    rcases hfo with hfo | hfo <;> rcases hfl with hfl | hfl
    · -- b.force = a.force, b.flavor = a.flavor: witness is a
      refine ⟨a, ha, ?_⟩
      rw [forceFlavor_ext (eq_of_beq hfo).symm (eq_of_beq hfl).symm]
      exact beq_self_eq_true _
    · -- b.force = a.force, b.flavor = c.flavor: IFF cross-product witness
      obtain ⟨w, hw, hwf, hwfl⟩ := hIFF a ha c hc
      refine ⟨w, hw, ?_⟩
      rw [forceFlavor_ext
        ((eq_of_beq hwf).trans (eq_of_beq hfo).symm)
        ((eq_of_beq hwfl).trans (eq_of_beq hfl).symm)]
      exact beq_self_eq_true _
    · -- b.force = c.force, b.flavor = a.flavor: IFF cross-product witness (reversed)
      obtain ⟨w, hw, hwf, hwfl⟩ := hIFF c hc a ha
      refine ⟨w, hw, ?_⟩
      rw [forceFlavor_ext
        ((eq_of_beq hwf).trans (eq_of_beq hfo).symm)
        ((eq_of_beq hwfl).trans (eq_of_beq hfl).symm)]
      exact beq_self_eq_true _
    · -- b.force = c.force, b.flavor = c.flavor: witness is c
      refine ⟨c, hc, ?_⟩
      rw [forceFlavor_ext (eq_of_beq hfo).symm (eq_of_beq hfl).symm]
      exact beq_self_eq_true _
  · -- Convex → IFF: ⟨fo₁, fl₂⟩ lies between ⟨fo₁, fl₁⟩ and ⟨fo₂, fl₂⟩
    intro hConv
    unfold isConvex at hConv
    unfold satisfiesIFF
    simp only [List.all_eq_true] at hConv
    simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
    intro ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂
    have h := hConv ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂ ⟨fo₁, fl₂⟩ (mem_universe _)
    rw [bool_ite_true] at h
    have hBet : isBetween ⟨fo₁, fl₂⟩ ⟨fo₁, fl₁⟩ ⟨fo₂, fl₂⟩ = true := by
      unfold isBetween; simp
    obtain ⟨w, hw, hweq⟩ := List.any_eq_true.mp (h hBet)
    have heq := eq_of_beq hweq
    subst heq
    exact ⟨⟨fo₁, fl₂⟩, hw, beq_self_eq_true _, beq_self_eq_true _⟩

/-- **Path-connectedness** — a weaker alternative to IFF/convexity.

    A set S is path-connected iff for any two members, *some* point
    between them is also in S. Equivalently: replace the "and" in IFF
    with "or" — if (fo₁, fl₁) and (fo₂, fl₂) ∈ S, then (fo₁, fl₂)
    or (fo₂, fl₁) ∈ S.

    Strictly weaker than IFF. @cite{steinert-threlkeld-imel-guo-2023} §4.2,
    footnote 17. -/
def satisfiesPathConnected (m : List ForceFlavor) : Bool :=
  m.all fun ⟨fo₁, fl₁⟩ =>
    m.all fun ⟨fo₂, fl₂⟩ =>
      m.any (fun ff => ff.force == fo₁ && ff.flavor == fl₂) ||
      m.any (fun ff => ff.force == fo₂ && ff.flavor == fl₁)

/-- IFF implies path-connectedness: if all between-points are present,
    certainly some are. -/
theorem iff_implies_pathConnected (m : List ForceFlavor)
    (h : satisfiesIFF m = true) :
    satisfiesPathConnected m = true := by
  unfold satisfiesIFF at h
  unfold satisfiesPathConnected
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
             Bool.or_eq_true] at h ⊢
  intro ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂
  exact Or.inl (h ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂)

/-- Path-connectedness does NOT imply IFF.
    Table 1(b) in @cite{steinert-threlkeld-imel-guo-2023}:
    {(◇,e),(◇,d),(◇,c),(□,d),(□,c)} is path-connected but not IFF
    (missing (□,e)). -/
theorem pathConnected_not_implies_iff :
    ∃ m : List ForceFlavor,
      satisfiesPathConnected m = true ∧ satisfiesIFF m = false := by
  exact ⟨[⟨.possibility, .epistemic⟩, ⟨.possibility, .deontic⟩,
          ⟨.possibility, .circumstantial⟩, ⟨.necessity, .deontic⟩,
          ⟨.necessity, .circumstantial⟩],
         by decide, by decide⟩

/-! ## Force Pattern (derived from meaning)

`ForcePattern` captures the observable force structure of a modal meaning:
how many distinct forces appear, and whether there is a single flavor.
This is derivable from the `List ForceFlavor` without theoretical
stipulation. The per-fragment `ForceAnalysis` (which distinguishes
`variableForce` from `strengthened`) adds an explanatory layer on top.

`ForceAnalysis.isConsistentWith` verifies that the stipulated analysis
is compatible with the observed pattern. -/

/-- The observable force structure of a modal meaning. -/
inductive ForcePattern where
  /-- Meaning is empty. -/
  | empty
  /-- Single force value (possibly across multiple flavors). -/
  | singleForce (f : ModalForce)
  /-- Multiple distinct force values. -/
  | multiForce
  deriving DecidableEq, Repr

/-- Derive the force pattern from a modal meaning. -/
def inferForcePattern (m : List ForceFlavor) : ForcePattern :=
  match forces m with
  | [] => .empty
  | [f] => .singleForce f
  | _ => .multiForce

open Core.Modality (ForceAnalysis)

/-- A `ForceAnalysis` is consistent with the observed `ForcePattern` when:
    - `fixed fo` requires `singleForce fo` (only one force attested)
    - `variableForce` requires `multiForce` (both forces attested)
    - `strengthened fo` requires `singleForce fo` (base semantics has one force;
      strengthened readings are pragmatic and not encoded in the meaning) -/
def ForceAnalysis.isConsistentWith : ForceAnalysis → ForcePattern → Bool
  | .fixed fo, .singleForce fo' => fo == fo'
  | .variableForce, .multiForce => true
  | .strengthened fo, .singleForce fo' => fo == fo'
  | _, .empty => true  -- vacuously consistent
  | _, _ => false

/-! ## Language-Level Measures -/

/-- A modal expression datum: a form paired with its meaning in the 3×3 space. -/
structure ModalExpression where
  form : String
  meaning : List ForceFlavor
  deriving Repr, BEq

/-- Project to the shared modal item core. Register defaults to neutral
    since typological surveys don't annotate register. -/
def ModalExpression.toModalItem (e : ModalExpression) : Core.Modality.ModalItem where
  form := e.form
  meaning := e.meaning

/-- A language's modal inventory. -/
structure ModalInventory where
  language : String
  family : String
  source : String
  expressions : List ModalExpression
  deriving Repr

/-- Whether all modals in a language satisfy IFF. -/
def ModalInventory.allIFF (inv : ModalInventory) : Bool :=
  inv.expressions.all fun e => satisfiesIFF e.meaning

/-- Number of IFF-satisfying modals in a language. -/
def ModalInventory.iffCount (inv : ModalInventory) : Nat :=
  (inv.expressions.filter fun e => satisfiesIFF e.meaning).length

/-- Total number of modals in a language. -/
def ModalInventory.size (inv : ModalInventory) : Nat :=
  inv.expressions.length

/-- IFF degree: fraction of modals satisfying IFF (as a rational).
    This is the paper's "naturalness" measure. -/
def ModalInventory.iffDegreeNum (inv : ModalInventory) : Nat × Nat :=
  (inv.iffCount, inv.size)

/-- Whether a language has any synonymous modals (same meaning, different form). -/
def ModalInventory.hasSynonymy (inv : ModalInventory) : Bool :=
  inv.expressions.any fun e₁ =>
    inv.expressions.any fun e₂ =>
      e₁.form != e₂.form && e₁.meaning == e₂.meaning

/-! ## Fragment Integration -/

/-- Construct a modal inventory from fragment auxiliary entries.
    Filters to entries with non-empty modal meanings. -/
def ModalInventory.fromAuxEntries {α : Type}
    (language family source : String) (entries : List α)
    (form : α → String) (meaning : α → List ForceFlavor) : ModalInventory where
  language := language
  family := family
  source := source
  expressions := entries.filterMap fun e =>
    let m := meaning e
    if m.isEmpty then none else some ⟨form e, m⟩

/-! ## Kratzer-Typology Bridge

Connects Kratzer's parameterized modal semantics (conversational backgrounds,
ordering sources) to the typological force-flavor space. A Kratzerian modal
with fixed force and contextually variable flavors produces a meaning
`cartesianProduct [force] flavors`, which satisfies both IFF and SAV.
Variable-force modals (e.g., Gitksan ima'a) produce
`cartesianProduct forces [flavor]`, also satisfying both. -/

open Semantics.Modality.Kratzer (KratzerParams)

/-- A flavor assignment maps each typological `ModalFlavor` to a
    Kratzer parameterization (modal base + ordering source). -/
structure FlavorAssignment where
  assign : ModalFlavor → KratzerParams

/-- Canonical assignment from the standard Kratzer flavor structures. -/
def canonicalAssignment
    (epist : Semantics.Modality.Kratzer.EpistemicFlavor)
    (deont : Semantics.Modality.Kratzer.DeonticFlavor)
    (boul : Semantics.Modality.Kratzer.BouleticFlavor)
    (teleo : Semantics.Modality.Kratzer.TeleologicalFlavor) :
    FlavorAssignment where
  assign
    | .epistemic => epist.toKratzerParams
    | .deontic => deont.toKratzerParams
    | .bouletic => boul.toKratzerParams
    | .circumstantial => teleo.toKratzerParams

/-! ## Bridge: ModalItem.decomposition ↔ satisfiesIFF

`ModalItem.decomposition` (Core/ModalLogic.lean) and `satisfiesIFF` (this file)
compute the same property through different algorithms:
- `decomposition` projects forces/flavors, builds the Cartesian product, checks containment
- `satisfiesIFF` checks the closure property directly on the meaning list

Both reduce to: ∀ fo ∈ forces(m), ∀ fl ∈ flavors(m), ⟨fo, fl⟩ ∈ m. -/

open Core.Modality (ModalItem ModalDecomposition)

/-- `eraseDups` preserves list membership.
    Required because Lean 4 core lacks this lemma for `BEq`-based `eraseDups`. -/
private theorem mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α] {a : α} :
    ∀ (l : List α), a ∈ l.eraseDups ↔ a ∈ l
  | [] => by constructor <;> simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  | hd :: tl => by
    rw [List.eraseDups_cons, List.mem_cons, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · left; rfl
      · right
        have h' := (mem_eraseDups (tl.filter (fun b => !(b == hd)))).mp h
        exact (List.mem_filter.mp h').1
    · rintro (rfl | h)
      · left; rfl
      · by_cases heq : (a == hd) = true
        · left; exact eq_of_beq heq
        · right
          exact (mem_eraseDups (tl.filter (fun b => !(b == hd)))).mpr
            (List.mem_filter.mpr ⟨h, by simp [heq]⟩)
termination_by l => l.length
decreasing_by all_goals simp +arith; exact List.length_filter_le _ _

/-- The Cartesian-product containment check used by `ModalItem.decomposition`
    computes the same Boolean as `satisfiesIFF`. Both reduce to: every
    combination of attested forces and attested flavors is itself attested. -/
private theorem cart_all_eq_satisfiesIFF (S : List ForceFlavor) :
    (ForceFlavor.cartesianProduct
      ((S.map ForceFlavor.force).eraseDups)
      ((S.map ForceFlavor.flavor).eraseDups)).all (S.contains ·) =
    satisfiesIFF S := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · -- Forward: all cart elements contained → satisfiesIFF
    intro hAll
    show satisfiesIFF S = true
    unfold satisfiesIFF
    simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
    intro ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂
    have hfo₁ : fo₁ ∈ (S.map ForceFlavor.force).eraseDups :=
      (mem_eraseDups _).mpr (List.mem_map.mpr ⟨⟨fo₁, fl₁⟩, h₁, rfl⟩)
    have hfl₂ : fl₂ ∈ (S.map ForceFlavor.flavor).eraseDups :=
      (mem_eraseDups _).mpr (List.mem_map.mpr ⟨⟨fo₂, fl₂⟩, h₂, rfl⟩)
    have hInCart := (mem_cartesianProduct ⟨fo₁, fl₂⟩
        ((S.map ForceFlavor.force).eraseDups)
        ((S.map ForceFlavor.flavor).eraseDups)).mpr ⟨hfo₁, hfl₂⟩
    have hContains := List.all_eq_true.mp hAll ⟨fo₁, fl₂⟩ hInCart
    have hmem : ⟨fo₁, fl₂⟩ ∈ S := by
      have ⟨a', ha', hbeq⟩ := List.contains_iff_exists_mem_beq.mp hContains
      exact eq_of_beq hbeq ▸ ha'
    exact ⟨⟨fo₁, fl₂⟩, hmem, beq_self_eq_true fo₁, beq_self_eq_true fl₂⟩
  · -- Backward: satisfiesIFF → all cart elements contained
    intro hIFF
    unfold satisfiesIFF at hIFF
    rw [List.all_eq_true]
    intro pair hInCart
    have ⟨hfo, hfl⟩ := (mem_cartesianProduct pair _ _).mp hInCart
    have hfo' := (mem_eraseDups _).mp hfo
    have hfl' := (mem_eraseDups _).mp hfl
    rw [List.mem_map] at hfo' hfl'
    obtain ⟨⟨fo_w, fl_w⟩, hw_fo_mem, hw_fo_eq⟩ := hfo'
    obtain ⟨⟨fo_v, fl_v⟩, hw_fl_mem, hw_fl_eq⟩ := hfl'
    simp at hw_fo_eq hw_fl_eq
    have h₁ := List.all_eq_true.mp hIFF ⟨fo_w, fl_w⟩ hw_fo_mem
    have h₂ := List.all_eq_true.mp h₁ ⟨fo_v, fl_v⟩ hw_fl_mem
    rw [hw_fo_eq, hw_fl_eq] at h₂
    rw [List.any_eq_true] at h₂
    obtain ⟨witness, hw_mem, hw_eq⟩ := h₂
    rw [Bool.and_eq_true] at hw_eq
    have ⟨hf_beq, hfl_beq⟩ := hw_eq
    have hmem_pair : pair ∈ S := by
      have heq : witness = pair := by
        cases witness with | mk wf wfl =>
        cases pair with | mk pf pfl =>
        simp at hf_beq hfl_beq
        exact congr_arg₂ ForceFlavor.mk hf_beq hfl_beq
      rw [← heq]; exact hw_mem
    exact List.contains_iff_exists_mem_beq.mpr ⟨pair, hmem_pair, beq_self_eq_true pair⟩

set_option maxHeartbeats 400000 in
/-- `ModalItem.decomposition` agrees with `satisfiesIFF`:
    a modal is decomposable iff its meaning satisfies IFF.

    Both sides reduce to checking that `m.meaning` is closed under
    force-flavor recombination:
    - Forward: if the Cartesian product of projected forces/flavors
      is contained in `m.meaning`, then for any two pairs `(fo₁, fl₁)`
      and `(fo₂, fl₂)` in `m.meaning`, `(fo₁, fl₂)` is in the product
      (since `fo₁ ∈ forces` and `fl₂ ∈ flavors`), hence in `m.meaning`.
    - Backward: if IFF holds, take any `(fo, fl)` in the Cartesian product.
      Then `fo ∈ forces` means `∃ (fo, fl₁) ∈ m.meaning`, and
      `fl ∈ flavors` means `∃ (fo₂, fl) ∈ m.meaning`.
      By IFF closure, `(fo, fl) ∈ m.meaning`. -/
theorem decomposition_eq_satisfiesIFF (m : ModalItem) :
    (m.decomposition == .decomposable) = satisfiesIFF m.meaning := by
  unfold ModalItem.decomposition
  simp only [cart_all_eq_satisfiesIFF]
  generalize satisfiesIFF m.meaning = b
  cases b <;> decide

/-! ## Corollaries: Decomposability via the Bridge

The equivalence `decomposition_eq_satisfiesIFF` transfers results freely between
the Core structural classifier (`ModalItem.decomposition`) and the typological
universal (`satisfiesIFF`). The following corollaries make this transfer explicit. -/

/-- Any Kratzer modal — whose meaning is a Cartesian product of forces and
    flavors — is decomposable. Follows from @cite{kratzer-1981}'s independent
    parameterization: `cartesianProduct_satisfies_iff` + bridge. -/
theorem cartesianProduct_decomposable
    (form : String) (fos : List ModalForce) (fls : List ModalFlavor) :
    ({ form, meaning := cartesianProduct fos fls } : ModalItem).decomposition
      == .decomposable := by
  rw [decomposition_eq_satisfiesIFF]
  exact cartesianProduct_satisfies_iff fos fls

/-- SAV modals are decomposable: if a modal varies on at most one axis,
    it is decomposable. Follows from `sav_implies_iff` + bridge. -/
theorem sav_implies_decomposable (m : ModalItem)
    (h : satisfiesSAV m.meaning = true) :
    (m.decomposition == .decomposable) = true := by
  rw [decomposition_eq_satisfiesIFF]
  exact sav_implies_iff m.meaning h

/-- Singleton meanings are decomposable, derived from the IFF universal
    rather than finite case analysis. -/
theorem singleton_decomposable (form : String) (ff : ForceFlavor) :
    ({ form, meaning := [ff] } : ModalItem).decomposition
      == .decomposable := by
  rw [decomposition_eq_satisfiesIFF]
  exact singleton_satisfies_iff ff

/-- Empty meanings are decomposable. -/
theorem empty_decomposable (form : String) :
    ({ form, meaning := [] } : ModalItem).decomposition
      == .decomposable := by
  rw [decomposition_eq_satisfiesIFF]
  exact empty_satisfies_iff

/-- A modal is unitary iff its meaning fails IFF. The contrapositive of
    `decomposition_eq_satisfiesIFF`. -/
theorem unitary_iff_not_iff (m : ModalItem) :
    m.isUnitary = !satisfiesIFF m.meaning := by
  unfold ModalItem.isUnitary
  have h := decomposition_eq_satisfiesIFF m
  have : ∀ d : ModalDecomposition, (d == .unitary) = !(d == .decomposable) := by
    intro d; cases d <;> decide
  rw [this, h]

/-- `ModalInventory.allIFF` is equivalent to checking that every expression
    is decomposable. Connects the typological survey predicate to the
    Kratzer-theoretic structural classifier. -/
theorem allIFF_eq_all_decomposable (inv : ModalInventory) :
    inv.allIFF = inv.expressions.all
      fun e => (e.toModalItem.decomposition == .decomposable) := by
  unfold ModalInventory.allIFF
  congr 1; ext e
  exact (decomposition_eq_satisfiesIFF e.toModalItem).symm

end Semantics.Modality.Typology
