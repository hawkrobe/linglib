import Mathlib.Data.Fintype.Powerset
import Linglib.Semantics.Mereology
import Linglib.Semantics.Plurality.MassCount

/-!
# Sutton and Filip (2021): The Count/Mass Distinction for Granular Nouns

This file formalizes [sutton-filip-2021]'s account of the lexical count/mass distinction and
its answer to the accessibility puzzle: *rice* denotes stuff made of perceptually salient
grains, yet *three rices* cannot mean three grains of rice while it can mean three bowls of
rice. A basic predicate is a frame with an extension and, when the concept has perceptually
or functionally identified units, a unit field (28)–(29), `Frame`; the object identifying
function returns the unit field where there is one and the predicate itself otherwise (30),
`Frame.objects`; a specific individuation schema selects a maximally disjoint subset of the
objects, a perspective, and the null schema unions all perspectives (32), the substrate's
`Mereology.IsMaxDisjointIn` and `Mereology.nullSchema`. A lexical entry is tripartite (33):
the basic predicate, a counting base built from it by the object function and a schema, and
an extension that is the counting base or its closure under sum, `Entry`, `Entry.cbase`,
`Entry.extn`. Grammatical counting is defined over disjoint counting bases only (A1), so an
entry is count exactly when its base is disjoint, `Entry.IsCount`. The features `[±O]` and
`[±S]` record whether the entry applies the object function and whether it carries a specific
schema, `Entry.features`. Every `[+S]` entry is count, `Entry.isCount_of_perspective`, and
since the null schema is the identity, `Mereology.nullSchema_eq`, a `[−S]` entry is count
exactly when the predicate its schema applies to is disjoint, `Entry.isCount_iff_of_null`.
Table 9.1 follows: prototypical objects and count granulars are `[+O,+S]` and count, mass
granulars and substances `[−O,−S]` and mass because the basic predicate overlaps, collective
artifacts `[+O,−S]` and mass because their functional units overlap, and Finnish *huonekalut*
is *furniture* with the null schema replaced by the schema of utterance, `huonekalut`.

A frame of units and their sums (29) overlaps as soon as it has two units, whether or not the
units do, `overlapPred_extn_ofUnits`; so the `[−O,−S]` entry for *rice* or Czech *čočka* is
mass while the `[+O,+S]` entry for *lentil* over a frame of the same kind is count,
`rice_mass`, `lentil_count`: the grains are in the basic predicate and inaccessible to
counting. The unit extracting classifier *grain of* inserts the object function and the
schema of utterance into the counting base (49)–(50), `unitShift`, and its result is count
for every entry whatever, `isCount_unitShift`; that is the generalized `[−O,−S]` to
`[+O,+S]` shift a language with a lexicalized distinction cannot license implicitly (9.5.4).
A container classifier instead counts by the receptacle's own base and leaves the argument's
individuation untouched (43)–(44), `containerExtn`, under the precondition that the argument's
extension is cumulative (45), which sum-closed extensions meet and singular count extensions
with two units fail, `cum_extn_of_sumClosed`, `not_cum_extn_of_singular`. The furniture and
rice models on subsets of three atoms witness both halves of the puzzle,
`furniture_two_perspectives`, `rice_accessibility`.

## Implementation notes

A specific schema is a function from predicates to perspectives in the paper; an entry here
records the perspective the schema of utterance selects on the predicate it applies to, with
its maximality, since only that value enters the counting base. Overlap is the substrate's
`Mereology.Overlap`, a shared non-null part. The cardinality comparisons licensed by `[+O]`,
the perceptual content of frames, the composition with verbs of Appendix B, and the notional
classes of Table 9.1 are not formalized.

## References

* [sutton-filip-2021]
* [landman-2011]
* [landman-2016]
* [krifka-1989]
-/

namespace SuttonFilip2021

open Mereology

section Entries

variable {α : Type*}

/-- A basic predicate frame (28)–(29): its extension and, when the concept has perceptually or
functionally identified units, its unit field. -/
structure Frame (α : Type*) where
  extn : Set α
  unit : Option (Set α)

/-- The object identifying function (30): the unit field where there is one, the predicate
itself otherwise. -/
def Frame.objects (F : Frame α) : Set α := F.unit.getD F.extn

/-- A substance frame: no unit field. -/
def Frame.substance (stuff : Set α) : Frame α := ⟨stuff, none⟩

@[simp] theorem Frame.objects_substance (stuff : Set α) : (substance stuff).objects = stuff :=
  rfl

variable [SemilatticeSup α]

/-- A frame whose extension is its units and their sums, the unit and collection fields of
(28)–(29): granular for disjoint units, a collective artifact for overlapping ones. -/
def Frame.ofUnits (units : Set α) : Frame α := ⟨{x | AlgClosure (· ∈ units) x}, some units⟩

@[simp] theorem Frame.objects_ofUnits (units : Set α) : (ofUnits units).objects = units := rfl

/-- A lexical entry (33): the basic predicate; whether the counting base applies the object
identifying function, `[±O]`; whether the extension is closed under sum, the `(*)` of (33);
and the perspective the schema of utterance selects, `[+S]`, or none for the null schema,
`[−S]`. -/
structure Entry (α : Type*) [SemilatticeSup α] where
  frame : Frame α
  objectFn : Bool
  sumClosed : Bool
  perspective : Option (Set α)
  perspective_max : ∀ D, perspective = some D →
    IsMaxDisjointIn Overlap D (if objectFn then frame.objects else frame.extn)

namespace Entry

variable (E : Entry α)

/-- The predicate the schema applies to: the objects under `[+O]`, the basic predicate under
`[−O]`. -/
def base : Set α := if E.objectFn then E.frame.objects else E.frame.extn

/-- The counting base: the perspective under a specific schema, the null schema otherwise. -/
def cbase : Set α := E.perspective.getD (nullSchema Overlap E.base)

/-- The extension: the counting base, closed under sum when the entry is. -/
def extn : Set α := if E.sumClosed then {x | AlgClosure (· ∈ E.cbase) x} else E.cbase

/-- Grammatical counting (A1) is defined over disjoint counting bases only: an entry is count
when its base is disjoint. -/
def IsCount : Prop := DisjointPred Overlap E.cbase

/-- The features `[±O]` and `[±S]`. -/
def features : Bool × Bool := (E.objectFn, E.perspective.isSome)

open scoped Classical in
/-- The morphosyntactic outcome of the categorization. -/
noncomputable def massCount : MassCount := if E.IsCount then .count else .mass

variable {E}

/-- A `[+S]` entry is count: its perspective is disjoint. -/
theorem isCount_of_perspective {D : Set α} (h : E.perspective = some D) : E.IsCount := by
  rw [IsCount, cbase, h, Option.getD_some]
  exact (E.perspective_max D h).2.1

/-- Under the null schema the counting base is the predicate the schema applies to. -/
theorem cbase_of_null (h : E.perspective = none) : E.cbase = E.base := by
  rw [cbase, h, Option.getD_none, nullSchema_eq]

/-- A `[−S]` entry is count exactly when the predicate its schema applies to is disjoint. -/
theorem isCount_iff_of_null (h : E.perspective = none) :
    E.IsCount ↔ DisjointPred Overlap E.base := by
  rw [IsCount, cbase_of_null h]

theorem massCount_eq_mass_iff : E.massCount = .mass ↔ ¬ E.IsCount := by
  unfold massCount; split_ifs <;> simp [*]

variable (E)

/-- The substitution of the null schema by the schema of utterance, `⟦furniture⟧^{𝒮₀ ↦ 𝒮ᵢ}`. -/
def withPerspective (D : Set α) (h : IsMaxDisjointIn Overlap D E.base) : Entry α :=
  { E with perspective := some D, perspective_max := λ _ hD => Option.some_inj.1 hD ▸ h }

theorem withPerspective_isCount (D : Set α) (h : IsMaxDisjointIn Overlap D E.base) :
    (E.withPerspective D h).IsCount :=
  isCount_of_perspective rfl

end Entry

/-! ### Unit extracting and container classifiers -/

/-- The unit extracting classifier (49): the object identifying function and the schema of
utterance inserted into the counting base of any entry, the extension closed under sum. -/
def unitShift (E : Entry α) (D : Set α) (h : IsMaxDisjointIn Overlap D E.frame.objects) :
    Entry α :=
  ⟨E.frame, true, true, some D, λ _ hD => Option.some_inj.1 hD ▸ h⟩

/-- The unit shift is the generalized `[−O,−S]` to `[+O,+S]` shift (9.5.4). -/
theorem features_unitShift (E : Entry α) (D : Set α)
    (h : IsMaxDisjointIn Overlap D E.frame.objects) :
    (unitShift E D h).features = (true, true) := rfl

/-- The unit shift makes every entry count. -/
theorem isCount_unitShift (E : Entry α) (D : Set α)
    (h : IsMaxDisjointIn Overlap D E.frame.objects) : (unitShift E D h).IsCount :=
  Entry.isCount_of_perspective rfl

/-- The extension of the container reading (44): sums of counted receptacles, each of which
contains something in the argument's extension; counting proceeds by the receptacle's
counting base, which the argument does not touch. -/
def containerExtn (R P : Entry α) (contain : α → α → Prop) : Set α :=
  {x | AlgClosure (· ∈ R.cbase) x ∧ ∀ z ∈ R.cbase, z ≤ x → ∃ v ∈ P.extn, contain z v}

/-- The precondition (45) of the container classifier: the argument's extension is
cumulative, which every sum-closed extension is. -/
theorem cum_extn_of_sumClosed {E : Entry α} (h : E.sumClosed = true) : CUM (· ∈ E.extn) := by
  simp only [Entry.extn, h, ite_true]
  exact algClosure_cum

/-- A singular count extension with two distinct units is not cumulative: the sum of two units
is not a unit, so *#a bowl of an apple*. -/
theorem not_cum_extn_of_singular {E : Entry α} (hs : E.sumClosed = false) (hc : E.IsCount)
    {u v : α} (hu : u ∈ E.cbase) (hv : v ∈ E.cbase) (hne : u ≠ v) (hu0 : ¬ IsBot u)
    (hv0 : ¬ IsBot v) : ¬ CUM (· ∈ E.extn) := by
  simp only [Entry.extn, hs, Bool.false_eq_true, ite_false]
  intro hcum
  have hsum : u ⊔ v ∈ E.cbase := hcum hu hv
  by_cases huv : u ⊔ v = u
  · exact hc ⟨u, hu, v, hv, hne, v, hv0, sup_eq_left.1 huv, le_rfl⟩
  · exact hc ⟨u, hu, u ⊔ v, hsum, Ne.symm huv, u, hu0, le_rfl, le_sup_left⟩

/-! ### Granular frames -/

/-- A frame of units and their sums overlaps as soon as it has two distinct non-null units:
a unit and its sum with another share the unit. -/
theorem overlapPred_extn_ofUnits {units : Set α} {u v : α} (hu : u ∈ units) (hv : v ∈ units)
    (hne : u ≠ v) (hu0 : ¬ IsBot u) (hv0 : ¬ IsBot v) :
    OverlapPred Overlap (Frame.ofUnits units).extn := by
  by_cases huv : u ⊔ v = u
  · exact ⟨u, .base hu, v, .base hv, hne, v, hv0, sup_eq_left.1 huv, le_rfl⟩
  · exact ⟨u, .base hu, u ⊔ v, .sum (.base hu) (.base hv), Ne.symm huv, u, hu0, le_rfl,
      le_sup_left⟩

/-- A `[−O,−S]` entry over a frame of units and their sums with two distinct non-null units is
mass: the grains of *rice* and *čočka* are in the basic predicate, not in the counting base. -/
theorem rice_mass {units : Set α} {u v : α} (hu : u ∈ units) (hv : v ∈ units) (hne : u ≠ v)
    (hu0 : ¬ IsBot u) (hv0 : ¬ IsBot v) (E : Entry α) (hF : E.frame = Frame.ofUnits units)
    (hO : E.objectFn = false) (hS : E.perspective = none) : ¬ E.IsCount := by
  rw [Entry.isCount_iff_of_null hS]
  simp only [Entry.base, hO, Bool.false_eq_true, ite_false, hF]
  exact λ h => h (overlapPred_extn_ofUnits hu hv hne hu0 hv0)

/-- The `[+O,+S]` entry over a frame of disjoint units, *lentil* (36)–(37): the perspective
is the units themselves. -/
def lentil (units : Set α) (hd : DisjointPred Overlap units) (sumClosed : Bool) : Entry α :=
  ⟨Frame.ofUnits units, true, sumClosed, some units,
    λ _ hD => Option.some_inj.1 hD ▸ isMaxDisjointIn_self _ hd⟩

/-- *lentil* is count, with the units as its counting base. -/
theorem lentil_count {units : Set α} (hd : DisjointPred Overlap units) (sumClosed : Bool) :
    (lentil units hd sumClosed).IsCount ∧ (lentil units hd sumClosed).cbase = units :=
  ⟨Entry.isCount_of_perspective rfl, rfl⟩

end Entries

/-! ### Furniture and rice on three atoms -/

section Model

/-- Parts are subsets of three atoms; overlap is a shared non-empty part. -/
abbrev Part := Finset (Fin 3)

instance : DecidableRel (Overlap (α := Part)) := λ s t =>
  decidable_of_iff (¬ Disjoint s t) overlap_iff_not_disjoint.symm

instance {a : Part} {P : Set Part} [DecidablePred (· ∈ P)] : DecidablePred (· ∈ insert a P) :=
  λ x => decidable_of_iff (x = a ∨ x ∈ P) (by simp [Set.mem_insert_iff])

instance {P : Set Part} [DecidablePred (· ∈ P)] : Decidable (OverlapPred Overlap P) := by
  unfold OverlapPred; infer_instance

instance {P : Set Part} [DecidablePred (· ∈ P)] : Decidable (DisjointPred Overlap P) :=
  decidable_of_iff (¬ OverlapPred Overlap P) Iff.rfl

instance {P Q : Set Part} [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Q)] : Decidable (P ⊆ Q) :=
  decidable_of_iff (∀ x, x ∈ P → x ∈ Q) Iff.rfl

instance {D P : Set Part} [DecidablePred (· ∈ D)] [DecidablePred (· ∈ P)] :
    Decidable (IsMaxDisjointIn Overlap D P) :=
  decidable_of_iff
    ((∀ x, x ∈ D → x ∈ P) ∧ DisjointPred Overlap D ∧
      ∀ x, x ∈ P → x ∉ D → OverlapPred Overlap (insert x D)) Iff.rfl

/-- The functional units of *furniture*: a table, a mirror, and the vanity they compose. -/
def furnitureUnits : Set Part := {s | s = {0} ∨ s = {1} ∨ s = {0, 1}}

instance : DecidablePred (· ∈ furnitureUnits) := λ s =>
  decidable_of_iff (s = {0} ∨ s = {1} ∨ s = {0, 1}) Iff.rfl

/-- The piece perspective: count the table and the mirror. -/
def piecePerspective : Set Part := {s | s = {0} ∨ s = {1}}

instance : DecidablePred (· ∈ piecePerspective) := λ s =>
  decidable_of_iff (s = {0} ∨ s = {1}) Iff.rfl

/-- The vanity perspective: count the composed unit. -/
def vanityPerspective : Set Part := {s | s = {0, 1}}

instance : DecidablePred (· ∈ vanityPerspective) := λ s => decidable_of_iff (s = {0, 1}) Iff.rfl

/-- *furniture* (40): `[+O,−S]` over the functional units and their sums. -/
def furniture : Entry Part :=
  ⟨Frame.ofUnits furnitureUnits, true, true, none, λ _ h => by simp at h⟩

/-- The functional units overlap, so *furniture* is mass although its units are identified. -/
theorem furniture_mass : ¬ furniture.IsCount := by
  rw [Entry.isCount_iff_of_null rfl]
  show ¬ DisjointPred Overlap furnitureUnits
  exact λ h => h (by decide)

/-- Two perspectives on the furniture units, the pieces and the vanity, are both maximal and
differ, which is why the null schema's base overlaps. -/
theorem furniture_two_perspectives :
    IsMaxDisjointIn Overlap piecePerspective furnitureUnits ∧
      IsMaxDisjointIn Overlap vanityPerspective furnitureUnits ∧
      piecePerspective ≠ vanityPerspective ∧ OverlapPred Overlap furniture.cbase := by
  refine ⟨by decide, by decide, λ h => ?_, ?_⟩
  · have h0 : ({0} : Part) ∈ vanityPerspective := by rw [← h]; exact Or.inl rfl
    exact absurd h0 (by decide)
  · rw [Entry.cbase_of_null rfl]
    show OverlapPred Overlap furnitureUnits
    decide

/-- *huonekalut* (41): *furniture* with the null schema replaced by the piece perspective, and
count. -/
def huonekalut : Entry Part :=
  furniture.withPerspective piecePerspective
    (by show IsMaxDisjointIn Overlap piecePerspective furnitureUnits; decide)

theorem huonekalut_count : huonekalut.IsCount := furniture.withPerspective_isCount _ _

/-- The grains of *rice*: the atoms. -/
def riceGrains : Set Part := {s | s = {0} ∨ s = {1} ∨ s = {2}}

instance : DecidablePred (· ∈ riceGrains) := λ s =>
  decidable_of_iff (s = {0} ∨ s = {1} ∨ s = {2}) Iff.rfl

/-- *rice* (38): `[−O,−S]` over the grains and their sums. -/
def rice : Entry Part := ⟨Frame.ofUnits riceGrains, false, true, none, λ _ h => by simp at h⟩

theorem riceGrains_disjoint : DisjointPred Overlap riceGrains := by decide

/-- The accessibility puzzle, both halves ((Q2), 9.5.3): the grains are disjoint and in the
basic predicate, yet *rice* is mass; *grains of rice* (50) is the *lentil* entry over the same
frame, count with the grains as its counting base. -/
theorem rice_accessibility :
    riceGrains ⊆ rice.frame.extn ∧ ¬ rice.IsCount ∧
      unitShift rice riceGrains (isMaxDisjointIn_self _ riceGrains_disjoint) =
        lentil riceGrains riceGrains_disjoint true ∧
      (lentil riceGrains riceGrains_disjoint true).IsCount ∧
      (lentil riceGrains riceGrains_disjoint true).cbase = riceGrains :=
  ⟨λ _ h => .base h,
    rice_mass (α := Part) (u := {0}) (v := {1}) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
      (by decide) (by decide) rice rfl rfl rfl,
    rfl, (lentil_count _ _).1, (lentil_count _ _).2⟩

/-- *mud* (39): `[−O,−S]` over the parts of some mud, which overlap. -/
def mud : Entry Part := ⟨Frame.substance {s | s.Nonempty}, false, true, none, λ _ h => by simp at h⟩

theorem mud_mass : ¬ mud.IsCount := by
  rw [Entry.isCount_iff_of_null rfl]
  show ¬ DisjointPred Overlap {s : Part | s.Nonempty}
  exact λ h => h ⟨{0}, by decide, {0, 1}, by decide, by decide, {0}, by decide, le_rfl, by decide⟩

end Model

end SuttonFilip2021
