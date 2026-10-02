module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Semantics.Plurality.Number
public import Linglib.Studies.Corbett2000

/-!
# Harbour (2014): Paucity, Abundance, and the Theory of Number

Harbour characterizes the approximative numbers, paucal and greater plural, by a feature
`[±additive]` of additive closure, beside the `[±atomic]` and `[±minimal]` that give the exact
numbers. Each feature acts on a lattice of atoms and their sums, and the same two parameters
govern all three: whether a feature is active on Number⁰ (22) and whether its two values may
cooccur (23). A sociosemantic convention fixes the height of the cut `[±additive]` induces (14).
A parameter setting generates a number system, the feature bundles with nonempty denotation, and
the typology of Table 3 and the implications of Table 1 are claims about these systems.

## Main definitions

* `Setting`, `Bundle`, `Convention`: parameter settings, feature bundles, and the placement of
  the cuts.
* `Setting.system`: the number system a setting generates.
* `PlusAdditive`: the `[+additive]` elements of a region cut horizontally.

## Main results

* `atomize_nonMinimalOf_iterate`: the successor-like function (31).
* `not_additiveIn_band`, `additiveIn_firstPerson_iff`: below a cut no element of the
  third-person lattice is `[+additive]`, and on the first-person lattice only the speaker is.
* `not_ordConnected_plusAdditive_firstPerson`: `{±additive}` alone cuts the first-person lattice
  nonconvexly, against the convexity condition (32).
* `table3_generated`: the systems of Table 3, with Corbett's records of its example languages.
* `wellFormed_toSystem_iff`: Table 1 holds of every legitimate setting but
  `{±additive(*), ±minimal*}`, two lacunae whose unit augmented has no augmented.
* `meleFila_system`, `meleFila_classes`: Mele-Fila's plural is `[+additive]` relative to the
  lower cut and `[−additive]` relative to the upper, sharing a form with each neighbour (Table 4).

## Implementation notes

* A bundle is a `Finset` of signed features, so the axiom of extension (27) is built in, and it
  is interpreted in the order (28); its cell is its denotation less the more specific bundles',
  as the plural of Figure 7 is `Q+ \ Q′`.
* The typology is computed on the strata of the third-person lattice over thirteen atoms, the
  cardinalities to which `card` carries the operators; low cuts sit at six and eight atoms, high
  ones at ten and twelve, and the labels (p. 201) follow Table 3 and its note b.

## TODO

* Banyun's greater and greatest plurals (Table 3, (18)) have no `Number` value, (24) omitting the
  greatest plural; the first-person `[+additive]` singular of n. 23 is outside the typology.
* The typology holds in one model; stating it for every lattice and every placement of the cuts
  needs the action of the features on strata symbolically, with the join of strata `k` and `m`
  ranging over `[max k m, k + m]`.

## References

* [harbour-2014]
* [corbett-2000]
* [gardenfors-2004]
-/

@[expose] public section

namespace Harbour2014

open Mereology
open Number (additiveIn atomsOf nonAtomsOf nonMinimalOf)

/-! ### Features act through cardinality (§2, (12)) -/

section Card

variable {α : Type*}

/-- On the strata `ℕ` the atom is `1`. -/
theorem atom_iff_eq_one {k : ℕ} : Atom k ↔ k = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h0 : k ≠ 0 := fun h0 ↦ h.1 (h0 ▸ isBot_bot)
    have := h.2 (y := 1) (by simp [isBot_iff_eq_bot]) (by omega)
    omega
  · rintro rfl
    exact ⟨by simp [isBot_iff_eq_bot], fun y hy _ ↦ by
      have : y ≠ 0 := fun h0 ↦ hy (h0 ▸ isBot_bot); omega⟩

instance : DecidablePred (Atom : ℕ → Prop) := fun _ ↦ decidable_of_iff _ atom_iff_eq_one.symm

instance (R : Finset ℕ) : DecidablePred (Minimal (· ∈ R)) := fun k ↦
  decidable_of_iff (k ∈ R ∧ ∀ j ∈ R, j ≤ k → k ≤ j) Iff.rfl

/-- `card` carries minimality in a union of strata to minimality among the strata. -/
theorem minimal_comp_card {S : ℕ → Prop} {s : Finset α} :
    Minimal (S ∘ Finset.card) s ↔ Minimal S s.card := by
  refine ⟨fun h ↦ ⟨h.1, fun j hj hle ↦ ?_⟩, fun h ↦ ⟨h.1, fun t ht hts ↦ ?_⟩⟩
  · obtain ⟨t, hts, rfl⟩ := Finset.exists_subset_card_eq hle
    exact Finset.card_le_card (h.2 hj hts)
  · exact (Finset.eq_of_subset_of_card_le hts (h.2 ht (Finset.card_le_card hts))).ge

/-- The atoms of the powerset lattice are the sets of one atom. -/
theorem atom_iff_card {s : Finset α} : Atom s ↔ Atom s.card := by
  have : (fun t : Finset α ↦ ¬ IsBot t) = (fun k : ℕ ↦ ¬ IsBot k) ∘ Finset.card := by
    ext t; simp [isBot_iff_eq_bot]
  simp only [Atom, this, minimal_comp_card]

variable {S : ℕ → Prop}

theorem atomize_comp_card : atomize (S ∘ Finset.card) = atomize S ∘ Finset.card (α := α) := by
  ext t; exact minimal_comp_card

variable [DecidableEq α]

theorem atomsOf_comp_card : atomsOf (S ∘ Finset.card) = atomsOf S ∘ Finset.card (α := α) := by
  ext t; simp [atomsOf, atom_iff_card]

theorem nonAtomsOf_comp_card :
    nonAtomsOf (S ∘ Finset.card) = nonAtomsOf S ∘ Finset.card (α := α) := by
  ext t; simp [nonAtomsOf, atom_iff_card]

theorem nonMinimalOf_comp_card :
    nonMinimalOf (S ∘ Finset.card) = nonMinimalOf S ∘ Finset.card (α := α) := by
  ext t; simp [nonMinimalOf, atomize_comp_card]

end Card

/-! ### The successor-like function (§4.4) -/

section Successor

variable {α : Type*} [DecidableEq α]

private theorem atomize_le (k : ℕ) : atomize (k ≤ ·) = (· = k) := by
  ext j
  exact ⟨fun h ↦ le_antisymm (h.2 le_rfl h.1) h.1, by rintro rfl; exact ⟨le_rfl, fun _ h _ ↦ h⟩⟩

private theorem nonMinimalOf_iterate (n : ℕ) : nonMinimalOf^[n] (2 ≤ ·) = (n + 2 ≤ ·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext j; simp only [nonMinimalOf, atomize_le]; omega

private theorem nonMinimalOf_iterate_comp_card (n : ℕ) (S : ℕ → Prop) :
    nonMinimalOf^[n] (S ∘ Finset.card) = nonMinimalOf^[n] S ∘ Finset.card (α := α) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      nonMinimalOf_comp_card]

/-- `(+minimal(−minimalⁿ(−atomic(P))))` holds of exactly the sums of `n + 2` atoms, the
successor-like function (31); `n = 0` gives the dual of (30) and `n = 1` the trial. -/
theorem atomize_nonMinimalOf_iterate (n : ℕ) (s : Finset α) :
    atomize (nonMinimalOf^[n] (nonAtomsOf Finset.Nonempty)) s ↔ s.card = n + 2 := by
  have hP : (Finset.Nonempty : Finset α → Prop) = (1 ≤ ·) ∘ Finset.card := by
    ext t; simp [Finset.one_le_card]
  have hna : nonAtomsOf (1 ≤ ·) = (2 ≤ ·) := by
    ext j; simp only [nonAtomsOf, atom_iff_eq_one]; omega
  rw [hP, nonAtomsOf_comp_card, hna, nonMinimalOf_iterate_comp_card, nonMinimalOf_iterate,
    atomize_comp_card, atomize_le]
  rfl

/-- `(+minimal(+atomic(P)))` holds of exactly the atoms, the singular of (30). -/
theorem atomize_atomsOf (s : Finset α) :
    atomize (atomsOf Finset.Nonempty) s ↔ s.card = 1 := by
  have hP : (Finset.Nonempty : Finset α → Prop) = (1 ≤ ·) ∘ Finset.card := by
    ext t; simp [Finset.one_le_card]
  have ha : atomsOf (1 ≤ ·) = ((· = 1) : ℕ → Prop) := by
    ext j; simp only [atomsOf, atom_iff_eq_one]; omega
  rw [hP, atomsOf_comp_card, ha, atomize_comp_card]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ hj _ ↦ hj ▸ h.le⟩⟩

end Successor

/-! ### Orders of composition (§§3.3, 4.1, 4.3) -/

section Orders

variable {D : Type*} [SemilatticeSup D]

/-- `(αatomic(ᾱatomic(P)))` is empty, so `[±atomic]*` adds nothing (§4.1, n. 15). -/
theorem not_atomsOf_nonAtomsOf (P : D → Prop) (x : D) : ¬ atomsOf (nonAtomsOf P) x :=
  fun h ↦ h.1.2 h.2

/-- `(+atomic(−minimal(P)))` is empty when `P` excludes the null individual, since an atom of `P`
is minimal in it (§4.3). -/
theorem not_atomsOf_nonMinimalOf {P : D → Prop} (hP : ∀ y, P y → ¬ IsBot y) (x : D) :
    ¬ atomsOf (nonMinimalOf P) x :=
  fun h ↦ h.1.2 (Number.singular_subset_minimal hP ⟨h.1.1, h.2⟩)

end Orders

/-! ### `[±additive]` and horizontal cuts (§3.1) -/

section Additive

variable {α : Type*} [DecidableEq α]

/-- A band holds of the sums of at least `lo` and fewer than `hi` atoms. -/
def Band (lo hi : ℕ) (s : Finset α) : Prop := lo ≤ s.card ∧ s.card < hi

/-- No element of a band above the null individual is additive in it, given infinitely many
atoms, since two of its elements can always sum past its upper bound. So the bounded region below
a cut of the third-person lattice is `[−additive]` throughout (10), and
`(+additive(−additive(P)))` is unsatisfiable (§3.3). -/
theorem not_additiveIn_band [Infinite α] {lo hi : ℕ} (hlo : 1 ≤ lo) (s : Finset α) :
    ¬ additiveIn (Band lo hi) s := by
  rintro ⟨⟨hl, hh⟩, h⟩
  obtain ⟨u, hsu, hu⟩ :=
    Infinite.exists_superset_card_eq s (s.card + max lo (hi - s.card)) (by omega)
  have hcard : (u \ s).card = max lo (hi - s.card) := by
    rw [Finset.card_sdiff_of_subset hsu, hu]; omega
  have := (h (u \ s) ⟨by omega, by omega⟩).2
  rw [Finset.sup_eq_union, Finset.union_sdiff_of_subset hsu, hu] at this
  omega

/-- Every element above a cut is additive in the region above it (10), whose complement below
the cut is thereby complement-complete (11). -/
theorem additiveIn_le_card {c : ℕ} {s : Finset α} (hs : c ≤ s.card) :
    additiveIn (c ≤ ·.card) s :=
  ⟨hs, fun _ _ ↦ hs.trans (Finset.card_le_card Finset.subset_union_left)⟩

/-- Likewise an element above a cut that contains a given atom is additive among such elements. -/
theorem additiveIn_le_card' {i : α} {c : ℕ} {s : Finset α} (hi : i ∈ s) (hs : c ≤ s.card) :
    additiveIn (fun t ↦ i ∈ t ∧ c ≤ t.card) s :=
  ⟨⟨hi, hs⟩, fun _ _ ↦ ⟨Finset.mem_union_left _ hi,
    hs.trans (Finset.card_le_card Finset.subset_union_left)⟩⟩

end Additive

/-! ### Convexity (§4.5) -/

section Convexity

variable {α : Type*} [DecidableEq α]

/-- An element of a region `P` cut at `c` is `[+additive]` (10) when it is additive in the bounded
region below the cut or in the unbounded region above it. -/
def PlusAdditive (c : ℕ) (P : Finset α → Prop) (s : Finset α) : Prop :=
  additiveIn (fun t ↦ P t ∧ t.card < c) s ∨ additiveIn (fun t ↦ P t ∧ c ≤ t.card) s

/-- On the third-person lattice, with infinitely many atoms, the `[+additive]` elements are those
above the cut. -/
theorem plusAdditive_nonempty_iff [Infinite α] {c : ℕ} (hc : 1 ≤ c) (s : Finset α) :
    PlusAdditive c Finset.Nonempty s ↔ c ≤ s.card := by
  have hb : (fun t : Finset α ↦ t.Nonempty ∧ t.card < c) = Band 1 c := by
    ext t; simp [Band, Finset.one_le_card]
  have ha : (fun t : Finset α ↦ t.Nonempty ∧ c ≤ t.card) = (c ≤ ·.card) := by
    ext t; exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.card_pos.mp (by omega), h⟩⟩
  rw [PlusAdditive, hb, ha]
  exact ⟨fun h ↦ h.elim (fun h ↦ (not_additiveIn_band le_rfl s h).elim) (·.1),
    fun h ↦ .inr (additiveIn_le_card h)⟩

/-- So `{±additive}` cuts the third-person lattice convexly (33), into paucal and plural. -/
theorem ordConnected_plusAdditive_nonempty [Infinite α] {c : ℕ} (hc : 1 ≤ c) :
    {s : Finset α | PlusAdditive c Finset.Nonempty s}.OrdConnected := by
  simp only [plusAdditive_nonempty_iff hc]
  exact IsUpperSet.ordConnected fun _ _ hst h ↦ h.trans (Finset.card_le_card hst)

/-- On the first-person exclusive lattice, the sums containing the speaker `i`, the speaker atom
is the only element additive below a cut (Figure 8), being the lattice's bottom. -/
theorem additiveIn_firstPerson_iff [Infinite α] {i : α} {c : ℕ} (hc : 2 ≤ c) (s : Finset α) :
    additiveIn (fun t ↦ i ∈ t ∧ t.card < c) s ↔ s = {i} := by
  refine ⟨fun ⟨⟨hi, hlt⟩, h⟩ ↦ ?_, ?_⟩
  · by_contra hne
    have h2 : 2 ≤ s.card := by
      by_contra h2
      exact hne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun x hx ↦
        Finset.card_le_one.mp (by omega) x hx i hi⟩)
    obtain ⟨u, hsu, hu⟩ := Infinite.exists_superset_card_eq s c hlt.le
    have hiu : i ∉ u \ s := fun h ↦ (Finset.mem_sdiff.mp h).2 hi
    have := (h (insert i (u \ s)) ⟨Finset.mem_insert_self i _, by
      rw [Finset.card_insert_of_notMem hiu, Finset.card_sdiff_of_subset hsu]; omega⟩).2
    rw [Finset.sup_eq_union, Finset.union_insert, Finset.union_sdiff_of_subset hsu,
      Finset.insert_eq_of_mem (hsu hi), hu] at this
    omega
  · rintro rfl
    refine ⟨⟨Finset.mem_singleton_self i, by simp; omega⟩, fun t ht ↦ ?_⟩
    rwa [Finset.sup_eq_union, Finset.singleton_union, Finset.insert_eq_of_mem ht.1]

/-- So `{±additive}` cuts the first-person lattice nonconvexly, a `[−additive]` paucal lying
between the `[+additive]` speaker and a `[+additive]` plural (p. 212), and by the convexity
condition (32), after [gardenfors-2004], `[±additive]` is never a language's sole number
feature. -/
theorem not_ordConnected_plusAdditive_firstPerson [Infinite α] (i : α) {c : ℕ} (hc : 3 ≤ c) :
    ¬ {s | PlusAdditive c (i ∈ ·) s}.OrdConnected := by
  intro h
  obtain ⟨o, ho⟩ := exists_ne i
  obtain ⟨u, hu, huc⟩ := Infinite.exists_superset_card_eq {i, o} c
    (by rw [Finset.card_pair ho.symm]; omega)
  have hmid := h.out (x := {i}) (y := u)
    (.inl ((additiveIn_firstPerson_iff (by omega) _).mpr rfl))
    (.inr (additiveIn_le_card' (hu (by simp)) huc.ge))
    ⟨Finset.singleton_subset_iff.mpr (by simp), hu⟩
  rcases hmid with hl | hr
  · have := congrArg Finset.card ((additiveIn_firstPerson_iff (by omega) _).mp hl)
    rw [Finset.card_pair ho.symm, Finset.card_singleton] at this
    omega
  · have := hr.1.2
    rw [Finset.card_pair ho.symm] at this
    omega

end Convexity

/-! ### Parameters and the typology (§§4.2, 5.1) -/

/-- Harbour's number features are `[±atomic]`, `[±minimal]` and `[±additive]`. -/
inductive Feature where
  | atomic
  | minimal
  | additive
  deriving DecidableEq, Fintype, Repr

/-- A feature on Number⁰ is inactive, active (22), or recursive, its two values allowed to
cooccur (23), written `[±F]*`. -/
inductive Activation where
  | inactive
  | active
  | recursive
  deriving DecidableEq, Fintype, Repr

/-- Under an activation a bundle carries no value of `[±F]`, one, or under recursion both, and no
more by the axiom of extension (27). -/
def Activation.signs : Activation → List (Finset Bool)
  | .inactive => [∅]
  | .active => [{true}, {false}]
  | .recursive => [{true}, {false}, {true, false}]

/-- A parameter setting fixes the activation of each feature. -/
structure Setting where
  /-- The activation of `[±atomic]`. -/
  atomic : Activation
  /-- The activation of `[±minimal]`. -/
  minimal : Activation
  /-- The activation of `[±additive]`. -/
  additive : Activation
  deriving DecidableEq, Fintype, Repr

/-- A feature bundle is the set of its signed features, `(F, true)` standing for `+F` (§2.3). -/
abbrev Bundle := Finset (Feature × Bool)

namespace Setting

/-- A bundle of a setting values every active feature once and a recursive one once or twice. -/
def bundles (σ : Setting) : List Bundle := do
  let a ← σ.atomic.signs
  let m ← σ.minimal.signs
  let d ← σ.additive.signs
  pure (a.image (.atomic, ·) ∪ m.image (.minimal, ·) ∪ d.image (.additive, ·))

/-- A setting is legitimate unless `[±additive]` is its sole feature, which the convexity
condition (32) rules out (§4.5, `not_ordConnected_plusAdditive_firstPerson`). -/
def Legitimate (σ : Setting) : Prop :=
  σ.additive ≠ .inactive → σ.atomic ≠ .inactive ∨ σ.minimal ≠ .inactive

instance (σ : Setting) : Decidable σ.Legitimate := by unfold Legitimate; infer_instance

end Setting

/-- A conventionalized cut (14) is low, bounding paucals, or high, bounding greater plurals. -/
inductive Height where
  | low
  | high
  deriving DecidableEq, Fintype, Repr

/-- The sociosemantic convention (14) places no cut without `[±additive]`, one cut with it, and
under recursion a low cut and a second cut above it (§3.3). Two high cuts, Banyun's greater and
greatest plurals, are left out. -/
inductive Convention where
  | none
  | one (h : Height)
  | two (h : Height)
  deriving DecidableEq, Fintype, Repr

namespace Convention

/-- A convention fits an activation of `[±additive]` when it has as many cuts. -/
def Fits : Convention → Activation → Prop
  | .none, .inactive | .one _, .active | .two _, .recursive => True
  | _, _ => False

instance : ∀ c a, Decidable (Fits c a)
  | .none, .inactive | .one _, .active | .two _, .recursive => isTrue trivial
  | .none, .active | .none, .recursive | .one _, .inactive | .one _, .recursive
  | .two _, .inactive | .two _, .active => isFalse id

/-- The lower cut lies at six atoms, or at ten for a single high cut. -/
def lower : Convention → ℕ
  | .one .high => 10
  | _ => 6

/-- The upper cut lies at eight atoms for a second low cut and at twelve for a second high one. -/
def upper : Convention → ℕ
  | .two .low => 8
  | .two .high => 12
  | c => c.lower

end Convention

/-- The strata of the third-person lattice over thirteen atoms (Figure 3) are one to thirteen. -/
def strata : Finset ℕ := Finset.Icc 1 13

/-- A bundle denotes the strata its features select, composed in the order (28). -/
def Bundle.denote (c : Convention) (b : Bundle) : Finset ℕ :=
  let R := if (.atomic, false) ∈ b then strata.filter (nonAtomsOf (· ∈ strata)) else strata
  let R := if (.atomic, true) ∈ b then R.filter (atomsOf (· ∈ R)) else R
  let R := if (.minimal, false) ∈ b then R.filter (nonMinimalOf (· ∈ R)) else R
  let R := if (.minimal, true) ∈ b then R.filter (atomize (· ∈ R)) else R
  let R := if (.additive, true) ∈ b then R.filter (c.lower ≤ ·) else R
  if (.additive, false) ∈ b then
    R.filter (· < if (.additive, true) ∈ b then c.upper else c.lower)
  else R

/-- The cell of a bundle in a setting is its denotation less those of the more specific bundles,
as the plural of Figure 7 is `Q+ \ Q′`. -/
def Setting.cell (σ : Setting) (c : Convention) (b : Bundle) : Finset ℕ :=
  b.denote c \ (σ.bundles.filter (b ⊂ ·)).foldr (fun b' R ↦ b'.denote c ∪ R) ∅

/-- A bundle is labelled with the descriptive name of its number (p. 201), after Table 3. -/
def Bundle.label (c : Convention) (b : Bundle) : Number :=
  if (.atomic, true) ∈ b then .singular
  else if (.minimal, true) ∈ b then
    if (.minimal, false) ∈ b then (if (.atomic, false) ∈ b then .trial else .unitAugmented)
    else if (.atomic, false) ∈ b then .dual else .minimal
  else if (.additive, false) ∈ b then
    if (.additive, true) ∈ b then (if c = .two .low then .greaterPaucal else .plural)
    else if c = .one .high then .plural else .paucal
  else if (.additive, true) ∈ b then
    (if c = .one .high ∨ c = .two .high then .greaterPlural else .plural)
  else if (.minimal, false) ∈ b ∧ (.atomic, false) ∉ b then .augmented
  else if b = ∅ then .general else .plural

namespace Setting

/-- The number system of a setting consists of its bundles with nonempty cells. -/
def system (σ : Setting) (c : Convention) : List Bundle :=
  σ.bundles.filter fun b ↦ (σ.cell c b).Nonempty

/-- The values of a setting's system are its bundles' labels. -/
def values (σ : Setting) (c : Convention) : List Number := (σ.system c).map (Bundle.label c)

/-- A setting's system as a `Number.System` sets general number apart. -/
def toSystem (σ : Setting) (c : Convention) : Number.System where
  name := ""
  values := (σ.values c).filter (· ≠ .general)
  hasGeneral := decide (.general ∈ σ.values c)

end Setting

/-- The cells of every system cover the lattice. -/
theorem exists_mem_cell : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    ∀ k ∈ strata, ∃ b ∈ σ.bundles, k ∈ σ.cell c b := by
  decide +kernel

/-- The cells of a system are disjoint, so the system partitions the lattice. -/
theorem disjoint_cell : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    ∀ b ∈ σ.system c, ∀ b' ∈ σ.system c, b ≠ b' → Disjoint (σ.cell c b) (σ.cell c b') := by
  decide +kernel

/-- Distinct numbers of a system have distinct labels. -/
theorem nodup_values : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    (σ.values c).Nodup := by
  decide +kernel

/-- `[±atomic]*` adds no number to `[±atomic]` (§4.1). -/
theorem values_atomic_recursive : ∀ m d : Activation, ∀ c : Convention,
    (Setting.mk .recursive m d).values c = (Setting.mk .active m d).values c := by
  decide +kernel

/-- The axiom of extension caps the exact numbers, the cells of a single stratum, at the trial
and unit augmented, three atoms on this lattice (§4.2). -/
theorem le_three_of_card_cell_eq_one : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    ∀ b ∈ σ.system c, (σ.cell c b).card = 1 → ∀ k ∈ σ.cell c b, k ≤ 3 := by
  decide +kernel

/-- (26)'s quadral `[+minimal −minimal −minimal −atomic]` is the trial bundle. -/
example : ({(.minimal, true), (.minimal, false), (.minimal, false), (.atomic, false)} : Bundle) =
    {(.minimal, true), (.minimal, false), (.atomic, false)} := by
  decide

/-- A system has at most two approximative numbers (p. 205). -/
theorem length_approximative_le_two : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    ((σ.values c).filter (· ∈ [.paucal, .greaterPaucal, .greaterPlural])).length ≤ 2 := by
  decide +kernel

/-- No system has more than six numbers. -/
theorem length_values_le_six : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    (σ.values c).length ≤ 6 := by
  decide +kernel

/-- Every legitimate setting satisfies the implicational universals of Table 1 except
`{±additive(*), ±minimal*}`, two lacunae of Table 3 whose unit augmented has no augmented. -/
theorem wellFormed_toSystem_iff : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    σ.Legitimate → ((σ.toSystem c).WellFormed ↔
      ¬ (σ.atomic = .inactive ∧ σ.minimal = .recursive ∧ σ.additive ≠ .inactive)) := by
  decide +kernel

instance (l : List Number) : Decidable (IsLowerSet {v | v ∈ l}) :=
  decidable_of_iff (∀ v ∈ l, ∀ u : Number, u ≤ v → u ∈ l)
    ⟨fun h _ _ huv hv ↦ h _ hv _ huv, fun h _ hv _ huv ↦ h huv hv⟩

/-- The same settings generate lower sets of the markedness order of `Number`. -/
theorem isLowerSet_values_iff : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    σ.Legitimate → (IsLowerSet {v | v ∈ σ.values c} ↔
      ¬ (σ.atomic = .inactive ∧ σ.minimal = .recursive ∧ σ.additive ≠ .inactive)) := by
  decide +kernel

/-- Table 3 pairs each setting and convention with the system of its example language, as
[corbett-2000] records it where it does, or of a lacuna; Banyun's row is left out. -/
def table3 : List (Setting × Convention × List Number) :=
  [(⟨.inactive, .inactive, .inactive⟩, .none, Corbett2000.piraha.values),
   (⟨.active, .inactive, .inactive⟩, .none, [.singular, .plural]),  -- Svan
   (⟨.inactive, .active, .inactive⟩, .none, [.minimal, .augmented]),  -- Winnebago
   (⟨.inactive, .recursive, .inactive⟩, .none, Corbett2000.rembarrnga.values),
   (⟨.active, .active, .inactive⟩, .none, [.singular, .dual, .plural]),  -- Kiowa
   (⟨.active, .inactive, .active⟩, .one .low, Corbett2000.bayso.values),
   (⟨.active, .inactive, .active⟩, .one .high, [.singular, .plural, .greaterPlural]),  -- Fula
   (⟨.inactive, .active, .active⟩, .one .low, [.minimal, .paucal, .plural]),  -- Mebengokre
   (⟨.active, .recursive, .inactive⟩, .none, Corbett2000.larike.values),
   (⟨.inactive, .recursive, .active⟩, .one .low, [.minimal, .unitAugmented, .paucal, .plural]),
   (⟨.inactive, .active, .recursive⟩, .two .low, [.minimal, .paucal, .greaterPaucal, .plural]),
   (⟨.inactive, .recursive, .recursive⟩, .two .low,
     [.minimal, .unitAugmented, .paucal, .greaterPaucal, .plural]),
   (⟨.active, .active, .active⟩, .one .low, Corbett2000.yimas.values),
   (⟨.active, .active, .active⟩, .one .high, Corbett2000.mokilese.values),
   (⟨.active, .recursive, .active⟩, .one .low, Corbett2000.marshallese.values),
   (⟨.active, .active, .recursive⟩, .two .low, Corbett2000.sursurunga.values),
   (⟨.active, .active, .recursive⟩, .two .high, Corbett2000.meleFila.values),
   (⟨.active, .recursive, .recursive⟩, .two .low,
     [.singular, .dual, .trial, .paucal, .greaterPaucal, .plural])]

/-- Every row of Table 3 is generated. -/
theorem table3_generated : ∀ r ∈ table3, (r.1.toSystem r.2.1).values.Perm r.2.2 := by
  decide +kernel

/-! ### Composed number (§5.2) -/

/-- In the singular–dual–paucal–plural system of Yimas and Motuna the paucal shares `[−additive]`
with the dual and `[−minimal]` with the plural, so Motuna composes it from a dual–paucal and a
paucal–plural morpheme ((38)–(40)) and Yimas marks it by `[−additive]` on a `[−minimal]` form
((44)–(45)). -/
theorem yimas_system :
    (((⟨.active, .active, .active⟩ : Setting).system (.one .low)).map
      fun b ↦ (b.label (.one .low), b)).Perm
    [(.singular, {(.atomic, true), (.minimal, true), (.additive, false)}),
     (.dual, {(.atomic, false), (.minimal, true), (.additive, false)}),
     (.paucal, {(.atomic, false), (.minimal, false), (.additive, false)}),
     (.plural, {(.atomic, false), (.minimal, false), (.additive, true)})] := by
  decide +kernel

/-- Mele-Fila's setting is `{±additive*, ±minimal, ±atomic}`, with a low and a high cut. -/
abbrev meleFila : Setting := ⟨.active, .active, .recursive⟩

/-- Mele-Fila's five numbers have the bundles of Table 4, the plural carrying both values of
`[±additive]`. -/
theorem meleFila_system :
    ((meleFila.system (.two .high)).map fun b ↦ (b.label (.two .high), b)).Perm
    [(.singular, {(.atomic, true), (.minimal, true), (.additive, false)}),
     (.dual, {(.atomic, false), (.minimal, true), (.additive, false)}),
     (.paucal, {(.atomic, false), (.minimal, false), (.additive, false)}),
     (.plural, {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)}),
     (.greaterPlural, {(.atomic, false), (.minimal, false), (.additive, true)})] := by
  decide +kernel

/-- The plural lies between the two cuts, `[+additive]` relative to the lower and `[−additive]`
relative to the upper. -/
theorem meleFila_cell_plural : meleFila.cell (.two .high)
    {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)} =
      Finset.Ico 6 12 := by
  decide +kernel

/-- So the plural belongs to two natural classes (Table 4), `[+additive]` with the greater plural,
realized by the article *a*, and `[−minimal −additive]` with the paucal, realized by the pronoun
*raateu*. -/
theorem meleFila_classes :
    (((meleFila.system (.two .high)).filter ((.additive, true) ∈ ·)).map
        (Bundle.label (.two .high))).Perm [.plural, .greaterPlural] ∧
      (((meleFila.system (.two .high)).filter
        fun b ↦ (.minimal, false) ∈ b ∧ (.additive, false) ∈ b).map
          (Bundle.label (.two .high))).Perm [.paucal, .plural] := by
  decide +kernel

end Harbour2014

end
