/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Collapse

/-!
# Local autosegmental configurations

The named building blocks of autosegmental representations. `AR.junction as bs` links
every melody node of `as` to every timing slot of `bs`; its planar specializations —
`single`, `bare`, `float`, `contour`, `spread` — are the local configurations of
autosegmental tonology, and `concat`-products of them build every representation in the
current tone studies (`Studies/Jardine2016Tone`, `Studies/Jardine2017`,
`Studies/Jardine2019`). Building through them (rather than raw structure literals)
carries the in-bounds proof at arbitrary alphabets, where the studies' `by decide`
cannot go, and gives every configuration a simp kit.

The keystone is `isPlanar_junction_iff`: a junction is planar iff one side has at most
one node, so among complete many-to-many associations the No-Crossing Constraint
([goldsmith-1976]) admits exactly the one-to-many (`spread`), many-to-one (`contour`)
and degenerate configurations. (Formaliser's synthesis: the literature treats the NCC
as a filter on representations, not as a characterisation of local generators.)

`concat` is the coproduct, so builder products reach exactly the block-diagonal link
relations; connected shared-node configurations (e.g. a spread-fed contour, H→μ₁ with
L→μ₁μ₂) are planar but not products. TODO: a gluing operation dual to `concat`
(identify a shared boundary slot) reaching them, with the completeness target *every
planar AR is a concat/glue expression over the builders*; at that point `junction`
becomes primary and the five kits derive from its (the
`SimpleGraph.completeBipartiteGraph` move).

## Main definitions

* `AR.junction` — complete many-to-many association of a melody onto a slot sequence.
* `AR.single`, `AR.bare`, `AR.float`, `AR.contour`, `AR.spread` — the planar local
  configurations: one-to-one, toneless slot, floating autosegment ([leben-1973]; the
  tier-with-floats object is `Floating.lean`), several nodes on one slot, one node over
  several slots.

## Main results

* `AR.isPlanar_junction_iff` — NCC-planarity of a junction: one side is at most a
  singleton.
* `AR.linearize_junction` — every slot of a junction carries the whole melody.
* Per-builder simp kits: tier projections (at the `LabeledTuple` level, so `.len`,
  `.toList`, `.get?` follow from the `ofList` kit), reduced link sets, linearization,
  planarity, and OCP-cleanliness.
-/

namespace Autosegmental

variable {α β : Type*} {a : α} {b : β} {as : List α} {bs : List β}

namespace AR

/-! ### The complete many-to-many association -/

/-- Complete many-to-many association: melody nodes `as`, timing slots `bs`, every node
linked to every slot. Planar only in the one-sided cases (`isPlanar_junction_iff`),
which carry the linguistic names below. -/
def junction (as : List α) (bs : List β) : AR α β :=
  ⟨⟨.ofList as, .ofList bs, Finset.range as.length ×ˢ Finset.range bs.length⟩, by
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact hp⟩

@[simp] theorem junction_upper : (junction as bs).upper = .ofList as := rfl

@[simp] theorem junction_lower : (junction as bs).lower = .ofList bs := rfl

theorem junction_links :
    (junction as bs).links = Finset.range as.length ×ˢ Finset.range bs.length := rfl

@[simp] theorem mem_links_junction {p : ℕ × ℕ} :
    p ∈ (junction as bs).links ↔ p.1 < as.length ∧ p.2 < bs.length := by
  rw [junction_links, Finset.mem_product, Finset.mem_range, Finset.mem_range]

/-- **The No-Crossing Constraint selects the one-sided junctions**: a complete
many-to-many association is planar iff one side has at most one node — the one-to-many
`spread`, the many-to-one `contour`, and their degenerate cases. Any 2×2 junction
contains the crossing pair `(0,1)`, `(1,0)`. -/
theorem isPlanar_junction_iff :
    (junction as bs).toGraph.IsPlanar ↔ as.length ≤ 1 ∨ bs.length ≤ 1 := by
  rw [Graph.IsPlanar, show (junction as bs).toGraph.links
      = Finset.range as.length ×ˢ Finset.range bs.length from rfl, isNonCrossing_iff]
  constructor
  · intro h
    by_contra hc
    have h01 := h (0, 1) (by rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; omega)
      (1, 0) (by rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; omega)
      (by norm_num)
    simp at h01
  · rintro (h | h) l₁ h₁ l₂ h₂ hlt <;>
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h₁ h₂ <;> omega

private theorem _root_.List.filterMap_getElem?_range {γ : Type*} (l : List γ) :
    (List.range l.length).filterMap (fun i => l[i]?) = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append,
      List.filterMap_congr (g := fun i => l[i]?) (fun i hi =>
        List.getElem?_append_left (by simpa using hi)), ih]
    simp

theorem junction_linkedLabels {j : ℕ} (hj : j < bs.length) :
    (junction as bs).toGraph.linkedLabels j = as := by
  unfold Graph.linkedLabels
  rw [show (junction as bs).toGraph.upper = LabeledTuple.ofList as from rfl,
    LabeledTuple.ofList_len,
    List.filter_eq_self.mpr (fun i hi => by
      rw [show (junction as bs).toGraph.links
          = Finset.range as.length ×ˢ Finset.range bs.length from rfl]
      simp only [Finset.mem_product, Finset.mem_range, decide_eq_true_eq]
      exact ⟨by simpa using hi, hj⟩)]
  exact List.filterMap_congr (fun i _ => LabeledTuple.ofList_get? as i) |>.trans
    (List.filterMap_getElem?_range as)

/-- Every slot of a junction carries the whole melody. -/
theorem linearize_junction : (junction as bs).linearize = bs.map fun b => (b, as) := by
  refine List.ext_getElem? fun j => ?_
  rw [AR.linearize_getElem?, List.getElem?_map,
    show (junction as bs).lower = LabeledTuple.ofList bs from rfl,
    LabeledTuple.ofList_get?]
  cases hj : bs[j]? with
  | none => rfl
  | some b =>
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    rw [Option.map_some, Option.map_some, junction_linkedLabels hlt]

theorem isCleanAR_junction [DecidableEq α] :
    IsCleanAR (junction as bs) ↔ OCP.IsClean as := by
  unfold IsCleanAR
  rw [junction_upper, LabeledTuple.toList_ofList]

/-! ### The planar local configurations -/

/-- One melody node linked to one timing slot. -/
def single (a : α) (b : β) : AR α β := junction [a] [b]

/-- A bare (unassociated) timing slot. -/
def bare (b : β) : AR α β := junction [] [b]

/-- A floating melody node: on the tier, linked to nothing ([leben-1973]). -/
def float (a : α) : AR α β := junction [a] []

/-- A contour: several melody nodes sharing one timing slot. -/
def contour (as : List α) (b : β) : AR α β := junction as [b]

/-- A spread: one melody node linked across several timing slots. -/
def spread (a : α) (bs : List β) : AR α β := junction [a] bs

/-! #### Tier projections -/

@[simp] theorem single_upper : (single a b).upper = .ofList [a] := rfl
@[simp] theorem single_lower : (single a b).lower = .ofList [b] := rfl
@[simp] theorem bare_upper : (bare b : AR α β).upper = .ofList [] := rfl
@[simp] theorem bare_lower : (bare b : AR α β).lower = .ofList [b] := rfl
@[simp] theorem float_upper : (float a : AR α β).upper = .ofList [a] := rfl
@[simp] theorem float_lower : (float a : AR α β).lower = .ofList [] := rfl
@[simp] theorem contour_upper : (contour as b).upper = .ofList as := rfl
@[simp] theorem contour_lower : (contour as b).lower = .ofList [b] := rfl
@[simp] theorem spread_upper : (spread a bs).upper = .ofList [a] := rfl
@[simp] theorem spread_lower : (spread a bs).lower = .ofList bs := rfl

/-! #### Link sets -/

@[simp] theorem single_links : (single a b).links = {(0, 0)} := by
  rw [single, junction_links, List.length_singleton, List.length_singleton]; decide

@[simp] theorem bare_links : (bare b : AR α β).links = ∅ := by
  rw [bare, junction_links, List.length_nil, List.length_singleton]; decide

@[simp] theorem float_links : (float a : AR α β).links = ∅ := by
  rw [float, junction_links, List.length_singleton, List.length_nil]; decide

@[simp] theorem contour_links :
    (contour as b).links = Finset.range as.length ×ˢ {0} := by
  rw [contour, junction_links, List.length_singleton, Finset.range_one]

@[simp] theorem spread_links :
    (spread a bs).links = {0} ×ˢ Finset.range bs.length := by
  rw [spread, junction_links, List.length_singleton, Finset.range_one]

/-! #### Linearization -/

@[simp] theorem linearize_single : (single a b).linearize = [(b, [a])] := by
  rw [single, linearize_junction]; rfl

@[simp] theorem linearize_bare : (bare b : AR α β).linearize = [(b, [])] := by
  rw [bare, linearize_junction]; rfl

@[simp] theorem linearize_float : (float a : AR α β).linearize = [] := by
  rw [float, linearize_junction]; rfl

@[simp] theorem linearize_contour : (contour as b).linearize = [(b, as)] := by
  rw [contour, linearize_junction]; rfl

@[simp] theorem linearize_spread :
    (spread a bs).linearize = bs.map fun b => (b, [a]) := linearize_junction

/-! #### Planarity: the builders live inside the NCC by construction -/

@[simp] theorem isPlanar_single : (single a b).toGraph.IsPlanar :=
  isPlanar_junction_iff.mpr (Or.inl (by simp))

@[simp] theorem isPlanar_bare : (bare b : AR α β).toGraph.IsPlanar :=
  isPlanar_junction_iff.mpr (Or.inl (by simp))

@[simp] theorem isPlanar_float : (float a : AR α β).toGraph.IsPlanar :=
  isPlanar_junction_iff.mpr (Or.inr (by simp))

@[simp] theorem isPlanar_contour : (contour as b).toGraph.IsPlanar :=
  isPlanar_junction_iff.mpr (Or.inr (by simp))

@[simp] theorem isPlanar_spread : (spread a bs).toGraph.IsPlanar :=
  isPlanar_junction_iff.mpr (Or.inl (by simp))

/-! #### OCP-cleanliness -/

variable [DecidableEq α]

@[simp] theorem isCleanAR_single : IsCleanAR (single a b) :=
  isCleanAR_junction.mpr (OCP.isClean_singleton a)

@[simp] theorem isCleanAR_bare : IsCleanAR (bare b : AR α β) :=
  isCleanAR_junction.mpr OCP.isClean_nil

@[simp] theorem isCleanAR_float : IsCleanAR (float a : AR α β) :=
  isCleanAR_junction.mpr (OCP.isClean_singleton a)

@[simp] theorem isCleanAR_spread : IsCleanAR (spread a bs) :=
  isCleanAR_junction.mpr (OCP.isClean_singleton a)

theorem isCleanAR_contour : IsCleanAR (contour as b) ↔ OCP.IsClean as :=
  isCleanAR_junction

/-! ### The junction in coordinates

The complete association as a two-tier `Representation` (`Bool`-indexed:
`true` the melody tier, `false` the timing tier), built by `ofData`; the
No-Crossing keystone in the foundational path form. -/

section CoordinateJunction

universe u
variable {α β : Type u}

/-- The two-tier alphabet: melody labels over `true`, timing labels over
    `false`. -/
abbrev TwoTier (α β : Type u) : Bool → Type u := fun b => bif b then α else β

/-- Complete many-to-many association of a melody onto a slot sequence, in
    coordinates. -/
def Representation.junction (as : List α) (bs : List β) :
    Representation (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool) :=
  Representation.ofData
    (fun b => match b with
      | true => (as : List (TwoTier α β true))
      | false => (bs : List (TwoTier α β false)))
    (fun i j p q => i = true ∧ j = false ∧ p < as.length ∧ q < bs.length)

instance (as : List α) (bs : List β) :
    Finite (Representation.junction as bs).obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

@[simp] theorem Representation.tierWord_junction_true (as : List α) (bs : List β) :
    (Representation.junction as bs).tierWord true = as :=
  Representation.tierWord_ofData true

@[simp] theorem Representation.tierWord_junction_false (as : List α) (bs : List β) :
    (Representation.junction as bs).tierWord false = bs :=
  Representation.tierWord_ofData false

/-- **The No-Crossing Constraint selects the one-sided junctions**: a complete
    association is planar iff one side has at most one node — the one-to-many
    `spread`, many-to-one `contour`, and degenerate cases. -/
theorem Representation.isPlanar_junction_iff (as : List α) (bs : List β) :
    IsPlanar (Representation.junction as bs).obj.graph ↔
      as.length ≤ 1 ∨ bs.length ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ha, hb⟩ := hc
    rw [Nat.not_le] at ha hb
    exact h (v := ⟨true, ⟨0, show 0 < as.length by omega⟩⟩)
      (v' := ⟨false, ⟨1, show 1 < bs.length by omega⟩⟩)
      (w := ⟨true, ⟨1, show 1 < as.length by omega⟩⟩)
      (w' := ⟨false, ⟨0, show 0 < bs.length by omega⟩⟩)
      ⟨by simp, Or.inl ⟨rfl, rfl, show (0 : ℕ) < as.length by omega,
        show (1 : ℕ) < bs.length by omega⟩⟩
      ⟨by simp, Or.inl ⟨rfl, rfl, show (1 : ℕ) < as.length by omega,
        show (0 : ℕ) < bs.length by omega⟩⟩
      ⟨rfl, show (0 : ℕ) < 1 by omega⟩ ⟨rfl, show (0 : ℕ) < 1 by omega⟩
  · rintro h ⟨bv, pv⟩ ⟨bv', pv'⟩ ⟨bw, pw⟩ ⟨bw', pw'⟩ hvv' hww' hvw hw'v'
    obtain ⟨hbvw, hpvw⟩ := hvw
    obtain ⟨hbw'v', hpw'v'⟩ := hw'v'
    cases hbvw
    cases hbw'v'
    have hv' : bv' = !bv := by
      rcases hvv' with ⟨hne, -⟩
      cases bv <;> cases bv' <;> simp_all
    subst hv'
    rcases h with h | h <;> cases bv
    · have h1 : (pv' : ℕ) < as.length := pv'.isLt
      have h2 : (pw' : ℕ) < as.length := pw'.isLt
      have h3 : (pw' : ℕ) < (pv' : ℕ) := hpw'v'
      omega
    · have h1 : (pv : ℕ) < as.length := pv.isLt
      have h2 : (pw : ℕ) < as.length := pw.isLt
      have h3 : (pv : ℕ) < (pw : ℕ) := hpvw
      omega
    · have h1 : (pv : ℕ) < bs.length := pv.isLt
      have h2 : (pw : ℕ) < bs.length := pw.isLt
      have h3 : (pv : ℕ) < (pw : ℕ) := hpvw
      omega
    · have h1 : (pv' : ℕ) < bs.length := pv'.isLt
      have h2 : (pw' : ℕ) < bs.length := pw'.isLt
      have h3 : (pw' : ℕ) < (pv' : ℕ) := hpw'v'
      omega

end CoordinateJunction

end AR

end Autosegmental
