/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Linglib.Core.Data.List.TakeDrop
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# Unbounded tonal plateauing

[hyman-katamba-2010]'s plateauing rule for Luganda: every tone-bearing unit between two
H-toned units surfaces H. Formalized over the string rendering of [jardine-2016]: a word
over `TBU` records each timing unit's association state (`H` associated to a H tone, `O`
unassociated), and `utp` rewrites it pointwise by `SurfacesH` — a position surfaces H iff
some H lies at or before it and some H at or after it.

The map is the flagship *unbounded circumambient* process: whether a position changes
depends on unboundedly distant material on **both** sides
(`utp_isUnboundedCircumambient`), and in the strong witness form
`utp_requiresBothSides` — perturbing either far side alone reverts the change — which
feeds the weak-determinism exclusion theorems of `Studies/Jardine2016Tone` (bimachine
rendering) and `Studies/Yolyan2025` (BMRS rendering).

## Main definitions

* `Tone.Plateauing.TBU` — the H/Ø string alphabet (association states; distinct from
  `Tone.TBUKind`, the phonological typology of timing units).
* `Tone.Plateauing.SurfacesH` — position `i` of `w` surfaces with a H tone.
* `Tone.Plateauing.utp` — the plateauing map.
* `Tone.Plateauing.plateau` — the set of surfacing positions.

## Main results

* `utp_getElem?_H_iff` / `utp_getElem?_O_iff` — pointwise characterization of the map.
* `utp_eq_plateau_indicator`, `plateau_eq_Icc` — the output is the indicator word of an
  interval, from the first trigger to the last.
* `utp_toneless`, `utp_single`, `utp_plateau` — the rule schemata: toneless words and
  lone Hs are unchanged; everything between the outermost Hs surfaces H.
* `utp_getElem?_H_of_getElem?_H`, `utp_mono`, `utp_utp` — plateauing is a closure
  operator in the pointwise H-order: extensive, monotone, idempotent.
* `utp_requiresBothSides` — deleting either flanking H reverts the plateau target, at
  every distance.
-/

namespace Tone.Plateauing

open Subregular

/-! ### The tone-bearing-unit alphabet -/

/-- A tone-bearing unit's association state: `H` is a TBU associated to a H tone, `O` an
unspecified TBU ([jardine-2016]'s Ø). -/
inductive TBU | H | O
  deriving DecidableEq, Repr

/-! ### Surfacing -/

/-- TBU `i` of `w` surfaces with a H tone: some H-toned TBU sits at a position `≤ i` and
some at a position `≥ i` — [hyman-katamba-2010]'s plateauing rule, pointwise. -/
def SurfacesH (w : List TBU) (i : ℕ) : Prop := .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i

instance (w : List TBU) (i : ℕ) : Decidable (SurfacesH w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {w : List TBU} {i j k : ℕ}

/-- Positionwise reading of `SurfacesH`: a H at some `j ≤ i` and a H at some `j ≥ i`. -/
theorem surfacesH_iff :
    SurfacesH w i ↔ (∃ j ≤ i, w[j]? = some .H) ∧ ∃ j ≥ i, w[j]? = some .H := by
  rw [SurfacesH, List.mem_take_iff, List.mem_drop_iff]; simp [Nat.lt_succ_iff]

theorem SurfacesH.lt_length (h : SurfacesH w i) : i < w.length := by
  have h₂ := List.length_pos_of_mem h.2; rw [List.length_drop] at h₂; omega

/-- The surfacing set is convex: `take`/`drop` windows only widen. -/
theorem SurfacesH.of_le_of_le (hi : SurfacesH w i) (hk : SurfacesH w k) (hij : i ≤ j)
    (hjk : j ≤ k) : SurfacesH w j :=
  ⟨w.take_subset_take_left (by omega) hi.1, w.drop_subset_drop_left (by omega) hk.2⟩

/-- A H-toned TBU surfaces H: it flanks itself. -/
theorem surfacesH_of_getElem?_H (h : w[i]? = some .H) : SurfacesH w i :=
  surfacesH_iff.mpr ⟨⟨i, le_rfl, h⟩, ⟨i, le_rfl, h⟩⟩

theorem SurfacesH.H_mem (h : SurfacesH w i) : .H ∈ w := List.take_subset _ _ h.1

/-- Reversal symmetry: under `reverse` the `take` and `drop` windows swap. -/
theorem surfacesH_reverse (hi : i < w.length) :
    SurfacesH w.reverse i ↔ SurfacesH w (w.length - 1 - i) := by
  rw [SurfacesH, SurfacesH, List.take_reverse, List.drop_reverse, List.mem_reverse,
    List.mem_reverse, show w.length - (i + 1) = w.length - 1 - i from by omega,
    show w.length - i = (w.length - 1 - i) + 1 from by omega, and_comm]

/-- TBU `i` surfaces H iff it is itself a H or is strictly flanked: split the `take`
window at its last slot and the `drop` window at its head. -/
theorem surfacesH_split {a : TBU} (h : w[i]? = some a) :
    SurfacesH w i ↔ a = .H ∨ (.H ∈ w.take i ∧ .H ∈ w.drop (i + 1)) := by
  rcases eq_or_ne a .H with rfl | ha
  · simp [surfacesH_of_getElem?_H h]
  · obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
    rw [SurfacesH, List.take_add_one, h, List.drop_eq_getElem_cons hi, hia]
    simp [ha, Ne.symm ha]

/-! ### The plateauing map -/

/-- The unbounded tonal plateauing map: every TBU between two H-toned TBUs surfaces as
H; everything else is unchanged. -/
def utp (w : List TBU) : List TBU := w.mapIdx fun i _ => if SurfacesH w i then .H else .O

@[simp] theorem utp_length : (utp w).length = w.length := by simp [utp]

theorem utp_getElem? :
    (utp w)[i]? = w[i]?.map fun _ => if SurfacesH w i then TBU.H else TBU.O := by
  simp [utp, List.getElem?_mapIdx]

theorem utp_getElem?_H_iff : (utp w)[j]? = some .H ↔ SurfacesH w j := by
  rw [utp_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, -, ha⟩; by_contra hs; rw [if_neg hs] at ha; exact TBU.noConfusion ha
  · exact fun hs => ⟨w[j]'hs.lt_length, List.getElem?_eq_getElem hs.lt_length, if_pos hs⟩

theorem utp_getElem?_O_iff : (utp w)[j]? = some .O ↔ j < w.length ∧ ¬ SurfacesH w j := by
  rw [utp_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hout⟩
    refine ⟨(List.getElem?_eq_some_iff.mp ha).1, fun hs => ?_⟩
    rw [if_pos hs] at hout; exact TBU.noConfusion hout
  · exact fun ⟨hj, hs⟩ => ⟨w[j], List.getElem?_eq_getElem hj, if_neg hs⟩

/-- Plateauing is symmetric under string reversal. -/
theorem utp_reverse : utp w.reverse = (utp w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · rw [utp_getElem?, List.getElem?_reverse (by simpa using hi),
      List.getElem?_reverse (by simpa using hi), utp_length, utp_getElem?]
    simp only [surfacesH_reverse hi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-! ### The plateau set -/

/-- The plateau of `w`: the set of positions that surface H. -/
def plateau (w : List TBU) : Finset ℕ := (Finset.range w.length).filter (SurfacesH w)

@[simp] theorem mem_plateau : j ∈ plateau w ↔ SurfacesH w j := by
  simp only [plateau, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact SurfacesH.lt_length

@[simp] theorem plateau_nonempty : (plateau w).Nonempty ↔ .H ∈ w :=
  ⟨fun ⟨_, hj⟩ => (mem_plateau.mp hj).H_mem, fun hw =>
    have ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    ⟨i, mem_plateau.mpr (surfacesH_of_getElem?_H hi)⟩⟩

/-- `utp` writes the indicator word of its plateau. -/
theorem utp_eq_plateau_indicator :
    utp w = (List.range w.length).map fun i => if i ∈ plateau w then TBU.H else TBU.O :=
  List.ext_getElem (by simp [utp]) fun i h₁ h₂ => by simp [utp, mem_plateau]

/-- Sandwich characterization: a word with Hs at `lo` and `hi` and none outside
`[lo, hi]` has plateau exactly `Finset.Icc lo hi`. -/
theorem plateau_eq_Icc_of {lo hi : ℕ} (hlo : w[lo]? = some .H) (hhi : w[hi]? = some .H)
    (hb : ∀ j, w[j]? = some .H → lo ≤ j ∧ j ≤ hi) : plateau w = Finset.Icc lo hi := by
  ext j
  rw [mem_plateau, Finset.mem_Icc, surfacesH_iff]
  constructor
  · rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
    have hb₁ := hb j₁ h₁; have hb₂ := hb j₂ h₂; omega
  · exact fun hj => ⟨⟨lo, hj.1, hlo⟩, hi, hj.2, hhi⟩

/-- The plateau is an interval, from the first trigger to the last. -/
theorem plateau_eq_Icc (hne : (plateau w).Nonempty) :
    plateau w = Finset.Icc ((plateau w).min' hne) ((plateau w).max' hne) := by
  ext j
  rw [Finset.mem_Icc]
  refine ⟨fun hj => ⟨(plateau w).min'_le j hj, (plateau w).le_max' j hj⟩, fun ⟨h₁, h₂⟩ =>
    mem_plateau.mpr (SurfacesH.of_le_of_le (mem_plateau.mp ((plateau w).min'_mem hne))
      (mem_plateau.mp ((plateau w).max'_mem hne)) h₁ h₂)⟩

/-! ### Closure laws

Plateauing is a closure operator in the pointwise H-order: extensive
(`utp_getElem?_H_of_getElem?_H`), monotone (`utp_mono`), idempotent (`utp_utp`). The
engine is convexity: the output's Hs are the plateau, an interval, so plateauing the
output surfaces nothing new (`surfacesH_utp`). -/

@[simp] theorem utp_nil : utp [] = [] := rfl

/-- Extensivity: every H survives plateauing. -/
theorem utp_getElem?_H_of_getElem?_H (h : w[i]? = some .H) : (utp w)[i]? = some .H :=
  utp_getElem?_H_iff.mpr (surfacesH_of_getElem?_H h)

/-- Surfacing is monotone in the word's H-set. -/
theorem SurfacesH.mono {w' : List TBU}
    (hw : ∀ j : ℕ, w[j]? = some TBU.H → w'[j]? = some TBU.H) (h : SurfacesH w i) :
    SurfacesH w' i := by
  obtain ⟨⟨l, hl, hlH⟩, r, hr, hrH⟩ := surfacesH_iff.mp h
  exact surfacesH_iff.mpr ⟨⟨l, hl, hw l hlH⟩, r, hr, hw r hrH⟩

/-- Monotonicity: pointwise more Hs in, pointwise more Hs out. -/
theorem utp_mono {w' : List TBU}
    (hw : ∀ j : ℕ, w[j]? = some TBU.H → w'[j]? = some TBU.H) (j : ℕ)
    (h : (utp w)[j]? = some TBU.H) : (utp w')[j]? = some TBU.H :=
  utp_getElem?_H_iff.mpr ((utp_getElem?_H_iff.mp h).mono hw)

/-- Surfacing is invariant under plateauing: the output's Hs are the plateau, whose
convexity flanks no new positions. -/
theorem surfacesH_utp : SurfacesH (utp w) i ↔ SurfacesH w i := by
  constructor
  · intro h
    obtain ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩ := surfacesH_iff.mp h
    rw [utp_getElem?_H_iff] at h₁ h₂
    obtain ⟨⟨l, hl, hlH⟩, -⟩ := surfacesH_iff.mp h₁
    obtain ⟨-, r, hr, hrH⟩ := surfacesH_iff.mp h₂
    exact surfacesH_iff.mpr ⟨⟨l, by omega, hlH⟩, r, by omega, hrH⟩
  · exact fun h => surfacesH_iff.mpr ⟨⟨i, le_rfl, utp_getElem?_H_iff.mpr h⟩,
      i, le_rfl, utp_getElem?_H_iff.mpr h⟩

@[simp] theorem plateau_utp : plateau (utp w) = plateau w := by
  ext j
  rw [mem_plateau, mem_plateau, surfacesH_utp]

/-- Idempotence: a plateau is already closed. -/
@[simp] theorem utp_utp : utp (utp w) = utp w := by
  rw [utp_eq_plateau_indicator (w := utp w), plateau_utp, utp_length,
    ← utp_eq_plateau_indicator]

/-! ### The plateauing rule

The rule schemata as theorems about `utp` rather than clauses of its definition. -/

/-- A toneless word is unchanged. -/
theorem utp_toneless (n : ℕ) : utp (List.replicate n .O) = List.replicate n .O := by
  have h : plateau (List.replicate n TBU.O) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (by simp)
  simp [utp_eq_plateau_indicator, h, List.map_const']

/-- A word with a single H is unchanged — one H cannot trigger a plateau. -/
theorem utp_single (m n : ℕ) :
    utp (List.replicate m .O ++ .H :: List.replicate n .O)
      = List.replicate m .O ++ .H :: List.replicate n .O := by
  have hH : ∀ j, (List.replicate m TBU.O ++ TBU.H :: List.replicate n TBU.O)[j]? = some TBU.H
      ↔ j = m := fun j => by
    simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
      List.length_replicate]
    split_ifs <;> simp_all <;> omega
  rw [utp_eq_plateau_indicator, plateau_eq_Icc_of ((hH m).mpr rfl) ((hH m).mpr rfl)
    fun j hj => by rw [hH j] at hj; omega]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.getElem_cons,
    List.getElem_replicate, List.length_replicate, Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- Everything between the outermost Hs surfaces H; the medial material `w` is
arbitrary. -/
theorem utp_plateau (m p : ℕ) (w : List TBU) :
    utp (List.replicate m .O ++ .H :: (w ++ .H :: List.replicate p .O))
      = List.replicate m .O ++ (List.replicate (w.length + 2) .H ++ List.replicate p .O) := by
  have hb : ∀ j, (List.replicate m TBU.O ++ TBU.H :: (w ++ TBU.H :: List.replicate p TBU.O))[j]?
      = some TBU.H → m ≤ j ∧ j ≤ m + 1 + w.length := fun j hj => by
    simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
      List.length_replicate] at hj
    split_ifs at hj <;> first | omega | simp_all
  rw [utp_eq_plateau_indicator, plateau_eq_Icc_of (by simp) (by
      simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
        List.length_replicate]
      split_ifs <;> first | rfl | omega) hb]
  refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_append,
    List.getElem_replicate, List.length_replicate, Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- No plateau without two Hs; `HØØH ↦ HHHH`. -/
example : utp [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

/-! ### Unbounded circumambience

The witness family at distance `d`: `flanked d x y` puts `x` and `y` around `2d+2`
toneless TBUs. The base `flanked d .H .H` is the plateau word with target `d+1`;
flipping either flank to `.O` is the far perturbation that reverts it. -/

/-- The distance-`d` witness word: flanks `x`, `y` around `2d+2` toneless TBUs. -/
private def flanked (d : ℕ) (x y : TBU) : List TBU :=
  x :: (List.replicate (2 * d + 2) .O ++ [y])

private theorem flanked_length (d : ℕ) (x y : TBU) : (flanked d x y).length = 2 * d + 4 := by
  simp [flanked]

private theorem flanked_getElem? (d : ℕ) (x y : TBU) (j : ℕ) :
    (flanked d x y)[j]? = if j = 0 then some x else if j = 2 * d + 3 then some y
      else if j < 2 * d + 4 then some .O else none := by
  simp only [flanked, List.getElem?_cons, List.getElem?_append, List.getElem?_replicate,
    List.length_replicate, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

/-- The target surfaces iff both flanks are H: the toneless fill offers no other
trigger on either side. -/
private theorem surfacesH_flanked_mid (d : ℕ) {x y : TBU} :
    SurfacesH (flanked d x y) (d + 1) ↔ x = .H ∧ y = .H := by
  rw [surfacesH_iff]
  constructor
  · rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
    rw [flanked_getElem?] at h₁ h₂
    split_ifs at h₁ h₂ <;> simp_all
    omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨0, by omega, by rw [flanked_getElem?]; split_ifs <;> first | rfl | omega⟩,
      2 * d + 3, by omega, by rw [flanked_getElem?]; split_ifs <;> first | rfl | omega⟩

/-- UTP requires both sides ([heinz-lai-2013]): deleting either flanking H reverts the
plateau target, at every distance. -/
theorem utp_requiresBothSides : RequiresBothSides utp := by
  intro d
  have hmid : ∀ x y : TBU, (flanked d x y)[d + 1]? = some .O := fun x y => by
    rw [flanked_getElem?, if_neg (by omega : ¬(d + 1 = 0)),
      if_neg (by omega : ¬(d + 1 = 2 * d + 3)), if_pos (by omega : d + 1 < 2 * d + 4)]
  have himg : ∀ x y : TBU, (utp (flanked d x y))[d + 1]?
      = if x = .H ∧ y = .H then some .H else some .O := fun x y => by
    split_ifs with h
    · exact utp_getElem?_H_iff.mpr ((surfacesH_flanked_mid d).mpr h)
    · exact utp_getElem?_O_iff.mpr ⟨by rw [flanked_length]; omega,
        fun hs => h ((surfacesH_flanked_mid d).mp hs)⟩
  have hagreeL : ∀ (x x' y : TBU) (k : ℕ), k ≠ 0 →
      (flanked d x y)[k]? = (flanked d x' y)[k]? := fun x x' y k h0 => by
    rw [flanked_getElem?, flanked_getElem?]; split_ifs <;> first | rfl | omega
  have hagreeR : ∀ (x y y' : TBU) (k : ℕ), k ≠ 2 * d + 3 →
      (flanked d x y)[k]? = (flanked d x y')[k]? := fun x y y' k h3 => by
    rw [flanked_getElem?, flanked_getElem?]; split_ifs <;> rfl
  refine ⟨flanked d .H .H, d + 1, by rw [flanked_length]; omega, ?_, ?_, ?_⟩
  · rw [himg, hmid]; simp
  · exact ⟨flanked d .O .H, by rw [flanked_length, flanked_length],
      fun k hk => hagreeL _ _ _ k (by omega), by rw [hmid, hmid],
      by rw [himg, hmid]; simp⟩
  · exact ⟨flanked d .H .O, by rw [flanked_length, flanked_length],
      fun k hk => hagreeR _ _ _ k (by omega), by rw [hmid, hmid],
      by rw [himg, hmid]; simp⟩

/-- UTP is an unbounded circumambient process: whether a position changes depends on
unboundedly distant material on both sides. -/
theorem utp_isUnboundedCircumambient : IsUnboundedCircumambient utp :=
  utp_requiresBothSides.isUnboundedCircumambient

end Tone.Plateauing
