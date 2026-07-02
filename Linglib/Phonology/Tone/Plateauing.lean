/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Linglib.Core.Data.List.TakeDrop
import Linglib.Core.Computability.Subregular.Function.Bimachine
import Linglib.Phonology.Autosegmental.Realization
import Linglib.Phonology.Autosegmental.Collapse
import Linglib.Phonology.Autosegmental.Junction
import Linglib.Phonology.Autosegmental.Hull
import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.Tone.Surfacing

/-!
# Unbounded tonal plateauing

[hyman-katamba-2010]'s plateauing rule for Luganda: every tone-bearing unit between two
H-toned units surfaces H. Formalized over the string rendering of [jardine-2016]: a word
over `TBU` records each timing unit's association state (`H` associated to a H tone, `O`
unassociated), and `utp` — a `Tone.Surfacing` process — rewrites it pointwise by its
surfacing predicate. What surfaces is the *representation*: `utp.Surfaces w i` is by
definition H-linkedness of timing node `i` in the output representation `plateauAR w`
(the OCP-merged input, hull-closed — fusion then spreading); the string reading is the
derived `utp.surfaces_def`. The map is `utp.map`, the surfacing set `plateau`.

The map is the flagship *unbounded circumambient* process: whether a position changes
depends on unboundedly distant material on **both** sides
(`utp.isUnboundedCircumambient`), and in the strong witness form
`utp.requiresBothSides` — perturbing either far side alone reverts the change — which
feeds the weak-determinism exclusion theorems of `Studies/Jardine2016Tone` (bimachine
rendering) and `Studies/Yolyan2025` (BMRS rendering).

## Main definitions

* `Tone.Plateauing.TBU` — the H/Ø string alphabet (association states; distinct from
  `Tone.TBUKind`, the phonological typology of timing units).
* `Tone.Plateauing.plateauAR` — the output representation (OCP-merged input,
  hull-closed); `utp.Surfaces` is H-linkedness in it, via `Graph.SurfacesWith` and
  `Graph.hull` (`Phonology/Autosegmental/Hull.lean`).
* `Tone.Plateauing.utp` — plateauing as a `Tone.Surfacing` process; `utp.map` the map.
* `Tone.Plateauing.plateau` — the set of surfacing positions.

## Main results

* `utp.map_getElem?_H_iff` / `utp.map_getElem?_O_iff` — pointwise characterization of the map.
* `utp_eq_plateau_indicator`, `plateau_eq_Icc` — the output is the indicator word of an
  interval, from the first trigger to the last.
* `utp.map_toneless`, `utp.map_single`, `utp.map_plateau` — the rule schemata: toneless words and
  lone Hs are unchanged; everything between the outermost Hs surfaces H.
* `utp.map_getElem?_H_of_getElem?_H`, `utp.map_mono`, `utp.map_map` — plateauing is a closure
  operator in the pointwise H-order: extensive, monotone, idempotent.
* `utp.requiresBothSides` — deleting either flanking H reverts the plateau target, at
  every distance.
-/

namespace Tone.Plateauing

open Subregular

/-! ### The tone-bearing-unit alphabet -/

/-- A tone-bearing unit's association state: `H` is a TBU associated to a H tone, `O` an
unspecified TBU ([jardine-2016]'s Ø). -/
inductive TBU | H | O
  deriving DecidableEq, Repr

/-! ### The output representation

The string rendering embeds into autosegmental representations, and plateauing on
representations is OCP-fusion followed by hull-closure of the association lines
([hyman-katamba-2010]'s rule as an operation on structures). What surfaces is the
representation: `utp.Surfaces` is *by definition* H-linkedness in the output
representation `plateauAR w`; the string-level `take`/`drop` reading is the derived
characterization `utp.surfaces_def`. -/

open Autosegmental

/-- A H-toned TBU is one H melody node linked to its timing unit; a toneless TBU a bare
timing unit. -/
def toAR : TBU → AR _root_.Tone.TRN Unit
  | .H => .single _root_.Tone.TRN.H ()
  | .O => .bare ()

theorem linearize_realize_toAR (w : List TBU) :
    (realize toAR w).linearize
      = w.map fun a => ((), if a = .H then [_root_.Tone.TRN.H] else []) := by
  rw [linearize_realize]
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.flatMap_cons, List.map_cons, ih]; cases a <;> simp [toAR]

theorem upper_realize_toAR (v : List TBU) :
    (realize toAR v).upper.toList = List.replicate (v.count .H) _root_.Tone.TRN.H := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [realize_cons, AR.concat_upper, LabeledTuple.toList_concat, ih]
    cases a <;> simp [toAR, List.replicate_succ]

/-- A timing node of the input representation is linked iff its TBU is H-toned. -/
theorem isLinkedLower_realize_toAR {w : List TBU} {j : ℕ} :
    (realize toAR w).toGraph.IsLinkedLower j ↔ w[j]? = some .H := by
  rw [AR.isLinkedLower_iff_linearize, linearize_realize_toAR]
  cases hv : w[j]? with
  | none => simp [List.getElem?_map, hv]
  | some a => cases a <;> simp [List.getElem?_map, hv]

/-- The merged input representation: one fused H, linked to exactly the H-positions. -/
theorem mem_links_realizeMerged_toAR {w : List TBU} {p : ℕ × ℕ} :
    p ∈ (realizeMerged toAR w).links ↔ p.1 = 0 ∧ w[p.2]? = some TBU.H := by
  rw [realizeMerged_def, mem_links_collapseAR_of_upper_replicate (upper_realize_toAR w),
    isLinkedLower_realize_toAR]

/-- With any H present, the fused melody node is the H at index `0`. -/
theorem upper_get?_realizeMerged_toAR {w : List TBU} (hw : .H ∈ w) :
    (realizeMerged toAR w).upper.get? 0 = some _root_.Tone.TRN.H := by
  obtain ⟨n, hn⟩ : ∃ n, w.count .H = n + 1 :=
    ⟨w.count .H - 1, by have := List.count_pos_iff.mpr hw; omega⟩
  rw [LabeledTuple.get?_eq_getElem?, realizeMerged_def, upper_collapseAR,
    upper_realize_toAR, hn, OCP.collapse_replicate]
  rfl

/-- The output representation: fuse, then spread — the merged input, hull-closed. -/
def plateauAR (w : List TBU) : AR _root_.Tone.TRN Unit := (realizeMerged toAR w).hull

/-- **What surfaces is the representation**: `i` is H-linked in `plateauAR w` iff some
H-toned TBU lies at or before `i` and some at or after it — the string-level reading. -/
theorem surfacesWith_plateauAR {w : List TBU} {i : ℕ} :
    (plateauAR w).SurfacesWith _root_.Tone.TRN.H i ↔ .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i := by
  rw [List.mem_take_iff, List.mem_drop_iff]
  constructor
  · rintro ⟨k, hlink, -⟩
    obtain ⟨j₁, j₂, h₁, h₂, hle₁, hle₂⟩ :=
      (Graph.mem_hull_links (realizeMerged toAR w).inBounds).mp hlink
    exact ⟨⟨j₁, by omega, (mem_links_realizeMerged_toAR.mp h₁).2⟩,
      j₂, hle₂, (mem_links_realizeMerged_toAR.mp h₂).2⟩
  · rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
    refine ⟨0, (Graph.mem_hull_links (realizeMerged toAR w).inBounds).mpr
      ⟨j₁, j₂, mem_links_realizeMerged_toAR.mpr ⟨rfl, h₁⟩,
        mem_links_realizeMerged_toAR.mpr ⟨rfl, h₂⟩, by omega, hj₂⟩, ?_⟩
    exact upper_get?_realizeMerged_toAR (List.mem_iff_getElem?.mpr ⟨j₁, h₁⟩)

/-! ### The plateauing process -/

/-- Unbounded tonal plateauing as a surfacing process: a TBU surfaces the marked tone
`H` iff its timing node is H-linked in the output representation. -/
def utp : Surfacing TBU where
  hi := .H
  lo := .O
  Surfaces w i := (plateauAR w).SurfacesWith _root_.Tone.TRN.H i
  hi_ne_lo := by decide
  lt_length h := by
    have h₂ := List.length_pos_of_mem (surfacesWith_plateauAR.mp h).2
    rw [List.length_drop] at h₂
    omega
  surfaces_of_hi h := surfacesWith_plateauAR.mpr
    ⟨List.mem_take_iff.mpr ⟨_, Nat.lt_succ_self _, h⟩, List.mem_drop_iff.mpr ⟨_, le_rfl, h⟩⟩
  decSurfaces w i := decidable_of_iff _ surfacesWith_plateauAR.symm

@[simp] theorem utp.hi_def : utp.hi = .H := rfl

@[simp] theorem utp.lo_def : utp.lo = .O := rfl

/-- The string-level reading of surfacing: the windowed form, now derived. -/
theorem utp.surfaces_def {w : List TBU} {i : ℕ} :
    utp.Surfaces w i ↔ .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i :=
  surfacesWith_plateauAR

variable {w : List TBU} {i j k : ℕ}

/-- Positionwise reading of surfacing: a H at some `j ≤ i` and a H at some `j ≥ i`. -/
theorem utp.surfaces_iff :
    utp.Surfaces w i ↔ (∃ j ≤ i, w[j]? = some .H) ∧ ∃ j ≥ i, w[j]? = some .H := by
  rw [utp.surfaces_def, List.mem_take_iff, List.mem_drop_iff]
  simp [Nat.lt_succ_iff]

/-- The surfacing set is convex: the windows only widen. -/
theorem _root_.Tone.Surfacing.Surfaces.of_le_of_le (hi : utp.Surfaces w i)
    (hk : utp.Surfaces w k) (hij : i ≤ j) (hjk : j ≤ k) : utp.Surfaces w j :=
  utp.surfaces_def.mpr
    ⟨w.take_subset_take_left (by omega) (utp.surfaces_def.mp hi).1,
      w.drop_subset_drop_left (by omega) (utp.surfaces_def.mp hk).2⟩

theorem _root_.Tone.Surfacing.Surfaces.H_mem (h : utp.Surfaces w i) : .H ∈ w :=
  List.take_subset _ _ (utp.surfaces_def.mp h).1

/-- Reversal symmetry: under `reverse` the two windows swap. -/
theorem utp.surfaces_reverse (hi : i < w.length) :
    utp.Surfaces w.reverse i ↔ utp.Surfaces w (w.length - 1 - i) := by
  rw [utp.surfaces_def, utp.surfaces_def, List.take_reverse, List.drop_reverse,
    List.mem_reverse, List.mem_reverse,
    show w.length - (i + 1) = w.length - 1 - i from by omega,
    show w.length - i = (w.length - 1 - i) + 1 from by omega, and_comm]

/-- TBU `i` surfaces iff it is itself a H or is strictly flanked. -/
theorem utp.surfaces_split {a : TBU} (h : w[i]? = some a) :
    utp.Surfaces w i ↔ a = .H ∨ (.H ∈ w.take i ∧ .H ∈ w.drop (i + 1)) := by
  rcases eq_or_ne a .H with rfl | ha
  · simp [utp.surfaces_of_hi h]
  · obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
    rw [utp.surfaces_def, List.take_add_one, h, List.drop_eq_getElem_cons hi, hia]
    simp [ha, Ne.symm ha]

theorem utp.map_getElem? :
    (utp.map w)[i]? = w[i]?.map fun _ => if utp.Surfaces w i then TBU.H else TBU.O :=
  Surfacing.map_getElem? utp

theorem utp.map_getElem?_H_iff : (utp.map w)[j]? = some .H ↔ utp.Surfaces w j :=
  utp.map_getElem?_hi_iff

theorem utp.map_getElem?_O_iff :
    (utp.map w)[j]? = some .O ↔ j < w.length ∧ ¬ utp.Surfaces w j :=
  utp.map_getElem?_lo_iff

/-- Plateauing is symmetric under string reversal. -/
theorem utp.map_reverse : utp.map w.reverse = (utp.map w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · rw [utp.map_getElem?, List.getElem?_reverse (by simpa using hi),
      List.getElem?_reverse (by simpa using hi), Surfacing.map_length, utp.map_getElem?]
    simp only [utp.surfaces_reverse hi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-! ### The plateau set -/

/-- The plateau of `w`: the set of positions that surface H. -/
def plateau (w : List TBU) : Finset ℕ := utp.support w

@[simp] theorem mem_plateau : j ∈ plateau w ↔ utp.Surfaces w j := utp.mem_support

@[simp] theorem plateau_nonempty : (plateau w).Nonempty ↔ .H ∈ w :=
  ⟨fun ⟨_, hj⟩ => (mem_plateau.mp hj).H_mem, fun hw =>
    have ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    ⟨i, mem_plateau.mpr (utp.surfaces_of_hi hi)⟩⟩

/-- `utp.map` writes the indicator word of its plateau. -/
theorem utp_eq_plateau_indicator :
    utp.map w
      = (List.range w.length).map fun i => if i ∈ plateau w then TBU.H else TBU.O :=
  utp.map_eq_indicator

/-- Sandwich characterization: a word with Hs at `lo` and `hi` and none outside
`[lo, hi]` has plateau exactly `Finset.Icc lo hi`. -/
theorem plateau_eq_Icc_of {lo hi : ℕ} (hlo : w[lo]? = some .H) (hhi : w[hi]? = some .H)
    (hb : ∀ j, w[j]? = some .H → lo ≤ j ∧ j ≤ hi) : plateau w = Finset.Icc lo hi := by
  ext j
  rw [mem_plateau, Finset.mem_Icc, utp.surfaces_iff]
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
    mem_plateau.mpr ((mem_plateau.mp ((plateau w).min'_mem hne)).of_le_of_le
      (mem_plateau.mp ((plateau w).max'_mem hne)) h₁ h₂)⟩

/-! ### Closure laws

Plateauing is a closure operator in the pointwise H-order: extensive
(`utp.map_getElem?_H_of_getElem?_H`), monotone (`utp.map_mono`), idempotent (`utp.map_map`). The
engine is convexity: the output's Hs are the plateau, an interval, so plateauing the
output surfaces nothing new (`utp.surfaces_map`). -/

/-- Extensivity: every H survives plateauing. -/
theorem utp.map_getElem?_H_of_getElem?_H (h : w[i]? = some .H) :
    (utp.map w)[i]? = some .H :=
  utp.map_getElem?_hi_of_getElem?_hi h

/-- Surfacing is monotone in the word's H-set. -/
theorem _root_.Tone.Surfacing.Surfaces.mono {w' : List TBU}
    (hw : ∀ j : ℕ, w[j]? = some TBU.H → w'[j]? = some TBU.H) (h : utp.Surfaces w i) :
    utp.Surfaces w' i := by
  obtain ⟨⟨l, hl, hlH⟩, r, hr, hrH⟩ := utp.surfaces_iff.mp h
  exact utp.surfaces_iff.mpr ⟨⟨l, hl, hw l hlH⟩, r, hr, hw r hrH⟩

/-- Monotonicity: pointwise more Hs in, pointwise more Hs out. -/
theorem utp.map_mono {w' : List TBU}
    (hw : ∀ j : ℕ, w[j]? = some TBU.H → w'[j]? = some TBU.H) (j : ℕ)
    (h : (utp.map w)[j]? = some TBU.H) : (utp.map w')[j]? = some TBU.H :=
  utp.map_getElem?_H_iff.mpr ((utp.map_getElem?_H_iff.mp h).mono hw)

/-- Surfacing is invariant under plateauing: the output's Hs are the plateau, whose
convexity flanks no new positions. -/
theorem utp.surfaces_map : utp.Surfaces (utp.map w) i ↔ utp.Surfaces w i := by
  constructor
  · intro h
    obtain ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩ := utp.surfaces_iff.mp h
    rw [utp.map_getElem?_H_iff] at h₁ h₂
    obtain ⟨⟨l, hl, hlH⟩, -⟩ := utp.surfaces_iff.mp h₁
    obtain ⟨-, r, hr, hrH⟩ := utp.surfaces_iff.mp h₂
    exact utp.surfaces_iff.mpr ⟨⟨l, by omega, hlH⟩, r, by omega, hrH⟩
  · exact fun h => utp.surfaces_iff.mpr ⟨⟨i, le_rfl, utp.map_getElem?_H_iff.mpr h⟩,
      i, le_rfl, utp.map_getElem?_H_iff.mpr h⟩

@[simp] theorem plateau_utp : plateau (utp.map w) = plateau w := by
  ext j
  rw [mem_plateau, mem_plateau, utp.surfaces_map]

/-- Idempotence: a plateau is already closed. -/
@[simp] theorem utp.map_map : utp.map (utp.map w) = utp.map w := by
  rw [utp_eq_plateau_indicator (w := utp.map w), plateau_utp, Surfacing.map_length,
    ← utp_eq_plateau_indicator]

/-! ### The plateauing rule

The rule schemata as theorems about `utp` rather than clauses of its definition. -/

/-- A toneless word is unchanged. -/
theorem utp.map_toneless (n : ℕ) : utp.map (List.replicate n .O) = List.replicate n .O := by
  have h : plateau (List.replicate n TBU.O) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (by simp)
  simp [utp_eq_plateau_indicator, h, List.map_const']

/-- A word with a single H is unchanged — one H cannot trigger a plateau. -/
theorem utp.map_single (m n : ℕ) :
    utp.map (List.replicate m .O ++ .H :: List.replicate n .O)
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
theorem utp.map_plateau (m p : ℕ) (w : List TBU) :
    utp.map (List.replicate m .O ++ .H :: (w ++ .H :: List.replicate p .O))
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
example : utp.map [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp.map [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp.map [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

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
    utp.Surfaces (flanked d x y) (d + 1) ↔ x = .H ∧ y = .H := by
  rw [utp.surfaces_iff]
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
theorem utp.requiresBothSides : RequiresBothSides utp.map := by
  intro d
  have hmid : ∀ x y : TBU, (flanked d x y)[d + 1]? = some .O := fun x y => by
    rw [flanked_getElem?, if_neg (by omega : ¬(d + 1 = 0)),
      if_neg (by omega : ¬(d + 1 = 2 * d + 3)), if_pos (by omega : d + 1 < 2 * d + 4)]
  have himg : ∀ x y : TBU, (utp.map (flanked d x y))[d + 1]?
      = if x = .H ∧ y = .H then some .H else some .O := fun x y => by
    split_ifs with h
    · exact utp.map_getElem?_H_iff.mpr ((surfacesH_flanked_mid d).mpr h)
    · exact utp.map_getElem?_O_iff.mpr ⟨by rw [flanked_length]; omega,
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
theorem utp.isUnboundedCircumambient : IsUnboundedCircumambient utp.map :=
  utp.requiresBothSides.isUnboundedCircumambient

end Tone.Plateauing
