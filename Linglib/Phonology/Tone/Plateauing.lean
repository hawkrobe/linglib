/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Linglib.Core.Data.List.TakeDrop
import Linglib.Core.Computability.Subregular.Function.Bimachine
import Linglib.Phonology.Autosegmental.OCP
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
* `realizeMerged_toAR_map` — the commuting square: the merged representation of the
  output string is the output representation `plateauAR`.
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

/-- `toAR` in coordinates: the two-tier representation of one association
    state (melody over `true`, timing over `false`). -/
noncomputable def toRep (a : TBU) :
    Autosegmental.AR
      (Sigma.fst : ((b : Bool) × Autosegmental.TwoTier _root_.Tone.TRN Unit b) → Bool) :=
  match a with
  | .H => Autosegmental.AR.single _root_.Tone.TRN.H ()
  | .O => Autosegmental.AR.bare ()

instance (a : TBU) : Finite (toRep a).obj.V := by
  cases a <;> exact inferInstanceAs (Finite ((_ : Bool) × Fin _))

instance : DecidableEq (Autosegmental.TwoTier _root_.Tone.TRN Unit true) :=
  inferInstanceAs (DecidableEq _root_.Tone.TRN)

/-- The output representation in coordinates: OCP-merge then hull, both at the
    melody tier. -/
noncomputable def plateauRep (w : List TBU) :
    Autosegmental.AR
      (Sigma.fst : ((b : Bool) × Autosegmental.TwoTier _root_.Tone.TRN Unit b) → Bool) :=
  ((Autosegmental.realize toRep w).collapse true).hull true

instance (w : List TBU) : Finite (plateauRep w).obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

section TierWords
open CategoryTheory
open scoped MonoidalCategory

/-- The melody word of a realized string: one `H` node per H-toned TBU. -/
theorem tierWord_realize_toRep_true (w : List TBU) :
    (Autosegmental.realize toRep w).tierWord true
      = List.replicate (w.count .H) _root_.Tone.TRN.H := by
  induction w with
  | nil => simp [Autosegmental.AR.tierWord_unit]
  | cons a w ih =>
    calc (Autosegmental.realize toRep (a :: w)).tierWord true
        = (toRep a ⊗ Autosegmental.realize toRep w).tierWord true := rfl
      _ = (toRep a).tierWord true ++ (Autosegmental.realize toRep w).tierWord true :=
          Autosegmental.AR.tierWord_tensor true
      _ = List.replicate ((a :: w).count .H) _root_.Tone.TRN.H := by
          rw [ih]
          cases a
          · rw [show (toRep TBU.H).tierWord true = [_root_.Tone.TRN.H] from
              Autosegmental.AR.tierWord_ofData true,
              List.count_cons_self, List.replicate_succ]
            rfl
          · rw [show (toRep TBU.O).tierWord true = [] from
              Autosegmental.AR.tierWord_ofData true,
              List.count_cons_of_ne (by decide)]
            rfl

/-- The timing word of a realized string: one slot per TBU. -/
theorem tierWord_realize_toRep_false (w : List TBU) :
    (Autosegmental.realize toRep w).tierWord false = List.replicate w.length () := by
  induction w with
  | nil => simp [Autosegmental.AR.tierWord_unit]
  | cons a w ih =>
    calc (Autosegmental.realize toRep (a :: w)).tierWord false
        = (toRep a ⊗ Autosegmental.realize toRep w).tierWord false := rfl
      _ = (toRep a).tierWord false ++ (Autosegmental.realize toRep w).tierWord false :=
          Autosegmental.AR.tierWord_tensor false
      _ = List.replicate (a :: w).length () := by
          rw [ih, List.length_cons, List.replicate_succ]
          cases a
          · rw [show (toRep TBU.H).tierWord false = [()] from
              Autosegmental.AR.tierWord_ofData false]
            rfl
          · rw [show (toRep TBU.O).tierWord false = [()] from
              Autosegmental.AR.tierWord_ofData false]
            rfl

/-- Links of a realized string: slot `j` links to melody node `p` exactly when
    TBU `j` is H-toned and `p` is its accumulated melody position. -/
theorem link_realize_toRep (w : List TBU) (p j : ℕ) :
    (Autosegmental.realize toRep w).link true false p j ↔
      p = (w.take j).count .H ∧ w[j]? = some .H := by
  induction w generalizing p j with
  | nil =>
    have h0 : (Autosegmental.realize toRep []).tierLength true = 0 := by
      rw [← Autosegmental.AR.length_tierWord,
        show (Autosegmental.realize toRep []).tierWord true = _ from
          Autosegmental.AR.tierWord_unit true, List.length_nil]
    constructor
    · rintro ⟨hp, -, -⟩
      omega
    · rintro ⟨-, h⟩
      simp at h
  | cons a w ih =>
    haveI := Autosegmental.realize.instFinite toRep w
    rw [show (Autosegmental.realize toRep (a :: w)).link true false p j
          = (toRep a ⊗ Autosegmental.realize toRep w).link true false p j from rfl,
      Autosegmental.AR.link_tensor (X := toRep a)
        (Y := Autosegmental.realize toRep w) true false p j]
    cases a
    · have hta : (toRep TBU.H).tierLength true = 1 := by
        rw [← Autosegmental.AR.length_tierWord,
          show (toRep TBU.H).tierWord true = [_root_.Tone.TRN.H] from
            Autosegmental.AR.tierWord_ofData true]
        rfl
      have hfa : (toRep TBU.H).tierLength false = 1 := by
        rw [← Autosegmental.AR.length_tierWord,
          show (toRep TBU.H).tierWord false = [()] from
            Autosegmental.AR.tierWord_ofData false]
        rfl
      have hj : (toRep TBU.H).link true false p j ↔ p = 0 ∧ j = 0 := by
        refine (Autosegmental.AR.link_junction
          [_root_.Tone.TRN.H] [()]).trans ?_
        constructor
        · rintro (⟨-, -, h1, h2⟩ | ⟨h, -⟩)
          · exact ⟨by simpa using h1, by simpa using h2⟩
          · exact absurd h (by decide)
        · rintro ⟨rfl, rfl⟩
          exact Or.inl ⟨rfl, rfl, by simp, by simp⟩
      rw [hj, hta, hfa, ih]
      rcases j with _ | j
      · simp
      · constructor
        · rintro (⟨-, h⟩ | ⟨hp1, -, hrec, hj1⟩)
          · exact absurd h (by omega)
          · rw [show j + 1 - 1 = j from rfl] at hrec
            refine ⟨?_, by simpa using hj1⟩
            rw [List.take_succ_cons, List.count_cons_self]
            omega
        · rintro ⟨hp, hj1⟩
          rw [List.take_succ_cons, List.count_cons_self] at hp
          refine Or.inr ⟨by omega, by omega, ?_, by simpa using hj1⟩
          have : j + 1 - 1 = j := by omega
          rw [this]
          omega
    · have hta : (toRep TBU.O).tierLength true = 0 := by
        rw [← Autosegmental.AR.length_tierWord,
          show (toRep TBU.O).tierWord true = [] from
            Autosegmental.AR.tierWord_ofData true]
        rfl
      have hfa : (toRep TBU.O).tierLength false = 1 := by
        rw [← Autosegmental.AR.length_tierWord,
          show (toRep TBU.O).tierWord false = [()] from
            Autosegmental.AR.tierWord_ofData false]
        rfl
      have hj : ¬ (toRep TBU.O).link true false p j := by
        intro h
        rcases (Autosegmental.AR.link_junction
          ([] : List _root_.Tone.TRN) [()]).mp h with ⟨-, -, h1, -⟩ | ⟨h1, -⟩
        · simp at h1
        · exact absurd h1 (by decide)
      rw [hta, hfa, ih]
      rcases j with _ | j
      · constructor
        · rintro (h | ⟨-, h, -⟩)
          · exact absurd h hj
          · omega
        · rintro ⟨-, h⟩
          simp at h
      · constructor
        · rintro (h | ⟨-, -, hrec, hj1⟩)
          · exact absurd h hj
          · rw [show j + 1 - 1 = j from rfl] at hrec
            refine ⟨?_, by simpa using hj1⟩
            rw [List.take_succ_cons, List.count_cons_of_ne (by decide)]
            omega
        · rintro ⟨hp, hj1⟩
          rw [List.take_succ_cons, List.count_cons_of_ne (by decide)] at hp
          refine Or.inr ⟨by omega, by omega, ?_, by simpa using hj1⟩
          have : j + 1 - 1 = j := by omega
          rw [this]
          omega

/-- Links of the OCP-merged realization: the single fused `H` node (index `0`)
    links exactly to the H-toned slots. -/
theorem link_realizeMerged (w : List TBU) (k j : ℕ) :
    ((Autosegmental.realize toRep w).collapse true).link true false k j ↔
      k = 0 ∧ w[j]? = some .H := by
  haveI := Autosegmental.realize.instFinite toRep w
  rw [Autosegmental.AR.link_collapse]
  constructor
  · rintro ⟨p, q, hl, hk, hjq⟩
    obtain ⟨hp, hq⟩ := (link_realize_toRep w p q).mp hl
    refine ⟨?_, ?_⟩
    · rw [← hk]
      unfold Autosegmental.AR.collapseIdx
      rw [if_pos rfl, tierWord_realize_toRep_true]
      exact OCP.runIdx_replicate _ _ _
    · rw [← hjq]
      unfold Autosegmental.AR.collapseIdx
      rw [if_neg (by decide)]
      exact hq
  · rintro ⟨rfl, hj⟩
    refine ⟨(w.take j).count .H, j, (link_realize_toRep w _ j).mpr ⟨rfl, hj⟩, ?_, ?_⟩
    · unfold Autosegmental.AR.collapseIdx
      rw [if_pos rfl, tierWord_realize_toRep_true]
      exact OCP.runIdx_replicate _ _ _
    · unfold Autosegmental.AR.collapseIdx
      rw [if_neg (by decide)]

/-- **What surfaces is the representation**: slot `j` is H-linked in
    `plateauRep w` iff some H-toned TBU lies at or before `j` and some at or
    after it — fusion then spreading, read back as the string window. -/
theorem link_plateauRep (w : List TBU) (j : ℕ) :
    (∃ k, (plateauRep w).link true false k j) ↔
      .H ∈ w.take (j + 1) ∧ .H ∈ w.drop j := by
  haveI := Autosegmental.realize.instFinite toRep w
  have hlen : ((Autosegmental.realize toRep w).collapse true).tierLength false
      = w.length := by
    rw [← Autosegmental.AR.length_tierWord,
      Autosegmental.AR.tierWord_collapse,
      show (Autosegmental.realize toRep w).collapsedWord true false
        = (Autosegmental.realize toRep w).tierWord false from
        Function.update_of_ne (by decide) _ _,
      tierWord_realize_toRep_false]
    exact List.length_replicate
  rw [List.mem_take_iff, List.mem_drop_iff]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨-, hjb, -⟩ := id hk
    have hlenh : (plateauRep w).tierLength false = w.length := by
      rw [← Autosegmental.AR.length_tierWord,
        show (plateauRep w).tierWord false
          = ((Autosegmental.realize toRep w).collapse true).tierWord false from
          Autosegmental.AR.tierWord_hull true _ false,
        Autosegmental.AR.length_tierWord, hlen]
    have hjw : j < w.length := hlenh ▸ hjb
    obtain ⟨q₁, q₂, h₁, h₂, hle₁, hle₂⟩ :=
      (Autosegmental.AR.link_hull_left true _ (by decide)
        (by omega : j < ((Autosegmental.realize toRep w).collapse true).tierLength false)).mp hk
    obtain ⟨-, hq₁⟩ := (link_realizeMerged w k q₁).mp h₁
    obtain ⟨-, hq₂⟩ := (link_realizeMerged w k q₂).mp h₂
    exact ⟨⟨q₁, by omega, hq₁⟩, q₂, hle₂, hq₂⟩
  · rintro ⟨⟨q₁, hq₁b, hq₁⟩, q₂, hq₂b, hq₂⟩
    have hq₂w : q₂ < w.length := by
      rcases List.getElem?_eq_some_iff.mp hq₂ with ⟨h, -⟩
      exact h
    have hl₁ := (link_realizeMerged w 0 q₁).mpr ⟨rfl, hq₁⟩
    have hl₂ := (link_realizeMerged w 0 q₂).mpr ⟨rfl, hq₂⟩
    exact ⟨0, (Autosegmental.AR.link_hull_left true _ (by decide)
      (by omega : j < ((Autosegmental.realize toRep w).collapse true).tierLength false)).mpr
      ⟨q₁, q₂, hl₁, hl₂, by omega, hq₂b⟩⟩

end TierWords

/-! ### The plateauing process -/

/-- Unbounded tonal plateauing as a surfacing process: a TBU surfaces the marked tone
`H` iff its timing node is H-linked in the output representation. -/
def utp : Surfacing TBU where
  hi := .H
  lo := .O
  Surfaces w i := .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i
  hi_ne_lo := by decide
  lt_length h := by
    have h₂ := List.length_pos_of_mem h.2
    rw [List.length_drop] at h₂
    omega
  surfaces_of_hi h :=
    ⟨List.mem_take_iff.mpr ⟨_, Nat.lt_succ_self _, h⟩, List.mem_drop_iff.mpr ⟨_, le_rfl, h⟩⟩
  decSurfaces w i := inferInstanceAs (Decidable (_ ∧ _))

/-- **What surfaces is the representation**: `utp.Surfaces w i` is H-linkedness
    of timing slot `i` in the coordinate output representation `plateauRep w` —
    the OCP-merged, hull-closed realization. -/
theorem utp.surfaces_iff_link_plateauRep {w : List TBU} {i : ℕ} :
    utp.Surfaces w i ↔ ∃ k, (plateauRep w).link true false k i :=
  (link_plateauRep w i).symm

@[simp] theorem utp.hi_def : utp.hi = .H := rfl

@[simp] theorem utp.lo_def : utp.lo = .O := rfl

/-- The string-level reading of surfacing: the windowed form, definitional. -/
theorem utp.surfaces_def {w : List TBU} {i : ℕ} :
    utp.Surfaces w i ↔ .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i :=
  Iff.rfl

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

/-- Plateauing preserves the presence of a trigger in both directions. -/
theorem utp.H_mem_map : .H ∈ utp.map w ↔ .H ∈ w :=
  ⟨fun h => have ⟨_, hi⟩ := List.mem_iff_getElem?.mp h
    (utp.map_getElem?_H_iff.mp hi).H_mem,
   fun h => have ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    List.mem_iff_getElem?.mpr ⟨i, utp.map_getElem?_H_of_getElem?_H hi⟩⟩

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

Whether the target surfaces is controlled by unboundedly distant flanks: instantiate
the flank-witness template with `2d+2` toneless TBUs between the flanks. -/

/-- UTP requires both sides ([heinz-lai-2013]): its trigger is the two-sided window
conjunction, so deleting either flanking H reverts the plateau target. -/
theorem utp.requiresBothSides : RequiresBothSides utp.map :=
  utp.requiresBothSides_of_surfaces_iff fun _ _ => utp.surfaces_iff

/-- UTP is an unbounded circumambient process: whether a position changes depends on
unboundedly distant material on both sides. -/
theorem utp.isUnboundedCircumambient : IsUnboundedCircumambient utp.map :=
  utp.requiresBothSides.isUnboundedCircumambient

end Tone.Plateauing
