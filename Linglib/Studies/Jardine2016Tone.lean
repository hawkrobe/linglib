/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Computability.Subregular.Function.LetterSubsequential
import Linglib.Core.Computability.Subregular.Function.Bimachine
import Linglib.Core.Computability.Subregular.Function.Hierarchy
import Linglib.Phonology.Autosegmental.Realization
import Linglib.Phonology.Autosegmental.Collapse
import Linglib.Phonology.Autosegmental.Junction
import Linglib.Phonology.Tone.Basic

/-!
# Jardine (2016): Computationally, tone is different

[jardine-2016] (Phonology 33) characterises a typological asymmetry computationally:
*unbounded circumambient* processes — application depends on unboundedly distant material
on both sides of the target — are common in tone but rare in segmental phonology, and
they are exactly the attested maps exceeding weak determinism. The flagship witness is
**unbounded tonal plateauing** (UTP; [hyman-katamba-2010]): every TBU between two H-toned
TBUs surfaces H. This file formalizes the paper's formal skeleton over its string
representation (§4.1: `H` a H-toned TBU, `O` the paper's Ø).

## Main definitions

* `utp` — the UTP map; `plateau w` — its set of surfacing positions.
* `utpBM` — a bimachine computing UTP.
* `markLeft`, `resolve` — the (43) two-pass decomposition over the `?`-enlarged alphabet.
* `toAR` — the (40) translation into autosegmental representations.

## Main results

* `utp_toneless`, `utp_single`, `utp_plateau` — the rule set (36), derived.
* `utp_isUnboundedCircumambient` — the paper's definition (2), instantiated by UTP.
* `utp_not_isSubsequential` — the central theorem (§4.2, online appendix): no
  deterministic FST computes UTP in either direction, via
  `IsLeftSubsequential.bounded_delay` and the reversal symmetry `utp_reverse`.
* `utp_not_isBimachineWeaklyDeterministic` — §5.2, via `RequiresBothSides`: no union of
  one-sided rules expresses UTP's conjunctive trigger.
* `utp_markup_decomposition` — (43): with the mark `?`, UTP is right-subsequential after
  left-subsequential; weak determinism forbids exactly this enlargement.
* `readTBU_linearize_realize` — §4.4: the TBU string is the linearization of the realized
  AR ((37a)), so string look-ahead is timing-tier look-ahead.
* `links_realizeMerged_utp`, `upper_realizeMerged_utp` — the OCP-merged realization of
  the UTP output is a single H multiply linked to the `plateau`
  ([hyman-katamba-2010] (7)).
* `utp_fullyRegular` — §7: UTP is regular but neither subsequential nor weakly
  deterministic.

Contrast `Studies/MeinhardtEtAl2024`: ATR spreading is circumambient as covariation yet
weakly deterministic; UTP's `RequiresBothSides` pushes it above that bound.
-/

namespace Jardine2016Tone

open Subregular

/-! ### The string-based representation

Strings of timing-tier symbols, each recording one TBU's association state (§4.4). -/

/-- A tone-bearing unit (§4.1): `H` is a TBU associated to a H tone, `O` an unspecified
TBU (the paper's Ø). -/
inductive TBU
  | H
  | O
  deriving DecidableEq, Repr

/-- TBU `i` of `w` surfaces with a H tone: some H-toned TBU sits at a position `≤ i` and
some at a position `≥ i` — [hyman-katamba-2010]'s plateauing rule (7), pointwise. -/
def SurfacesH (w : List TBU) (i : ℕ) : Prop :=
  .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i

instance (w : List TBU) (i : ℕ) : Decidable (SurfacesH w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {w : List TBU} {i j k : ℕ}

/-- The unbounded tonal plateauing map (36): every TBU between two H-toned TBUs surfaces
as H; everything else is unchanged. -/
def utp (w : List TBU) : List TBU :=
  w.mapIdx fun i _ => if SurfacesH w i then .H else .O

@[simp] theorem utp_length : (utp w).length = w.length := by
  simp [utp]

theorem utp_getElem? :
    (utp w)[i]? = w[i]?.map fun _ => if SurfacesH w i then TBU.H else TBU.O := by
  simp [utp, List.getElem?_mapIdx]

private theorem mem_take_iff {α : Type*} {a : α} {w : List α} {k : ℕ} :
    a ∈ w.take k ↔ ∃ j < k, w[j]? = some a := by
  simp [List.mem_iff_getElem?, List.getElem?_take]

private theorem mem_drop_iff {α : Type*} {a : α} {w : List α} {k : ℕ} :
    a ∈ w.drop k ↔ ∃ j ≥ k, w[j]? = some a := by
  simp only [List.mem_iff_getElem?, List.getElem?_drop]
  exact ⟨fun ⟨t, ht⟩ => ⟨k + t, Nat.le_add_right k t, ht⟩,
    fun ⟨j, hkj, hj⟩ => ⟨j - k, by rwa [Nat.add_sub_cancel' hkj]⟩⟩

/-- Positionwise reading of `SurfacesH`: a H at some `j ≤ i` and a H at some `j ≥ i`. -/
theorem surfacesH_iff :
    SurfacesH w i ↔ (∃ j ≤ i, w[j]? = some .H) ∧ ∃ j ≥ i, w[j]? = some .H := by
  rw [SurfacesH, mem_take_iff, mem_drop_iff]
  simp [Nat.lt_succ_iff]

theorem SurfacesH.lt_length (h : SurfacesH w i) : i < w.length := by
  have h₂ := List.length_pos_of_mem h.2
  rw [List.length_drop] at h₂
  omega

/-- The surfacing set is convex: `take`/`drop` windows only widen. -/
theorem SurfacesH.of_le_of_le (hi : SurfacesH w i) (hk : SurfacesH w k) (hij : i ≤ j)
    (hjk : j ≤ k) : SurfacesH w j :=
  ⟨w.take_subset_take_left (by omega) hi.1, w.drop_subset_drop_left (by omega) hk.2⟩

/-- A H-toned TBU surfaces H: it flanks itself. -/
theorem surfacesH_of_getElem?_H (h : w[i]? = some .H) : SurfacesH w i :=
  surfacesH_iff.mpr ⟨⟨i, le_rfl, h⟩, ⟨i, le_rfl, h⟩⟩

theorem SurfacesH.H_mem (h : SurfacesH w i) : .H ∈ w := List.take_subset _ _ h.1

theorem utp_getElem?_H_iff : (utp w)[j]? = some .H ↔ SurfacesH w j := by
  rw [utp_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, -, ha⟩
    by_contra hs
    rw [if_neg hs] at ha
    exact TBU.noConfusion ha
  · exact fun hs => ⟨w[j]'hs.lt_length, List.getElem?_eq_getElem hs.lt_length, if_pos hs⟩

/-- The plateau of `w`: the set of positions that surface H. -/
def plateau (w : List TBU) : Finset ℕ := (Finset.range w.length).filter (SurfacesH w)

@[simp] theorem mem_plateau : j ∈ plateau w ↔ SurfacesH w j := by
  simp only [plateau, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact SurfacesH.lt_length

@[simp] theorem plateau_nonempty : (plateau w).Nonempty ↔ .H ∈ w := by
  constructor
  · rintro ⟨j, hj⟩
    exact (mem_plateau.mp hj).H_mem
  · intro hw
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    exact ⟨i, mem_plateau.mpr (surfacesH_of_getElem?_H hi)⟩

/-- `utp` writes the indicator word of its plateau. -/
theorem utp_eq_plateau_indicator :
    utp w = (List.range w.length).map fun i => if i ∈ plateau w then TBU.H else TBU.O := by
  refine List.ext_getElem (by simp [utp]) fun i h₁ h₂ => ?_
  simp [utp, mem_plateau]

/-- Sandwich characterization: a word with Hs at `lo` and `hi` and none outside
`[lo, hi]` has plateau exactly `Finset.Icc lo hi`. -/
theorem plateau_eq_Icc_of {lo hi : ℕ} (hlo : w[lo]? = some .H) (hhi : w[hi]? = some .H)
    (hb : ∀ j, w[j]? = some .H → lo ≤ j ∧ j ≤ hi) : plateau w = Finset.Icc lo hi := by
  ext j
  rw [mem_plateau, Finset.mem_Icc, surfacesH_iff]
  constructor
  · rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
    have hb₁ := hb j₁ h₁
    have hb₂ := hb j₂ h₂
    omega
  · exact fun hj => ⟨⟨lo, hj.1, hlo⟩, hi, hj.2, hhi⟩

/-- The plateau is an interval, from the first trigger to the last: the set form of
(36c). -/
theorem plateau_eq_Icc (hne : (plateau w).Nonempty) :
    plateau w = Finset.Icc ((plateau w).min' hne) ((plateau w).max' hne) := by
  ext j
  rw [Finset.mem_Icc]
  constructor
  · intro hj
    exact ⟨(plateau w).min'_le j hj, (plateau w).le_max' j hj⟩
  · rintro ⟨h₁, h₂⟩
    exact mem_plateau.mpr (SurfacesH.of_le_of_le
      (mem_plateau.mp ((plateau w).min'_mem hne))
      (mem_plateau.mp ((plateau w).max'_mem hne)) h₁ h₂)

/-- TBU `i` surfaces H iff it is itself a H or is strictly flanked: split the `take`
window at its last slot and the `drop` window at its head. -/
private theorem surfacesH_split {a : TBU} (h : w[i]? = some a) :
    SurfacesH w i ↔ a = .H ∨ (.H ∈ w.take i ∧ .H ∈ w.drop (i + 1)) := by
  rcases eq_or_ne a .H with rfl | ha
  · simp [surfacesH_of_getElem?_H h]
  · obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
    rw [SurfacesH, List.take_add_one, h, List.drop_eq_getElem_cons hi, hia]
    simp [ha, Ne.symm ha]

/-! ### The rule set (36)

The paper's three schemata for UTP, derived as theorems about `utp` rather than clauses
of its definition. -/

/-- (36a): a toneless word is unchanged. -/
theorem utp_toneless (n : ℕ) : utp (List.replicate n .O) = List.replicate n .O := by
  have h : plateau (List.replicate n TBU.O) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (by simp)
  simp [utp_eq_plateau_indicator, h, List.map_const']

/-- (36b): a word with a single H is unchanged — one H cannot trigger a plateau. -/
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

/-- (36c): everything between the outermost Hs surfaces H; the medial material `w` is
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

/-- The (43) sample rows: no plateau without two Hs; `HØØH ↦ HHHH`. -/
example : utp [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

/-! ### UTP is regular

§4.2 exhibits a nondeterministic FST (Fig. 5); here UTP is computed by a bimachine — one
deterministic pass per direction — so what fails below is one-directional determinism. -/

/-- The UTP bimachine: each side flags "a H occurs on my side"; a toneless cell surfaces
H exactly when both flags are set. -/
def utpBM : Bimachine Bool Bool TBU TBU :=
  .ofFlags (· == .H) (· == .H) fun l a r => if a == .H || (l && r) then .H else .O

/-- The bimachine computes UTP. -/
theorem utpBM_run : utpBM.run = utp := by
  funext w
  refine List.ext_getElem? fun i => ?_
  rw [utpBM, Bimachine.ofFlags_run_getElem?, utp_getElem?]
  cases h : w[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some]
    congr 1
    have hb : (a == TBU.H || ((w.take i).any (· == .H) && (w.drop (i + 1)).any (· == .H)))
        = true ↔ SurfacesH w i := by
      rw [surfacesH_split h]
      simp [List.any_eq_true]
    by_cases hs : SurfacesH w i
    · rw [if_pos (hb.mpr hs), if_pos hs]
    · rw [if_neg (fun hbt => hs (hb.mp hbt)), if_neg hs]

/-- UTP is regular (§4.2): computable by a finite bimachine. -/
theorem utp_isBimachineComputable : IsBimachineComputable utp :=
  utpBM_run ▸ isBimachineComputable utpBM

/-! ### UTP is unboundedly circumambient

The witness family for definition (2), at distance `d`: the plateau word `H Ø^(2d+2) H`
with target `d+1`; deleting either flanking H reverts it. -/

/-- The distance-`d` plateau word: Hs at positions `0` and `2d+3`, toneless in between. -/
def plateauBase (d : ℕ) : List TBU :=
  .H :: (List.replicate (2 * d + 2) .O ++ [.H])

@[simp] theorem plateauBase_length (d : ℕ) : (plateauBase d).length = 2 * d + 4 := by
  simp [plateauBase]

private theorem plateauBase_getElem?_H_iff (d : ℕ) {j : ℕ} :
    (plateauBase d)[j]? = some TBU.H ↔ j = 0 ∨ j = 2 * d + 3 := by
  cases j with
  | zero => simp [plateauBase]
  | succ t =>
    rw [plateauBase, List.getElem?_cons_succ]
    rcases lt_trichotomy t (2 * d + 2) with hj | rfl | hj
    · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_replicate, if_pos hj]
      simp
      omega
    · rw [List.getElem?_append_right (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp; omega)]
      have : 1 ≤ t - (List.replicate (2 * d + 2) TBU.O).length := by simp; omega
      rw [List.getElem?_eq_none (by simpa using this)]
      simp
      omega

private theorem plateauBase_getElem?_mid (d : ℕ) : (plateauBase d)[d + 1]? = some TBU.O := by
  rw [plateauBase, List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega),
    List.getElem?_replicate, if_pos (by omega)]

private theorem utp_plateauBase_mid (d : ℕ) : (utp (plateauBase d))[d + 1]? = some TBU.H :=
  utp_getElem?_H_iff.mpr <| surfacesH_iff.mpr
    ⟨⟨0, by omega, (plateauBase_getElem?_H_iff d).mpr (Or.inl rfl)⟩,
      2 * d + 3, by omega, (plateauBase_getElem?_H_iff d).mpr (Or.inr rfl)⟩

private theorem utp_set_perturbed (d : ℕ) {pos : ℕ} (hpos : pos = 0 ∨ pos = 2 * d + 3) :
    (utp ((plateauBase d).set pos .O))[d + 1]? = some TBU.O := by
  have hmid : ((plateauBase d).set pos TBU.O)[d + 1]? = some TBU.O := by
    rw [List.getElem?_set_ne (by omega)]
    exact plateauBase_getElem?_mid d
  rw [utp_getElem?, hmid, Option.map_some, if_neg]
  rw [surfacesH_iff]
  rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
  have key : ∀ j, ((plateauBase d).set pos TBU.O)[j]? = some TBU.H
      → j ≠ pos ∧ (j = 0 ∨ j = 2 * d + 3) := fun j hj => by
    rcases eq_or_ne j pos with rfl | hne
    · rw [List.getElem?_set_self (by simp only [plateauBase_length]; omega)] at hj
      simp at hj
    · rw [List.getElem?_set_ne (Ne.symm hne)] at hj
      exact ⟨hne, (plateauBase_getElem?_H_iff d).mp hj⟩
  have k₁ := key _ h₁
  have k₂ := key _ h₂
  omega

/-- UTP requires both sides ([heinz-lai-2013]): deleting either flanking H reverts the
plateau target. -/
theorem utp_requiresBothSides : RequiresBothSides utp := by
  intro d
  refine ⟨plateauBase d, d + 1, by simp only [plateauBase_length]; omega, ?_, ?_, ?_⟩
  · rw [utp_plateauBase_mid, plateauBase_getElem?_mid]
    simp
  · refine ⟨(plateauBase d).set 0 .O, by simp,
      fun k hk => (List.getElem?_set_ne (by omega)).symm, List.getElem?_set_ne (by omega), ?_⟩
    rw [utp_set_perturbed d (Or.inl rfl), List.getElem?_set_ne (by omega),
      plateauBase_getElem?_mid]
  · refine ⟨(plateauBase d).set (2 * d + 3) .O, by simp,
      fun k hk => (List.getElem?_set_ne (by omega)).symm, List.getElem?_set_ne (by omega), ?_⟩
    rw [utp_set_perturbed d (Or.inr rfl), List.getElem?_set_ne (by omega),
      plateauBase_getElem?_mid]

/-- UTP is an unbounded circumambient process (definition (2)). -/
theorem utp_isUnboundedCircumambient : IsUnboundedCircumambient utp :=
  utp_requiresBothSides.isUnboundedCircumambient

/-! ### UTP is not subsequential

The paper's central theorem (§4.2, online appendix), by bounded delay: a left machine
reading `H Øⁿ` has emitted at most one symbol (`utp (H Øⁿ) = H Øⁿ` and
`utp (H Øⁿ H) = H^(n+2)` diverge at position 1), so it withholds `n` symbols. -/

/-- UTP is not left-subsequential (§4.2, online appendix). -/
theorem utp_not_isLeftSubsequential : ¬ IsLeftSubsequential utp := by
  refine not_isLeftSubsequential_of_diverging fun N =>
    ⟨.H :: List.replicate (N + 1) .O, [.H], 1, ?_, ?_⟩
  · simp only [utp_length, List.length_cons, List.length_replicate]
    omega
  · -- image of `H Ø^(N+1)`: itself, by (36b); of `H Ø^(N+1) H`: a total plateau, by (36c)
    have h1 : (utp (TBU.H :: List.replicate (N + 1) TBU.O))[1]? = some TBU.O := by
      rw [show (TBU.H :: List.replicate (N + 1) TBU.O)
            = List.replicate 0 TBU.O ++ TBU.H :: List.replicate (N + 1) TBU.O by simp,
        utp_single]
      simp only [List.replicate_zero, List.nil_append]
      rw [List.getElem?_cons_succ, List.getElem?_replicate, if_pos (by omega)]
    have h2 : (utp ((TBU.H :: List.replicate (N + 1) TBU.O) ++ [TBU.H]))[1]? = some TBU.H := by
      rw [show (TBU.H :: List.replicate (N + 1) TBU.O) ++ [TBU.H]
            = List.replicate 0 TBU.O ++ TBU.H :: (List.replicate (N + 1) TBU.O
                ++ TBU.H :: List.replicate 0 TBU.O) by simp,
        utp_plateau]
      simp only [List.replicate_zero, List.nil_append, List.append_nil, List.length_replicate]
      rw [List.getElem?_replicate, if_pos (by omega)]
    rw [h1, h2]
    simp

/-- Plateauing is symmetric under string reversal. -/
theorem utp_reverse : utp w.reverse = (utp w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · have hrl : (utp w).length = w.length := utp_length
    rw [utp_getElem?, List.getElem?_reverse (by simpa using hi),
      List.getElem?_reverse (by simpa [hrl] using hi), hrl, utp_getElem?]
    have hiff : SurfacesH w.reverse i ↔ SurfacesH w (w.length - 1 - i) := by
      rw [surfacesH_iff, surfacesH_iff]
      constructor
      · rintro ⟨⟨j₁, hj₁, h₁⟩, ⟨j₂, hj₂, h₂⟩⟩
        obtain ⟨hlt₁, -⟩ := List.getElem?_eq_some_iff.mp h₁
        obtain ⟨hlt₂, -⟩ := List.getElem?_eq_some_iff.mp h₂
        simp only [List.length_reverse] at hlt₁ hlt₂
        rw [List.getElem?_reverse (by simpa using hlt₁)] at h₁
        rw [List.getElem?_reverse (by simpa using hlt₂)] at h₂
        exact ⟨⟨w.length - 1 - j₂, by omega, h₂⟩, ⟨w.length - 1 - j₁, by omega, h₁⟩⟩
      · rintro ⟨⟨j₁, hj₁, h₁⟩, ⟨j₂, hj₂, h₂⟩⟩
        obtain ⟨hlt₁, -⟩ := List.getElem?_eq_some_iff.mp h₁
        obtain ⟨hlt₂, -⟩ := List.getElem?_eq_some_iff.mp h₂
        refine ⟨⟨w.length - 1 - j₂, by omega, ?_⟩, ⟨w.length - 1 - j₁, by omega, ?_⟩⟩
        · rw [List.getElem?_reverse (by omega), show w.length - 1 - (w.length - 1 - j₂) = j₂ by omega]
          exact h₂
        · rw [List.getElem?_reverse (by omega), show w.length - 1 - (w.length - 1 - j₁) = j₁ by omega]
          exact h₁
    rw [show (if SurfacesH w.reverse i then TBU.H else TBU.O)
          = (if SurfacesH w (w.length - 1 - i) then TBU.H else TBU.O) by simp [hiff]]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- UTP is not right-subsequential: by the reversal symmetry, a right machine faces the
mirror-image unbounded look-ahead. -/
theorem utp_not_isRightSubsequential : ¬ IsRightSubsequential utp := by
  intro hf
  rw [isRightSubsequential_iff_left_reverse] at hf
  have heq : (fun xs : List TBU => (utp xs.reverse).reverse) = utp := by
    funext xs
    rw [utp_reverse, List.reverse_reverse]
  exact utp_not_isLeftSubsequential (heq ▸ hf)

/-- UTP is subsequential in neither direction. -/
theorem utp_not_isSubsequential : ∀ d, ¬ IsSubsequential d utp
  | .left => utp_not_isLeftSubsequential
  | .right => utp_not_isRightSubsequential

/-! ### UTP is not weakly deterministic

Under the non-interacting-bimachine rendering of [heinz-lai-2013]'s weak determinism,
§5.2's claim is a theorem: UTP `RequiresBothSides`, which no union of one-sided rules
expresses. -/

/-- UTP is not weakly deterministic (§5.2). -/
theorem utp_not_isBimachineWeaklyDeterministic : ¬ IsBimachineWeaklyDeterministic utp :=
  not_isBimachineWeaklyDeterministic_of_requiresBothSides utp_requiresBothSides

/-! ### The (43) mark-up decomposition

With one extra symbol the two-pass decomposition exists: a left pass marks every
toneless TBU after a H with `?`; a right pass resolves `?` by whether a H follows. The
mark is exactly the alphabet enlargement weak determinism disallows, so with the
impossibility theorem this locates UTP precisely. -/

/-- The mark-up alphabet of (43): `Q` is the paper's `?`. -/
inductive Mark
  | H
  | O
  | Q
  deriving DecidableEq, Repr

/-- Left pass of (43): mark every toneless TBU after a H with `?`. -/
def markLeft : Mealy Bool TBU Mark :=
  .ofFlag (· == .H) fun l a =>
    match a with
    | .H => .H
    | .O => if l then .Q else .O

/-- Right pass of (43): resolve `?` to H when a H follows, else to Ø. -/
def resolveRight : Mealy Bool Mark TBU :=
  .ofFlag (· == .H) fun r a =>
    match a with
    | .H => .H
    | .O => .O
    | .Q => if r then .H else .O

/-- The right pass as a right-to-left string function: reverse, run, reverse. -/
def resolve (x : List Mark) : List TBU := (resolveRight.run x.reverse).reverse

private theorem markLeft_run_H_iff (w : List TBU) (j : ℕ) :
    (markLeft.run w)[j]? = some Mark.H ↔ w[j]? = some TBU.H := by
  rw [markLeft, Mealy.ofFlag_run_getElem?]
  cases hv : w[j]? with
  | none => simp
  | some a => cases a <;> simp [ite_eq_iff]

/-- The (43) decomposition computes UTP. -/
theorem utp_eq_resolve_mark (w : List TBU) : utp w = resolve (markLeft.run w) := by
  have hmark : ∀ i : ℕ, Mark.H ∈ (markLeft.run w).drop (i + 1) ↔ TBU.H ∈ w.drop (i + 1) :=
    fun i => by simp only [mem_drop_iff, markLeft_run_H_iff]
  refine List.ext_getElem? fun i => ?_
  rw [utp_getElem?, resolve, resolveRight, Mealy.ofFlag_run_reverse_getElem?]
  simp only [List.any_beq', List.contains_eq_mem, decide_eq_decide.mpr (hmark i)]
  rw [markLeft, Mealy.ofFlag_run_getElem?, Option.map_map]
  simp only [List.any_beq', List.contains_eq_mem]
  cases ha : w[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Function.comp_apply]
    congr 1
    cases a with
    | H => simp [surfacesH_of_getElem?_H ha]
    | O =>
      by_cases hL : TBU.H ∈ w.take i <;> by_cases hR : TBU.H ∈ w.drop (i + 1) <;>
        simp [surfacesH_split ha, hL, hR]

/-- The (43) mark-up decomposition (§5.2): over the `?`-enlarged alphabet, UTP is a
right-subsequential map after a left-subsequential map. -/
theorem utp_markup_decomposition :
    IsLeftSubsequential markLeft.run ∧ IsRightSubsequential resolve
      ∧ utp = resolve ∘ markLeft.run := by
  refine ⟨markLeft.isLetterLeftSubsequential.isLeftSubsequential, ?_,
    funext utp_eq_resolve_mark⟩
  rw [isRightSubsequential_iff_left_reverse]
  have heq : (fun xs : List Mark => (resolve xs.reverse).reverse) = resolveRight.run := by
    funext xs
    rw [resolve, List.reverse_reverse, List.reverse_reverse]
  exact heq ▸ resolveRight.isLetterLeftSubsequential.isLeftSubsequential

/-! ### The autosegmental grounding ((40), §4.4)

The string representation is the linearisation of the autosegmental one: `toAR` is the
paper's (40) translation, and by `Autosegmental.linearize_realize` the association-state
string of the realized AR is the input string. So the TBU string is recoverable from the
AR ((37a)) and string look-ahead is timing-tier look-ahead ((37b)). -/

section AutosegmentalGrounding

open Autosegmental

/-- The (40) translation: a H-toned TBU is one H melody node linked to its timing unit;
a toneless TBU is a bare timing unit. -/
def toAR : TBU → AR Tone.TRN Unit
  | .H => .single Tone.TRN.H ()
  | .O => .bare ()

theorem linearize_realize_toAR (w : List TBU) :
    (realize toAR w).linearize
      = w.map fun a => ((), if a = .H then [Tone.TRN.H] else []) := by
  rw [linearize_realize]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.flatMap_cons, List.map_cons, ih]
    cases a <;> simp [toAR]

/-- Read a timing unit's association state back as a TBU symbol. -/
def readTBU (s : Unit × List Tone.TRN) : TBU := if s.2.isEmpty then .O else .H

/-- (37a): the TBU string is recoverable from the realized AR, so the complexity results
transfer to the autosegmental analysis. -/
theorem readTBU_linearize_realize (w : List TBU) :
    ((realize toAR w).linearize).map readTBU = w := by
  rw [linearize_realize_toAR, List.map_map]
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left fun a ha => ?_
  cases a <;> rfl

/-! #### The fused plateau ([hyman-katamba-2010] (7))

The OCP-merging realization `Autosegmental.realizeMerged` fuses the plateau's run of H
nodes into one, giving [hyman-katamba-2010]'s output representation (7): a single H
autosegment multiply linked to exactly the `plateau`, over an unchanged timing tier. -/

private theorem upper_realize_toAR (v : List TBU) :
    (realize toAR v).upper.toList = List.replicate (v.count .H) Tone.TRN.H := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [realize_cons, AR.concat_upper, LabeledTuple.toList_concat, ih]
    cases a <;> simp [toAR, List.replicate_succ]

theorem mem_links_realizeMerged_utp (p : ℕ × ℕ) :
    p ∈ (realizeMerged toAR (utp w)).links ↔ p.1 = 0 ∧ SurfacesH w p.2 := by
  have hL : ∀ j, (realize toAR (utp w)).toGraph.IsLinkedLower j ↔ SurfacesH w j := fun j => by
    rw [AR.isLinkedLower_iff_linearize, linearize_realize_toAR, ← utp_getElem?_H_iff]
    cases hv : (utp w)[j]? with
    | none => simp [List.getElem?_map, hv]
    | some a => cases a <;> simp [List.getElem?_map, hv]
  rw [realizeMerged_def,
    mem_links_collapseAR_of_upper_replicate (upper_realize_toAR (utp w)), hL]

/-- Multiple association ((7)): the merged realization links melody node `0` to exactly
the `plateau`. Unconditional: a toneless word has an empty plateau and no lines. -/
theorem links_realizeMerged_utp :
    (realizeMerged toAR (utp w)).links = {0} ×ˢ plateau w := by
  ext ⟨k, j⟩
  rw [mem_links_realizeMerged_utp]
  simp [and_comm, eq_comm]

/-- The timing tier survives the merge: one slot per input TBU. -/
theorem lower_realizeMerged_utp :
    (realizeMerged toAR (utp w)).lower.toList = List.replicate w.length () := by
  rw [realizeMerged_def, collapseAR_lower]
  have h := List.eq_replicate_of_mem
    (l := (realize toAR (utp w)).lower.toList) (a := ()) fun _ _ => rfl
  rwa [LabeledTuple.toList_length, ← AR.linearize_length, linearize_realize_toAR,
    List.length_map, utp_length] at h

/-- The fused plateau ((7)): with at least one H, the merged melody tier is a single H
autosegment. -/
theorem upper_realizeMerged_utp (hw : .H ∈ w) :
    (realizeMerged toAR (utp w)).upper.toList = [Tone.TRN.H] := by
  obtain ⟨m, hm⟩ : ∃ m, (utp w).count .H = m + 1 := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    have := List.count_pos_iff.mpr <| List.mem_iff_getElem?.mpr
      ⟨i, utp_getElem?_H_iff.mpr (surfacesH_of_getElem?_H hi)⟩
    exact ⟨(utp w).count .H - 1, by omega⟩
  rw [realizeMerged_def, upper_collapseAR, upper_realize_toAR, hm, OCP.collapse_replicate]

/-- (7) concretely: `HØØH` fuses to one H linked to all four TBUs. -/
example :
    (realizeMerged toAR (utp [.H, .O, .O, .H])).links
      = {(0, 0), (0, 1), (0, 2), (0, 3)} := by decide

end AutosegmentalGrounding

/-- Computationally, tone is different (§7): UTP is fully regular — regular but neither
subsequential in either direction nor weakly deterministic, the bound segmental
phonology respects. -/
theorem utp_fullyRegular :
    IsBimachineComputable utp ∧ (∀ d, ¬ IsSubsequential d utp)
      ∧ ¬ IsBimachineWeaklyDeterministic utp :=
  ⟨utp_isBimachineComputable, utp_not_isSubsequential, utp_not_isBimachineWeaklyDeterministic⟩

end Jardine2016Tone
