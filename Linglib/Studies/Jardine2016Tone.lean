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
import Linglib.Phonology.Autosegmental.Constructions
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
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    have hjk : j < k := by
      by_contra hge
      rw [List.getElem?_take_eq_none (le_of_not_gt hge)] at hj
      simp at hj
    exact ⟨j, hjk, by rwa [List.getElem?_take_of_lt hjk] at hj⟩
  · rintro ⟨j, hjk, hj⟩
    exact ⟨j, by rwa [List.getElem?_take_of_lt hjk]⟩

private theorem mem_drop_iff {α : Type*} {a : α} {w : List α} {k : ℕ} :
    a ∈ w.drop k ↔ ∃ j, k ≤ j ∧ w[j]? = some a := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨k + t, Nat.le_add_right k t, by rwa [List.getElem?_drop] at ht⟩
  · rintro ⟨j, hkj, hj⟩
    exact ⟨j - k, by rw [List.getElem?_drop, Nat.add_sub_cancel' hkj]; exact hj⟩

/-- Positionwise reading of `SurfacesH`: a H at some `j ≤ i` and a H at some `j ≥ i`. -/
theorem surfacesH_iff :
    SurfacesH w i ↔ (∃ j ≤ i, w[j]? = some .H) ∧ ∃ j, i ≤ j ∧ w[j]? = some .H := by
  rw [SurfacesH, mem_take_iff, mem_drop_iff]
  simp [Nat.lt_succ_iff]

theorem SurfacesH.lt_length (h : SurfacesH w i) : i < w.length := by
  obtain ⟨-, j, hij, hj⟩ := surfacesH_iff.mp h
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
  omega

/-- The surfacing set is convex. -/
theorem SurfacesH.of_le_of_le (hi : SurfacesH w i) (hk : SurfacesH w k) (hij : i ≤ j)
    (hjk : j ≤ k) : SurfacesH w j := by
  obtain ⟨⟨j₁, hj₁, h₁⟩, -⟩ := surfacesH_iff.mp hi
  obtain ⟨-, j₂, hj₂, h₂⟩ := surfacesH_iff.mp hk
  exact surfacesH_iff.mpr ⟨⟨j₁, by omega, h₁⟩, ⟨j₂, by omega, h₂⟩⟩

/-- A H-toned TBU surfaces H: it flanks itself. -/
theorem surfacesH_of_getElem?_H (h : w[i]? = some .H) : SurfacesH w i :=
  surfacesH_iff.mpr ⟨⟨i, le_rfl, h⟩, ⟨i, le_rfl, h⟩⟩

theorem utp_getElem?_H_iff : (utp w)[j]? = some .H ↔ SurfacesH w j := by
  rw [utp_getElem?]
  cases hw : w[j]? with
  | none =>
    refine iff_of_false (by simp) fun hs => ?_
    rw [List.getElem?_eq_none_iff] at hw
    exact absurd hs.lt_length (by omega)
  | some a =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h
      by_contra hs
      rw [if_neg hs] at h
      exact TBU.noConfusion h
    · intro hs
      rw [if_pos hs]

/-- The plateau of `w`: the set of positions that surface H. -/
def plateau (w : List TBU) : Finset ℕ := (Finset.range w.length).filter (SurfacesH w)

@[simp] theorem mem_plateau : j ∈ plateau w ↔ SurfacesH w j := by
  unfold plateau
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.lt_length, h⟩⟩

@[simp] theorem plateau_nonempty : (plateau w).Nonempty ↔ .H ∈ w := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨⟨j₁, -, h₁⟩, -⟩ := surfacesH_iff.mp (mem_plateau.mp hj)
    exact List.mem_iff_getElem?.mpr ⟨j₁, h₁⟩
  · intro hw
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    exact ⟨i, mem_plateau.mpr (surfacesH_of_getElem?_H hi)⟩

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

/-- TBU `i` surfaces H iff it is itself a H or is strictly flanked. -/
private theorem surfacesH_split {a : TBU} (h : w[i]? = some a) :
    SurfacesH w i ↔ a = .H ∨ (.H ∈ w.take i ∧ .H ∈ w.drop (i + 1)) := by
  rw [surfacesH_iff]
  constructor
  · rintro ⟨⟨j₁, hj₁, h₁⟩, ⟨j₂, hj₂, h₂⟩⟩
    by_cases ha : a = TBU.H
    · exact Or.inl ha
    · refine Or.inr ⟨mem_take_iff.mpr ⟨j₁, ?_, h₁⟩, mem_drop_iff.mpr ⟨j₂, ?_, h₂⟩⟩
      · rcases Nat.lt_or_ge j₁ i with hlt | hge
        · exact hlt
        · obtain rfl : j₁ = i := by omega
          rw [h] at h₁
          exact absurd (Option.some.inj h₁) ha
      · rcases Nat.lt_or_ge i j₂ with hlt | hge
        · omega
        · obtain rfl : j₂ = i := by omega
          rw [h] at h₂
          exact absurd (Option.some.inj h₂) ha
  · rintro (rfl | ⟨h₁, h₂⟩)
    · exact ⟨⟨i, le_rfl, h⟩, ⟨i, le_rfl, h⟩⟩
    · obtain ⟨j₁, hj₁, hh₁⟩ := mem_take_iff.mp h₁
      obtain ⟨j₂, hj₂, hh₂⟩ := mem_drop_iff.mp h₂
      exact ⟨⟨j₁, by omega, hh₁⟩, ⟨j₂, by omega, hh₂⟩⟩

/-! ### The rule set (36)

The paper's three schemata for UTP, derived as theorems about `utp` rather than clauses
of its definition. -/

private theorem singleH_getElem?_H_iff (m n : ℕ) :
    (List.replicate m TBU.O ++ TBU.H :: List.replicate n TBU.O)[j]? = some TBU.H ↔ j = m := by
  rcases lt_trichotomy j m with hj | rfl | hj
  · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_replicate]
    simp [hj]
    omega
  · rw [List.getElem?_append_right (by simp)]
    simp
  · rw [List.getElem?_append_right (by simp; omega)]
    obtain ⟨t, ht⟩ : ∃ t, j - (List.replicate m TBU.O).length = t + 1 := ⟨j - m - 1, by simp; omega⟩
    rw [ht, List.getElem?_cons_succ, List.getElem?_replicate]
    simp
    omega

/-- (36a): a toneless word is unchanged. -/
theorem utp_toneless (n : ℕ) : utp (List.replicate n .O) = List.replicate n .O := by
  refine List.ext_getElem? fun i => ?_
  rw [utp_getElem?]
  cases h : (List.replicate n TBU.O)[i]? with
  | none => rfl
  | some a =>
    have ha : a = TBU.O := by
      rw [List.getElem?_replicate] at h
      split at h <;> simp_all
    have hs : ¬ SurfacesH (List.replicate n TBU.O) i := by
      rw [surfacesH_iff]
      rintro ⟨⟨j, -, hj⟩, -⟩
      rw [List.getElem?_replicate] at hj
      split at hj <;> simp_all
    simp [hs, ha]

/-- (36b): a word with a single H is unchanged — one H cannot trigger a plateau. -/
theorem utp_single (m n : ℕ) :
    utp (List.replicate m .O ++ .H :: List.replicate n .O)
      = List.replicate m .O ++ .H :: List.replicate n .O := by
  refine List.ext_getElem? fun i => ?_
  rw [utp_getElem?]
  cases h : (List.replicate m TBU.O ++ TBU.H :: List.replicate n TBU.O)[i]? with
  | none => rfl
  | some a =>
    have hS : SurfacesH (List.replicate m TBU.O ++ TBU.H :: List.replicate n TBU.O) i ↔ i = m := by
      rw [surfacesH_iff]
      constructor
      · rintro ⟨⟨j₁, hj₁, h₁⟩, ⟨j₂, hj₂, h₂⟩⟩
        rw [singleH_getElem?_H_iff] at h₁ h₂
        omega
      · rintro rfl
        exact ⟨⟨_, le_rfl, (singleH_getElem?_H_iff _ n).mpr rfl⟩,
               ⟨_, le_rfl, (singleH_getElem?_H_iff _ n).mpr rfl⟩⟩
    by_cases him : i = m
    · subst him
      have : a = TBU.H := by
        have := (singleH_getElem?_H_iff i n).mpr rfl
        rw [h] at this
        exact Option.some.inj this
      simp [hS, this]
    · have : a = TBU.O := by
        cases a with
        | H => exact absurd ((singleH_getElem?_H_iff m n).mp h) him
        | O => rfl
      simp [hS, him, this]

private theorem plateau_getElem?_first (m p : ℕ) (w : List TBU) :
    (List.replicate m TBU.O ++ TBU.H :: (w ++ TBU.H :: List.replicate p TBU.O))[m]?
      = some TBU.H := by
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem plateau_getElem?_second (m p : ℕ) (w : List TBU) :
    (List.replicate m TBU.O ++ TBU.H :: (w ++ TBU.H :: List.replicate p TBU.O))[m + 1 + w.length]?
      = some TBU.H := by
  rw [List.getElem?_append_right (by simp; omega)]
  obtain ⟨t, ht⟩ : ∃ t, m + 1 + w.length - (List.replicate m TBU.O).length = t + 1 :=
    ⟨w.length, by simp; omega⟩
  rw [ht, List.getElem?_cons_succ]
  have htw : t = w.length := by simp at ht; omega
  rw [htw, List.getElem?_append_right le_rfl]
  simp

private theorem plateau_getElem?_H_bounds {m p : ℕ}
    (h : (List.replicate m TBU.O ++ TBU.H :: (w ++ TBU.H :: List.replicate p TBU.O))[j]?
      = some TBU.H) :
    m ≤ j ∧ j ≤ m + 1 + w.length := by
  constructor
  · by_contra hlt
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate] at h
    split at h <;> simp_all
  · by_contra hgt
    rw [List.getElem?_append_right (by simp; omega)] at h
    obtain ⟨t, ht⟩ : ∃ t, j - (List.replicate m TBU.O).length = t + 1 := ⟨j - m - 1, by simp; omega⟩
    rw [ht, List.getElem?_cons_succ] at h
    have htw : w.length < t := by simp at ht; omega
    rw [List.getElem?_append_right (by omega)] at h
    obtain ⟨s, hs⟩ : ∃ s, t - w.length = s + 1 := ⟨t - w.length - 1, by omega⟩
    rw [hs, List.getElem?_cons_succ, List.getElem?_replicate] at h
    split at h <;> simp_all

/-- (36c): everything between the outermost Hs surfaces H; the medial material `w` is
arbitrary. -/
theorem utp_plateau (m p : ℕ) (w : List TBU) :
    utp (List.replicate m .O ++ .H :: (w ++ .H :: List.replicate p .O))
      = List.replicate m .O ++ (List.replicate (w.length + 2) .H ++ List.replicate p .O) := by
  set u := List.replicate m TBU.O ++ TBU.H :: (w ++ TBU.H :: List.replicate p TBU.O) with hu
  have hlen : u.length = m + 1 + w.length + 1 + p := by simp [hu]; omega
  have hS : ∀ i, SurfacesH u i ↔ m ≤ i ∧ i ≤ m + 1 + w.length := fun i => by
    rw [surfacesH_iff]
    constructor
    · rintro ⟨⟨j₁, hj₁, h₁⟩, ⟨j₂, hj₂, h₂⟩⟩
      have b₁ := plateau_getElem?_H_bounds h₁
      have b₂ := plateau_getElem?_H_bounds h₂
      omega
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨m, h₁, plateau_getElem?_first m p w⟩,
             ⟨m + 1 + w.length, h₂, plateau_getElem?_second m p w⟩⟩
  refine List.ext_getElem? fun i => ?_
  rw [utp_getElem?]
  rcases Nat.lt_or_ge i m with h1 | h1
  · -- leading toneless stretch: unchanged `O`
    have hui : u[i]? = some TBU.O := by
      rw [List.getElem?_append_left (by simpa using h1), List.getElem?_replicate, if_pos h1]
    rw [hui, Option.map_some, if_neg ((hS i).not.mpr (by omega)),
      List.getElem?_append_left (by simpa using h1), List.getElem?_replicate, if_pos h1]
  rcases Nat.lt_or_ge i (m + 1 + w.length + 1) with h2 | h2
  · -- the plateau band: everything surfaces H
    have hui : i < u.length := by omega
    rw [List.getElem?_eq_getElem hui, Option.map_some, if_pos ((hS i).mpr ⟨h1, by omega⟩),
      List.getElem?_append_right (by simpa using h1),
      List.getElem?_append_left (by simp only [List.length_replicate]; omega),
      List.getElem?_replicate, if_pos (by simp only [List.length_replicate]; omega)]
  rcases Nat.lt_or_ge i u.length with h3 | h3
  · -- trailing toneless stretch: unchanged `O`
    have hui : u[i]? = some TBU.O := by
      rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
      obtain ⟨t, ht⟩ : ∃ t, i - (List.replicate m TBU.O).length = t + 1 :=
        ⟨i - m - 1, by simp only [List.length_replicate]; omega⟩
      rw [ht, List.getElem?_cons_succ]
      have htw : w.length < t := by simp only [List.length_replicate] at ht; omega
      rw [List.getElem?_append_right (by omega)]
      obtain ⟨s, hs⟩ : ∃ s, t - w.length = s + 1 := ⟨t - w.length - 1, by omega⟩
      rw [hs, List.getElem?_cons_succ, List.getElem?_replicate,
        if_pos (by simp only [List.length_replicate] at ht; omega)]
    rw [hui, Option.map_some, if_neg ((hS i).not.mpr (by omega)),
      List.getElem?_append_right (by simp only [List.length_replicate]; omega),
      List.getElem?_append_right (by simp only [List.length_replicate]; omega),
      List.getElem?_replicate, if_pos (by simp only [List.length_replicate]; omega)]
  · -- past the end: both sides `none`
    rw [List.getElem?_eq_none (by omega), Option.map_none,
      List.getElem?_eq_none (by simp only [List.length_append, List.length_replicate]; omega)]

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

private theorem utp_plateauBase_mid (d : ℕ) : (utp (plateauBase d))[d + 1]? = some TBU.H := by
  rw [utp_getElem?, plateauBase_getElem?_mid, Option.map_some, if_pos]
  rw [surfacesH_iff]
  exact ⟨⟨0, by omega, (plateauBase_getElem?_H_iff d).mpr (Or.inl rfl)⟩,
         ⟨2 * d + 3, by omega, (plateauBase_getElem?_H_iff d).mpr (Or.inr rfl)⟩⟩

private theorem utp_left_perturbed (d : ℕ) :
    (utp ((plateauBase d).set 0 .O))[d + 1]? = some TBU.O := by
  have hmid : ((plateauBase d).set 0 TBU.O)[d + 1]? = some TBU.O := by
    rw [List.getElem?_set_ne (by omega)]
    exact plateauBase_getElem?_mid d
  rw [utp_getElem?, hmid, Option.map_some, if_neg]
  rw [surfacesH_iff]
  rintro ⟨⟨j, hj, hH⟩, -⟩
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [List.getElem?_set_self (by simp)] at hH
    simp at hH
  · rw [List.getElem?_set_ne (Ne.symm hj0)] at hH
    rcases (plateauBase_getElem?_H_iff d).mp hH with rfl | rfl
    · exact hj0 rfl
    · omega

private theorem utp_right_perturbed (d : ℕ) :
    (utp ((plateauBase d).set (2 * d + 3) .O))[d + 1]? = some TBU.O := by
  have hmid : ((plateauBase d).set (2 * d + 3) TBU.O)[d + 1]? = some TBU.O := by
    rw [List.getElem?_set_ne (by omega)]
    exact plateauBase_getElem?_mid d
  rw [utp_getElem?, hmid, Option.map_some, if_neg]
  rw [surfacesH_iff]
  rintro ⟨-, ⟨j, hj, hH⟩⟩
  rcases eq_or_ne j (2 * d + 3) with rfl | hj0
  · rw [List.getElem?_set_self (by simp)] at hH
    simp at hH
  · rw [List.getElem?_set_ne (Ne.symm hj0)] at hH
    rcases (plateauBase_getElem?_H_iff d).mp hH with rfl | rfl
    · omega
    · exact hj0 rfl

/-- UTP requires both sides ([heinz-lai-2013]): deleting either flanking H reverts the
plateau target. -/
theorem utp_requiresBothSides : RequiresBothSides utp := by
  intro d
  refine ⟨plateauBase d, d + 1, by simp only [plateauBase_length]; omega, ?_, ?_, ?_⟩
  · rw [utp_plateauBase_mid, plateauBase_getElem?_mid]
    simp
  · refine ⟨(plateauBase d).set 0 .O, by simp,
      fun k hk => (List.getElem?_set_ne (by omega)).symm, List.getElem?_set_ne (by omega), ?_⟩
    rw [utp_left_perturbed, List.getElem?_set_ne (by omega), plateauBase_getElem?_mid]
  · refine ⟨(plateauBase d).set (2 * d + 3) .O, by simp,
      fun k hk => (List.getElem?_set_ne (by omega)).symm, List.getElem?_set_ne (by omega), ?_⟩
    rw [utp_right_perturbed, List.getElem?_set_ne (by omega), plateauBase_getElem?_mid]

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
def markLeft : Mealy Bool TBU Mark where
  initial := false
  step l a :=
    match a with
    | .H => (true, .H)
    | .O => (l, if l then .Q else .O)

/-- Right pass of (43): resolve `?` to H when a H follows, else to Ø. -/
def resolveRight : Mealy Bool Mark TBU where
  initial := false
  step r a :=
    match a with
    | .H => (true, .H)
    | .O => (r, .O)
    | .Q => (r, if r then .H else .O)

/-- The right pass as a right-to-left string function: reverse, run, reverse. -/
def resolve (x : List Mark) : List TBU := (resolveRight.run x.reverse).reverse

private theorem markLeft_stateAfter (b : Bool) (pre : List TBU) :
    markLeft.stateAfter b pre = (b || pre.any (· == .H)) := by
  induction pre generalizing b with
  | nil => simp
  | cons x xs ih =>
    rw [Mealy.stateAfter_cons]
    cases x with
    | H => rw [show (markLeft.step b .H).1 = true from rfl, ih]; simp
    | O =>
      rw [show (markLeft.step b .O).1 = b from rfl, ih]
      simp only [List.any_cons, show (TBU.O == TBU.H) = false from rfl, Bool.false_or]

private theorem resolveRight_stateAfter (b : Bool) (pre : List Mark) :
    resolveRight.stateAfter b pre = (b || pre.any (· == .H)) := by
  induction pre generalizing b with
  | nil => simp
  | cons x xs ih =>
    rw [Mealy.stateAfter_cons]
    cases x with
    | H => rw [show (resolveRight.step b .H).1 = true from rfl, ih]; simp
    | O =>
      rw [show (resolveRight.step b .O).1 = b from rfl, ih]
      simp only [List.any_cons, show (Mark.O == Mark.H) = false from rfl, Bool.false_or]
    | Q =>
      rw [show (resolveRight.step b .Q).1 = b from rfl, ih]
      simp only [List.any_cons, show (Mark.Q == Mark.H) = false from rfl, Bool.false_or]

private theorem markLeft_run_getElem? (w : List TBU) (i : ℕ) :
    (markLeft.run w)[i]?
      = w[i]?.map fun a =>
          match a with
          | .H => Mark.H
          | .O => if (w.take i).any (· == .H) then Mark.Q else Mark.O := by
  rw [show markLeft.run w = markLeft.runFrom markLeft.initial w from rfl,
    Mealy.runFrom_getElem?]
  cases h : w[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some]
    congr 1
    cases a with
    | H => rfl
    | O =>
      show (if markLeft.stateAfter markLeft.initial (w.take i) = true
          then Mark.Q else Mark.O) = _
      rw [markLeft_stateAfter, show markLeft.initial = false from rfl]
      simp

private theorem markLeft_run_H_iff (w : List TBU) (j : ℕ) :
    (markLeft.run w)[j]? = some Mark.H ↔ w[j]? = some TBU.H := by
  rw [markLeft_run_getElem?]
  cases h : w[j]? with
  | none => simp
  | some a =>
    cases a with
    | H => simp
    | O =>
      simp only [Option.map_some]
      constructor
      · intro hc
        exfalso
        split at hc <;> exact Mark.noConfusion (Option.some.inj hc)
      · intro hc
        exact absurd (Option.some.inj hc) (by simp)

@[simp] private theorem markLeft_run_length (w : List TBU) :
    (markLeft.run w).length = w.length := markLeft.run_length w

/-- The (43) decomposition computes UTP. -/
theorem utp_eq_resolve_mark (w : List TBU) : utp w = resolve (markLeft.run w) := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · have hn : (markLeft.run w).reverse.length = w.length := by simp
    rw [utp_getElem?, resolve,
      List.getElem?_reverse (by rw [resolveRight.run_length]; simpa using hi),
      resolveRight.run_length, hn,
      show resolveRight.run (markLeft.run w).reverse
        = resolveRight.runFrom resolveRight.initial (markLeft.run w).reverse from rfl,
      Mealy.runFrom_getElem?, resolveRight_stateAfter,
      List.getElem?_reverse (by rw [hn] at *; simp; omega)]
    have hidx : (markLeft.run w).length - 1 - (w.length - 1 - i) = i := by
      rw [markLeft_run_length]; omega
    rw [hidx, markLeft_run_getElem?]
    -- the right flag of the resolving pass = "a H-toned TBU occurs strictly after `i`"
    have hflag : (((markLeft.run w).reverse.take (w.length - 1 - i)).any (· == Mark.H))
        = ((w.drop (i + 1)).any (· == TBU.H)) := by
      have htk : (markLeft.run w).reverse.take (w.length - 1 - i)
          = ((markLeft.run w).drop (i + 1)).reverse := by
        rw [List.take_reverse, markLeft_run_length,
          show w.length - (w.length - 1 - i) = i + 1 from by omega]
      rw [htk, List.any_reverse, Bool.eq_iff_iff]
      simp only [List.any_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨j, hj, hxj⟩ := mem_drop_iff.mp hx
        exact ⟨.H, mem_drop_iff.mpr ⟨j, hj, (markLeft_run_H_iff w j).mp hxj⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨j, hj, hxj⟩ := mem_drop_iff.mp hx
        exact ⟨.H, mem_drop_iff.mpr ⟨j, hj, (markLeft_run_H_iff w j).mpr hxj⟩, rfl⟩
    rw [hflag]
    obtain ⟨a, ha⟩ : ∃ a, w[i]? = some a := ⟨w[i], List.getElem?_eq_getElem hi⟩
    rw [ha]
    simp only [Option.map_some]
    congr 1
    have hsp := surfacesH_split ha
    cases a with
    | H => simp [surfacesH_iff.mpr ⟨⟨i, le_rfl, ha⟩, ⟨i, le_rfl, ha⟩⟩, resolveRight]
    | O =>
      by_cases hL : (w.take i).any (· == TBU.H) = true
      · have hLm : TBU.H ∈ w.take i := by
          simp only [List.any_eq_true, beq_iff_eq] at hL
          obtain ⟨x, hx, rfl⟩ := hL
          exact hx
        by_cases hR : (w.drop (i + 1)).any (· == TBU.H) = true
        · have hRm : TBU.H ∈ w.drop (i + 1) := by
            simp only [List.any_eq_true, beq_iff_eq] at hR
            obtain ⟨x, hx, rfl⟩ := hR
            exact hx
          simp [hsp.mpr (Or.inr ⟨hLm, hRm⟩), hL, hR, resolveRight]
        · have hs : ¬ SurfacesH w i := fun hs => by
            rcases hsp.mp hs with h' | ⟨-, hRm⟩
            · exact TBU.noConfusion h'
            · exact hR (by
                obtain ⟨j, hj, hjH⟩ := mem_drop_iff.mp hRm
                simp only [List.any_eq_true, beq_iff_eq]
                exact ⟨.H, mem_drop_iff.mpr ⟨j, hj, hjH⟩, rfl⟩)
          simp [hs, hL, hR, resolveRight]
      · have hs : ¬ SurfacesH w i := fun hs => by
          rcases hsp.mp hs with h' | ⟨hLm, -⟩
          · exact TBU.noConfusion h'
          · exact hL (by
              obtain ⟨j, hj, hjH⟩ := mem_take_iff.mp hLm
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨.H, mem_take_iff.mpr ⟨j, hj, hjH⟩, rfl⟩)
        simp [hs, hL, resolveRight]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by
      rw [resolve, List.length_reverse, resolveRight.run_length]
      simp
      omega)]

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

private theorem linearize_toAR (a : TBU) :
    (toAR a).linearize = [((), if a = .H then [Tone.TRN.H] else [])] := by
  cases a <;> simp [toAR]

theorem linearize_realize_toAR (w : List TBU) :
    (realize toAR w).linearize
      = w.map fun a => ((), if a = .H then [Tone.TRN.H] else []) := by
  rw [linearize_realize]
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.flatMap_cons, List.map_cons, ih, linearize_toAR a]; rfl

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

private theorem mem_upper_realize_toAR (v : List TBU) :
    ∀ b ∈ (realize toAR v).upper.toList, b = Tone.TRN.H := by
  induction v with
  | nil =>
    have h : (realize toAR ([] : List TBU)).upper.toList = [] :=
      List.eq_nil_of_length_eq_zero (by simp [realize_nil, AR.empty, Graph.empty])
    rw [h]
    intro b hb
    simp at hb
  | cons a v ih =>
    intro b hb
    rw [realize_cons, AR.concat_upper, LabeledTuple.toList_concat, List.mem_append] at hb
    rcases hb with hb | hb
    · cases a with
      | H => simpa [toAR] using hb
      | O => simp [toAR] at hb
    · exact ih b hb

private theorem upper_realize_toAR (v : List TBU) :
    (realize toAR v).upper.toList
      = List.replicate (realize toAR v).upper.len Tone.TRN.H := by
  have h := List.eq_replicate_of_mem (mem_upper_realize_toAR v)
  rwa [LabeledTuple.toList_length] at h

private theorem lower_realize_toAR (v : List TBU) :
    (realize toAR v).lower.toList = List.replicate v.length () := by
  have hlen : (realize toAR v).lower.len = v.length := by
    rw [← AR.linearize_length, linearize_realize_toAR, List.length_map]
  have h := List.eq_replicate_of_mem
    (l := (realize toAR v).lower.toList) (a := ()) fun _ _ => rfl
  rwa [LabeledTuple.toList_length, hlen] at h

private theorem isLinkedLower_realize_toAR (v : List TBU) (j : ℕ) :
    (∃ k, (k, j) ∈ (realize toAR v).links) ↔ v[j]? = some .H := by
  induction v generalizing j with
  | nil =>
    refine iff_of_false ?_ (by simp)
    rintro ⟨k, hk⟩
    rw [realize_nil] at hk
    simp [AR.empty, Graph.empty] at hk
  | cons a v ih =>
    cases a with
    | H =>
      rw [realize_cons, show toAR TBU.H = .single Tone.TRN.H () from rfl, AR.links_concat]
      simp only [AR.single_links, AR.single_upper, AR.single_lower, LabeledTuple.ofList_len,
        List.length_singleton]
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero]
        exact iff_of_true ⟨0, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩ trivial
      | succ t =>
        rw [List.getElem?_cons_succ, ← ih t]
        constructor
        · rintro ⟨k, hk⟩
          rcases Finset.mem_union.mp hk with hk | hk
          · rw [Finset.mem_singleton, Prod.mk.injEq] at hk
            exact absurd hk.2 (by omega)
          · obtain ⟨⟨q₁, q₂⟩, hq, hqe⟩ := Finset.mem_image.mp hk
            simp only [shiftLink_apply, Prod.mk.injEq] at hqe
            obtain rfl : q₂ = t := by omega
            exact ⟨q₁, hq⟩
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨(k, t), hk, by rw [shiftLink_apply]⟩)⟩
    | O =>
      rw [realize_cons, show toAR TBU.O = .bare () from rfl, AR.links_concat]
      simp only [AR.bare_links, AR.bare_upper, AR.bare_lower, LabeledTuple.ofList_len,
        List.length_singleton, List.length_nil]
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero]
        refine iff_of_false ?_ (by simp)
        rintro ⟨k, hk⟩
        rcases Finset.mem_union.mp hk with hk | hk
        · exact absurd hk (Finset.notMem_empty _)
        · obtain ⟨⟨q₁, q₂⟩, hq, hqe⟩ := Finset.mem_image.mp hk
          simp only [shiftLink_apply, Prod.mk.injEq] at hqe
          omega
      | succ t =>
        rw [List.getElem?_cons_succ, ← ih t]
        constructor
        · rintro ⟨k, hk⟩
          rcases Finset.mem_union.mp hk with hk | hk
          · exact absurd hk (Finset.notMem_empty _)
          · obtain ⟨⟨q₁, q₂⟩, hq, hqe⟩ := Finset.mem_image.mp hk
            simp only [shiftLink_apply, Prod.mk.injEq] at hqe
            obtain rfl : q₂ = t := by omega
            exact ⟨q₁, hq⟩
        · rintro ⟨k, hk⟩
          exact ⟨k, Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨(k, t), hk, by simp [shiftLink_apply]⟩)⟩

theorem mem_links_realizeMerged_utp (p : ℕ × ℕ) :
    p ∈ (realizeMerged toAR (utp w)).links ↔ p.1 = 0 ∧ SurfacesH w p.2 := by
  obtain ⟨k, j⟩ := p
  rw [realizeMerged_def,
    show (collapseAR (realize toAR (utp w))).links
        = ((realize toAR (utp w)).links).image
            (Prod.map (runIdx ((realize toAR (utp w)).upper.toList)) id) from rfl,
    upper_realize_toAR]
  simp only [Finset.mem_image, Prod.exists, Prod.map_apply, id_eq, runIdx_replicate,
    Prod.mk.injEq]
  constructor
  · rintro ⟨q₁, q₂, hq, rfl, rfl⟩
    exact ⟨rfl, utp_getElem?_H_iff.mp ((isLinkedLower_realize_toAR (utp w) q₂).mp ⟨q₁, hq⟩)⟩
  · rintro ⟨rfl, hS⟩
    obtain ⟨q₁, hq⟩ := (isLinkedLower_realize_toAR (utp w) j).mpr (utp_getElem?_H_iff.mpr hS)
    exact ⟨q₁, j, hq, rfl, rfl⟩

/-- Multiple association ((7)): the merged realization links melody node `0` to exactly
the `plateau`. Unconditional: a toneless word has an empty plateau and no lines. -/
theorem links_realizeMerged_utp :
    (realizeMerged toAR (utp w)).links = (plateau w).image fun j => ((0 : ℕ), j) := by
  ext ⟨k, j⟩
  rw [mem_links_realizeMerged_utp]
  simp only [Finset.mem_image, mem_plateau, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, hS⟩
    exact ⟨j, hS, rfl, rfl⟩
  · rintro ⟨j', hS, rfl, rfl⟩
    exact ⟨rfl, hS⟩

/-- The timing tier survives the merge: one slot per input TBU. -/
theorem lower_realizeMerged_utp :
    (realizeMerged toAR (utp w)).lower.toList = List.replicate w.length () := by
  rw [realizeMerged_def, collapseAR_lower, lower_realize_toAR, utp_length]

/-- The fused plateau ((7)): with at least one H, the merged melody tier is a single H
autosegment. -/
theorem upper_realizeMerged_utp (hw : .H ∈ w) :
    (realizeMerged toAR (utp w)).upper.toList = [Tone.TRN.H] := by
  have hn : 0 < (realize toAR (utp w)).upper.len := by
    obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp hw
    obtain ⟨q₁, hq⟩ := (isLinkedLower_realize_toAR (utp w) i₀).mpr
      (utp_getElem?_H_iff.mpr (surfacesH_of_getElem?_H hi₀))
    exact Nat.lt_of_le_of_lt (Nat.zero_le q₁) ((realize toAR (utp w)).inBounds _ hq).1
  obtain ⟨m, hm⟩ : ∃ m, (realize toAR (utp w)).upper.len = m + 1 :=
    ⟨(realize toAR (utp w)).upper.len - 1, by omega⟩
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
