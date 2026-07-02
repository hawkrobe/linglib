/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Computability.Subregular.Function.LetterSubsequential
import Linglib.Core.Computability.Subregular.Function.Bimachine
import Linglib.Core.Computability.Subregular.Function.Hierarchy
import Linglib.Phonology.Autosegmental.Realization
import Linglib.Phonology.Tone.Basic

/-!
# Jardine (2016): Computationally, tone is different

[jardine-2016] (Phonology 33: 247–283) establishes a typological asymmetry — *unbounded
circumambient* processes, whose application depends on information unboundedly far away on
**both** sides of the target, are common in tonal phonology but rare in segmental phonology —
and characterises it computationally: segmental maps are at most weakly deterministic, while
tonal maps are not. The flagship witness is **unbounded tonal plateauing** (UTP; Luganda,
Digo, Xhosa, Zulu, Yaka, Saramaccan, …; [hyman-katamba-2010]): every tone-bearing unit
between two H-toned TBUs surfaces H.

This file formalizes the paper's formal skeleton over its string-based representation
(§4.1: `H` = TBU associated to a H tone, `O` = the paper's Ø, an unspecified TBU):

* `utp` — the UTP map, with the paper's rule set (36) derived as equations
  (`utp_toneless`, `utp_single`, `utp_plateau`) and the (43) input/output rows checked
  by `decide`.
* `utp_isBimachineComputable` — UTP **is** regular (§4.2 exhibits a nondeterministic FST;
  here the sharper positive: an explicit bimachine, deterministic in each direction).
* `utp_isUnboundedCircumambient` — the paper's definition (2) of an unbounded circumambient
  process, instantiated by UTP: for every distance `d` one plateau word has a target whose
  output flips under a far-left and a far-right perturbation.
* `utp_not_isLeftSubsequential` / `utp_not_isRightSubsequential` — the paper's central
  theorem (§4.2; proof in its online appendix): no deterministic FST computes UTP in either
  scan direction. The proof runs on the substrate's bounded-delay property
  (`IsLeftSubsequential.bounded_delay`): on input `H Øⁿ` a left machine may emit at most
  `H` (the images of `H Øⁿ` and `H Øⁿ H` diverge at position 1), so it must withhold `n`
  symbols — impossible with finitely many states. The right direction follows by the
  reversal symmetry of plateauing (`utp_reverse`).
* `utp_not_isBimachineWeaklyDeterministic` — §5.2's claim that UTP is not weakly
  deterministic. [jardine-2016] argues this in [heinz-lai-2013]'s decomposition terms: the
  mark-up-free composition of two subsequential passes cannot carry "a H appears to the
  left" across the string (the (43) decomposition needs an enlarged alphabet). The project-
  canonical rendering of weak determinism is the non-interacting bimachine
  (`IsBimachineWeaklyDeterministic`, `Core/Computability/Subregular/Function/Bimachine`),
  and under it the claim is a theorem: UTP `RequiresBothSides` — perturbing either far
  trigger reverts the target — which no union of one-sided rules can express.
* `utp_markup_decomposition` — the paper's (43): over the alphabet enlarged with the mark
  `?`, UTP *is* a right-subsequential map after a left-subsequential map. Weak
  determinism forbids exactly this enlargement, so (43) and the impossibility theorem
  together locate UTP precisely.
* `readTBU_linearize_realize` — §4.4's defense of the string-based representation, via
  the substrate's `Autosegmental.AR.linearize`: the (40) translation `toAR` realizes a
  TBU string as an autosegmental representation whose association-state string *is* the
  input ((37a)), so string-measured look-ahead is timing-tier look-ahead ((37b)).
* `utp_fullyRegular` — the paper's thesis (§7) in one statement: UTP is *fully regular*,
  i.e. regular but neither subsequential in either direction nor weakly deterministic.
  Tone thereby exceeds the complexity bound that segmental phonology respects.

Contrast `Studies/MeinhardtEtAl2024`: bidirectional ATR spreading is unbounded circumambient
*as covariation* yet weakly deterministic (a two-sided union); UTP's conjunctive trigger
demand (`RequiresBothSides`) is what pushes it above the weakly deterministic bound.
-/

namespace Jardine2016Tone

open Subregular

/-! ### The string-based representation

[jardine-2016] §4.4 defends analysing the tonal map over strings of timing-tier symbols:
each symbol records one TBU's association state (its (40) linearisation), so look-ahead is
measured on the timing tier. -/

/-- A tone-bearing unit in [jardine-2016]'s string-based representation (§4.1): `H` is a
TBU associated to a H tone, `O` an unspecified TBU (the paper's Ø). -/
inductive TBU
  | H
  | O
  deriving DecidableEq, Repr

/-- TBU `i` of `w` surfaces with a H tone: some H-toned TBU sits at a position `≤ i` and
some at a position `≥ i`. An underlyingly H-toned TBU witnesses both sides itself; a
toneless TBU surfaces H exactly when flanked, which is the plateauing rule (7) of
[hyman-katamba-2010] as a pointwise condition. -/
def SurfacesH (w : List TBU) (i : ℕ) : Prop :=
  .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i

instance (w : List TBU) (i : ℕ) : Decidable (SurfacesH w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The **unbounded tonal plateauing** map, [jardine-2016] (36): any number of TBUs
between two H-toned TBUs surface as H; everything else is unchanged. -/
def utp (w : List TBU) : List TBU :=
  w.mapIdx fun i _ => if SurfacesH w i then .H else .O

@[simp] theorem utp_length (w : List TBU) : (utp w).length = w.length := by
  simp [utp]

theorem utp_getElem? (w : List TBU) (i : ℕ) :
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
theorem surfacesH_iff {w : List TBU} {i : ℕ} :
    SurfacesH w i ↔ (∃ j ≤ i, w[j]? = some .H) ∧ ∃ j, i ≤ j ∧ w[j]? = some .H := by
  rw [SurfacesH, mem_take_iff, mem_drop_iff]
  simp [Nat.lt_succ_iff]

/-- Splitting off the position itself: given the symbol at `i`, TBU `i` surfaces H iff it
is itself a H or is strictly flanked. -/
private theorem surfacesH_split {w : List TBU} {i : ℕ} {a : TBU} (h : w[i]? = some a) :
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

[jardine-2016] specifies UTP by three schemata: toneless words and words with a single H
map to themselves; between the outermost two Hs everything surfaces H. Here they are
theorems about `utp` rather than clauses of its definition. -/

private theorem singleH_getElem?_H_iff (m n : ℕ) {j : ℕ} :
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

private theorem plateau_getElem?_H_bounds {m p : ℕ} {w : List TBU} {j : ℕ}
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

/-- (36c): everything between the outermost Hs surfaces H — the plateau. The medial
material `w` is arbitrary (the paper's `{Ø,H}ⁿ`). -/
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

/-- The (43) sample rows of [jardine-2016]: no plateau without two Hs; `HØØH ↦ HHHH`. -/
example : utp [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

/-! ### UTP is regular

§4.2 exhibits a nondeterministic FST (Fig. 5) for UTP. The sharper positive fact fitting
the substrate: UTP is computed by a **bimachine** — one deterministic pass per direction,
each tracking "H seen on my side", conjoined at the cell. Regularity is thus witnessed
without nondeterminism; what fails (below) is *one-directional* determinism. -/

/-- The UTP bimachine: a flag bimachine (`Bimachine.ofFlags`) whose sides record whether
a H occurs on that side; a toneless cell surfaces H exactly when both flags are set. -/
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

/-- **UTP is regular** ([jardine-2016] §4.2, Fig. 5): computable by a finite bimachine. -/
theorem utp_isBimachineComputable : IsBimachineComputable utp :=
  utpBM_run ▸ isBimachineComputable utpBM

/-! ### UTP is unboundedly circumambient

Definition (2) of [jardine-2016]: application depends on the presence of triggers on both
sides of the target, with no bound on their distance. The witness family at distance `d`:
a plateau word `H Ø^(2d+2) H` with target `d+1`; deleting either flanking H reverts it. -/

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

/-- The base target surfaces H: both flanking Hs are present. -/
private theorem utp_plateauBase_mid (d : ℕ) : (utp (plateauBase d))[d + 1]? = some TBU.H := by
  rw [utp_getElem?, plateauBase_getElem?_mid, Option.map_some, if_pos]
  rw [surfacesH_iff]
  exact ⟨⟨0, by omega, (plateauBase_getElem?_H_iff d).mpr (Or.inl rfl)⟩,
         ⟨2 * d + 3, by omega, (plateauBase_getElem?_H_iff d).mpr (Or.inr rfl)⟩⟩

/-- Deleting the left H (perturbation at position 0) reverts the target to `O`. -/
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

/-- Deleting the right H (perturbation at position `2d+3`) reverts the target to `O`. -/
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

/-- UTP requires both sides ([heinz-lai-2013]'s interaction structure): the plateau
target changes, yet deleting *either* flanking H reverts it to the identity. -/
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

/-- **UTP is an unbounded circumambient process** — [jardine-2016]'s definition (2): for
every distance `d`, some plateau target flips under a far-left and a far-right
perturbation. Derived: requiring both sides is the conjunctive strengthening. -/
theorem utp_isUnboundedCircumambient : IsUnboundedCircumambient utp :=
  utp_requiresBothSides.isUnboundedCircumambient

/-! ### UTP is not subsequential

The paper's central theorem (§4.2; full proof in its online appendix). The argument here
is the bounded-delay one: a left machine reading `H Øⁿ` has emitted at most the common
prefix of `utp (H Øⁿ) = H Øⁿ` and `utp (H Øⁿ H) = H^(n+2)` — a single symbol — so its
final output must carry the withheld `n` symbols, exceeding any finite-state bound. -/

/-- **UTP is not left-subsequential** ([jardine-2016] §4.2, appendix). At every delay
bound `N`, the images of `H Ø^(N+1)` and `H Ø^(N+1) H` disagree already at position 1. -/
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

/-- Plateauing is symmetric under string reversal — the formal content of "the position of
the first triggering H is just as arbitrarily far to the right as the second is to the
left" ([jardine-2016] §4.2). -/
theorem utp_reverse (w : List TBU) : utp w.reverse = (utp w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · have hrl : (utp w).length = w.length := utp_length w
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

/-- **UTP is not right-subsequential** ([jardine-2016] §4.2, appendix): by the reversal
symmetry of plateauing, a right machine faces the mirror-image unbounded look-ahead. -/
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

§5.2: a mark-up-free decomposition into two subsequential passes would have to carry "a H
occurs to the left" rightward through unboundedly many toneless TBUs without changing the
alphabet — [jardine-2016], following [heinz-lai-2013], argues none exists. Under the
project-canonical non-interacting-bimachine rendering of weak determinism, the claim is a
theorem: UTP `RequiresBothSides`, the conjunctive-trigger structure no union of one-sided
rules can express. -/

/-- **UTP is not weakly deterministic** ([jardine-2016] §5.2). -/
theorem utp_not_isBimachineWeaklyDeterministic : ¬ IsBimachineWeaklyDeterministic utp :=
  not_isBimachineWeaklyDeterministic_of_requiresBothSides utp_requiresBothSides

/-! ### The (43) mark-up decomposition

With one extra symbol the two-pass decomposition *does* exist ([jardine-2016] (43)): a
left pass marks every toneless TBU after a H with `?`; a right pass resolves `?` to H
when a H follows and to Ø otherwise. The intermediate `?` carries "a H appears to the
left" across unboundedly many TBUs — precisely the Elgot–Mezei-style mark-up that
[heinz-lai-2013]'s weak determinism disallows. Together with
`utp_not_isBimachineWeaklyDeterministic`, this locates UTP exactly: subsequential in
neither direction, weakly deterministic only *with* alphabet enlargement. -/

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

/-- Right pass of (43), scanning right-to-left: resolve `?` to H when a H follows,
else to Ø. -/
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

/-- Coordinate characterization of the marking pass. -/
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

/-- Marking neither creates nor destroys H-toned TBUs. -/
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

/-- **The (43) decomposition computes UTP**: resolving the marked string right-to-left
recovers the plateau. -/
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

/-- **The (43) mark-up decomposition** ([jardine-2016] §5.2): over the alphabet enlarged
with `?`, UTP is a right-subsequential map after a left-subsequential map. Weak
determinism forbids exactly this enlargement — UTP is Elgot–Mezei-decomposable but not
weakly deterministic. -/
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

The string-based representation is not a rival of the autosegmental one but its
linearisation: each TBU symbol records one timing unit's association state. `toAR` is
the paper's (40) translation — a H-toned TBU is one `Tone.TRN.H` melody node linked to
its timing unit, a toneless TBU a bare timing unit — and by the substrate hom law
`Autosegmental.linearize_realize`, the association-state string of the realized AR is
the input string, symbol by symbol. So the TBU string is recoverable from the AR
((37a)), and look-ahead measured on the string is look-ahead measured on the timing
tier ((37b)). -/

section AutosegmentalGrounding

open Autosegmental

/-- The (40) translation: a H-toned TBU realizes as one H melody node (`Tone.TRN.H`)
linked to its timing unit; a toneless TBU is a bare timing unit. -/
def toAR : TBU → AR Tone.TRN Unit
  | .H => ⟨⟨LabeledTuple.ofList [Tone.TRN.H], LabeledTuple.ofList [()], {(0, 0)}⟩, by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      subst hp
      exact ⟨by simp, by simp⟩⟩
  | .O => ⟨⟨LabeledTuple.empty, LabeledTuple.ofList [()], ∅⟩, by
      intro p hp
      simp at hp⟩

private theorem linearize_toAR (a : TBU) :
    (toAR a).linearize = [((), if a = .H then [Tone.TRN.H] else [])] := by
  cases a <;> decide

/-- (40): linearizing the realized AR returns the TBU string's association profiles. -/
theorem linearize_realize_toAR (w : List TBU) :
    (realize toAR w).linearize
      = w.map fun a => ((), if a = .H then [Tone.TRN.H] else []) := by
  rw [linearize_realize]
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.flatMap_cons, List.map_cons, ih, linearize_toAR a]; rfl

/-- Read a timing unit's association state back as a TBU symbol. -/
def readTBU (s : Unit × List Tone.TRN) : TBU := if s.2.isEmpty then .O else .H

/-- **(37a)**: the TBU string is recoverable from the realized autosegmental
representation — the string carries exactly the timing-tier association information, so
the complexity results transfer to the autosegmental analysis. -/
theorem readTBU_linearize_realize (w : List TBU) :
    ((realize toAR w).linearize).map readTBU = w := by
  rw [linearize_realize_toAR, List.map_map]
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left fun a ha => ?_
  cases a <;> rfl

end AutosegmentalGrounding

/-- **Computationally, tone is different** ([jardine-2016] §7): UTP is *fully regular* —
regular (bimachine-computable) but neither left- nor right-subsequential nor weakly
deterministic. Tonal phonology thereby exceeds the weakly deterministic bound that
segmental phonology respects, which is the paper's characterisation of the unbounded
circumambient asymmetry. -/
theorem utp_fullyRegular :
    IsBimachineComputable utp ∧ (∀ d, ¬ IsSubsequential d utp)
      ∧ ¬ IsBimachineWeaklyDeterministic utp :=
  ⟨utp_isBimachineComputable, utp_not_isSubsequential, utp_not_isBimachineWeaklyDeterministic⟩

end Jardine2016Tone
