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
import Linglib.Phonology.Autosegmental.Collapse
import Linglib.Phonology.Autosegmental.Junction
import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.Tone.Plateauing

/-!
# Jardine (2016): Computationally, tone is different

[jardine-2016] (Phonology 33) characterises a typological asymmetry computationally:
*unbounded circumambient* processes — application depends on unboundedly distant material
on both sides of the target — are common in tone but rare in segmental phonology, and
they are exactly the attested maps exceeding weak determinism. The flagship witness is
**unbounded tonal plateauing** (UTP; [hyman-katamba-2010]): every TBU between two H-toned
TBUs surfaces H. This file formalizes the paper's formal skeleton over its string
representation (§4.1: `H` a H-toned TBU, `O` the paper's Ø).

The map itself and its plateau/circumambience API live in `Phonology/Tone/Plateauing`
(the rule set (36) as `utp.map_toneless`/`utp.map_single`/`utp.map_plateau`; definition (2) as
`utp.isUnboundedCircumambient`); this file keeps the paper's theorems about it.

## Main definitions

* `utpBM` — a bimachine computing UTP.
* `markLeft`, `resolve` — the (43) two-pass decomposition over the `?`-enlarged alphabet.
* `toAR` — the (40) translation into autosegmental representations.

## Main results

* `utp_not_isSubsequential` — the central theorem (§4.2, online appendix): no
  deterministic FST computes UTP in either direction, via
  `IsLeftSubsequential.bounded_delay` and the reversal symmetry `utp.map_reverse`.
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

open Subregular Tone.Plateauing

variable {w : List TBU} {i j k : ℕ}

/-! ### UTP is regular

§4.2 exhibits a nondeterministic FST (Fig. 5); here UTP is computed by a bimachine — one
deterministic pass per direction — so what fails below is one-directional determinism. -/

/-- The UTP bimachine: each side flags "a H occurs on my side"; a toneless cell surfaces
H exactly when both flags are set. -/
def utpBM : Bimachine Bool Bool TBU TBU :=
  .ofFlags (· == .H) (· == .H) fun l a r => if a == .H || (l && r) then .H else .O

/-- The bimachine computes UTP. -/
theorem utpBM_run : utpBM.run = utp.map := by
  funext w
  refine List.ext_getElem? fun i => ?_
  rw [utpBM, Bimachine.ofFlags_run_getElem?, utp.map_getElem?]
  cases h : w[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some]
    congr 1
    have hb : (a == TBU.H || ((w.take i).any (· == .H) && (w.drop (i + 1)).any (· == .H)))
        = true ↔ utp.Surfaces w i := by
      rw [utp.surfaces_split h]; simp [List.any_eq_true]
    by_cases hs : utp.Surfaces w i
    · rw [if_pos (hb.mpr hs), if_pos hs]
    · rw [if_neg (fun hbt => hs (hb.mp hbt)), if_neg hs]

/-- UTP is regular (§4.2): computable by a finite bimachine. -/
theorem utp_isBimachineComputable : IsBimachineComputable utp.map :=
  utpBM_run ▸ isBimachineComputable utpBM

/-! ### UTP is not subsequential

The paper's central theorem (§4.2, online appendix), by bounded delay: a left machine
reading `H Øⁿ` has emitted at most one symbol (`utp.map (H Øⁿ) = H Øⁿ` and
`utp.map (H Øⁿ H) = H^(n+2)` diverge at position 1), so it withholds `n` symbols. -/

/-- UTP is not left-subsequential (§4.2, online appendix). -/
theorem utp_not_isLeftSubsequential : ¬ IsLeftSubsequential utp.map := by
  refine not_isLeftSubsequential_of_diverging fun N =>
    ⟨.H :: List.replicate (N + 1) .O, [.H], 1, ?_, ?_⟩
  · simp only [Tone.Surfacing.map_length, List.length_cons, List.length_replicate]; omega
  · -- the images disagree at position 1: toneless there without the second H, plateau with it
    have h1 : (utp.map (TBU.H :: List.replicate (N + 1) TBU.O))[1]? = some TBU.O :=
      utp.map_getElem?_O_iff.mpr ⟨by simp, fun hs => by simpa using (utp.surfaces_def.mp hs).2⟩
    have h2 : (utp.map ((TBU.H :: List.replicate (N + 1) TBU.O) ++ [TBU.H]))[1]? = some TBU.H :=
      utp.map_getElem?_H_iff.mpr (utp.surfaces_def.mpr ⟨by simp, by simp⟩)
    rw [h1, h2]; simp

/-- UTP is not right-subsequential: by the reversal symmetry, a right machine faces the
mirror-image unbounded look-ahead. -/
theorem utp_not_isRightSubsequential : ¬ IsRightSubsequential utp.map := by
  intro hf
  rw [isRightSubsequential_iff_left_reverse] at hf
  have heq : (fun xs : List TBU => (utp.map xs.reverse).reverse) = utp.map := by
    funext xs; rw [utp.map_reverse, List.reverse_reverse]
  exact utp_not_isLeftSubsequential (heq ▸ hf)

/-- UTP is subsequential in neither direction. -/
theorem utp_not_isSubsequential : ∀ d, ¬ IsSubsequential d utp.map
  | .left => utp_not_isLeftSubsequential
  | .right => utp_not_isRightSubsequential

/-! ### UTP is not weakly deterministic

Under the non-interacting-bimachine rendering of [heinz-lai-2013]'s weak determinism,
§5.2's claim is a theorem: UTP `RequiresBothSides`, which no union of one-sided rules
expresses. -/

/-- UTP is not weakly deterministic (§5.2). -/
theorem utp_not_isBimachineWeaklyDeterministic : ¬ IsBimachineWeaklyDeterministic utp.map :=
  not_isBimachineWeaklyDeterministic_of_requiresBothSides utp.requiresBothSides

/-! ### The (43) mark-up decomposition

With one extra symbol the two-pass decomposition exists: a left pass marks every
toneless TBU after a H with `?`; a right pass resolves `?` by whether a H follows. The
mark is exactly the alphabet enlargement weak determinism disallows, so with the
impossibility theorem this locates UTP precisely. -/

/-- The mark-up alphabet of (43): `Q` is the paper's `?`. -/
inductive Mark | H | O | Q
  deriving DecidableEq, Repr

/-- Left pass of (43): mark every toneless TBU after a H with `?`. -/
def markLeft : Mealy Bool TBU Mark :=
  .ofFlag (· == .H) fun l a => match a with | .H => .H | .O => if l then .Q else .O

/-- Right pass of (43): resolve `?` to H when a H follows, else to Ø. -/
def resolveRight : Mealy Bool Mark TBU :=
  .ofFlag (· == .H) fun r a =>
    match a with | .H => .H | .O => .O | .Q => if r then .H else .O

/-- The right pass as a right-to-left string function: reverse, run, reverse. -/
def resolve (x : List Mark) : List TBU := (resolveRight.run x.reverse).reverse

private theorem markLeft_run_H_iff (w : List TBU) (j : ℕ) :
    (markLeft.run w)[j]? = some Mark.H ↔ w[j]? = some TBU.H := by
  rw [markLeft, Mealy.ofFlag_run_getElem?]
  cases hv : w[j]? with
  | none => simp
  | some a => cases a <;> simp [ite_eq_iff]

/-- The (43) decomposition computes UTP. -/
theorem utp_eq_resolve_mark (w : List TBU) : utp.map w = resolve (markLeft.run w) := by
  have hmark : ∀ i : ℕ, Mark.H ∈ (markLeft.run w).drop (i + 1) ↔ TBU.H ∈ w.drop (i + 1) :=
    fun i => by simp only [List.mem_drop_iff, markLeft_run_H_iff]
  refine List.ext_getElem? fun i => ?_
  rw [utp.map_getElem?, resolve, resolveRight, Mealy.ofFlag_run_reverse_getElem?]
  simp only [List.any_beq', List.contains_eq_mem, decide_eq_decide.mpr (hmark i)]
  rw [markLeft, Mealy.ofFlag_run_getElem?, Option.map_map]
  simp only [List.any_beq', List.contains_eq_mem]
  cases ha : w[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Function.comp_apply]
    congr 1
    cases a with
    | H => simp [utp.surfaces_of_hi ha]
    | O =>
      by_cases hL : TBU.H ∈ w.take i <;> by_cases hR : TBU.H ∈ w.drop (i + 1) <;>
        simp [utp.surfaces_split ha, hL, hR]

/-- The (43) mark-up decomposition (§5.2): over the `?`-enlarged alphabet, UTP is a
right-subsequential map after a left-subsequential map. -/
theorem utp_markup_decomposition :
    IsLeftSubsequential markLeft.run ∧ IsRightSubsequential resolve
      ∧ utp.map = resolve ∘ markLeft.run := by
  refine ⟨markLeft.isLetterLeftSubsequential.isLeftSubsequential, ?_,
    funext utp_eq_resolve_mark⟩
  rw [isRightSubsequential_iff_left_reverse]
  have heq : (fun xs : List Mark => (resolve xs.reverse).reverse) = resolveRight.run := by
    funext xs; rw [resolve, List.reverse_reverse, List.reverse_reverse]
  exact heq ▸ resolveRight.isLetterLeftSubsequential.isLeftSubsequential

/-! ### The autosegmental grounding ((40), §4.4)

The string representation is the linearisation of the autosegmental one: `toAR` is the
paper's (40) translation, and by `Autosegmental.linearize_realize` the association-state
string of the realized AR is the input string. So the TBU string is recoverable from the
AR ((37a)) and string look-ahead is timing-tier look-ahead ((37b)). -/

section AutosegmentalGrounding

open Autosegmental

/-- Read a timing unit's association state back as a TBU symbol. -/
def readTBU (s : Unit × List Tone.TRN) : TBU := if s.2.isEmpty then .O else .H

/-- (37a): the TBU string is recoverable from the realized AR, so the complexity results
transfer to the autosegmental analysis. -/
theorem readTBU_linearize_realize (w : List TBU) :
    ((realize toAR w).linearize).map readTBU = w := by
  rw [linearize_realize_toAR, List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun a _ => by cases a <;> rfl

/-! #### The fused plateau ([hyman-katamba-2010] (7))

The OCP-merging realization `Autosegmental.realizeMerged` fuses the plateau's run of H
nodes into one, giving [hyman-katamba-2010]'s output representation (7): a single H
autosegment multiply linked to exactly the `plateau`, over an unchanged timing tier. -/

theorem mem_links_realizeMerged_utp (p : ℕ × ℕ) :
    p ∈ (realizeMerged toAR (utp.map w)).links ↔ p.1 = 0 ∧ utp.Surfaces w p.2 := by
  have hL : ∀ j, (realize toAR (utp.map w)).toGraph.IsLinkedLower j ↔ utp.Surfaces w j :=
    fun j => by rw [isLinkedLower_realize_toAR, utp.map_getElem?_H_iff]
  rw [realizeMerged_def,
    mem_links_collapseAR_of_upper_replicate (upper_realize_toAR (utp.map w)), hL]

/-- Multiple association ((7)): the merged realization links melody node `0` to exactly
the `plateau`. Unconditional: a toneless word has an empty plateau and no lines. -/
theorem links_realizeMerged_utp :
    (realizeMerged toAR (utp.map w)).links = {0} ×ˢ plateau w := by
  ext ⟨k, j⟩; rw [mem_links_realizeMerged_utp]; simp [and_comm, eq_comm]

/-- The timing tier survives the merge: one slot per input TBU. -/
theorem lower_realizeMerged_utp :
    (realizeMerged toAR (utp.map w)).lower.toList = List.replicate w.length () := by
  rw [realizeMerged_def, collapseAR_lower]
  have h := List.eq_replicate_of_mem
    (l := (realize toAR (utp.map w)).lower.toList) (a := ()) fun _ _ => rfl
  rwa [LabeledTuple.toList_length, ← AR.linearize_length, linearize_realize_toAR,
    List.length_map, Tone.Surfacing.map_length] at h

/-- The fused plateau ((7)): with at least one H, the merged melody tier is a single H
autosegment. -/
theorem upper_realizeMerged_utp (hw : .H ∈ w) :
    (realizeMerged toAR (utp.map w)).upper.toList = [Tone.TRN.H] := by
  obtain ⟨m, hm⟩ : ∃ m, ((utp.map w).count .H) = m + 1 := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    have := List.count_pos_iff.mpr <| List.mem_iff_getElem?.mpr
      ⟨i, utp.map_getElem?_H_iff.mpr (utp.surfaces_of_hi hi)⟩
    exact ⟨(utp.map w).count .H - 1, by omega⟩
  rw [realizeMerged_def, upper_collapseAR, upper_realize_toAR, hm, OCP.collapse_replicate]

/-- (7) concretely: `HØØH` fuses to one H linked to all four TBUs. -/
example :
    (realizeMerged toAR (utp.map [.H, .O, .O, .H])).links
      = {(0, 0), (0, 1), (0, 2), (0, 3)} := by decide

end AutosegmentalGrounding

/-- Computationally, tone is different (§7): UTP is fully regular — regular but neither
subsequential in either direction nor weakly deterministic, the bound segmental
phonology respects. -/
theorem utp_fullyRegular :
    IsBimachineComputable utp.map ∧ (∀ d, ¬ IsSubsequential d utp.map)
      ∧ ¬ IsBimachineWeaklyDeterministic utp.map :=
  ⟨utp_isBimachineComputable, utp_not_isSubsequential, utp_not_isBimachineWeaklyDeterministic⟩

end Jardine2016Tone
