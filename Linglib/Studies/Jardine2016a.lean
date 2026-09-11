/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ElgotMezei
import Linglib.Data.Examples.Jardine2016a
import Linglib.Phonology.Tone.Plateauing

/-!
# Jardine (2016): Computationally, tone is different

This file formalizes [jardine-2016a], the computational characterization of a typological
asymmetry: unbounded circumambient processes, whose application depends on unboundedly distant
material on both sides of the target, (2), are common in tonal phonology and rare in segmental
phonology, and they are the attested maps beyond weak determinism. The witness is unbounded
tonal plateauing, every TBU between two H-toned TBUs surfacing H ([hyman-katamba-2010]'s rule,
(7)), as the string map (36) of Section 4.1 over `H` and Ø, which is `Tone.utp` and reproduces
the plateaus of Section 2.2 (`utp_map_rows`). The map is neither left- nor right-subsequential,
Section 4.2 (`utp_not_isSubsequential`), by bounded delay and the reversal symmetry; it is
regular, since the mark-up decomposition (43), a left-to-right pass writing `?` after a H and a
right-to-left pass resolving `?`, is a bimachine ([elgot-mezei-1965], `utp_eq_resolve_mark`,
`utp_isBimachineComputable`); and it is not weakly deterministic, Section 5.2, no union of
one-sided rules expressing a map that requires both sides (`utp_not_weaklyDeterministic`), so it
is fully regular, the class Section 5.3 places tone in and bars segmental phonology from
(`utp_fullyRegular`). Read back into autosegmental representations by (40), the OCP-merged
output is one H linked to the plateau, Section 4.4.

## Implementation notes

* Weak determinism is rendered as computability by a non-interacting bimachine
  (`IsNonInteractingBimachineComputable`), the class of [meinhardt-mai-bakovic-mccollum-2024]; the
  paper conjectures, after [heinz-lai-2013], that no mark-up-free decomposition of UTP exists,
  and under this rendering the conjecture is a theorem.
* The rows write the paper's string representation one symbol per mora, a long vowel counting
  two; the Digo, Xhosa and Yaka data, whose plateaus interact with tone shift or an accentual
  analysis, are not encoded.

## References

* [jardine-2016a]
* [hyman-katamba-2010]
* [heinz-lai-2013]
* [elgot-mezei-1965]
* [meinhardt-mai-bakovic-mccollum-2024]
-/

namespace Jardine2016a

open Data.Examples Tone

/-! ### The plateauing data

The paper's string representation of Section 4.1, one symbol per mora, `H` a TBU associated to a
H tone and Ø, written `O`, an unspecified one. -/

/-- A row of Section 2.2: the underlying and surface TBU strings. -/
structure Row where
  underlying : List TBU
  surface : List TBU
  deriving DecidableEq

/-- A TBU string from its `H`/`O` spelling. -/
def tbuString (s : String) : List TBU := s.toList.map λ c => if c = 'H' then .H else .O

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let u ← e.feature? "underlying"
  let s ← e.feature? "surface"
  some ⟨tbuString u, tbuString s⟩

/-- The plateauing data of Section 2.2: Luganda (8) to (12), Zulu (18b) and Saramaccan (21). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The map (36) reproduces every row: no change with at most one H, a plateau between the
outermost Hs otherwise. -/
theorem utp_map_rows : ∀ r ∈ rows, utp.map r.underlying = r.surface := by decide

variable {w : List TBU} {j k : ℕ}

/-! ### UTP is not subsequential

By bounded delay: a left machine reading `H Øⁿ⁺¹` has emitted at most one symbol, since
`utp.map (H Øⁿ⁺¹) = H Øⁿ⁺¹` and `utp.map (H Øⁿ⁺¹ H) = Hⁿ⁺³` already differ at position `1`;
so it withholds `n + 1` symbols. -/

/-- UTP is not left-subsequential (§4.2, online appendix). -/
theorem utp_not_isLeftSubsequential : ¬ IsLeftSubsequential utp.map :=
  not_isLeftSubsequential_of_diverging fun N =>
    ⟨.H :: List.replicate (N + 1) .O, [.H], 1,
      by simp only [Surfacing.map_length, List.length_cons, List.length_replicate]; omega, by
      rw [show utp.map (.H :: List.replicate (N + 1) .O) = .H :: List.replicate (N + 1) .O from
          by simpa using utp.map_single 0 (N + 1),
        show utp.map (.H :: List.replicate (N + 1) .O ++ [.H])
            = List.replicate (N + 1 + 2) .H from
          by simpa using utp.map_plateau 0 0 (List.replicate (N + 1) .O)]
      simp [show (1 : ℕ) < N + 1 + 2 by omega]⟩

/-- UTP is not right-subsequential: by the reversal symmetry, a right machine faces the
mirror-image unbounded look-ahead. -/
theorem utp_not_isRightSubsequential : ¬ IsRightSubsequential utp.map := by
  rw [isRightSubsequential_iff_left_reverse]
  simpa [utp.map_reverse] using utp_not_isLeftSubsequential

/-- UTP is subsequential in neither direction. -/
theorem utp_not_isSubsequential : ∀ d, ¬ IsSubsequential d utp.map
  | .left => utp_not_isLeftSubsequential
  | .right => utp_not_isRightSubsequential

/-! ### UTP is not weakly deterministic

Under the non-interacting-bimachine rendering of weak determinism, the conjecture of Section 5.2,
that UTP has no mark-up-free decomposition, is a theorem: UTP `RequiresBothSides`, which no union
of one-sided rules expresses. -/

/-- UTP is not weakly deterministic (§5.2). -/
theorem utp_not_weaklyDeterministic : ¬ IsNonInteractingBimachineComputable utp.map :=
  utp.requiresBothSides.not_isNonInteractingBimachineComputable

/-! ### The (43) mark-up decomposition

With one extra symbol the two-pass decomposition exists: a left pass marks every toneless
TBU after a H with `?`; a right pass resolves `?` by whether a H follows. The mark is
exactly the alphabet enlargement weak determinism disallows, so with the impossibility
theorem this locates UTP precisely. -/

/-- The mark-up alphabet of (43): `Q` is the paper's `?`. -/
inductive Mark | H | O | Q
  deriving DecidableEq, Repr

/-- Left pass of (43): mark every toneless TBU after a H with `?`. -/
def markLeft : Mealy Bool TBU Mark :=
  .ofFlag (· == .H) fun l a => match a with | .H => .H | .O => if l then .Q else .O

/-- Right pass of (43), run right-to-left: resolve `?` to H when a H follows, else to Ø. -/
def resolveRight : Mealy Bool Mark TBU :=
  .ofFlag (· == .H) fun r a =>
    match a with | .H => .H | .O => .O | .Q => if r then .H else .O

/-- The left pass writes `H` exactly where the input has `H`. -/
theorem markLeft_run_getElem?_H_iff :
    (markLeft.run w)[j]? = some Mark.H ↔ w[j]? = some TBU.H := by
  rw [markLeft, Mealy.getElem?_ofFlag_run]
  cases hv : w[j]? with
  | none => simp
  | some a => cases a <;> simp [ite_eq_iff]

/-- The (43) decomposition computes UTP: mark left-to-right, then resolve right-to-left.
Both passes run finite Mealy machines, so this exhibits UTP as a right-subsequential map
after a left-subsequential one (`Mealy.isLeftSubsequential_run`,
`Mealy.isRightSubsequential_runRight`). -/
theorem utp_eq_resolve_mark (w : List TBU) :
    utp.map w = resolveRight.runRight (markLeft.run w) := by
  have hmark (i : ℕ) : Mark.H ∈ (markLeft.run w).drop (i + 1) ↔ TBU.H ∈ w.drop (i + 1) := by
    simp only [List.mem_iff_getElem?, List.getElem?_drop, markLeft_run_getElem?_H_iff]
  refine List.ext_getElem? fun i => ?_
  rw [utp.map_getElem?, resolveRight, Mealy.getElem?_ofFlag_runRight]
  simp only [List.any_beq', List.contains_eq_mem, decide_eq_decide.mpr (hmark i)]
  rw [markLeft, Mealy.getElem?_ofFlag_run, Option.map_map]
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

/-- UTP is regular (§4.2): the (43) decomposition is a right-to-left Mealy pass after a
left-to-right one, and such a composite is computed by a bimachine — one deterministic
pass per direction ([elgot-mezei-1965]). So what fails above is one-directional
determinism, not finite-state computability. -/
theorem utp_isBimachineComputable : IsBimachineComputable utp.map := by
  rw [show utp.map = resolveRight.runRight ∘ markLeft.run from funext utp_eq_resolve_mark]
  exact resolveRight.isRightSubsequential_runRight.isBimachineComputable_comp
    markLeft.isLeftSubsequential_run rfl

/-- UTP is *fully regular* (§5.3): regular but not weakly deterministic — the class the
paper places tone in and bars segmental phonology from. -/
theorem utp_fullyRegular :
    IsBimachineComputable utp.map ∧ ¬ IsNonInteractingBimachineComputable utp.map :=
  ⟨utp_isBimachineComputable, utp_not_weaklyDeterministic⟩

/-! ### The autosegmental reading (§4.4)

The string representation reads back into autosegmental representations by `TBU.toAR`
((40)); the OCP-merged representation of the output has one `H`, linked exactly to the
plateau — [hyman-katamba-2010]'s rule as given in (7). -/

open Autosegmental in
/-- The merged output's links are the fused `H` over the surfacing positions. -/
theorem link_collapse_realize_toAR_map :
    ((AR.realize TBU.toAR (utp.map w)).collapse true).link true false k j ↔
      k = 0 ∧ utp.Surfaces w j := by
  rw [TBU.link_collapse_realize_toAR, utp.map_getElem?_H_iff]

/-- `HØØH` fuses to one H linked to all four TBUs. -/
example : ∀ j < 4,
    ((Autosegmental.AR.realize TBU.toAR (utp.map [.H, .O, .O, .H])).collapse true).link
      true false 0 j := by
  simp only [link_collapse_realize_toAR_map, true_and]
  decide

end Jardine2016a
