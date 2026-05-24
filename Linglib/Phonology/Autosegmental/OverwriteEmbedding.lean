import Linglib.Phonology.Autosegmental.Floating

/-!
# Overwrite-to-Floating embedding and divergence theorem

The McPherson–Lamont 2026 floating-tone encoding (`FloatingForm S TRN`) is
strictly more expressive than the Rolle 2018 overwrite encoding
(`List (TBU S)` via `tonalOverwrite`). This file makes the divergence
explicit:

1. `FloatingForm.ofTBUList` lifts any TBU list into a `FloatingForm`
   with tautomorphic single-tone links — the canonical image of the
   overwrite encoding under uniform morpheme assignment.

2. `FloatingForm.ofTBUList_linksTo_subsingleton` shows every TBU in
   the image carries at most one surface tone.

3. `FloatingForm.exists_multi_tone_TBU` constructs a `FloatingForm`
   with two surface tones on one TBU — a configuration unreachable
   by the embedding.

The substantive consequence: constraints requiring multi-tone TBUs
(*FALL, *CROWD per @cite{mcpherson-lamont-2026}) and heteromorphic
links (*TAUTDOCK after @cite{wolf-2007}) are evaluable on
`FloatingForm` but not on overwrite outputs. This formalises the
docstring claim in `Floating.lean` that the floating substrate
"refactors over" the overwrite substrate — the gap is theorem-level,
not editorial.

## Main definitions

* `FloatingForm.ofTBUList` — embedding from the overwrite substrate.

## Main results

* `FloatingForm.ofTBUList_linksTo_subsingleton` — embedding produces
  ≤ 1 surface tone per TBU.
* `FloatingForm.exists_multi_tone_TBU` — the floating substrate admits
  multi-tone TBUs.

## References

* @cite{rolle-2018} — replacive-dominant GT via `tonalOverwrite`
* @cite{mcpherson-lamont-2026} — multi-tone TBUs in Poko
* @cite{wolf-2007} — *TAUTDOCK requires heteromorphic discrimination
-/

namespace Phonology.Autosegmental

open Phonology.Autosegmental.GrammaticalTone (TBU)
open Phonology.Autosegmental.RegisterTier (TRN)

/-! ### Embedding -/

/-- Embed a `List (TBU S)` (the output type of `tonalOverwrite`) into
    `FloatingForm S TRN`, assigning all TBUs and their tones the same
    morpheme `m`. Each TBU at position `i` becomes a `SegSpec`, each
    tone becomes a `TierSpec TRN` at the same position, and surface link
    `(i, i)` connects them. All resulting links are tautomorphic. -/
def FloatingForm.ofTBUList {S : Type*} (host : List (TBU S)) (m : Morpheme) :
    FloatingForm S TRN where
  lower := host.map (fun tbu => { seg := tbu.seg, morpheme := m })
  upper := host.map (fun tbu => { value := tbu.tone, morpheme := m })
  links := ((List.range host.length).map (fun i => (i, i))).toFinset
  deletedTier := ∅
  surfaceLinks := ((List.range host.length).map (fun i => (i, i))).toFinset

/-! ### Divergence theorems -/

/-- **Divergence (universal direction).** After the embedding via
    `FloatingForm.ofTBUList`, every TBU has at most one surface tone —
    the unique tautomorphic link `(i, i)`. -/
theorem FloatingForm.ofTBUList_linksTo_subsingleton {S : Type*}
    (host : List (TBU S)) (m : Morpheme) (i : SegIdx) :
    ((FloatingForm.ofTBUList host m).linksTo i).length ≤ 1 := by
  -- Two-line argument: the filter result is `Nodup` (filter of `range`),
  -- and all its elements equal `i` (the only `(k, i)` in the diagonal
  -- surface-link set has `k = i`). So `count i = length` and the `Nodup`
  -- bound `count i ≤ 1` gives `length ≤ 1`.
  have h_all : ∀ k ∈ (FloatingForm.ofTBUList host m).linksTo i, k = i := by
    intro k hk
    unfold FloatingForm.linksTo at hk
    rw [List.mem_filter] at hk
    obtain ⟨_, hPred⟩ := hk
    have hMem : (k, i) ∈ (FloatingForm.ofTBUList host m).surfaceLinks :=
      of_decide_eq_true hPred
    unfold FloatingForm.ofTBUList at hMem
    rw [List.mem_toFinset, List.mem_map] at hMem
    obtain ⟨j, _, hPair⟩ := hMem
    have hjk : j = k := ((Prod.mk.injEq _ _ _ _).mp hPair).1
    have hji : j = i := ((Prod.mk.injEq _ _ _ _).mp hPair).2
    exact hjk.symm.trans hji
  have h_nodup : ((FloatingForm.ofTBUList host m).linksTo i).Nodup := by
    unfold FloatingForm.linksTo
    exact List.nodup_range.sublist List.filter_sublist
  have h_count_le : ((FloatingForm.ofTBUList host m).linksTo i).count i ≤ 1 :=
    List.nodup_iff_count_le_one.mp h_nodup i
  have h_count_eq : ((FloatingForm.ofTBUList host m).linksTo i).count i =
                    ((FloatingForm.ofTBUList host m).linksTo i).length :=
    List.count_eq_length.mpr (fun b hb => (h_all b hb).symm)
  omega

/-- **Divergence (existence direction).** There is a `FloatingForm`
    with two surface tones on a single TBU — a configuration unreachable
    by `FloatingForm.ofTBUList`. Witnesses the expressive gap between
    the overwrite encoding (@cite{rolle-2018}) and the floating encoding
    (@cite{mcpherson-lamont-2026}). -/
theorem FloatingForm.exists_multi_tone_TBU :
    ∃ f : FloatingForm Unit TRN, ∃ i : SegIdx, 2 ≤ (f.linksTo i).length := by
  refine ⟨?_, 0, ?_⟩
  · exact
    { lower := [{ seg := (), morpheme := { form := "m" } }]
      upper :=
        [{ value := TRN.H, morpheme := { form := "m" } },
         { value := TRN.L, morpheme := { form := "m" } }]
      links := ∅
      deletedTier := ∅
      surfaceLinks := {(0, 0), (1, 0)} }
  · decide

end Phonology.Autosegmental
