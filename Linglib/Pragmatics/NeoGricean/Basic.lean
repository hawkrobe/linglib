import Mathlib.Data.Set.Insert
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Neo-Gricean pragmatics: secondary implicatures and the Standard Recipe

This file defines [sauerland-2004]'s consistency-gated derivation of secondary implicatures
and the Standard Recipe of [geurts-2010]. A speaker's epistemic state is a set of worlds
`s : Set W` — the same object as the `ContextSet` of `Discourse/CommonGround.lean` — and a
proposition is a `Set W`, so the speaker knows `φ` iff `s ⊆ φ`, knows `¬φ` iff `s ⊆ φᶜ`, and
is competent about `φ` iff `s ⊆ φ ∨ s ⊆ φᶜ`; consistency of the speaker is the hypothesis
`s.Nonempty` (the `Filter.NeBot` convention).
Asserting `φ` yields the primary implicature `¬Kψ` for each stronger alternative `ψ`; the
secondary implicature `K¬ψ` arises only when it is consistent with the assertion and all
primary implicatures, and the Standard Recipe obtains it from `¬Kψ` under competence.

## Main definitions

* `SatisfiesPrimaries`, `SecondaryLicensed`: the commitment set after an assertion and the
  consistency condition licensing a secondary implicature.

## Main results

* `secondaryLicensed_iff`: licensing decomposes over the alternatives, so a blocked secondary
  implicature is always blocked by a single primary; the disjunction case (K¬(A∧B) licensed,
  K¬A blocked) is `Studies/Sauerland2004.lean`.
* `secondaryLicensed_of_ssubset`: a lone asymmetrically stronger alternative always licenses
  its secondary implicature.
* `subset_compl_iff_not_subset`: the Standard Recipe — for a competent speaker, the strong
  implicature `K¬ψ` is exactly the weak implicature `¬Kψ`.

## References

* [sauerland-2004] — primary vs secondary implicatures and the consistency condition
* [geurts-2010] — the Standard Recipe; textbook presentation
* [soames-1982], [horn-1989] — the epistemic modalization `¬Kψ`
* [vanrooij-schulz-2004], [spector-2006] — the competence step `Kψ ∨ K¬ψ`
-/

namespace NeoGricean

variable {W : Type*} {s φ ψ χ : Set W} {alts : List (Set W)}

/-! ### The Sauerland derivation

Asserting `φ` against scalar alternatives `alts` commits the speaker to `Kφ` plus, for each
alternative, the primary implicature `¬Kψ` ([sauerland-2004] (42), verified p. 383). A
secondary implicature `K¬ψ` arises exactly when it is *consistent* with that commitment set
([sauerland-2004] (43)): when some nonempty epistemic state realizes the commitments together
with `K¬ψ`. -/

/-- The speaker commitment after asserting `φ` against `alts`: `Kφ` and the primary implicature
`¬Kψ` for each alternative. Per [sauerland-2004], the caller supplies only the asymmetrically
stronger alternatives (`ψ ⊂ φ`); the definition does not enforce the filter. -/
def SatisfiesPrimaries (s φ : Set W) (alts : List (Set W)) : Prop :=
  s ⊆ φ ∧ ∀ ψ ∈ alts, ¬ s ⊆ ψ

/-- [sauerland-2004]'s consistency condition: the secondary implicature `K¬ψ` is licensed iff
some nonempty epistemic state realizes the assertion, all primary implicatures, and `K¬ψ`
jointly. -/
def SecondaryLicensed (φ : Set W) (alts : List (Set W)) (ψ : Set W) : Prop :=
  ∃ s : Set W, s.Nonempty ∧ SatisfiesPrimaries s φ alts ∧ s ⊆ ψᶜ

/-- Licensing decomposes over the alternatives: `K¬ψ` is consistent with the commitments iff
the strengthened meaning `φ \ ψ` is realizable and, for each alternative `χ`, realizable
outside `ψ ∪ χ`. A blocked secondary implicature is thus always blocked by a single primary. -/
theorem secondaryLicensed_iff :
    SecondaryLicensed φ alts ψ ↔ (φ \ ψ).Nonempty ∧ ∀ χ ∈ alts, (φ \ (ψ ∪ χ)).Nonempty := by
  constructor
  · rintro ⟨s, hs, ⟨hφ, hprim⟩, hψ⟩
    refine ⟨hs.mono fun w hw => ⟨hφ hw, hψ hw⟩, fun χ hχ => ?_⟩
    obtain ⟨w, hw, hχ⟩ := Set.not_subset.1 (hprim χ hχ)
    exact ⟨w, hφ hw, fun h => h.elim (hψ hw) hχ⟩
  · rintro ⟨⟨w₀, hw₀⟩, h⟩
    induction alts with
    | nil =>
      exact ⟨{w₀}, Set.singleton_nonempty w₀, ⟨Set.singleton_subset_iff.2 hw₀.1, by simp⟩,
        Set.singleton_subset_iff.2 hw₀.2⟩
    | cons χ alts ih =>
      obtain ⟨s, hs, ⟨hφ, hprim⟩, hψ⟩ := ih fun χ' hχ' => h χ' (List.mem_cons_of_mem χ hχ')
      obtain ⟨w, hφw, hw⟩ := h χ List.mem_cons_self
      obtain ⟨hψw, hχw⟩ := not_or.1 hw
      refine ⟨insert w s, Set.insert_nonempty w s,
        ⟨Set.insert_subset_iff.2 ⟨hφw, hφ⟩, List.forall_mem_cons.2 ⟨?_, ?_⟩⟩,
        Set.insert_subset_iff.2 ⟨hψw, hψ⟩⟩
      · exact fun hk => hχw (hk (Set.mem_insert w s))
      · exact fun χ' hχ' hk => hprim χ' hχ' ((Set.subset_insert w s).trans hk)

/-- For a lone alternative `χ`, `K¬ψ` is licensed iff `φ` is realizable outside `ψ ∪ χ`. -/
theorem secondaryLicensed_singleton :
    SecondaryLicensed φ [χ] ψ ↔ (φ \ (ψ ∪ χ)).Nonempty := by
  rw [secondaryLicensed_iff, List.forall_mem_singleton]
  exact and_iff_right_of_imp fun h => h.mono (Set.sdiff_subset_sdiff_right Set.subset_union_left)

/-- Against its own alternative alone, `K¬ψ` is licensed iff the strengthened meaning `φ \ ψ`
is realizable. -/
theorem secondaryLicensed_singleton_self : SecondaryLicensed φ [ψ] ψ ↔ (φ \ ψ).Nonempty := by
  simp [secondaryLicensed_singleton]

/-- A lone asymmetrically stronger alternative always yields its secondary implicature: the
*some ⇝ not all* case. -/
theorem secondaryLicensed_of_ssubset (h : ψ ⊂ φ) : SecondaryLicensed φ [ψ] ψ :=
  secondaryLicensed_singleton_self.2 (Set.sdiff_nonempty.2 h.2)

/-! ### Competence and the Standard Recipe

Competence about `ψ` is [sauerland-2004]'s `Kψ ∨ K¬ψ`, `s ⊆ ψ ∨ s ⊆ ψᶜ` — the speaker *knows
whether* `ψ`, which is support of the polar question `Question.polar ψ` by
`Question.mem_polar`. -/

/-- A consistent speaker cannot both know `ψ` and know `¬ψ`. -/
theorem not_subset_compl_of_subset (hs : s.Nonempty) (h : s ⊆ ψ) : ¬ s ⊆ ψᶜ :=
  fun h' => hs.elim fun _ hw => h' hw (h hw)

/-- The Standard Recipe: for a consistent speaker competent about `ψ`, the strong implicature
`K¬ψ` is exactly the weak implicature `¬Kψ`. -/
theorem subset_compl_iff_not_subset (hs : s.Nonempty) (hc : s ⊆ ψ ∨ s ⊆ ψᶜ) :
    s ⊆ ψᶜ ↔ ¬ s ⊆ ψ :=
  ⟨fun h h' => not_subset_compl_of_subset hs h' h, hc.resolve_left⟩

end NeoGricean
