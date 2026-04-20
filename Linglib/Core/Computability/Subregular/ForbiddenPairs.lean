/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Tier

/-!
# Forbidden-Pair TSL_2 Grammars

A reusable schema for tier-based strictly 2-local languages defined by a
*forbidden-pair* relation `R : α → α → Prop`. The TSL_2 grammar
`TSLGrammar.ofForbiddenPairs R p` rules out any string whose tier projection
contains an adjacent pair `(a, b)` with `R a b`.

The canonical instance is `R := (· = ·)`: no two adjacent identicals on
the tier projection. This is the OCP (`Phonology.Subregular.OCP`).
Long-distance harmony patterns over a single segmental tier instantiate
other choices of `R` (e.g. `R := disagree-on-feature-X`).

Note that stress-rhythm constraints (\*Lapse, \*Clash) and the syllable
phonotactic \*Coda ban are *not* TSL_2 instances over the segmental
alphabet: \*Lapse and \*Clash are SL_2 over a *syllable*-level alphabet
(carrying stress weight), and \*Coda is SL_1. See
`Subregular/ForbiddenSingletons.lean` for the SL_1 helper.

The single bridge theorem `mem_ofForbiddenPairs_lang_iff_filter_isChain`
characterizes language membership as an `IsChain` check on the projected
string. This is the chain-side payoff of the boundary-vacuity machinery
in `Subregular/Basic.lean`. Phonological-constraint bridges
(`mkForbidPairsOnTier_zero_iff_in_lang`) layer on top in
`Theories/Phonology/Subregular/`.
-/

namespace Core.Computability.Subregular

variable {α : Type*}

/-- The set of forbidden 2-factors induced by a binary relation `R`: pairs
`[some a, some b]` with `R a b`. Boundary-adjacent factors are not
forbidden — the chain relation `CleanPair R` is boundary-vacuous. -/
def forbiddenPairsSet (R : α → α → Prop) : Set (Augmented α) :=
  { f | ∃ a b, R a b ∧ f = [some a, some b] }

/-- Chain relation associated with a forbidden-pair relation `R`: two
augmented symbols are *clean as a pair* iff they are not both `some`
related by `R`. Boundary symbols are vacuously clean on either side
(`CleanPair.isBoundaryVacuous`). -/
def CleanPair (R : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => ¬ R a b
  | _, _ => True

namespace CleanPair

variable {R : α → α → Prop}

@[simp] lemma none_left (u : Option α) : CleanPair R none u := by
  cases u <;> exact True.intro

@[simp] lemma none_right (u : Option α) : CleanPair R u none := by
  cases u <;> exact True.intro

lemma some_some (a b : α) :
    CleanPair R (some a) (some b) ↔ ¬ R a b := Iff.rfl

/-- The clean-pair relation is boundary-vacuous: `none` always satisfies it
on either side. Used to lift chain-membership of the boundary-padded
augmented string to the unpadded core. -/
lemma isBoundaryVacuous : IsBoundaryVacuous (CleanPair (α := α) R) :=
  ⟨none_left, none_right⟩

end CleanPair

/-- A list of `Option α` has no `[some a, some b]` 2-factor with `R a b`
iff it is a chain for `CleanPair R`. The factor-membership/chain bridge
underlying `mem_forbidPairs_lang_iff_filter_isChain`. -/
lemma forall_kFactors_two_not_forbiddenPairsSet_iff_isChain
    (R : α → α → Prop) (xs : List (Option α)) :
    (∀ f ∈ kFactors 2 xs, f ∉ forbiddenPairsSet R) ↔
      xs.IsChain (CleanPair R) := by
  induction xs with
  | nil =>
    refine ⟨fun _ => List.isChain_nil, ?_⟩
    intro _ f hf
    simp [kFactors] at hf
  | cons a rest ih =>
    cases rest with
    | nil =>
      refine ⟨fun _ => List.isChain_singleton _, ?_⟩
      intro _ f hf
      simp [kFactors] at hf
    | cons b rest' =>
      rw [kFactors_two_cons_cons, List.forall_mem_cons, List.isChain_cons_cons,
          ih]
      refine and_congr_left' ?_
      constructor
      · intro h1
        cases a with
        | none => exact CleanPair.none_left _
        | some a' =>
          cases b with
          | none => exact CleanPair.none_right _
          | some b' =>
            rw [CleanPair.some_some]
            intro hab
            exact h1 ⟨a', b', hab, rfl⟩
      · intro h1
        rintro ⟨a', b', hR, hz⟩
        simp only [List.cons.injEq, and_true] at hz
        obtain ⟨rfl, rfl⟩ := hz
        exact h1 hR

/-- The TSL_2 grammar capturing "no tier-adjacent pair satisfies `R`": tier
projection (via `Tier.byClass p`) followed by an SL_2 ban on
`forbiddenPairsSet R`. OCP and any single-tier adjacency-based markedness
constraint factor through this constructor. -/
def TSLGrammar.ofForbiddenPairs (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] : TSLGrammar 2 α where
  tier := p
  permitted := (forbiddenPairsSet R)ᶜ

/-- **Bridge** (TSL_2 language form): membership in
`TSLGrammar.ofForbiddenPairs R p` reduces to an `IsChain (¬ R · ·)` check on
the tier-projected string. The single generic membership characterization
that all forbidden-pair markedness constraints inherit. Composes (i) the
factor/chain bridge `forall_kFactors_two_not_forbiddenPairsSet_iff_isChain`,
(ii) the boundary-vacuity of `CleanPair R`, and (iii) `List.isChain_map` to
drop the `some`. -/
lemma mem_ofForbiddenPairs_lang_iff_filter_isChain (R : α → α → Prop)
    [DecidableRel R] (p : α → Prop) [DecidablePred p] (w : List α) :
    w ∈ (TSLGrammar.ofForbiddenPairs R p).lang ↔
      (w.filter (fun x => decide (p x))).IsChain (fun a b => ¬ R a b) := by
  rw [TSLGrammar.mem_lang]
  simp only [TSLGrammar.ofForbiddenPairs, Set.mem_compl_iff]
  rw [forall_kFactors_two_not_forbiddenPairsSet_iff_isChain,
      CleanPair.isBoundaryVacuous.isChain_boundary_two_iff,
      tierProject_eq_filter, List.isChain_map]
  rfl

end Core.Computability.Subregular
