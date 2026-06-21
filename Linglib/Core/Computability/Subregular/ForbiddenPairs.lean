/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Tier
import Linglib.Core.Data.List.Factors
import Linglib.Core.Data.List.Chain

/-!
# Forbidden-pair TSL_2 grammars

A tier-based strictly 2-local schema [heinz-rawal-tanner-2011]: for a
*forbidden-pair* relation `R : α → α → Prop` and tier predicate `p`,
`TSLGrammar.ofForbiddenPairs R p` bans any string whose tier projection has an
adjacent pair `(a, b)` with `R a b`. The canonical instance is the OCP
[mccarthy-1986] (`R := (· = ·)`); OCP-Feature and single-tier harmony (with `p`
carrying blocking/transparency [mcmullin-2016]) are other choices of `R`.

## Main definitions

* `Subregular.TSLGrammar.ofForbiddenPairs R p` — the TSL_2 grammar above.
* `Subregular.countAdjacent R xs` — count of `R`-related adjacent pairs in `xs`.

## Main results

* `Subregular.mem_ofForbiddenPairs_lang_iff_filter_isChain` — membership reduces
  to an `IsChain (¬ R · ·)` check on the tier-projected string.

## Implementation notes

Out of scope (they need a richer-than-segmental alphabet): \*Lapse/\*Clash (SL_2
over a syllable alphabet) and \*Coda (SL_1, via `mkForbidSingletonOnTier`).
Similarity-graded [hansson-2010] and interval-conditioned (ITSL) harmony, and
cross-tier dependencies (MTSL), also fall outside this single-tier constructor.
-/

namespace Subregular

variable {α : Type*} (R : α → α → Prop)

/-- The forbidden 2-factors induced by `R`: the pairs `[some a, some b]` with
`R a b`. -/
def forbiddenPairs : Set (Augmented α) :=
  { f | ∃ a b, R a b ∧ f = [some a, some b] }

/-- The adjacency relation for `R`: a pair is clean unless both symbols are
`some` and `R`-related (`none` is vacuously clean — `CleanPair.isBoundaryVacuous`). -/
def CleanPair : Option α → Option α → Prop
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

/-- `CleanPair R` is boundary-vacuous: `none` satisfies it on either side. -/
lemma isBoundaryVacuous : IsBoundaryVacuous (CleanPair (α := α) R) :=
  ⟨none_left, none_right⟩

end CleanPair

/-- A list has no forbidden 2-factor iff it is a chain for `CleanPair R`. -/
lemma forbiddenPairFree_iff_isChain (xs : Augmented α) :
    (∀ f ∈ List.kFactors 2 xs, f ∉ forbiddenPairs R) ↔ xs.IsChain (CleanPair R) := by
  induction xs with
  | nil => simp
  | cons a rest ih => cases rest with
    | nil => simp
    | cons b rest' =>
      rw [List.kFactors_two_cons_cons, List.forall_mem_cons, List.isChain_cons_cons, ih]
      exact and_congr_left' (by cases a <;> cases b <;> simp [forbiddenPairs, CleanPair])

/-- The TSL_2 grammar banning tier-adjacent pairs satisfying `R`: tier `p`,
permitting everything but `forbiddenPairs R`. -/
def TSLGrammar.ofForbiddenPairs (p : α → Prop) [DecidablePred p] : TSLGrammar 2 α where
  tier := p
  permitted := (forbiddenPairs R)ᶜ

/-- Membership in `ofForbiddenPairs R p` reduces to an `IsChain (¬ R · ·)` check
on the tier-projected string — the characterization all forbidden-pair
constraints inherit. -/
lemma mem_ofForbiddenPairs_lang_iff_filter_isChain (p : α → Prop) [DecidablePred p] (w : List α) :
    w ∈ (TSLGrammar.ofForbiddenPairs R p).lang ↔
      (w.filter (fun x => decide (p x))).IsChain (fun a b => ¬ R a b) := by
  rw [TSLGrammar.mem_lang]
  simp only [TSLGrammar.ofForbiddenPairs, Set.mem_compl_iff]
  rw [forbiddenPairFree_iff_isChain,
      CleanPair.isBoundaryVacuous.isChain_boundary_two_iff,
      tierProject_eq_filter, List.isChain_map]
  rfl

/-! ### Adjacent-pair counting

`countAdjacent` is the violation-count companion of the membership view; the
OT-side `mkForbidPairsOnTier` consumes it via `countAdjacent_eq_zero_iff_isChain`. -/

/-- Count of adjacent pairs `(a, b)` in `xs` with `R a b`. -/
def countAdjacent [DecidableRel R] : List α → Nat
  | [] | [_] => 0
  | a :: b :: rest => (if R a b then 1 else 0) + countAdjacent (b :: rest)

/-- `countAdjacent R xs = 0` iff `xs` is a chain for `¬ R · ·`. -/
lemma countAdjacent_eq_zero_iff_isChain [DecidableRel R] (xs : List α) :
    countAdjacent R xs = 0 ↔ xs.IsChain (fun a b => ¬ R a b) := by
  induction xs with
  | nil => simp [countAdjacent]
  | cons a rest ih => cases rest with
    | nil => simp [countAdjacent]
    | cons b rest' =>
      rw [List.isChain_cons_cons, ← ih]
      by_cases hRab : R a b <;> simp [countAdjacent, hRab]

/-! ### API around `ofForbiddenPairs` -/

/-- Membership in `(ofForbiddenPairs R p).lang` is decidable, via the `IsChain`
characterization. -/
instance decidableMemOfForbiddenPairsLang [DecidableRel R] (p : α → Prop) [DecidablePred p] (w : List α) :
    Decidable (w ∈ (TSLGrammar.ofForbiddenPairs R p).lang) :=
  decidable_of_iff _ (mem_ofForbiddenPairs_lang_iff_filter_isChain R p w).symm

/-- The empty string is in every forbidden-pair language. -/
@[simp] lemma nil_mem_ofForbiddenPairs_lang (p : α → Prop) [DecidablePred p] :
    ([] : List α) ∈ (TSLGrammar.ofForbiddenPairs R p).lang :=
  (mem_ofForbiddenPairs_lang_iff_filter_isChain R p []).mpr List.isChain_nil

/-- Forbidding more pairs shrinks the language: `R ≤ R'` gives
`lang R' ≤ lang R`. -/
lemma lang_antitone_R {R R' : α → α → Prop} (h : ∀ a b, R a b → R' a b)
    (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs R' p).lang ≤
      (TSLGrammar.ofForbiddenPairs R p).lang := fun w hw =>
  (mem_ofForbiddenPairs_lang_iff_filter_isChain R p w).mpr <|
    ((mem_ofForbiddenPairs_lang_iff_filter_isChain R' p w).mp hw).imp
      fun _ _ hR' hR => hR' (h _ _ hR)

/-- If no pair is forbidden (`R = ⊥`), the language is universal. -/
@[simp] lemma lang_R_bot (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs (fun _ _ : α => False) p).lang = Set.univ := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  exact ⟨fun _ => Set.mem_univ _, fun _ =>
    (List.isChain_top _).imp (fun _ _ _ h => h.elim)⟩

/-- If no symbol is on the tier (`p = ⊥`), the language is universal. -/
@[simp] lemma lang_p_bot :
    (TSLGrammar.ofForbiddenPairs R (fun _ : α => False)).lang = Set.univ := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  rw [show w.filter (fun x => decide ((fun _ : α => False) x)) = [] from
        List.filter_eq_nil_iff.mpr (fun _ _ h => by
          simp only [decide_false, Bool.false_eq_true] at h)]
  exact List.isChain_nil

/-- With no tier filtering (`p = ⊤`) the language is the SL_2 case: no two
adjacent symbols of the raw string are `R`-related. (Not `@[simp]`: the RHS is
no simpler than the LHS.) -/
lemma lang_p_top :
    (TSLGrammar.ofForbiddenPairs R (fun _ : α => True)).lang =
      { w | w.IsChain (fun a b => ¬ R a b) } := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  have hfilter : w.filter (fun x => decide ((fun _ : α => True) x)) = w := by
    rw [List.filter_eq_self]; intros; simp only [decide_true]
  rw [hfilter]; rfl

/-- Forbidding `R₁ ∨ R₂` on one tier is conjunctive membership in the two
languages. (Cross-tier composition needs MTSL, not this constructor.) -/
lemma mem_lang_R_sup_iff (R₁ R₂ : α → α → Prop) (p : α → Prop) [DecidablePred p] (w : List α) :
    w ∈ (TSLGrammar.ofForbiddenPairs (fun a b => R₁ a b ∨ R₂ a b) p).lang ↔
      w ∈ (TSLGrammar.ofForbiddenPairs R₁ p).lang ∧
        w ∈ (TSLGrammar.ofForbiddenPairs R₂ p).lang := by
  simp only [mem_ofForbiddenPairs_lang_iff_filter_isChain, not_or, List.isChain_and_iff]

/-- Lattice form of `mem_lang_R_sup_iff`: `lang (R₁ ∨ R₂) = lang R₁ ⊓ lang R₂`. -/
lemma lang_R_sup_eq_inf (R₁ R₂ : α → α → Prop) (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs (fun a b => R₁ a b ∨ R₂ a b) p).lang =
      (TSLGrammar.ofForbiddenPairs R₁ p).lang ⊓
        (TSLGrammar.ofForbiddenPairs R₂ p).lang :=
  Set.ext fun w => mem_lang_R_sup_iff R₁ R₂ p w

/-! ### Design boundary: non-monotonicity in the tier predicate

`(ofForbiddenPairs R p).lang` is **neither monotone nor antitone** in the tier
predicate `p` (`lang_p_not_monotone`/`lang_p_not_antitone` below): which segments
project is a substantive commitment, not just a monotone refinement. -/

/-- Two-element alphabet used as a witness for the design-boundary
non-monotonicity theorems. Local to this section. -/
private inductive TwoSym | s | t deriving DecidableEq

private def Pₛ : TwoSym → Prop | .s => True | .t => False
private def Pₛₜ : TwoSym → Prop | _ => True

private instance : DecidablePred Pₛ
  | .s => isTrue trivial
  | .t => isFalse not_false
private instance : DecidablePred Pₛₜ := fun _ => isTrue trivial

/-- `(ofForbiddenPairs R p).lang` is not monotone in `p`: for `Pₛ ≤ Pₛₜ`,
`[s, t, t] ∈ lang Pₛ` (tier filter `[s]` is a chain) but `∉ lang Pₛₜ` (filter
`[s, t, t]` has the OCP-violating `t, t`). -/
private theorem lang_p_not_monotone :
    (∀ a, Pₛ a → Pₛₜ a) ∧
      [TwoSym.s, .t, .t] ∈ (TSLGrammar.ofForbiddenPairs (· = ·) Pₛ).lang ∧
      [TwoSym.s, .t, .t] ∉ (TSLGrammar.ofForbiddenPairs (· = ·) Pₛₜ).lang :=
  ⟨fun _ _ => trivial, by decide, by decide⟩

/-- `(ofForbiddenPairs R p).lang` is not antitone in `p`: for `Pₛ ≤ Pₛₜ`,
`[s, t, s] ∉ lang Pₛ` (tier filter `[s, s]` violates OCP) but `∈ lang Pₛₜ`
(filter `[s, t, s]` is a chain — the `t` separates the `s`s). -/
private theorem lang_p_not_antitone :
    (∀ a, Pₛ a → Pₛₜ a) ∧
      [TwoSym.s, .t, .s] ∉ (TSLGrammar.ofForbiddenPairs (· = ·) Pₛ).lang ∧
      [TwoSym.s, .t, .s] ∈ (TSLGrammar.ofForbiddenPairs (· = ·) Pₛₜ).lang :=
  ⟨fun _ _ => trivial, by decide, by decide⟩

end Subregular
