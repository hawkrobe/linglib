/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Tier

/-!
# Forbidden-Pair TSL_2 Grammars

A reusable schema @cite{heinz-rawal-tanner-2011} for tier-based strictly
2-local languages defined by a *forbidden-pair* relation
`R : α → α → Prop`. The TSL_2 grammar `TSLGrammar.ofForbiddenPairs R p`
rules out any string whose tier projection contains an adjacent pair
`(a, b)` with `R a b`.

The canonical instance is `R := (· = ·)`: no two adjacent identicals on
the tier projection. This is the OCP @cite{mccarthy-1986}
(`Phonology.Subregular.OCP`). The schema is general enough to capture
OCP-Feature variants (`R := share-feature-X`) and any single-tier
2-factor markedness constraint over a fixed subset projection.
Long-distance harmony patterns over a single segmental tier instantiate
other choices of `R` (e.g. `R := disagree-on-feature-X`).

Note that stress-rhythm constraints (\*Lapse, \*Clash) and the syllable
phonotactic \*Coda ban are *not* TSL_2 instances over the segmental
alphabet: \*Lapse and \*Clash are SL_2 over a *syllable*-level alphabet
(carrying stress weight), and \*Coda is SL_1 over an alphabet that
encodes syllable structure (e.g. CV templates with marked coda symbols).
The OT-side helper for the SL_1 case is `mkForbidSingletonOnTier` in
`Theories/Phonology/OptimalityTheory/Constraints.lean`; the language-side
SL_1 substrate is in `Subregular/StrictlyLocal.lean` (the `k = 1` case).

The single bridge theorem `mem_ofForbiddenPairs_lang_iff_filter_isChain`
characterizes language membership as an `IsChain` check on the projected
string. This is the chain-side payoff of the boundary-vacuity machinery
in `Subregular/Defs.lean`. Phonological-constraint bridges
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
    simp only [kFactors_two_nil, List.not_mem_nil] at hf
  | cons a rest ih =>
    cases rest with
    | nil =>
      refine ⟨fun _ => List.isChain_singleton _, ?_⟩
      intro _ f hf
      simp only [kFactors_two_singleton, List.not_mem_nil] at hf
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

/-! ### Adjacent-pair counting

Promoted from `Theories/Phonology/OptimalityTheory/Constraints.lean`:
`countAdjacent R xs` counts the adjacent `(a, b)` pairs in `xs` with
`R a b`. Alphabet-generic; nothing OT-specific. The OT-side
`mkForbidPairsOnTier` constructor consumes this directly, and the
chain-bridge `countAdjacent_eq_zero_iff_isChain` connects it to the
language-level `IsChain` characterization above. -/

/-- Count adjacent pairs `(a, b)` in a list satisfying a binary relation
`R`. The shared engine behind any "forbidden adjacent pair" markedness
or violation count: OCP (`R := (· = ·)`), agreement (`R := (· ≠ ·)`),
and asymmetric harmony all pass through. -/
def countAdjacent (R : α → α → Prop) [DecidableRel R] : List α → Nat
  | [] | [_] => 0
  | a :: b :: rest => (if R a b then 1 else 0) + countAdjacent R (b :: rest)

/-- `countAdjacent R xs = 0` iff no two consecutive elements of `xs` are
related by `R`. The chain-form characterisation of zero-violation
forbidden-pair candidates. -/
lemma countAdjacent_eq_zero_iff_isChain (R : α → α → Prop) [DecidableRel R]
    (xs : List α) :
    countAdjacent R xs = 0 ↔ xs.IsChain (fun a b => ¬ R a b) := by
  induction xs with
  | nil => exact ⟨fun _ => List.isChain_nil, fun _ => rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil => exact ⟨fun _ => List.isChain_singleton _, fun _ => rfl⟩
    | cons b rest' =>
      show (if R a b then 1 else 0) + countAdjacent R (b :: rest') = 0 ↔ _
      rw [List.isChain_cons_cons]
      by_cases hRab : R a b
      · simp [hRab]
      · simp [hRab, ih]

/-! ### API around `ofForbiddenPairs` -/

/-- Membership in `(ofForbiddenPairs R p).lang` is decidable, derived from
the `IsChain` characterization. -/
instance decidableMemOfForbiddenPairsLang (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] (w : List α) :
    Decidable (w ∈ (TSLGrammar.ofForbiddenPairs R p).lang) :=
  decidable_of_iff _ (mem_ofForbiddenPairs_lang_iff_filter_isChain R p w).symm

/-- The empty string is in every forbidden-pair language: there are no
tier-adjacent pairs to check. -/
@[simp] lemma nil_mem_ofForbiddenPairs_lang (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] :
    ([] : List α) ∈ (TSLGrammar.ofForbiddenPairs R p).lang :=
  (mem_ofForbiddenPairs_lang_iff_filter_isChain R p []).mpr List.isChain_nil

/-- **Antitonicity in `R`**: forbidding more pairs (`R ≤ R'`) shrinks the
language. The chain witness for the larger `R'` immediately yields one for
the smaller `R` since `¬ R' a b → ¬ R a b`. -/
lemma lang_antitone_R {R R' : α → α → Prop} [DecidableRel R] [DecidableRel R']
    (h : ∀ a b, R a b → R' a b) (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs R' p).lang ≤
      (TSLGrammar.ofForbiddenPairs R p).lang := fun w hw =>
  (mem_ofForbiddenPairs_lang_iff_filter_isChain R p w).mpr <|
    ((mem_ofForbiddenPairs_lang_iff_filter_isChain R' p w).mp hw).imp
      fun _ _ hR' hR => hR' (h _ _ hR)

/-- **Boundary case** (`R = ⊥`): if no pair is forbidden, the language is
universal. -/
@[simp] lemma lang_R_bot (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs (fun _ _ : α => False) p).lang = Set.univ := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  exact ⟨fun _ => Set.mem_univ _, fun _ =>
    (List.isChain_top _).imp (fun _ _ _ h => h.elim)⟩

/-- **Boundary case** (`p = ⊥`): if no symbol is on the tier, the projection is
empty and the language is universal. -/
@[simp] lemma lang_p_bot (R : α → α → Prop) [DecidableRel R] :
    (TSLGrammar.ofForbiddenPairs R (fun _ : α => False)).lang = Set.univ := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  rw [show w.filter (fun x => decide ((fun _ : α => False) x)) = [] from
        List.filter_eq_nil_iff.mpr (fun _ _ h => by
          simp only [decide_false, Bool.false_eq_true] at h)]
  exact List.isChain_nil

/-- **Boundary case** (`p = ⊤`): with no tier filtering the language reduces
to the SL_2 case — no two adjacent symbols of the raw string may be
`R`-related. Not marked `@[simp]`: the RHS is not a simpler normal form
than the LHS (compare `lang_R_bot`/`lang_p_bot` which simplify to
`Set.univ`). -/
lemma lang_p_top (R : α → α → Prop) [DecidableRel R] :
    (TSLGrammar.ofForbiddenPairs R (fun _ : α => True)).lang =
      { w | w.IsChain (fun a b => ¬ R a b) } := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  have hfilter : w.filter (fun x => decide ((fun _ : α => True) x)) = w := by
    rw [List.filter_eq_self]; intros; simp only [decide_true]
  rw [hfilter]; rfl

/-- **Same-tier composition** (membership form): forbidding the disjunction of
two relations on a single tier coincides with conjunctive membership in the
two corresponding languages. The cross-tier case (two relations on *different*
tiers `p₁ ≠ p₂`) does NOT factor through this constructor — that is precisely
the empirical and formal motivation for multi-tier strictly local languages
(MTSL). -/
lemma mem_lang_R_sup_iff (R₁ R₂ : α → α → Prop) [DecidableRel R₁]
    [DecidableRel R₂] (p : α → Prop) [DecidablePred p] (w : List α) :
    w ∈ (TSLGrammar.ofForbiddenPairs (fun a b => R₁ a b ∨ R₂ a b) p).lang ↔
      w ∈ (TSLGrammar.ofForbiddenPairs R₁ p).lang ∧
        w ∈ (TSLGrammar.ofForbiddenPairs R₂ p).lang := by
  simp only [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  refine ⟨fun h => ⟨h.imp (fun _ _ hne h1 => hne (Or.inl h1)),
                    h.imp (fun _ _ hne h2 => hne (Or.inr h2))⟩, ?_⟩
  rintro ⟨h1, h2⟩
  exact (h1.and h2).imp (fun _ _ ⟨hne1, hne2⟩ => fun
    | Or.inl hR1 => hne1 hR1
    | Or.inr hR2 => hne2 hR2)

/-- **Same-tier composition** (lattice form): forbidding the disjunction of two
relations on a single tier equals the meet of the two corresponding
languages. The cross-tier case is *not* expressible — see MTSL. -/
lemma lang_R_sup_eq_inf (R₁ R₂ : α → α → Prop) [DecidableRel R₁]
    [DecidableRel R₂] (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs (fun a b => R₁ a b ∨ R₂ a b) p).lang =
      (TSLGrammar.ofForbiddenPairs R₁ p).lang ⊓
        (TSLGrammar.ofForbiddenPairs R₂ p).lang :=
  Set.ext fun w => mem_lang_R_sup_iff R₁ R₂ p w

/-! ### Design boundary (mathematical)

The language `(ofForbiddenPairs R p).lang` is **neither monotone nor
antitone** in the tier predicate `p`. Both failure directions are
witnessed by the theorems `lang_p_not_monotone` and `lang_p_not_antitone`
below. This is the formal counterpart of the linguistic intuition that
*which segments project to the tier* is not just a monotone refinement
but a substantive theoretical commitment, and it is why TSL_2 over
different tiers gives genuinely incomparable theories. -/

/-- Two-element alphabet used as a witness for the design-boundary
non-monotonicity theorems. Local to this section. -/
private inductive TwoSym | s | t deriving DecidableEq

private def Pₛ : TwoSym → Prop | .s => True | .t => False
private def Pₛₜ : TwoSym → Prop | _ => True

private instance : DecidablePred Pₛ
  | .s => isTrue trivial
  | .t => isFalse not_false
private instance : DecidablePred Pₛₜ := fun _ => isTrue trivial

/-- **Non-monotonicity** of `(ofForbiddenPairs R p).lang` in the tier
predicate `p` (forward direction): there exist `p ≤ p'` and a string `xs`
such that `xs ∈ lang p` but `xs ∉ lang p'`. Witness: `R := (· = ·)`,
`p := {s}`, `p' := {s, t}`, `xs := [s, t, t]`; `filter` under `p` gives
`[s]` (chain), but under `p'` gives `[s, t, t]` (the adjacent `t, t`
violates the OCP). -/
theorem lang_p_not_monotone :
    ∃ (R : TwoSym → TwoSym → Prop) (_ : DecidableRel R)
      (p p' : TwoSym → Prop) (_ : DecidablePred p) (_ : DecidablePred p')
      (xs : List TwoSym),
      (∀ a, p a → p' a) ∧
        xs ∈ (TSLGrammar.ofForbiddenPairs R p).lang ∧
        xs ∉ (TSLGrammar.ofForbiddenPairs R p').lang :=
  ⟨(· = ·), inferInstance, Pₛ, Pₛₜ, inferInstance, inferInstance,
    [.s, .t, .t], by intro a _; cases a <;> trivial,
    by decide, by decide⟩

/-- **Non-antitonicity** of `(ofForbiddenPairs R p).lang` in the tier
predicate `p` (reverse direction): there exist `p ≤ p'` and a string `xs`
such that `xs ∉ lang p` but `xs ∈ lang p'`. Witness: `R := (· = ·)`,
`p := {s}`, `p' := {s, t}`, `xs := [s, t, s]`; `filter` under `p` gives
`[s, s]` (the adjacent `s, s` violates the OCP), but under `p'` gives
`[s, t, s]` (chain — interleaving `t` separates the `s`s). -/
theorem lang_p_not_antitone :
    ∃ (R : TwoSym → TwoSym → Prop) (_ : DecidableRel R)
      (p p' : TwoSym → Prop) (_ : DecidablePred p) (_ : DecidablePred p')
      (xs : List TwoSym),
      (∀ a, p a → p' a) ∧
        xs ∉ (TSLGrammar.ofForbiddenPairs R p).lang ∧
        xs ∈ (TSLGrammar.ofForbiddenPairs R p').lang :=
  ⟨(· = ·), inferInstance, Pₛ, Pₛₜ, inferInstance, inferInstance,
    [.s, .t, .s], by intro a _; cases a <;> trivial,
    by decide, by decide⟩

/-! ### Design boundary (empirical)

The substantive empirical force of the non-monotonicity result is the
gradient similarity-based OCP of @cite{frisch-pierrehumbert-broe-2004}:
Arabic co-occurrence restrictions decay with featural distance rather
than following a clean tier cut, so the same `R` paired with different
`p` yields incomparable predictions about which root pairs are licit.
See `Studies/FrischPierrehumbertBroe2004.lean` for
the load-bearing instance: the natural-classes similarity metric
(FPB eq. 7), the worked examples /f, m/ → 2/9 and /b, f/ → 3/8, and
the `categorical_fails_three_test_points` divergence theorem witnessing
that no TSL_2 grammar with `R := λ a b => similarity la b ≥ t` can
reproduce three specific Table IV bins.

Dependencies on multiple tiers — e.g. simultaneous consonantal and
vocalic harmony — likewise fall outside this single-tier constructor.
The natural way to combine constraints across tiers is the multi-tier
strictly local (MTSL) family, which is *not* a special case of this
constructor. -/

end Core.Computability.Subregular
