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

/-! ### API around `ofForbiddenPairs` -/

/-- Membership in `(ofForbiddenPairs R p).lang` is decidable, derived from
the `IsChain` characterization. -/
instance decidableMemOfForbiddenPairsLang (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] (w : List α) :
    Decidable (w ∈ (TSLGrammar.ofForbiddenPairs R p).lang) :=
  decidable_of_iff _ (mem_ofForbiddenPairs_lang_iff_filter_isChain R p w).symm

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

/-- Any list is a chain for the always-true relation. Used as the trivial
witness for `lang_R_bot`. -/
private lemma _isChain_true : ∀ (l : List α),
    l.IsChain (fun _ _ : α => True)
  | [] => List.isChain_nil
  | [_] => List.isChain_singleton _
  | _ :: _ :: _ => by
      rw [List.isChain_cons_cons]
      exact ⟨trivial, _isChain_true _⟩

/-- **Boundary case** (`R = ⊥`): if no pair is forbidden, the language is
universal. -/
@[simp] lemma lang_R_bot (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs (fun _ _ : α => False) p).lang = Set.univ := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  exact ⟨fun _ => Set.mem_univ _, fun _ =>
    (_isChain_true _).imp (fun _ _ _ h => h.elim)⟩

/-- **Boundary case** (`p = ⊥`): if no symbol is on the tier, the projection is
empty and the language is universal. -/
@[simp] lemma lang_p_bot (R : α → α → Prop) [DecidableRel R] :
    (TSLGrammar.ofForbiddenPairs R (fun _ : α => False)).lang = Set.univ := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  rw [show w.filter (fun x => decide ((fun _ : α => False) x)) = [] by
        induction w with
        | nil => rfl
        | cons _ _ ih => simp]
  exact List.isChain_nil

/-- **Boundary case** (`p = ⊤`): with no tier filtering the language reduces
to the SL_2 case — no two adjacent symbols of the raw string may be
`R`-related. -/
lemma lang_p_top (R : α → α → Prop) [DecidableRel R] :
    (TSLGrammar.ofForbiddenPairs R (fun _ : α => True)).lang =
      { w | w.IsChain (fun a b => ¬ R a b) } := by
  ext w
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  have hfilter : w.filter (fun x => decide ((fun _ : α => True) x)) = w := by
    rw [List.filter_eq_self]; intros; simp
  rw [hfilter]; rfl

/-- Two `IsChain` witnesses on the same list combine into a chain for the
conjunction relation. Used as a helper for `lang_R_sup_eq_inter`. -/
private lemma _isChain_and {S T : α → α → Prop} : ∀ {l : List α},
    l.IsChain S → l.IsChain T → l.IsChain (fun a b => S a b ∧ T a b)
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | _ :: _ :: _, hS, hT => by
    rw [List.isChain_cons_cons] at hS hT ⊢
    exact ⟨⟨hS.1, hT.1⟩, _isChain_and hS.2 hT.2⟩

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
  exact (_isChain_and h1 h2).imp (fun _ _ ⟨hne1, hne2⟩ => fun
    | Or.inl hR1 => hne1 hR1
    | Or.inr hR2 => hne2 hR2)

/-- **Same-tier composition** (lattice form): forbidding the disjunction of two
relations on a single tier equals the meet of the two corresponding
languages. The cross-tier case is *not* expressible — see MTSL. -/
lemma lang_R_sup_eq_inf (R₁ R₂ : α → α → Prop) [DecidableRel R₁]
    [DecidableRel R₂] (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.ofForbiddenPairs (fun a b => R₁ a b ∨ R₂ a b) p).lang =
      (TSLGrammar.ofForbiddenPairs R₁ p).lang ⊓
        (TSLGrammar.ofForbiddenPairs R₂ p).lang := by
  ext w; exact mem_lang_R_sup_iff R₁ R₂ p w

/-! ### Design boundary

The language `(ofForbiddenPairs R p).lang` is **neither monotone nor
antitone** in the tier predicate `p`. Counterexample: take
`R := (· = ·)`, `p := { s }`, `p' := { s, t }` with `p ≤ p'`, and
`xs := [s, t, t]`. Then `xs.filter p = [s]` is a chain (singleton), so
`xs ∈ lang p`, but `xs.filter p' = [s, t, t]` is not a chain (`t = t` is
adjacent), so `xs ∉ lang p'`. The reverse direction also fails — see
`xs := [s, s, t]`. This is the formal counterpart of the linguistic
intuition that *which segments project to the tier* is not just a
monotone refinement but a substantive theoretical commitment, and it is
why TSL_2 over different tiers gives genuinely incomparable theories.

The substantive empirical force of this boundary is the gradient
similarity-based OCP of @cite{frisch-pierrehumbert-broe-2004}: Arabic
co-occurrence restrictions decay with featural distance rather than
following a clean tier cut, so the same `R` paired with different `p`
yields incomparable predictions about which root pairs are licit.
Dependencies on multiple tiers — e.g. simultaneous consonantal and
vocalic harmony — likewise fall outside this single-tier constructor.
The natural way to combine constraints across tiers is the multi-tier
strictly local (MTSL) family, which is *not* a special case of this
constructor. -/

end Core.Computability.Subregular
