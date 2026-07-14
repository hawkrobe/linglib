import Linglib.Semantics.Modification.Classification
import Linglib.Core.Logic.Trivalent
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Kamp (1975): Two Theories about Adjectives
[kamp-1975]

Theory 1 classifies adjective meanings (functions from properties to
properties) by meaning postulates — the classification lives in
`Semantics/Modification/Classification.lean`. Theory 2, building on
[van-fraassen-1969]'s supervaluations, derives the comparative from
quantification over completions of a partial model; we formalize its
comparative core, leaving the model apparatus abstract.

## Main results

* `kleene_dilemma`: no truth-functional conjunction is both idempotent
  at the borderline value and false on borderline contradictions.
* `kampPreorder`: the completion comparative, definition (12).
* `kampMeasureLe`: the measure comparative, definition (13);
  `kampMeasureLe_total` is Kamp's objection to it and
  `clever_incomparable` his Smith/Jones witness.
* `kampPreorder_le_iff_kampMeasureLe`: for one-dimensional adjectives,
  (12) and (13) coincide.
* `grayAdj`, `fakeAdj`, `skillfulAdj`, `allegedAdj`: witnesses for the
  four classes, shared by `Partee2010.lean` and `DelPinal2015.lean`.
-/

namespace Kamp1975

open Modification Modifier

/-! ### Bridge to single-world predicates

The classification (`Modifier.isIntersective`, `.isSubsective`, …) is
one order-theoretic definition instantiated at two carriers: the
intensional `Property W E = W → E → Prop` and the single-world
`E → Prop`. The bridge theorems below show that fixing a world sends
the first instance to the second. -/

section Bridge

variable {W E : Type*}

/-- Single-world specialization: given a fixed world, the intensional
    instance of `Modifier.isIntersective` reduces to the `E → Prop`
    instance on the rigidified single-world view `N ↦ adj (fun _ => N) w`. -/
theorem intersective_at_world {adj : Modifier (Property W E)}
    (h : isIntersective adj) (w : W) :
    isIntersective (fun N : E → Prop => adj (fun _ => N) w) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q w, fun N => congrFun (hQ fun _ => N) w⟩

/-- Single-world specialization of `Modifier.isSubsective`. -/
theorem subsective_at_world {adj : Modifier (Property W E)}
    (h : isSubsective adj) (w : W) :
    isSubsective (fun N : E → Prop => adj (fun _ => N) w) :=
  fun N => h (fun _ => N) w

end Bridge

/-! ### The many-valued dilemma -/

/-- No truth-functional conjunction is both idempotent at the borderline
    value and false on borderline contradictions: with `neg indet = indet`,
    both demands constrain the same input pair. This is the dilemma of
    [kamp-1975], pp. 130–131, stated there for every linearly ordered
    n-valued logic; `Trivalent` is the minimal witness. -/
theorem kleene_dilemma :
    ¬∃ (meet : Trivalent → Trivalent → Trivalent),
      meet .indet .indet = .indet ∧
      meet .indet (Trivalent.neg .indet) = .false := by
  rintro ⟨meet, hidem, hcontra⟩
  rw [Trivalent.neg_indet, hidem] at hcontra
  cases hcontra

/-- Strong Kleene conjunction (`⊓` on `Trivalent`) takes the idempotent
    horn of the dilemma, so borderline contradictions are not false
    (`Trivalent.inf_compl_indet_ne_bot`) — the cost `kleene_dilemma`
    predicts for any truth-functional choice. -/
example : Trivalent.indet ⊓ Trivalent.indet = Trivalent.indet ∧
    Trivalent.indet ⊓ Trivalent.indetᶜ ≠ ⊥ :=
  ⟨inf_idem _, Trivalent.inf_compl_indet_ne_bot⟩

/-! ### Kamp's completion comparative, definition (12)

Definition (12) (paper § 4): u₁ is at least as A as u₂ iff every
admissible completion that puts u₂ in the extension also puts u₁ in it.
[klein-1980] § 5.3 states the strict comparative existentially over
comparison classes; the bridge is
`Klein1980.kleinPreorder_eq_kampPreorder`. -/

/-- Kamp's completion comparative (definition (12), paper § 4) as a
    `Preorder`: `le u₁ u₂` iff every completion in `S` that puts `u₂` in
    the extension also puts `u₁` in — `le` reads "u₁ is at least as A as
    u₂", Kamp's `≥`. The S-restricted analogue of `kleinPreorder` in
    `Delineation.lean`. Kamp credits (12) to Lewis (1970), where it is
    attributed to Kaplan. -/
@[reducible] def kampPreorder {E C : Type*} (ext : C → E → Prop) (S : Set C) :
    Preorder E where
  le u₁ u₂ := ∀ c ∈ S, ext c u₂ → ext c u₁
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ hab hbc := fun c hc h => hab c hc (hbc c hc h)

/-- The Kamp preorder is `Antitone` in S: enlarging S (more completions
    to quantify over) makes `≤` harder to satisfy. -/
theorem kampPreorder_antitone {E C : Type*} (ext : C → E → Prop) (u₁ u₂ : E) :
    Antitone (fun S => (kampPreorder ext S).le u₁ u₂) :=
  fun _ _ hle hall c hc => hall c (hle hc)

/-! ### (12) vs (13): definite vs measured comparatives

Kamp's second candidate, definition (13) (paper § 4), compares the
*measures* of the completion sets rather than the sets themselves. His
§ 5 argues against (13) for multi-criteria adjectives: it makes any two
entities comparable, while (12) leaves Smith and Jones incomparable in
cleverness — for Kamp the right verdict. For one-dimensional adjectives
(*heavy*, *tall*, *hot*) the two provably coincide. -/

section MeasuredComparative

variable {E C : Type*} (ext : C → E → Prop) [∀ c e, Decidable (ext c e)]
  (S : Finset C) (p : C → ℚ)

/-- [kamp-1975] definition (13) (paper § 4): the measure-based
    comparative — `u₁ ≤ u₂` iff the measure of completions putting `u₂`
    in the extension is at most that putting `u₁` in (`kampPreorder`'s
    orientation). Kamp's probability measure over a field of subsets is
    specialized to atomic ℚ weights over a finite completion set; only
    the ordering matters, so weights need not sum to 1. -/
def kampMeasureLe (u₁ u₂ : E) : Prop :=
  ∑ c ∈ S with ext c u₂, p c ≤ ∑ c ∈ S with ext c u₁, p c

/-- (13) is total: it makes any two objects comparable. This is Kamp's
    § 5 objection to (13); (12) does not share the property
    (`clever_incomparable`). -/
theorem kampMeasureLe_total (u₁ u₂ : E) :
    kampMeasureLe ext S p u₁ u₂ ∨ kampMeasureLe ext S p u₂ u₁ :=
  le_total _ _

/-- Definite comparison entails measured comparison: (12) implies (13)
    for nonnegative weights. -/
theorem kampMeasureLe_of_kampPreorder_le (hp : ∀ c ∈ S, 0 ≤ p c) {u₁ u₂ : E}
    (h : (kampPreorder ext (S : Set C)).le u₁ u₂) :
    kampMeasureLe ext S p u₁ u₂ := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun c hc _ => hp c (Finset.mem_filter.mp hc).1
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, h c hc.1 hc.2⟩

/-! #### The Smith/Jones incomparability witness (§ 5)

Two criteria for *clever* — problem-solving and quick-wittedness — as
two completions; Smith passes one, Jones the other. Under (12) the two
are incomparable, which Kamp argues is correct; (13) must issue a
verdict (`kampMeasureLe_total`). Kamp's own scenario is asymmetric
(Smith *much* better at problems, only slightly worse in wit, so (13)
wrongly makes Smith cleverer); this symmetric toy witnesses the
incomparability and the forced verdict, not that specific outcome. -/

private inductive Crit | problemSolving | quickWit deriving DecidableEq

private inductive P2 | smith | jones deriving DecidableEq

private def cleverExt : Crit → P2 → Prop
  | .problemSolving, .smith => True
  | .quickWit,       .jones => True
  | _,               _      => False

/-- Under (12), Smith and Jones are incomparable in cleverness — Kamp's
    argument that (12) "captures the comparative correctly" for
    multi-criteria adjectives, against (13)'s forced totality. -/
theorem clever_incomparable :
    ¬ (kampPreorder cleverExt Set.univ).le .smith .jones ∧
    ¬ (kampPreorder cleverExt Set.univ).le .jones .smith :=
  ⟨fun h => h .quickWit trivial trivial,
   fun h => h .problemSolving trivial trivial⟩

/-! #### One-dimensionality -/

/-- One-dimensional adjectives ([kamp-1975] § 5: *heavy*, *tall*, *hot*):
    any two entities' completion-sets are `⊆`-comparable, so the
    extensions form a chain (threshold structure). The formal condition
    is Kamp's (18), stated in § 6 where it grounds the adjective/noun
    asymmetry. -/
def OneDimensional : Prop :=
  ∀ u₁ u₂ : E, (∀ c ∈ S, ext c u₁ → ext c u₂) ∨ (∀ c ∈ S, ext c u₂ → ext c u₁)

/-- For one-dimensional adjectives with strictly positive weights, the
    measured comparative (13) collapses to the definite comparative (12)
    — Kamp's § 5 observation that "for this special case the two
    definitions are equivalent", with strict positivity rendering his
    "provided p has been correctly specified". -/
theorem kampPreorder_le_iff_kampMeasureLe (hp : ∀ c ∈ S, 0 < p c)
    (h18 : OneDimensional ext S) (u₁ u₂ : E) :
    (kampPreorder ext (S : Set C)).le u₁ u₂ ↔ kampMeasureLe ext S p u₁ u₂ := by
  refine ⟨kampMeasureLe_of_kampPreorder_le ext S p fun c hc => (hp c hc).le,
          fun h13 => ?_⟩
  rcases h18 u₂ u₁ with h | h
  · exact fun c hc => h c hc
  · intro c hcS hc₂
    by_contra hc₁
    have hlt : ∑ c ∈ S with ext c u₁, p c < ∑ c ∈ S with ext c u₂, p c := by
      refine Finset.sum_lt_sum_of_subset ?_ (i := c) ?_ ?_ (hp c hcS) ?_
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, h d hd.1 hd.2⟩
      · exact Finset.mem_filter.mpr ⟨hcS, hc₂⟩
      · simp [hc₁]
      · exact fun d hd _ => (hp d (Finset.mem_filter.mp hd).1).le
    exact absurd h13 (not_le.mpr hlt)

end MeasuredComparative

/-! ### Concrete Witnesses for Each Class

Each class in the hierarchy is non-empty: explicit denotations that
provably satisfy each definition from `Classification.lean`, modeling
the classic examples from the literature — "gray" (intersective), "fake"
(privative), "skillful" (subsective but not extensional), "alleged"
(non-subsective/modal).

[partee-2010] argues that the privative class should be eliminated
in favor of subsective + noun coercion. The witness `fakeAdj` below
models the traditional analysis; see `Partee2010.lean` for the
coercion reanalysis. -/

section Witnesses

/-- Two worlds suffice to distinguish extensional from non-extensional. -/
inductive W2 | w₁ | w₂

/-- Three entities suffice for all witness constructions. -/
inductive E3 | a | b | c

/-- "gray": an intersective adjective ([kamp-1975] definition (4),
    "predicative") — a fixed property conjoined with the noun, so
    "gray cat" entails both "gray" and "cat". -/
def grayAdj : Modifier (Property W2 E3) := fun N w x =>
  (match x with | .a => True | _ => False) ∧ N w x

theorem gray_intersective : isIntersective grayAdj :=
  isIntersective_iff.mpr
    ⟨fun _ x => match x with | .a => True | _ => False,
     fun N w x => by cases x <;> simp [grayAdj]⟩

/-- "gray" is therefore also extensional and subsective. -/
example : Intensional.IsExtensional grayAdj :=
  isExtensional_of_isIntersective gray_intersective
example : isSubsective grayAdj := gray_intersective.isSubsective

/-- "fake": a privative adjective ([kamp-1975] definition (5); *fake* and
    *false* are his examples) — "fake gun" entails "not a gun". Kamp
    doubts any English adjective is privative "in all of its
    possible uses", anticipating [partee-2010]'s subsective-plus-coercion
    reanalysis; see `Partee2010.lean`. -/
def fakeAdj : Modifier (Property W2 E3) := fun N w x =>
  (match x with | .b => True | _ => False) ∧ ¬ N w x

theorem fake_privative : isPrivative fakeAdj :=
  isPrivative_iff.mpr fun _ _ _ h => h.2

/-- "skillful": subsective ([kamp-1975] definition (6), "affirmative")
    but not extensional — "skillful surgeon" entails "surgeon", yet skill
    depends on the noun's intension, not just its current extension
    (Kamp's example, crediting the cobblers/darts-players case to David
    Lewis). -/
def skillfulAdj : Modifier (Property W2 E3) := fun N w x =>
  N w x ∧ match x with
    | .a => N .w₁ .a  -- a's skill assessment depends on N's intension
    | _  => False

theorem skillful_subsective : isSubsective skillfulAdj :=
  fun _ _ _ h => h.1

theorem skillful_not_extensional : ¬ Intensional.IsExtensional skillfulAdj := by
  intro hext
  let N₁ : Property W2 E3 := fun _ _ => True
  let N₂ : Property W2 E3 := fun w x => match w, x with
    | .w₁, .a => False
    | _, _    => True
  have hagree : N₁ .w₂ = N₂ .w₂ := by
    funext x; cases x <;> simp [N₁, N₂]
  have h := hext .w₂ N₁ N₂ hagree
  have hLHS : skillfulAdj N₁ .w₂ .a := ⟨trivial, trivial⟩
  exact (congrFun h .a ▸ hLHS).2

/-- "alleged": a non-subsective (modal) adjective — [kamp-1975]'s opening
    example (1), "Every alleged thief is a thief" is no logical truth. No
    meaning postulate relates the modified and unmodified extensions
    (likewise "potential", "putative"). -/
def allegedAdj : Modifier (Property W2 E3) := fun _N _ x =>
  match x with | .a => True | _ => False

/-- "alleged" ignores the noun entirely, so it is trivially extensional —
    with `skillful_not_extensional` and `skillful_subsective`, this
    witnesses that extensionality is orthogonal to subsectivity. -/
theorem alleged_extensional : Intensional.IsExtensional allegedAdj :=
  fun _ _ _ _ => rfl

/-- "alleged N" does not entail "N" (not subsective). -/
theorem alleged_not_subsective : ¬ isSubsective allegedAdj := by
  intro h
  exact h (fun _ _ => False) .w₁ .a trivial

/-- "alleged N" does not entail "not N" (not privative). -/
theorem alleged_not_privative : ¬ isPrivative allegedAdj := by
  intro h
  exact isPrivative_iff.mp h (fun _ _ => True) .w₁ .a trivial trivial

end Witnesses

end Kamp1975
