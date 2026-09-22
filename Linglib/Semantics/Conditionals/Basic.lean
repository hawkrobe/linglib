module

public import Mathlib.Data.Set.Basic
public import Linglib.Semantics.Conditionals.SimilarityOrdering

/-!
# Conditional operators

The basic conditional operators. A conditional operator sends an antecedent and a consequent,
propositions as sets of worlds, to the proposition the conditional expresses; rival theories
differ in what the operator is derived from, and comparisons and non-entailments between them
are stated over this shared signature.

## Main definitions

- `materialImp p q`: the truth-functional conditional, `w ∈ p → w ∈ q`.
- `strictImp access p q`: the strict conditional over an accessibility map `access : I → Set W`
  (a modal base), `access i ∩ p ⊆ q`.
- `variablyStrictImp sim p q`: the variably strict conditional of [lewis-1973] §2.3 over a
  similarity ordering: vacuously true without antecedent-worlds, and otherwise true iff the
  consequent holds at every antecedent-world at least as close as some antecedent-world.
- `closestImp sim p q`: the consequent holds at every closest antecedent-world, the
  simplification of §1.4 under the Limit Assumption.
- `might op p q`: the *might* counterfactual of a *would* conditional, *not (if p, would not
  q)*, as in [lewis-1973] §1.5.
- `conditionalPerfection p q`: the perfected ("only if") reading, `materialImp pᶜ qᶜ`.

## Main results

- `strictImp_anti_left`: antecedent strengthening, valid for the strict conditional and the
  signature property variably strict semantics rejects.
- `mem_strictImp_of_subset` / `not_subset_of_mem_strictImp`: a strict conditional whose
  consequent exhausts the domain is trivially true; a true non-trivial one has an antecedent
  that excludes a live world ([stalnaker-1975], [von-fintel-1999], [mizuno-2024]).
- `closestImp_eq_variablyStrictImp`: on a total ordering the two variably strict conditionals
  coincide wherever closest antecedent-worlds exist, in particular for finite antecedents
  (`closestImp_eq_variablyStrictImp_of_finite`); without them *if p, would not v* holds for every
  world `v` (`mem_variablyStrictImp_compl_singleton`).
- `mem_closestImp_union` / `mem_closestImp_or_of_mem_union`: a conditional holding of both
  disjuncts holds of the disjunction, and on a total ordering conversely of one of them.
- `strict_implies_material`, `closestImp_subset_materialImp`,
  `variablyStrictImp_subset_materialImp`: the modal conditionals refine the material one
  under reflexivity or centering.
- `perfection_not_entailed` / `perfection_not_entailed_variablyStrict`: conditional perfection
  is not entailed, even variably strictly; it is a pragmatic inference
  ([grusdt-lassiter-franke-2022]).

The Kratzer restrictor conditional (necessity over a restricted conversational background)
lives in `Conditionals/Restrictor.lean`, which bridges to `strictImp` via
`conditionalNecessity_iff_mem_strictImp`.

## References

* [lewis-1973]
* [stalnaker-1975]
* [stalnaker-1981]
* [von-fintel-1999]
* [mizuno-2024]
* [grusdt-lassiter-franke-2022]
-/

@[expose] public section


namespace Conditional

variable {I W : Type*} {access : I → Set W} {p p' q q' : Set W} {i : I} {w : W}

/-! ### Material conditional -/

/-- The material conditional: true wherever the antecedent fails or the
consequent holds (`pᶜ ∪ q`). Classical semantics keeps this literal meaning
and derives its apparent exceptions pragmatically
([grusdt-lassiter-franke-2022]). -/
def materialImp (p q : Set W) : Set W := {w | w ∈ p → w ∈ q}

@[simp]
theorem mem_materialImp : w ∈ materialImp p q ↔ (w ∈ p → w ∈ q) := Iff.rfl

/-- Contraposition, valid for the material conditional. [stalnaker-1975] (§4)
observes that it fails for indicative conditionals under his semantics — see
`Studies/Stalnaker1975`. -/
theorem contraposition : materialImp p q ⊆ materialImp qᶜ pᶜ :=
  fun _ h hq hp ↦ hq (h hp)

/-! ### Strict conditional -/

/-- The strict conditional over an accessibility map: the consequent holds
throughout the accessible antecedent worlds, `access i ∩ p ⊆ q`. The
evaluation points `I` may differ from the worlds `W` quantified over — e.g. a
historical modal base `Index W T → Set W` evaluates at world-time
indices ([condoravdi-2002]); the classical case is `I = W`. -/
def strictImp (access : I → Set W) (p q : Set W) : Set I :=
  {i | access i ∩ p ⊆ q}

@[simp]
theorem mem_strictImp : i ∈ strictImp access p q ↔ access i ∩ p ⊆ q := Iff.rfl

/-- The quantifier reading of the strict conditional. -/
theorem mem_strictImp_forall :
    i ∈ strictImp access p q ↔ ∀ w ∈ access i, w ∈ p → w ∈ q :=
  ⟨fun h _ hw hp ↦ h ⟨hw, hp⟩, fun h w hw ↦ h w hw.1 hw.2⟩

/-- The strict conditional is monotone in its consequent. -/
theorem strictImp_mono_right (hq : q ⊆ q') :
    strictImp access p q ⊆ strictImp access p q' :=
  fun _ h ↦ h.trans hq

/-- **Antecedent strengthening**: the strict conditional is antitone in its
antecedent — the signature property of strict (and material) conditionals
that variably strict semantics rejects ([lewis-1973] Sobel sequences). -/
theorem strictImp_anti_left (hp : p' ⊆ p) :
    strictImp access p q ⊆ strictImp access p' q :=
  fun _ h ↦ (Set.inter_subset_inter (Set.Subset.refl _) hp).trans h

/-- **Triviality**: when the consequent already holds throughout the
accessible worlds, the strict conditional holds for *any* antecedent — the
if-clause does no work ([stalnaker-1975], [von-fintel-1999]; the
Anderson-conditional application is [mizuno-2024] §2). -/
theorem mem_strictImp_of_subset (h : access i ⊆ q) :
    i ∈ strictImp access p q :=
  Set.inter_subset_left.trans h

/-- **Informativity**: a true strict conditional whose consequent is *not*
trivial over the accessible worlds has an antecedent that excludes at least
one accessible world (`Set.not_subset` gives the witness form)
([mizuno-2024] §2). -/
theorem not_subset_of_mem_strictImp
    (hm : i ∈ strictImp access p q) (hq : ¬ access i ⊆ q) :
    ¬ access i ⊆ p :=
  fun hp ↦ hq (fun _ hw ↦ hm ⟨hw, hp hw⟩)

/-- With reflexive access, the strict conditional refines the material one. -/
theorem strict_implies_material {R : W → Set W} (h_refl : w ∈ R w)
    (h : w ∈ strictImp R p q) : w ∈ materialImp p q :=
  fun hp ↦ h ⟨h_refl, hp⟩

/-! ### Variably strict conditionals

[lewis-1973] §2.3 states the counterfactual over a comparative similarity system, a total
preorder of the worlds for each center: *if p, q* is true at `w` iff there is no
antecedent-world, or some antecedent-world `v` is such that the consequent holds at every
antecedent-world at least as close to `w` as `v` (`variablyStrictImp`). Under the Limit
Assumption, that closest antecedent-worlds exist whenever antecedent-worlds do, §1.4
simplifies the clause to the consequent holding at every closest antecedent-world
(`closestImp`); the two coincide on total orderings wherever the Limit Assumption holds
(`closestImp_eq_variablyStrictImp`), in particular for finite antecedents. `closestImp` is
also meaningful on a similarity preorder that is not total, where the closest worlds are the
minimal ones. `might` is §1.5's *might* counterfactual, the dual of a *would* conditional. -/

/-- The *might* counterfactual of a *would* conditional `op`: *if p, might q* is
*not (if p, would not q)*, [lewis-1973] §1.5's definition. -/
def might (op : Set W → Set W → Set W) (p q : Set W) : Set W := (op p qᶜ)ᶜ

@[simp]
theorem mem_might {op : Set W → Set W → Set W} : w ∈ might op p q ↔ w ∉ op p qᶜ := Iff.rfl

instance {op : Set W → Set W → Set W} [Decidable (w ∈ op p qᶜ)] : Decidable (w ∈ might op p q) :=
  inferInstanceAs (Decidable (w ∉ _))

section VariablyStrict

variable {sim : SimilarityOrdering W} {r : Set W}

/-- The variably strict conditional of [lewis-1973] §2.3 for a universal system, one in which
every world is accessible: vacuously true without antecedent-worlds, and otherwise true iff
the consequent holds at every antecedent-world at least as close as some antecedent-world. -/
def variablyStrictImp (sim : SimilarityOrdering W) (p q : Set W) : Set W :=
  {w | p = ∅ ∨ ∃ v ∈ p, ∀ u ∈ p, sim.closer w u v → u ∈ q}

@[simp]
theorem mem_variablyStrictImp :
    w ∈ variablyStrictImp sim p q ↔ p = ∅ ∨ ∃ v ∈ p, ∀ u ∈ p, sim.closer w u v → u ∈ q :=
  Iff.rfl

/-- The conditional of the closest antecedent-worlds: true iff the consequent holds at every
antecedent-world closest to the evaluation world, [lewis-1973] §1.4's simplification of the
variably strict conditional under the Limit Assumption. -/
def closestImp (sim : SimilarityOrdering W) (p q : Set W) : Set W :=
  {w | sim.closest w p ⊆ q}

@[simp]
theorem mem_closestImp : w ∈ closestImp sim p q ↔ sim.closest w p ⊆ q := Iff.rfl

theorem mem_closestImp_iff_closestWorlds [Fintype W] [DecidableEq W] [DecidablePred (· ∈ p)] :
    w ∈ closestImp sim p q ↔ ∀ v ∈ sim.closestWorlds w (Finset.univ.filter (· ∈ p)), v ∈ q := by
  have hp : (↑(Finset.univ.filter (· ∈ p)) : Set W) = p := by ext; simp
  have h := sim.coe_closestWorlds w (Finset.univ.filter (· ∈ p))
  rw [hp] at h
  rw [mem_closestImp, ← h]
  exact ⟨fun h v hv ↦ h (Finset.mem_coe.2 hv), fun h v hv ↦ h v (Finset.mem_coe.1 hv)⟩

instance [Fintype W] [DecidableEq W] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    Decidable (w ∈ closestImp sim p q) :=
  decidable_of_iff _ mem_closestImp_iff_closestWorlds.symm

/-- On a total ordering the variably strict conditional entails the conditional of the closest
antecedent-worlds. -/
theorem variablyStrictImp_subset_closestImp (htot : sim.Total) :
    variablyStrictImp sim p q ⊆ closestImp sim p q := by
  rintro w (rfl | ⟨v, hv, h⟩) u hu
  · exact absurd hu.1 id
  · exact h u hu.1 (((SimilarityOrdering.mem_closest_iff_of_total htot).1 hu).2 v hv)

/-- On a total ordering satisfying the Limit Assumption for `p`, the two conditionals coincide
([lewis-1973] §1.4). -/
theorem closestImp_eq_variablyStrictImp (htot : sim.Total)
    (hlim : ∀ w, p.Nonempty → (sim.closest w p).Nonempty) :
    closestImp sim p q = variablyStrictImp sim p q := by
  refine subset_antisymm (fun w hw ↦ ?_) (variablyStrictImp_subset_closestImp htot)
  rcases p.eq_empty_or_nonempty with hp | hp
  · exact .inl hp
  obtain ⟨v, hv⟩ := hlim w hp
  rw [SimilarityOrdering.mem_closest_iff_of_total htot] at hv
  refine .inr ⟨v, hv.1, fun u hu huv ↦ hw ?_⟩
  exact (SimilarityOrdering.mem_closest_iff_of_total htot).2
    ⟨hu, fun x hx ↦ sim.closer_trans w u v x huv (hv.2 x hx)⟩

/-- A finite antecedent satisfies the Limit Assumption. -/
theorem closestImp_eq_variablyStrictImp_of_finite (htot : sim.Total) (hp : p.Finite) :
    closestImp sim p q = variablyStrictImp sim p q :=
  closestImp_eq_variablyStrictImp htot fun w ↦ sim.closest_nonempty w hp

/-- Without closest antecedent-worlds the conditional of the closest worlds is vacuous: where
the Limit Assumption fails it and the variably strict conditional come apart. -/
theorem mem_closestImp_of_closest_eq_empty (h : sim.closest w p = ∅) :
    w ∈ closestImp sim p q :=
  (mem_closestImp.2 (h ▸ Set.empty_subset q))

/-- Without closest antecedent-worlds, [lewis-1973] §1.4's case of a line more than an inch
long: for every world `v`, if `p` were the case it would not be `v`, since every
antecedent-world has a strictly closer one. -/
theorem mem_variablyStrictImp_compl_singleton (h : sim.closest w p = ∅) (v : W) :
    w ∈ variablyStrictImp sim p {v}ᶜ := by
  rcases p.eq_empty_or_nonempty with hp | ⟨u, hu⟩
  · exact .inl hp
  by_cases hv : v ∈ p
  · have hvc : v ∉ sim.closest w p := h ▸ Set.notMem_empty v
    simp only [SimilarityOrdering.mem_closest, hv, true_and, not_forall, not_or, not_not] at hvc
    obtain ⟨x, hx, hvx, hxv⟩ := hvc
    exact .inr ⟨x, hx, fun y _ hyx hyv ↦ hvx (hyv ▸ hyx)⟩
  · exact .inr ⟨u, hu, fun y hy _ hyv ↦ hv (hyv ▸ hy)⟩

/-- So there is no world that `p` might have been: [stalnaker-1981]'s objection to [lewis-1973]
without the Limit Assumption. -/
theorem notMem_might_variablyStrictImp_singleton (h : sim.closest w p = ∅) (v : W) :
    w ∉ might (variablyStrictImp sim) p {v} :=
  fun hm ↦ hm (mem_variablyStrictImp_compl_singleton h v)

/-- Under strong centering both conditionals refine the material one. -/
theorem closestImp_subset_materialImp (hc : sim.isCentered) :
    closestImp sim p q ⊆ materialImp p q :=
  fun _ h hp ↦ h ((SimilarityOrdering.closest_eq_singleton_of_mem hc hp).symm ▸ rfl)

theorem variablyStrictImp_subset_materialImp (hc : sim.isCentered) :
    variablyStrictImp sim p q ⊆ materialImp p q := by
  rintro w (rfl | ⟨v, _, h⟩) hp
  · exact absurd hp id
  · rcases eq_or_ne w v with rfl | hne
    · exact h w hp (sim.closer_refl w w)
    · exact h w hp (hc w v hne).1

theorem closestImp_eq_univ_of_subset (h : p ⊆ q) : closestImp sim p q = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ (sim.closest_subset _ p).trans h

/-- A conditional holding of each of two antecedents holds of their disjunction. -/
theorem mem_closestImp_union (hp : w ∈ closestImp sim p r) (hq : w ∈ closestImp sim q r) :
    w ∈ closestImp sim (p ∪ q) r :=
  fun _ hu ↦ (SimilarityOrdering.closest_union_subset hu).elim (hp ·) (hq ·)

/-- On a total ordering, a conditional with a disjunctive antecedent entails the conditional of
one of the disjuncts. -/
theorem mem_closestImp_or_of_mem_union (htot : sim.Total) (h : w ∈ closestImp sim (p ∪ q) r) :
    w ∈ closestImp sim p r ∨ w ∈ closestImp sim q r := by
  by_contra hn
  simp only [not_or, mem_closestImp, Set.not_subset] at hn
  obtain ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩ := hn
  rw [SimilarityOrdering.mem_closest_iff_of_total htot] at hx hy
  rcases htot w x y with hxy | hyx
  · refine hxr (h ((SimilarityOrdering.mem_closest_iff_of_total htot).2 ⟨.inl hx.1, ?_⟩))
    exact fun u hu ↦ hu.elim (hx.2 u) fun hu ↦ sim.closer_trans w x y u hxy (hy.2 u hu)
  · refine hyr (h ((SimilarityOrdering.mem_closest_iff_of_total htot).2 ⟨.inr hy.1, ?_⟩))
    exact fun u hu ↦ hu.elim (fun hu ↦ sim.closer_trans w y x u hyx (hx.2 u hu)) (hy.2 u)

/-- With a unique closest antecedent-world, Lewis's *might* collapses into *would*. -/
theorem mem_might_closestImp_iff_of_closest_eq_singleton {v : W} (h : sim.closest w p = {v}) :
    w ∈ might (closestImp sim) p q ↔ w ∈ closestImp sim p q := by
  simp [h]

/-- Conditional Excluded Middle collapses Lewis's *might* into *would*: [lewis-1973]'s objection
to a semantics validating it, as [stalnaker-1981] states it. -/
theorem mem_might_closestImp_iff_of_cem (h_nonempty : (sim.closest w p).Nonempty)
    (h_cem : w ∈ closestImp sim p q ∨ w ∈ closestImp sim p qᶜ) :
    w ∈ might (closestImp sim) p q ↔ w ∈ closestImp sim p q := by
  obtain ⟨v, hv⟩ := h_nonempty
  rcases h_cem with h | h
  · exact ⟨fun _ ↦ h, fun _ hn ↦ hn hv (h hv)⟩
  · exact ⟨fun hm ↦ absurd h hm, fun hq ↦ absurd (hq hv) (h hv)⟩

end VariablyStrict


/-! ### Conditional perfection -/

/-- Conditional perfection: the strengthened converse reading of a
conditional ("if not A, not C"), as `materialImp pᶜ qᶜ`. Observed
pragmatically but not entailed (`perfection_not_entailed`);
[grusdt-lassiter-franke-2022] derive it as an RSA implicature. -/
def conditionalPerfection (p q : Set W) : Set W := materialImp pᶜ qᶜ

/-- Conditional perfection is not entailed: the material conditional can
hold (vacuously, at an antecedent-false world) where its perfection fails. -/
theorem perfection_not_entailed :
    ∃ (W : Type) (p q : Set W) (w : W),
      w ∈ materialImp p q ∧ w ∉ conditionalPerfection p q :=
  ⟨Bool, {w | w = true}, Set.univ, false, fun _ ↦ trivial,
    fun h ↦ h Bool.false_ne_true trivial⟩

/-- Perfection is not entailed even variably strictly: the [lewis-1973] conditional is stronger
than material implication, yet still does not entail the converse. -/
theorem perfection_not_entailed_variablyStrict :
    ∃ (W : Type) (sim : SimilarityOrdering W) (p q : Set W) (w : W),
      w ∈ variablyStrictImp sim p q ∧ w ∉ conditionalPerfection p q :=
  ⟨Bool, .ofRank fun _ _ ↦ (0 : ℕ), {w | w = true}, Set.univ, false,
    .inr ⟨true, rfl, fun _ _ _ ↦ trivial⟩, fun h ↦ h Bool.false_ne_true trivial⟩

end Conditional
