module

public import Mathlib.Data.Set.Basic
public import Linglib.Core.Order.Minimals

/-!
# Conditional operators

This file defines conditional operators on propositions, taken as sets of worlds. Most theories
of the conditional derive it from a domain of antecedent-worlds: *if p, q* is true when `q` holds
throughout the domain that `p` picks out from the evaluation point. The theories differ in the
domain, which is the accessible antecedent-worlds for the strict conditional and the closest
antecedent-worlds for the variably strict conditional under the Limit Assumption.

## Main definitions

* `ofDomain`: the conditional quantifying over a domain of antecedent-worlds.
* `materialImp`, `strictImp`: the material and strict conditionals.
* `variablyStrictImp`: Lewis's variably strict conditional over a family of preorders.
* `IsCentered`: strong centering of a family of preorders.
* `closestImp`: the conditional of the minimal antecedent-worlds.
* `orderingImp`: the conditional over the best accessible antecedent-worlds under a preorder.
* `might`: the *might* counterfactual of a *would* conditional.

## Main results

* `closestImp_eq_variablyStrictImp`: on a total ordering the two variably strict conditionals
  coincide wherever the Limit Assumption holds.
* `mem_variablyStrictImp_compl_singleton`: without closest antecedent-worlds, *if p, it would not
  be v* holds for every world `v`.

## References

* [D. Lewis, *Counterfactuals* (1973)][lewis-1973]
* [D. Lewis, *Adverbs of Quantification* (1975)][lewis-1975]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *Indicative conditionals* (1975)][stalnaker-1975]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [A. Kratzer, *Conditionals* (1986)][kratzer-1986]
* [C. Condoravdi, *Temporal Interpretation of Modals: Modals for the Present and for the Past*
  (2002)][condoravdi-2002]
* [K. von Fintel, *NPI Licensing, Strawson Entailment, and Context Dependency*
  (1999)][von-fintel-1999]
* [B. Grusdt, D. Lassiter and M. Franke, *Probabilistic Modeling of Rational Communication with
  Conditionals* (2022)][grusdt-lassiter-franke-2022]
* [T. Mizuno, *Strategies for Anderson Conditionals: Their Implications for the Typology of
  O-Marking and X-Marking* (2024)][mizuno-2024]
-/

@[expose] public section


namespace Conditional

variable {I W : Type*} {access : I → Set W} {p p' q q' : Set W} {i : I} {w : W}

/-! ### Material conditional -/

/-- The material conditional, true wherever the antecedent fails or the consequent holds.
Classical semantics keeps this meaning and derives its apparent exceptions pragmatically
([grusdt-lassiter-franke-2022]). -/
def materialImp (p q : Set W) : Set W := {w | w ∈ p → w ∈ q}

@[simp]
theorem mem_materialImp : w ∈ materialImp p q ↔ (w ∈ p → w ∈ q) := Iff.rfl

/-- Contraposition is valid for the material conditional, though not for the indicative
conditional of [stalnaker-1975]. -/
theorem contraposition : materialImp p q ⊆ materialImp qᶜ pᶜ :=
  fun _ h hq hp ↦ hq (h hp)

/-! ### Conditionals over a domain

A theory of the conditional picks out, for an evaluation point `i` and an antecedent `p`, a
domain of `p`-worlds, and *if p, q* is true at `i` iff `q` holds throughout it (`ofDomain`): the
accessible `p`-worlds for the strict conditional, the closest ones for [lewis-1973] under the
Limit Assumption (`closestImp`), the selected one for [stalnaker-1968] (`selectionConditional`),
the best worlds of the modal base restricted by the antecedent for the restrictor analysis
([lewis-1975], [kratzer-1986]). Principles about a single antecedent are properties of its
domain: consequent monotonicity and agglomeration always hold, Conditional Excluded Middle and
distribution over a disjunctive consequent when the domain has at most one world, and modus
ponens when an antecedent-world lies in its own domain. Principles relating antecedents, such as
antecedent strengthening or reasoning by cases, depend on how the domain varies with the
antecedent. -/

section Domain

variable {D : I → Set W → Set W} {r : Set W}

/-- The conditional quantifying over the domain `D i p`, true at `i` when `q` holds at every
world of `D i p`. -/
def ofDomain (D : I → Set W → Set W) (p q : Set W) : Set I := {i | D i p ⊆ q}

@[simp]
theorem mem_ofDomain : i ∈ ofDomain D p q ↔ D i p ⊆ q := Iff.rfl

theorem ofDomain_mono_right (hq : q ⊆ q') : ofDomain D p q ⊆ ofDomain D p q' :=
  fun _ h ↦ h.trans hq

/-- A conditional holds of a conjunctive consequent iff it holds of both conjuncts. -/
theorem ofDomain_inter : ofDomain D p (q ∩ r) = ofDomain D p q ∩ ofDomain D p r :=
  Set.ext fun _ ↦ Set.subset_inter_iff

theorem ofDomain_eq_univ (h : ∀ i, D i p ⊆ q) : ofDomain D p q = Set.univ :=
  Set.eq_univ_of_forall h

/-- Antecedent strengthening holds when the domain of the stronger antecedent lies within the
domain of the weaker. -/
theorem ofDomain_anti_left (hD : ∀ i, D i p' ⊆ D i p) : ofDomain D p q ⊆ ofDomain D p' q :=
  fun i h ↦ (hD i).trans h

/-- A conditional holding of two antecedents holds of their disjunction when the domain of the
disjunction lies within theirs. -/
theorem mem_ofDomain_union (hD : D i (p ∪ p') ⊆ D i p ∪ D i p') (hp : i ∈ ofDomain D p q)
    (hp' : i ∈ ofDomain D p' q) : i ∈ ofDomain D (p ∪ p') q :=
  fun _ hv ↦ (hD hv).elim (hp ·) (hp' ·)

/-- A conditional over a domain with at most one world distributes over a disjunctive
consequent. -/
theorem mem_ofDomain_or (h : (D i p).Subsingleton) (hq : i ∈ ofDomain D p (q ∪ r)) :
    i ∈ ofDomain D p q ∨ i ∈ ofDomain D p r := by
  rcases h.eq_empty_or_singleton with h0 | ⟨v, hv⟩
  · exact .inl (by simp [h0])
  · simpa only [mem_ofDomain, hv, Set.singleton_subset_iff, Set.mem_union] using hq

/-- A conditional over a domain with at most one world satisfies Conditional Excluded
Middle. -/
theorem mem_ofDomain_or_compl (h : (D i p).Subsingleton) :
    i ∈ ofDomain D p q ∨ i ∈ ofDomain D p qᶜ :=
  mem_ofDomain_or h (by simp)

/-- Modus ponens holds when every antecedent-world lies in its own domain. -/
theorem ofDomain_subset_materialImp {D : W → Set W → Set W} (hD : ∀ w ∈ p, w ∈ D w p) :
    ofDomain D p q ⊆ materialImp p q :=
  fun w h hp ↦ h (hD w hp)

/-- The material conditional quantifies over the evaluation world when it is an
antecedent-world. -/
theorem materialImp_eq_ofDomain : materialImp p q = ofDomain (fun w p ↦ {w} ∩ p) p q :=
  Set.ext fun _ ↦ ⟨fun h _ hv ↦
      (Set.mem_singleton_iff.1 hv.1) ▸ h ((Set.mem_singleton_iff.1 hv.1) ▸ hv.2),
    fun h hp ↦ h ⟨rfl, hp⟩⟩

end Domain

/-! ### Strict conditional -/

/-- The strict conditional over an accessibility map, true at `i` when the consequent holds at
every accessible antecedent-world. The evaluation points may differ from the worlds quantified
over, as for a historical modal base evaluated at world-time indices ([condoravdi-2002]). -/
def strictImp (access : I → Set W) (p q : Set W) : Set I :=
  ofDomain (fun i p ↦ access i ∩ p) p q

@[simp]
theorem mem_strictImp : i ∈ strictImp access p q ↔ access i ∩ p ⊆ q := Iff.rfl

/-- The quantifier reading of the strict conditional. -/
theorem mem_strictImp_forall :
    i ∈ strictImp access p q ↔ ∀ w ∈ access i, w ∈ p → w ∈ q :=
  ⟨fun h _ hw hp ↦ h ⟨hw, hp⟩, fun h w hw ↦ h w hw.1 hw.2⟩

/-- The strict conditional is monotone in its consequent. -/
theorem strictImp_mono_right (hq : q ⊆ q') :
    strictImp access p q ⊆ strictImp access p q' :=
  ofDomain_mono_right hq

/-- The strict conditional is antitone in its antecedent, the antecedent strengthening that
the variably strict conditional of [lewis-1973] rejects. -/
theorem strictImp_anti_left (hp : p' ⊆ p) :
    strictImp access p q ⊆ strictImp access p' q :=
  ofDomain_anti_left fun _ ↦ Set.inter_subset_inter_right _ hp

/-- A strict conditional whose consequent holds throughout the accessible worlds is true for
every antecedent ([stalnaker-1975], [von-fintel-1999], [mizuno-2024]). -/
theorem mem_strictImp_of_subset (h : access i ⊆ q) :
    i ∈ strictImp access p q :=
  Set.inter_subset_left.trans h

/-- A true strict conditional whose consequent does not hold throughout the accessible worlds
has an antecedent that excludes some accessible world ([mizuno-2024]). -/
theorem not_subset_of_mem_strictImp
    (hm : i ∈ strictImp access p q) (hq : ¬ access i ⊆ q) :
    ¬ access i ⊆ p :=
  fun hp ↦ hq (fun _ hw ↦ hm ⟨hw, hp hw⟩)

/-- With reflexive access, the strict conditional entails the material conditional at the
evaluation world. -/
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
(`closestImp_eq_variablyStrictImp`), in particular for finite antecedents.

The operators take any family `ord : W → Preorder W` of preorders indexed by the evaluation
world, the closest antecedent-worlds being the minimal ones (`Preorder.minimals`). Lewis reads
the family as comparative similarity and requires it to be total and strongly centered
(`IsCentered`); `closestImp` is also meaningful on preorders that are not total. `might` is
§1.5's *might* counterfactual, the dual of a *would* conditional. -/

/-- The *might* counterfactual of a *would* conditional `op`, *not (if p, would not q)*
([lewis-1973] §1.5). -/
def might (op : Set W → Set W → Set W) (p q : Set W) : Set W := (op p qᶜ)ᶜ

@[simp]
theorem mem_might {op : Set W → Set W → Set W} : w ∈ might op p q ↔ w ∉ op p qᶜ := Iff.rfl

instance {op : Set W → Set W → Set W} [Decidable (w ∈ op p qᶜ)] : Decidable (w ∈ might op p q) :=
  inferInstanceAs (Decidable (w ∉ _))

section VariablyStrict

variable {ord : W → Preorder W} {r : Set W}

/-- A family of preorders is strongly centered when every world is strictly below every other
world in its own preorder, [lewis-1973]'s requirement that each world be closer to itself than
any other world is. -/
def IsCentered (ord : W → Preorder W) : Prop := ∀ w w' : W, w ≠ w' → (ord w).lt w w'

/-- Under strong centering every world is at least as close to itself as any world is. -/
theorem IsCentered.le (hc : IsCentered ord) (w w' : W) : (ord w).le w w' := by
  let := ord w
  rcases eq_or_ne w w' with rfl | h
  exacts [le_rfl, (hc w w' h).le]

/-- Under strong centering no other world is as close to a world as the world itself. -/
theorem IsCentered.not_le (hc : IsCentered ord) {w w' : W} (h : w ≠ w') : ¬ (ord w).le w' w :=
  let := ord w
  (hc w w' h).not_ge

/-- Under strong centering a world is its own unique closest world in any set containing it. -/
theorem IsCentered.minimals_eq_singleton (hc : IsCentered ord) (hw : w ∈ p) :
    (ord w).minimals p = {w} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hw, fun u _ _ ↦ hc.le w u⟩, fun u hu ↦ ?_⟩
  by_contra hne
  exact hc.not_le (Ne.symm hne) (hu.2 hw (hc.le w u))


/-- The variably strict conditional of [lewis-1973] §2.3 for a universal system, one in which
every world is accessible. It is vacuously true without antecedent-worlds, and otherwise true
when the consequent holds at every antecedent-world at least as close as some antecedent-world. -/
def variablyStrictImp (ord : W → Preorder W) (p q : Set W) : Set W :=
  {w | p = ∅ ∨ ∃ v ∈ p, ∀ u ∈ p, (ord w).le u v → u ∈ q}

@[simp]
theorem mem_variablyStrictImp :
    w ∈ variablyStrictImp ord p q ↔ p = ∅ ∨ ∃ v ∈ p, ∀ u ∈ p, (ord w).le u v → u ∈ q :=
  Iff.rfl

/-- The conditional of the closest antecedent-worlds, true when the consequent holds at every
closest antecedent-world. It is [lewis-1973]'s simplification of the variably strict
conditional under the Limit Assumption (§1.4). -/
def closestImp (ord : W → Preorder W) (p q : Set W) : Set W :=
  ofDomain (fun w ↦ (ord w).minimals) p q

@[simp]
theorem mem_closestImp : w ∈ closestImp ord p q ↔ (ord w).minimals p ⊆ q := Iff.rfl

/-- Membership in `closestImp` over a finite type, decided by filtering the antecedent-worlds once
rather than quantifying over every world. -/
theorem mem_closestImp_iff_forall_filter [Fintype W] [DecidablePred (· ∈ p)] :
    w ∈ closestImp ord p q ↔ ∀ v ∈ Finset.univ.filter (· ∈ p),
      (∀ u ∈ Finset.univ.filter (· ∈ p), (ord w).le u v → (ord w).le v u) → v ∈ q := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h v hv hmin ↦ h ⟨hv, fun u hu ↦ hmin u hu⟩, fun h v hv ↦ h v hv.1 fun u hu ↦ hv.2 hu⟩

instance [Fintype W] [DecidableRel (ord w).le] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    Decidable (w ∈ closestImp ord p q) :=
  decidable_of_iff _ mem_closestImp_iff_forall_filter.symm

/-- On a total ordering the variably strict conditional entails the conditional of the closest
antecedent-worlds. -/
theorem variablyStrictImp_subset_closestImp (htot : ∀ w, Std.Total (ord w).le) :
    variablyStrictImp ord p q ⊆ closestImp ord p q := by
  rintro w (rfl | ⟨v, hv, h⟩) u hu
  · exact absurd hu.1 id
  · exact h u hu.1 (((Preorder.mem_minimals_iff_forall_le (htot _)).1 hu).2 v hv)

/-- On a total ordering satisfying the Limit Assumption for `p`, the two conditionals coincide
([lewis-1973] §1.4). -/
theorem closestImp_eq_variablyStrictImp (htot : ∀ w, Std.Total (ord w).le)
    (hlim : ∀ w, p.Nonempty → ((ord w).minimals p).Nonempty) :
    closestImp ord p q = variablyStrictImp ord p q := by
  refine subset_antisymm (fun w hw ↦ ?_) (variablyStrictImp_subset_closestImp htot)
  rcases p.eq_empty_or_nonempty with hp | hp
  · exact .inl hp
  obtain ⟨v, hv⟩ := hlim w hp
  rw [Preorder.mem_minimals_iff_forall_le (htot _)] at hv
  refine .inr ⟨v, hv.1, fun u hu huv ↦ hw ?_⟩
  exact (Preorder.mem_minimals_iff_forall_le (htot _)).2
    ⟨hu, fun x hx ↦ (ord w).le_trans u v x huv (hv.2 x hx)⟩

/-- On a total ordering the two conditionals coincide for a finite antecedent, which satisfies
the Limit Assumption. -/
theorem closestImp_eq_variablyStrictImp_of_finite (htot : ∀ w, Std.Total (ord w).le)
    (hp : p.Finite) :
    closestImp ord p q = variablyStrictImp ord p q :=
  closestImp_eq_variablyStrictImp htot fun w ↦ (ord w).minimals_nonempty_of_finite hp

/-- Without closest antecedent-worlds the conditional of the closest worlds is vacuously true. -/
theorem mem_closestImp_of_closest_eq_empty (h : (ord w).minimals p = ∅) :
    w ∈ closestImp ord p q :=
  (mem_closestImp.2 (h ▸ Set.empty_subset q))

/-- Where an antecedent has no closest worlds, as for [lewis-1973]'s line more than an inch long,
*if p, it would not be v* is true for every world `v`, since every antecedent-world has a
strictly closer one. -/
theorem mem_variablyStrictImp_compl_singleton (h : (ord w).minimals p = ∅) (v : W) :
    w ∈ variablyStrictImp ord p {v}ᶜ := by
  rcases p.eq_empty_or_nonempty with hp | ⟨u, hu⟩
  · exact .inl hp
  by_cases hv : v ∈ p
  · have hvc : v ∉ (ord w).minimals p := h ▸ Set.notMem_empty v
    simp only [Preorder.mem_minimals_iff, hv, true_and, not_forall] at hvc
    obtain ⟨x, hx, -, hvx⟩ := hvc
    exact .inr ⟨x, hx, fun y _ hyx hyv ↦ hvx (hyv ▸ hyx)⟩
  · exact .inr ⟨u, hu, fun y hy _ hyv ↦ hv (hyv ▸ hy)⟩

/-- So no world is one that `p` might have been, [stalnaker-1981]'s objection to [lewis-1973]
without the Limit Assumption. -/
theorem notMem_might_variablyStrictImp_singleton (h : (ord w).minimals p = ∅) (v : W) :
    w ∉ might (variablyStrictImp ord) p {v} :=
  fun hm ↦ hm (mem_variablyStrictImp_compl_singleton h v)

/-- Under strong centering the conditional of the closest worlds entails the material
conditional. -/
theorem closestImp_subset_materialImp (hc : IsCentered ord) :
    closestImp ord p q ⊆ materialImp p q :=
  ofDomain_subset_materialImp fun w hw ↦ ⟨hw, fun u _ _ ↦ hc.le w u⟩

theorem variablyStrictImp_subset_materialImp (hc : IsCentered ord) :
    variablyStrictImp ord p q ⊆ materialImp p q := by
  rintro w (rfl | ⟨v, _, h⟩) hp
  exacts [absurd hp id, h w hp (hc.le w v)]

theorem closestImp_eq_univ_of_subset (h : p ⊆ q) : closestImp ord p q = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ (Preorder.minimals_subset _ p).trans h

/-- A conditional holding of each of two antecedents holds of their disjunction. -/
theorem mem_closestImp_union (hp : w ∈ closestImp ord p r) (hq : w ∈ closestImp ord q r) :
    w ∈ closestImp ord (p ∪ q) r :=
  fun _ hu ↦ (Preorder.minimals_union_subset hu).elim (hp ·) (hq ·)

/-- On a total ordering, a conditional with a disjunctive antecedent entails the conditional of
one of the disjuncts. -/
theorem mem_closestImp_or_of_mem_union (htot : ∀ w, Std.Total (ord w).le)
    (h : w ∈ closestImp ord (p ∪ q) r) :
    w ∈ closestImp ord p r ∨ w ∈ closestImp ord q r := by
  by_contra hn
  simp only [not_or, mem_closestImp, Set.not_subset] at hn
  obtain ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩ := hn
  rw [Preorder.mem_minimals_iff_forall_le (htot _)] at hx hy
  rcases (htot w).total x y with hxy | hyx
  · refine hxr (h ((Preorder.mem_minimals_iff_forall_le (htot _)).2 ⟨.inl hx.1, ?_⟩))
    exact fun u hu ↦ hu.elim (hx.2 u) fun hu ↦ (ord w).le_trans x y u hxy (hy.2 u hu)
  · refine hyr (h ((Preorder.mem_minimals_iff_forall_le (htot _)).2 ⟨.inr hy.1, ?_⟩))
    exact fun u hu ↦ hu.elim (fun hu ↦ (ord w).le_trans y x u hyx (hx.2 u hu)) (hy.2 u)

/-- With a unique closest antecedent-world, Lewis's *might* coincides with *would*. -/
theorem mem_might_closestImp_iff_of_closest_eq_singleton {v : W} (h : (ord w).minimals p = {v}) :
    w ∈ might (closestImp ord) p q ↔ w ∈ closestImp ord p q := by
  simp [h]

/-- When the antecedent has closest worlds and Conditional Excluded Middle holds, Lewis's *might*
coincides with *would*, [lewis-1973]'s objection to a semantics validating it as
[stalnaker-1981] reports it. -/
theorem mem_might_closestImp_iff_of_cem (h_nonempty : ((ord w).minimals p).Nonempty)
    (h_cem : w ∈ closestImp ord p q ∨ w ∈ closestImp ord p qᶜ) :
    w ∈ might (closestImp ord) p q ↔ w ∈ closestImp ord p q := by
  obtain ⟨v, hv⟩ := h_nonempty
  rcases h_cem with h | h
  · exact ⟨fun _ ↦ h, fun _ hn ↦ hn hv (h hv)⟩
  · exact ⟨fun hm ↦ absurd h hm, fun hq ↦ absurd (hq hv) (h hv)⟩

end VariablyStrict

/-! ### Conditionals over an accessibility relation and an ordering

A modal base and an ordering source ([kratzer-1981]) give each evaluation point a set of
accessible worlds and a preorder ranking them, and on the restrictor analysis ([lewis-1975],
[kratzer-1986]) *if p, q* is true when `q` holds at the best accessible `p`-worlds
(`orderingImp`). The strict conditional is the case of the preorder relating every two worlds,
under which every accessible antecedent-world is best (`strictImp_eq_orderingImp`), and the
conditional of the closest worlds the case in which every world is accessible
(`closestImp_eq_orderingImp`). -/

section Ordering

variable {ord : I → Preorder W}

/-- The conditional over the best accessible antecedent-worlds, the minimal worlds of
`access i ∩ p` under the preorder `ord i`. -/
def orderingImp (access : I → Set W) (ord : I → Preorder W) (p q : Set W) : Set I :=
  ofDomain (fun i p ↦ (ord i).minimals (access i ∩ p)) p q

@[simp]
theorem mem_orderingImp :
    i ∈ orderingImp access ord p q ↔ (ord i).minimals (access i ∩ p) ⊆ q := Iff.rfl

/-- The strict conditional is the conditional over the preorder relating every two worlds. -/
theorem strictImp_eq_orderingImp : strictImp access p q = orderingImp access (fun _ ↦ ⊤) p q := by
  ext; simp [strictImp]

/-- The conditional of the closest worlds is the conditional in which every world is
accessible. -/
theorem closestImp_eq_orderingImp {ord : W → Preorder W} :
    closestImp ord p q = orderingImp (fun _ ↦ Set.univ) ord p q := by
  ext; simp

end Ordering


end Conditional
