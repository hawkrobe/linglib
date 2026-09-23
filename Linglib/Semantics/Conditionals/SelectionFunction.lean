module

public import Mathlib.Data.Set.Basic
public import Linglib.Semantics.Conditionals.Basic
public import Mathlib.Order.Extension.Linear
public import Mathlib.Data.Fintype.Card

/-!
# Selection functions

This file defines selection functions and the selection conditional. A selection function takes
a world and a possible proposition to a world at which the proposition holds, the world itself
when it holds there: intuitively the closest world at which the proposition holds. The selection
conditional *if p, q* is true when `q` holds at the world selected for `p`, and vacuously true
when `p` is impossible. A similarity ordering with ties corresponds to the class of selection
functions its completions determine, and for a single conditional the supervaluation over them is
the conditional of the closest worlds.

## Main definitions

* `SelectionFunction`: a selection function.
* `selectionConditional`: the selection conditional.
* `SimilarityOrdering.Completion`: a linear extension of a similarity ordering at each center.
* `SelectionFunction.Compatible`: selection by a completion of a similarity ordering.

## Main results

* `SelectionFunction.Compatible.cso`: selection by a completion is coherent across antecedents.
* `mem_closestImp_iff_forall_compatible`: the conditional of the closest worlds is the
  supervaluation over completions.

## References

* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *Indicative conditionals* (1975)][stalnaker-1975]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
-/

@[expose] public section

namespace Conditional

/-- A selection function ([stalnaker-1968]) takes a world and a proposition to a selected
world, one at which the proposition holds when it is possible, and the world itself when the
proposition holds there. -/
structure SelectionFunction (W : Type*) where
  /-- The selection map. -/
  sel : W → Set W → W
  /-- The world selected for a possible proposition is one at which it holds. -/
  inclusion : ∀ (w : W) (A : Set W), A.Nonempty → sel w A ∈ A
  /-- A world at which the proposition holds selects itself. -/
  centering : ∀ (w : W) (A : Set W), w ∈ A → sel w A = w

namespace SelectionFunction

variable {W : Type*}

end SelectionFunction

section SelectionConditional

variable {W : Type*} (s : SelectionFunction W) {p q r : Set W} {w : W}

/-- The domain of the selection conditional, the world selected for `p` when `p` is possible and
nothing otherwise. [stalnaker-1968] selects the absurd world, at which every sentence is true,
exactly for an impossible antecedent (conditions (1) and (2)), so the conditional is vacuously
true there. With every world possible relative to every other, an antecedent is impossible when
it is empty. -/
def SelectionFunction.domain (w : W) (p : Set W) : Set W := {s.sel w p} ∩ p

theorem SelectionFunction.domain_eq_singleton (hp : p.Nonempty) :
    s.domain w p = {s.sel w p} :=
  Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (s.inclusion w p hp))

theorem SelectionFunction.subsingleton_domain : (s.domain w p).Subsingleton :=
  Set.subsingleton_singleton.anti Set.inter_subset_left

/-- The selection conditional of [stalnaker-1968], true at `w` when `q` holds at the world `s`
selects for `p` and vacuously true when `p` is impossible. The indicative reading of
[stalnaker-1975] and the counterfactual reading of [stalnaker-1981] share this clause and differ
in which selection functions are admissible. -/
def selectionConditional (p q : Set W) : Set W := ofDomain s.domain p q

theorem mem_selectionConditional :
    w ∈ selectionConditional s p q ↔ (p.Nonempty → s.sel w p ∈ q) := by
  rcases p.eq_empty_or_nonempty with rfl | hp
  · simp [selectionConditional, SelectionFunction.domain]
  · simp [selectionConditional, s.domain_eq_singleton hp, hp]

theorem mem_selectionConditional_of_nonempty (hp : p.Nonempty) :
    w ∈ selectionConditional s p q ↔ s.sel w p ∈ q := by
  simp [mem_selectionConditional, hp]

/-- The selection conditional satisfies Conditional Excluded Middle, since a single selected world
settles every consequent. -/
theorem selectionConditional_cem :
    w ∈ selectionConditional s p q ∨ w ∈ selectionConditional s p qᶜ :=
  mem_ofDomain_or_compl s.subsingleton_domain

/-- The selection conditional distributes over a disjunctive consequent. -/
theorem selectionConditional_or (h : w ∈ selectionConditional s p (q ∪ r)) :
    w ∈ selectionConditional s p q ∨ w ∈ selectionConditional s p r :=
  mem_ofDomain_or s.subsingleton_domain h

/-- The selection conditional entails the material conditional, since by centering an
antecedent-world selects itself. -/
theorem selectionConditional_subset_materialImp : selectionConditional s p q ⊆ materialImp p q :=
  ofDomain_subset_materialImp fun w hw ↦ ⟨(s.centering w p hw).symm, hw⟩

end SelectionConditional

/-- `w₁` is preferred to `w₂` from `w₀` when the selection function picks `w₁` from `{w₁, w₂}`. -/
def selectionPrefers {W : Type*} (s : SelectionFunction W)
    (w₀ w₁ w₂ : W) : Prop :=
  s.sel w₀ {w₁, w₂} = w₁

/-- A selection function is coherent when its pairwise preference is transitive. Coherence is
weaker than [stalnaker-1968]'s condition (4), which selection by a completion satisfies and which
makes the similarity relation a selection function induces a well ordering ([stalnaker-1981]). -/
def SelectionFunction.isCoherent {W : Type*} (s : SelectionFunction W) : Prop :=
  ∀ w₀ w₁ w₂ w₃ : W,
    selectionPrefers s w₀ w₁ w₂ → selectionPrefers s w₀ w₂ w₃ →
    selectionPrefers s w₀ w₁ w₃

/-! ### Selection functions compatible with a similarity ordering

[stalnaker-1981] reads a similarity ordering with ties and incomparabilities as the class of its
completions, the well orderings of the worlds that extend it, and a conditional as true when it
is true on every completion. -/

section Compatible

variable {W : Type*} {sim : SimilarityOrdering W} {s : SelectionFunction W} {p q : Set W}
  {w v : W}

/-- A completion of a similarity ordering assigns to each center a linear order of the worlds that
extends the strict similarity order. -/
structure SimilarityOrdering.Completion (sim : SimilarityOrdering W) where
  /-- The completed order at each center. -/
  le : W → W → W → Prop
  linear : ∀ w, IsLinearOrder W (le w)
  le_of_lt : ∀ w x y, sim.closer w x y → ¬ sim.closer w y x → le w x y

/-- A selection function is selected by a completion when it selects, for each center, the least
possible antecedent-world in the completion's order. -/
def SelectionFunction.SelectedBy (s : SelectionFunction W) (c : sim.Completion) : Prop :=
  ∀ w p, p.Nonempty → ∀ u ∈ p, c.le w (s.sel w p) u

/-- A selection function is compatible with a similarity ordering when some completion of the
ordering selects it. -/
def SelectionFunction.Compatible (s : SelectionFunction W) (sim : SimilarityOrdering W) : Prop :=
  ∃ c : sim.Completion, s.SelectedBy c

/-- A selection function selected by a completion satisfies [stalnaker-1968]'s condition (4), that
two antecedents each true at the world selected for the other select the same world. -/
theorem SelectionFunction.Compatible.cso (hs : s.Compatible sim) {p p' : Set W}
    (hp : p.Nonempty) (hp' : p'.Nonempty) (h₁ : s.sel w p' ∈ p) (h₂ : s.sel w p ∈ p') :
    s.sel w p = s.sel w p' := by
  obtain ⟨c, hc⟩ := hs
  have := c.linear w
  exact antisymm (hc w p hp _ h₁) (hc w p' hp' _ h₂)

/-- A compatible selection function selects a closest antecedent-world. -/
theorem SelectionFunction.Compatible.sel_mem_closest (hs : s.Compatible sim) (hp : p.Nonempty) :
    s.sel w p ∈ sim.closest w p := by
  obtain ⟨c, hc⟩ := hs
  have := c.linear w
  refine ⟨s.inclusion w p hp, fun u hu ↦ or_iff_not_imp_right.2 fun hlt ↦ ?_⟩
  by_contra hn
  have hlt' := c.le_of_lt w u _ (not_not.1 hlt) hn
  have hsel := hc w p hp u hu
  exact hn (antisymm hlt' hsel ▸ sim.closer_refl w u)

theorem SelectionFunction.Compatible.domain_subset (hs : s.Compatible sim) :
    s.domain w p ⊆ sim.closest w p := by
  rintro v ⟨rfl, hv⟩
  exact hs.sel_mem_closest ⟨_, hv⟩

/-- Every compatible selection function makes true what the closest worlds make true. -/
theorem SelectionFunction.Compatible.closestImp_subset (hs : s.Compatible sim) :
    closestImp sim p q ⊆ selectionConditional s p q :=
  fun _ h ↦ hs.domain_subset.trans h

/-- The strict similarity order at a center, with equality, is a partial order. -/
private theorem isPartialOrder_strict (sim : SimilarityOrdering W) (w : W) :
    IsPartialOrder W fun x y ↦ x = y ∨ (sim.closer w x y ∧ ¬ sim.closer w y x) where
  refl _ := .inl rfl
  trans x y z hxy hyz := by
    rcases hxy with rfl | ⟨h₁, h₂⟩
    · exact hyz
    rcases hyz with rfl | ⟨h₃, h₄⟩
    · exact .inr ⟨h₁, h₂⟩
    exact .inr ⟨sim.closer_trans w x y z h₁ h₃, fun h ↦ h₄ (sim.closer_trans w z x y h h₁)⟩
  antisymm x y hxy hyx := by
    rcases hxy with rfl | ⟨h₁, h₂⟩
    · rfl
    rcases hyx with rfl | ⟨h₃, -⟩
    · rfl
    exact absurd h₃ h₂

open Classical in
/-- Any closest antecedent-world comes first among the antecedent-worlds in some completion, which
orders the worlds strictly closer than it, then it, then the rest. -/
theorem SimilarityOrdering.exists_completion (hv : v ∈ sim.closest w p) :
    ∃ c : sim.Completion, ∀ u ∈ p, c.le w v u := by
  choose L hL hext using fun w' ↦ @extend_partialOrder W _ (isPartialOrder_strict sim w')
  let key : W → ℕ := fun u ↦
    if sim.closer w u v ∧ ¬ sim.closer w v u then 0 else if u = v then 1 else 2
  let le : W → W → W → Prop := fun w' x y ↦
    if w' = w then key x < key y ∨ (key x = key y ∧ L w x y) else L w' x y
  have lin : ∀ w', IsLinearOrder W (le w') := by
    intro w'
    have := hL w'
    have := hL w
    by_cases hw : w' = w
    · subst hw
      simp only [le, ↓reduceIte]
      exact
        { refl := fun x ↦ .inr ⟨rfl, refl x⟩
          trans := fun x y z hxy hyz ↦ by
            rcases hxy with h | ⟨h, h'⟩ <;> rcases hyz with g | ⟨g, g'⟩
            · exact .inl (h.trans g)
            · exact .inl (g ▸ h)
            · exact .inl (h ▸ g)
            · exact .inr ⟨h.trans g, _root_.trans h' g'⟩
          antisymm := fun x y hxy hyx ↦ by
            rcases hxy with h | ⟨h, h'⟩ <;> rcases hyx with g | ⟨g, g'⟩
            · exact absurd (h.trans g) (lt_irrefl _)
            · exact absurd h (g ▸ lt_irrefl _)
            · exact absurd g (h ▸ lt_irrefl _)
            · exact antisymm h' g'
          total := fun x y ↦ by
            rcases lt_trichotomy (key x) (key y) with h | h | h
            · exact .inl (.inl h)
            · exact (total_of (L w') x y).imp (fun g ↦ .inr ⟨h, g⟩) fun g ↦ .inr ⟨h.symm, g⟩
            · exact .inr (.inl h) }
    · simp only [le, hw, ↓reduceIte]
      exact hL w'
  have hkey : ∀ x y, sim.closer w x y → ¬ sim.closer w y x → key x ≤ key y := by
    intro x y hxy hyx
    have h₀ : sim.closer w y v ∧ ¬ sim.closer w v y → sim.closer w x v ∧ ¬ sim.closer w v x :=
      fun h ↦ ⟨sim.closer_trans w x y v hxy h.1, fun h' ↦ h.2 (sim.closer_trans w v x y h' hxy)⟩
    have h₁ : y = v → sim.closer w x v ∧ ¬ sim.closer w v x := fun h ↦ h ▸ ⟨hxy, hyx⟩
    simp only [key]
    split_ifs <;> first | omega | (exfalso; tauto)
  refine ⟨⟨le, lin, fun w' x y hxy hyx ↦ ?_⟩, fun u hu ↦ ?_⟩
  · by_cases hw : w' = w
    · simp only [le, hw, ↓reduceIte]
      rw [hw] at hxy hyx
      rcases (hkey x y hxy hyx).lt_or_eq with hk | hk
      · exact .inl hk
      · exact .inr ⟨hk, hext w x y (.inr ⟨hxy, hyx⟩)⟩
    · simp only [le, hw, ↓reduceIte]
      exact hext w' x y (.inr ⟨hxy, hyx⟩)
  · simp only [le, ↓reduceIte]
    rcases eq_or_ne u v with rfl | huv
    · have := hL w
      exact .inr ⟨rfl, refl u⟩
    · refine .inl ?_
      have h0 : ¬ (sim.closer w u v ∧ ¬ sim.closer w v u) := fun h ↦
        (hv.2 u hu).elim h.2 fun h' ↦ h' h.1
      have hv0 : ¬ (sim.closer w v v ∧ ¬ sim.closer w v v) := fun h ↦ h.2 h.1
      simp [key, h0, hv0, huv]

open Classical in
/-- On a finite, strongly centered ordering, any closest antecedent-world is selected by some
compatible selection function. -/
theorem SelectionFunction.exists_compatible [Finite W] (hc : sim.isCentered)
    (hv : v ∈ sim.closest w p) : ∃ s : SelectionFunction W, s.Compatible sim ∧ s.sel w p = v := by
  obtain ⟨c, hcv⟩ := SimilarityOrdering.exists_completion hv
  have hleast : ∀ w' (p' : Set W), p'.Nonempty → ∃ m ∈ p', ∀ u ∈ p', c.le w' m u := by
    intro w' p' hp'
    have := c.linear w'
    let lt : W → W → Prop := fun x y ↦ c.le w' x y ∧ ¬ c.le w' y x
    have : IsTrans W lt :=
      ⟨fun x y z h g ↦ ⟨_root_.trans h.1 g.1, fun hzx ↦ h.2 (_root_.trans g.1 hzx)⟩⟩
    have : Std.Irrefl lt := ⟨fun x h ↦ h.2 h.1⟩
    obtain ⟨m, hm, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl lt).has_min p' hp'
    exact ⟨m, hm, fun u hu ↦ (total_of (c.le w') m u).elim id fun hum ↦
      not_not.1 fun hmu ↦ hmin u hu ⟨hum, hmu⟩⟩
  choose! m hm hmle using hleast
  refine ⟨⟨fun w' p' ↦ if h : p'.Nonempty then m w' p' else w', fun w' p' hp' ↦ ?_,
    fun w' p' hw' ↦ ?_⟩, ⟨c, fun w' p' hp' u hu ↦ ?_⟩, ?_⟩
  · simpa [hp'] using hm w' p' hp'
  · have := c.linear w'
    have hne : p'.Nonempty := ⟨w', hw'⟩
    show (if h : p'.Nonempty then m w' p' else w') = w'
    simp only [hne, ↓reduceDIte]
    rcases eq_or_ne (m w' p') w' with h | h
    · exact h
    · exact antisymm (hmle w' p' ⟨w', hw'⟩ w' hw')
        (c.le_of_lt w' w' _ (hc w' _ h.symm).1 (hc w' _ h.symm).2)
  · simpa [hp'] using hmle w' p' hp' u hu
  · have := c.linear w
    have hp : p.Nonempty := ⟨v, sim.closest_subset w p hv⟩
    show (if h : p.Nonempty then m w p else w) = v
    simp only [hp, ↓reduceDIte]
    exact antisymm (hmle w p hp v (sim.closest_subset w p hv)) (hcv _ (hm w p hp))

/-- On a finite, strongly centered ordering, the conditional of the closest worlds holds iff the
selection conditional is true on every completion, [stalnaker-1981]'s supervaluation for a
single conditional. -/
theorem mem_closestImp_iff_forall_compatible [Finite W] (hc : sim.isCentered) :
    w ∈ closestImp sim p q ↔
      ∀ s : SelectionFunction W, s.Compatible sim → w ∈ selectionConditional s p q := by
  refine ⟨fun h s hs ↦ hs.closestImp_subset h, fun h v hv ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := SelectionFunction.exists_compatible hc hv
  exact (mem_selectionConditional_of_nonempty s ⟨_, sim.closest_subset w p hv⟩).1 (h s hs)

/-- Conditional Excluded Middle is true on every completion ([stalnaker-1981]), though under a tie
neither conditional need be. -/
theorem cem_superTrue (sim : SimilarityOrdering W) (p q : Set W) (w : W) :
    ∀ s : SelectionFunction W, s.Compatible sim →
      w ∈ selectionConditional s p q ∪ selectionConditional s p qᶜ :=
  fun s _ ↦ selectionConditional_cem s

end Compatible

end Conditional
