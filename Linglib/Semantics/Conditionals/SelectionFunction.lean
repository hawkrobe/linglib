module

public import Mathlib.Data.Set.Basic
public import Linglib.Semantics.Conditionals.Basic
public import Mathlib.Order.Extension.Linear
public import Mathlib.Data.Fintype.Card

/-!
# Selection functions

A **selection function** ([stalnaker-1968]) takes a world `w` and a possible proposition `A` to a
world `s.sel w A ∈ A` (condition (1), `inclusion`), `w` itself when `A` holds there (condition
(3), `centering`): intuitively the closest `A`-world. [cariani-santorio-2018]'s selectional
*will* uses the same structure.

The selection conditional (`selectionConditional`) is true at `w` iff its consequent holds at the
selected world, and vacuously true for an impossible antecedent, where [stalnaker-1968] selects
the absurd world. It quantifies over a domain of at most one world (`SelectionFunction.domain`),
so Conditional Excluded Middle and distribution over a disjunctive consequent hold
(`selectionConditional_cem`, `selectionConditional_or`).

[stalnaker-1981] interprets a similarity ordering with ties by supervaluation over its
completions (`SimilarityOrdering.Completion`), each selecting its least antecedent-world
(`SelectionFunction.Compatible`). Selection by a completion satisfies [stalnaker-1968]'s condition
(4) (`Compatible.cso`), and every closest antecedent-world is selected by some completion
(`SelectionFunction.exists_compatible`), so for a single conditional the supervaluation is the
conditional of the closest worlds (`mem_closestImp_iff_forall_compatible`).

## References

* [stalnaker-1968]
* [stalnaker-1981]
* [cariani-santorio-2018]
* [stalnaker-1975]
-/

@[expose] public section

namespace Conditional

/-- A **selection function** on `W`: maps a world and a proposition to
    a "selected" world, satisfying [stalnaker-1968]'s Inclusion
    and Centering axioms. -/
structure SelectionFunction (W : Type*) where
  /-- The selection map. -/
  sel : W → Set W → W
  /-- **Inclusion**: if `A` is non-empty, the selected world is in `A`. -/
  inclusion : ∀ (w : W) (A : Set W), A.Nonempty → sel w A ∈ A
  /-- **Centering**: if `w ∈ A`, then `sel w A = w`. -/
  centering : ∀ (w : W) (A : Set W), w ∈ A → sel w A = w

namespace SelectionFunction

variable {W : Type*}

/-- Centering specialized to a singleton: `sel w {w} = w`. -/
theorem sel_singleton (s : SelectionFunction W) (w : W) :
    s.sel w {w} = w :=
  s.centering w _ rfl

/-- The selected world satisfies the input proposition (Inclusion). -/
theorem sel_mem (s : SelectionFunction W) (w : W) (A : Set W)
    (hA : A.Nonempty) : s.sel w A ∈ A :=
  s.inclusion w A hA

/-- **Selection Excluded Middle** — the structural origin of [stalnaker-1968]'s
    Conditional Excluded Middle and [cariani-santorio-2018]'s Will
    Excluded Middle. Because `sel w f` is a *single* world, every
    predicate evaluated there satisfies excluded middle. The selection
    function reduces a quantificational question over a set to a
    propositional question at one point. -/
theorem sel_em (s : SelectionFunction W) (A : W → Prop) (f : Set W)
    (w : W) :
    A (s.sel w f) ∨ ¬ A (s.sel w f) :=
  Classical.em _

/-- **Selection Negation Swap** — negation commutes through evaluation
    at the selected world: applying a pointwise-negated predicate to
    `sel w f` is the same as negating the application. This is the
    structural origin of [cariani-santorio-2018]'s Negation Swap
    for *will*. The equivalence is `Iff.rfl` once the prejacent has
    been reduced to a propositional question at the selected point. -/
theorem sel_neg_swap (s : SelectionFunction W) (A : W → Prop) (f : Set W)
    (w : W) :
    (fun w' => ¬ A w') (s.sel w f) ↔ ¬ A (s.sel w f) := Iff.rfl

end SelectionFunction

section SelectionConditional

variable {W : Type*} (s : SelectionFunction W) {p q r : Set W} {w : W}

/-- The domain of the selection conditional: the world selected for `p` at `w` when `p` is
possible, and nothing when it is not. [stalnaker-1968] selects the absurd world, at which every
sentence is true, only for an antecedent true at no world possible relative to the base world
(its condition (2)), and its condition (1) forces that choice when the antecedent is impossible,
so the conditional is vacuously true there. With every world possible relative to every other,
as here, an antecedent is impossible exactly when it is empty. -/
def SelectionFunction.domain (w : W) (p : Set W) : Set W := {s.sel w p} ∩ p

theorem SelectionFunction.domain_eq_singleton (hp : p.Nonempty) :
    s.domain w p = {s.sel w p} :=
  Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (s.inclusion w p hp))

theorem SelectionFunction.subsingleton_domain : (s.domain w p).Subsingleton :=
  Set.subsingleton_singleton.anti Set.inter_subset_left

/-- **Selection conditional** ([stalnaker-1968]): *if p, q* is true at `w` iff `q` holds at the
world `s` selects for `p`, vacuously when `p` is impossible. The indicative refinement
([stalnaker-1975], a pragmatic constraint on `s`) and the counterfactual reading
([stalnaker-1981], supervaluation over the completions of a similarity ordering)
share this clause and differ in which selection functions are admissible. -/
def selectionConditional (p q : Set W) : Set W := ofDomain s.domain p q

theorem mem_selectionConditional :
    w ∈ selectionConditional s p q ↔ (p.Nonempty → s.sel w p ∈ q) := by
  rcases p.eq_empty_or_nonempty with rfl | hp
  · simp [selectionConditional, SelectionFunction.domain]
  · simp [selectionConditional, s.domain_eq_singleton hp, hp]

theorem mem_selectionConditional_of_nonempty (hp : p.Nonempty) :
    w ∈ selectionConditional s p q ↔ s.sel w p ∈ q := by
  simp [mem_selectionConditional, hp]

/-- **Conditional Excluded Middle**: a single selected world settles every consequent. -/
theorem selectionConditional_cem :
    w ∈ selectionConditional s p q ∨ w ∈ selectionConditional s p qᶜ :=
  mem_ofDomain_or_compl s.subsingleton_domain

/-- Distribution over a disjunctive consequent. -/
theorem selectionConditional_or (h : w ∈ selectionConditional s p (q ∪ r)) :
    w ∈ selectionConditional s p q ∨ w ∈ selectionConditional s p r :=
  mem_ofDomain_or s.subsingleton_domain h

/-- Modus ponens: by centering, an antecedent-world selects itself. -/
theorem selectionConditional_subset_materialImp : selectionConditional s p q ⊆ materialImp p q :=
  ofDomain_subset_materialImp fun w hw ↦ ⟨(s.centering w p hw).symm, hw⟩

end SelectionConditional

/-- **Pairwise preference induced by a selection function.**

`w₁` is preferred to `w₂` from center `w₀` iff when choosing between
just the two of them, the selection function picks `w₁`. -/
def selectionPrefers {W : Type*} (s : SelectionFunction W)
    (w₀ w₁ w₂ : W) : Prop :=
  s.sel w₀ {w₁, w₂} = w₁

/-- **A selection function is coherent** iff its induced pairwise
preference is transitive. It is strictly weaker than [stalnaker-1968]'s condition (4), which
selection by a completion of a similarity ordering satisfies (`Compatible.cso`); a selection
function satisfying (4) determines a *well-ordering* of possible
worlds ([stalnaker-1981]).

Not all selection functions satisfying `inclusion` + `centering` are
coherent — coherence is an additional rationality constraint. -/
def SelectionFunction.isCoherent {W : Type*} (s : SelectionFunction W) : Prop :=
  ∀ w₀ w₁ w₂ w₃ : W,
    selectionPrefers s w₀ w₁ w₂ → selectionPrefers s w₀ w₂ w₃ →
    selectionPrefers s w₀ w₁ w₃

/-! ### Selection functions compatible with a similarity ordering

[stalnaker-1981] reads a similarity ordering with ties and incomparabilities as the class of its
completions, the well orderings of the worlds that extend it, and a conditional as true when it
is true on every completion; a selection function selects, for each center, the least
antecedent-world of one completion (`SelectionFunction.Compatible`). Selection by a completion
satisfies [stalnaker-1968]'s condition (4) (`Compatible.cso`), and on a finite, strongly centered
ordering the supervaluation of a single conditional is the conditional of the closest worlds
(`mem_closestImp_iff_forall_compatible`). -/

section Compatible

variable {W : Type*} {sim : SimilarityOrdering W} {s : SelectionFunction W} {p q : Set W}
  {w v : W}

/-- A completion of a similarity ordering: for each center, a linear order of the worlds
extending the strict similarity order. -/
structure SimilarityOrdering.Completion (sim : SimilarityOrdering W) where
  /-- The completed order at each center. -/
  le : W → W → W → Prop
  linear : ∀ w, IsLinearOrder W (le w)
  le_of_lt : ∀ w x y, sim.closer w x y → ¬ sim.closer w y x → le w x y

/-- `s` is selected by the completion `c`: it selects, for each center, the least possible
antecedent-world in `c`'s order. -/
def SelectionFunction.SelectedBy (s : SelectionFunction W) (c : sim.Completion) : Prop :=
  ∀ w p, p.Nonempty → ∀ u ∈ p, c.le w (s.sel w p) u

/-- A selection function compatible with a similarity ordering is selected by one of its
completions. -/
def SelectionFunction.Compatible (s : SelectionFunction W) (sim : SimilarityOrdering W) : Prop :=
  ∃ c : sim.Completion, s.SelectedBy c

/-- A selection function selected by a completion satisfies [stalnaker-1968]'s condition (4):
if each of two antecedents holds at the world selected for the other, they select the same
world. -/
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
/-- Any closest antecedent-world comes first in some completion: order the worlds strictly
closer than it, then it, then the rest, each block by a linear extension of the strict order. -/
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

/-- [stalnaker-1981]'s supervaluation for a single conditional: on a finite, strongly centered
ordering, the conditional of the closest worlds holds iff the selection conditional is true on
every completion of the ordering. -/
theorem mem_closestImp_iff_forall_compatible [Finite W] (hc : sim.isCentered) :
    w ∈ closestImp sim p q ↔
      ∀ s : SelectionFunction W, s.Compatible sim → w ∈ selectionConditional s p q := by
  refine ⟨fun h s hs ↦ hs.closestImp_subset h, fun h v hv ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := SelectionFunction.exists_compatible hc hv
  exact (mem_selectionConditional_of_nonempty s ⟨_, sim.closest_subset w p hv⟩).1 (h s hs)

/-- Conditional Excluded Middle is super-true ([stalnaker-1981]): on every completion one of the
two conditionals holds, though under a tie neither need hold on all. -/
theorem cem_superTrue (sim : SimilarityOrdering W) (p q : Set W) (w : W) :
    ∀ s : SelectionFunction W, s.Compatible sim →
      w ∈ selectionConditional s p q ∪ selectionConditional s p qᶜ :=
  fun s _ ↦ selectionConditional_cem s

end Compatible

end Conditional
