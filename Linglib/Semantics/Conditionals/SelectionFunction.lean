module

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
* `SelectionFunction.IsCSO`: Stalnaker's condition (4), that antecedents each true at the world
  selected for the other select the same world.
* `SelectionFunction.restrict`: a selection function restricted to a set of worlds.
* `Completion`: a linear extension of a family of preorders at each center.
* `SelectionFunction.Compatible`: selection by a completion of a family of preorders.

## Main results

* `SelectionFunction.Compatible.isCSO`: selection by a completion satisfies condition (4).
* `mem_closestImp_iff_forall_compatible`: the conditional of the closest worlds is the
  supervaluation over completions.

## References

* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *Indicative conditionals* (1975)][stalnaker-1975]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
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

/-- Centering says that on `p` the selection for `p` is the identity, as an equality of
functions. -/
theorem SelectionFunction.eqOn_sel : Set.EqOn (s.sel · p) id p := fun w hw ↦ s.centering w p hw

theorem SelectionFunction.domain_of_mem (hw : w ∈ p) : s.domain w p = {w} := by
  rw [SelectionFunction.domain, s.centering w p hw,
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hw)]

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

/-- At an antecedent-world the selection conditional reduces to its consequent, by centering. -/
theorem mem_selectionConditional_of_mem (hw : w ∈ p) :
    w ∈ selectionConditional s p q ↔ w ∈ q := by
  rw [mem_selectionConditional_of_nonempty s ⟨w, hw⟩, s.centering w p hw]

theorem selectionConditional_inter_self : selectionConditional s p q ∩ p = q ∩ p :=
  Set.ext fun _ ↦ and_congr_left (mem_selectionConditional_of_mem s)

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
  fun _ h hp ↦ (mem_selectionConditional_of_mem s hp).1 h

end SelectionConditional

/-! ### Condition (4) and restriction -/

section CSO

variable {W : Type*} {s : SelectionFunction W} {w : W} {p q : Set W}

/-- A selection function satisfies [stalnaker-1968]'s condition (4) when two possible antecedents
each true at the world selected for the other select the same world. -/
def SelectionFunction.IsCSO (s : SelectionFunction W) : Prop :=
  ∀ w (p p' : Set W), p.Nonempty → p'.Nonempty → s.sel w p' ∈ p → s.sel w p ∈ p' →
    s.sel w p = s.sel w p'

/-- Under condition (4), the world selected for `p` lies in `q` iff it is the world selected for
`p ∩ q`. -/
theorem SelectionFunction.IsCSO.sel_mem_iff (hs : s.IsCSO) (h : (p ∩ q).Nonempty) :
    s.sel w p ∈ q ↔ s.sel w p = s.sel w (p ∩ q) :=
  ⟨fun hq ↦ hs w p (p ∩ q) (h.mono Set.inter_subset_left) h (s.inclusion w _ h).1
      ⟨s.inclusion w p (h.mono Set.inter_subset_left), hq⟩,
    fun he ↦ he ▸ (s.inclusion w _ h).2⟩

open Classical in
/-- The restriction of a selection function to a set `C`, which at a world of `C` selects among
the antecedent-worlds in `C` when there are any and otherwise selects as before. -/
noncomputable def SelectionFunction.restrict (s : SelectionFunction W) (C : Set W) :
    SelectionFunction W where
  sel w A := if w ∈ C ∧ (A ∩ C).Nonempty then s.sel w (A ∩ C) else s.sel w A
  inclusion w A hA := by
    split_ifs with h
    · exact (s.inclusion w (A ∩ C) h.2).1
    · exact s.inclusion w A hA
  centering w A hw := by
    split_ifs with h
    · exact s.centering w (A ∩ C) ⟨hw, h.1⟩
    · exact s.centering w A hw

theorem SelectionFunction.restrict_sel_of_mem (s : SelectionFunction W) (C : Set W) {A : Set W}
    (hw : w ∈ C) (hA : (A ∩ C).Nonempty) : (s.restrict C).sel w A = s.sel w (A ∩ C) := by
  simp [SelectionFunction.restrict, hw, hA]

theorem SelectionFunction.restrict_sel_of_not_nonempty (s : SelectionFunction W) (C : Set W)
    {A : Set W} (hA : ¬ (A ∩ C).Nonempty) : (s.restrict C).sel w A = s.sel w A := by
  simp [SelectionFunction.restrict, hA]

end CSO

/-! ### Selection functions compatible with a similarity ordering

[stalnaker-1981] reads a similarity ordering with ties and incomparabilities as the class of its
completions, the well orderings of the worlds that extend it, and a conditional as true when it
is true on every completion. -/

section Compatible

variable {W : Type*} {ord : W → Preorder W} {s : SelectionFunction W} {p q : Set W} {w v : W}

/-- A completion of a family of preorders assigns to each center a linear order of the worlds that
extends its strict order. -/
structure Completion (ord : W → Preorder W) where
  /-- The completed order at each center. -/
  le : W → W → W → Prop
  linear : ∀ w, IsLinearOrder W (le w)
  le_of_lt : ∀ w x y, (ord w).lt x y → le w x y

/-- A selection function is selected by a completion when it selects, for each center, the least
possible antecedent-world in the completion's order. -/
def SelectionFunction.SelectedBy (s : SelectionFunction W) (c : Completion ord) : Prop :=
  ∀ w p, p.Nonempty → ∀ u ∈ p, c.le w (s.sel w p) u

/-- A selection function is compatible with a family of preorders when some completion of the
family selects it. -/
def SelectionFunction.Compatible (s : SelectionFunction W) (ord : W → Preorder W) : Prop :=
  ∃ c : Completion ord, s.SelectedBy c

/-- A selection function selected by a completion satisfies [stalnaker-1968]'s condition (4). -/
theorem SelectionFunction.Compatible.isCSO (hs : s.Compatible ord) : s.IsCSO := by
  intro w p p' hp hp' h₁ h₂
  obtain ⟨c, hc⟩ := hs
  have := c.linear w
  exact antisymm (hc w p hp _ h₁) (hc w p' hp' _ h₂)

/-- A compatible selection function selects a closest antecedent-world. -/
theorem SelectionFunction.Compatible.sel_mem_minimals (hs : s.Compatible ord) (hp : p.Nonempty) :
    s.sel w p ∈ (ord w).minimals p := by
  obtain ⟨c, hc⟩ := hs
  have := c.linear w
  let := ord w
  refine ⟨s.inclusion w p hp, fun u hu hus ↦ ?_⟩
  by_contra hn
  have hu := antisymm (c.le_of_lt w u _ (hus.lt_of_not_ge hn)) (hc w p hp u hu)
  exact hn (hu ▸ le_rfl)

theorem SelectionFunction.Compatible.domain_subset (hs : s.Compatible ord) :
    s.domain w p ⊆ (ord w).minimals p := by
  rintro v ⟨rfl, hv⟩
  exact hs.sel_mem_minimals ⟨_, hv⟩

/-- Every compatible selection function makes true what the closest worlds make true. -/
theorem SelectionFunction.Compatible.closestImp_subset (hs : s.Compatible ord) :
    closestImp ord p q ⊆ selectionConditional s p q :=
  fun _ h ↦ hs.domain_subset.trans h

/-- A strict order with equality is a partial order. -/
private theorem isPartialOrder_eq_or_lt (P : Preorder W) :
    IsPartialOrder W fun x y ↦ x = y ∨ P.lt x y :=
  let := P
  { refl := fun _ ↦ .inl rfl
    trans := fun x y z hxy hyz ↦ by
      rcases hxy with rfl | h₁
      · exact hyz
      rcases hyz with rfl | h₂
      exacts [.inr h₁, .inr (h₁.trans h₂)]
    antisymm := fun x y hxy hyx ↦ by
      rcases hxy with rfl | h₁
      · rfl
      rcases hyx with rfl | h₂
      exacts [rfl, absurd h₂ h₁.asymm] }

open Classical in
/-- Any closest antecedent-world comes first among the antecedent-worlds in some completion, which
orders the worlds strictly closer than it, then it, then the rest. -/
theorem exists_completion (hv : v ∈ (ord w).minimals p) :
    ∃ c : Completion ord, ∀ u ∈ p, c.le w v u := by
  choose L hL hext using fun w' ↦ @extend_partialOrder W _ (isPartialOrder_eq_or_lt (ord w'))
  let key : W → ℕ := fun u ↦ if (ord w).lt u v then 0 else if u = v then 1 else 2
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
  have hkey : ∀ x y, (ord w).lt x y → key x ≤ key y := by
    intro x y hxy
    let := ord w
    have h₀ : y < v → x < v := hxy.trans
    have h₁ : y = v → x < v := fun h ↦ h ▸ hxy
    simp only [key]
    split_ifs <;> first | omega | (exfalso; tauto)
  refine ⟨⟨le, lin, fun w' x y hxy ↦ ?_⟩, fun u hu ↦ ?_⟩
  · by_cases hw : w' = w
    · subst hw
      simp only [le, ↓reduceIte]
      rcases (hkey x y hxy).lt_or_eq with hk | hk
      exacts [.inl hk, .inr ⟨hk, hext w' x y (.inr hxy)⟩]
    · simp only [le, hw, ↓reduceIte]
      exact hext w' x y (.inr hxy)
  · simp only [le, ↓reduceIte]
    rcases eq_or_ne u v with rfl | huv
    · have := hL w
      exact .inr ⟨rfl, refl u⟩
    · refine .inl ?_
      let := ord w
      have h0 : ¬ u < v := fun h ↦ h.not_ge (hv.2 hu h.le)
      simp [key, h0, huv]

open Classical in
/-- On a finite, strongly centered family of preorders, any closest antecedent-world is selected
by some compatible selection function. -/
theorem SelectionFunction.exists_compatible [Finite W] (hc : IsCentered ord)
    (hv : v ∈ (ord w).minimals p) :
    ∃ s : SelectionFunction W, s.Compatible ord ∧ s.sel w p = v := by
  obtain ⟨c, hcv⟩ := exists_completion hv
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
    · exact antisymm (hmle w' p' ⟨w', hw'⟩ w' hw') (c.le_of_lt w' w' _ (hc w' _ h.symm))
  · simpa [hp'] using hmle w' p' hp' u hu
  · have := c.linear w
    have hp : p.Nonempty := ⟨v, hv.1⟩
    show (if h : p.Nonempty then m w p else w) = v
    simp only [hp, ↓reduceDIte]
    exact antisymm (hmle w p hp v hv.1) (hcv _ (hm w p hp))

/-- On a finite, strongly centered family of preorders, the conditional of the closest worlds
holds iff the selection conditional is true on every completion, [stalnaker-1981]'s
supervaluation for a single conditional. -/
theorem mem_closestImp_iff_forall_compatible [Finite W] (hc : IsCentered ord) :
    w ∈ closestImp ord p q ↔
      ∀ s : SelectionFunction W, s.Compatible ord → w ∈ selectionConditional s p q := by
  refine ⟨fun h s hs ↦ hs.closestImp_subset h, fun h v hv ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := SelectionFunction.exists_compatible hc hv
  exact (mem_selectionConditional_of_nonempty s ⟨_, hv.1⟩).1 (h s hs)

end Compatible

end Conditional
