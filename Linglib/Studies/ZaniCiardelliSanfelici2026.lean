import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
import Linglib.Studies.BarLevFox2020

/-!
# Zani, Ciardelli and Sanfelici (2026): Simplification of Disjunctive Antecedents

This file formalizes the semantic predictions that [zani-ciardelli-sanfelici-2026] tests in
an acquisition study of conditionals with disjunctive antecedents, *if A or B, C*. The three
readings of Table 2 are truth conditions over a similarity model: the simplification reading
SDA is the conjunction of the two simplifications, the substrate's `Distributive`; the
disjunctive conditional reading `DCR` is their disjunction; and the asymmetric reading AR is
the simplification of the more realistic disjunct. Under [lewis-1973]'s minimal-change
semantics, the substrate's `would`, the DAC quantifies over the closest worlds of the
disjunction, and §2's case analysis follows: when neither disjunct is more realistic than the
other the DAC is equivalent to SDA (`would_iff_distributive_of_equallyRealistic`), and when
one is more realistic it is equivalent to that disjunct's simplification
(`would_iff_of_moreRealistic`). The readings are ordered by strength, SDA entails AR entails
DCR (`would_of_distributive`, `dcr_of_would`).

The experiment's target items (9) are evaluated in the race scenario of §4: the squirrel and
the tortoise compete, the prize named in the consequent belongs to one of them, and the
similarity orderings of Figure 3 make the squirrel a more realistic winner than the tortoise
or tie them. Table 3's response patterns follow by computation (`table3_sda`, `table3_dcr`,
`table3_ar`), and acceptance of the closeness evaluation item *if the hare doesn't win, the
squirrel will win* reveals that the participant regards the squirrel as the more realistic
winner (`moreRealistic_of_closeness`). On the homogeneity accounts of [santorio-2018] and
[cariani-goldstein-2020], SDA is the universal and DCR the existential resolution of the
homogeneous quantification over the disjuncts (`dcr_iff_homogeneity_ne_false`), which is the
source of the paper's prediction that children shift from DCR to SDA as they do for plural
definites; on [bar-lev-fox-2020]'s account, the literal meaning is Lewis's (`literal_eq_would`)
and exhaustification strengthens it to SDA (`distributive_of_exh`).

## Implementation notes

* A proposition is more realistic than another at `w` when it has closest worlds and each of
  them is strictly closer than every closest world of the other (`MoreRealistic`); the case
  analysis of §2 assumes a total similarity ordering.
* The scenario's worlds are the three possible winners, ordered by speed from the actual
  world in which the hare wins; the two orderings realize the conditions of Figure 3.

## TODO

* The response patterns of Tables 5–8, the rates of Figures 4 and 5 and the regression of
  Table 4 await a data format for experimental results.

## References

* [zani-ciardelli-sanfelici-2026]
* [lewis-1973]
* [alonso-ovalle-2009]
* [santorio-2018]
* [cariani-goldstein-2020]
* [bar-lev-fox-2020]
* [tieu-kriz-chemla-2019]
-/

namespace ZaniCiardelliSanfelici2026

open Conditional Conditional.Counterfactual

section Closest

variable {W : Type*} [DecidableEq W] (sim : SimilarityOrdering W) (A B : Finset W) (w : W)

/-! ### Realism (§2) -/

/-- `A` is more realistic than `B` at `w`: `A` has closest worlds, and each of them is strictly
closer to `w` than every closest `B`-world. -/
def MoreRealistic : Prop :=
  (sim.closestWorlds w A).Nonempty ∧
    ∀ a ∈ sim.closestWorlds w A, ∀ b ∈ sim.closestWorlds w B,
      sim.closer w a b ∧ ¬ sim.closer w b a

variable {sim A B w}

/-- Under a total ordering every world of a set is at least as far as some closest world. -/
private theorem exists_closest_closer
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁) {S : Finset W} {x : W}
    (hx : x ∈ S) : ∃ b ∈ sim.closestWorlds w S, sim.closer w b x := by
  obtain ⟨b, hb⟩ := sim.closestWorlds_nonempty w ⟨x, hx⟩
  refine ⟨b, hb, ?_⟩
  rw [SimilarityOrdering.mem_closestWorlds] at hb
  exact (hb.2 x hx).elim id fun h ↦ (htot w b x).resolve_right h

/-- Two closest worlds of the same set are equally close under a total ordering. -/
private theorem closer_of_mem_closest
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁) {S : Finset W} {x y : W}
    (hx : x ∈ sim.closestWorlds w S) (hy : y ∈ sim.closestWorlds w S) : sim.closer w x y := by
  rw [SimilarityOrdering.mem_closestWorlds] at hx hy
  exact (hx.2 y hy.1).elim id fun h ↦ (htot w x y).resolve_right h

/-- Case 2 of §2: when `A` is more realistic than `B`, the closest worlds of the disjunction are
the closest `A`-worlds. -/
theorem closestWorlds_union_of_moreRealistic
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (h : MoreRealistic sim A B w) :
    sim.closestWorlds w (A ∪ B) = sim.closestWorlds w A := by
  obtain ⟨⟨a₀, ha₀⟩, hAB⟩ := h
  ext x
  constructor
  · intro hx
    have hx' := hx
    rw [SimilarityOrdering.mem_closestWorlds, Finset.mem_union] at hx'
    refine sim.mem_closestWorlds_of_subset Finset.subset_union_left hx (hx'.1.resolve_right ?_)
    intro hxB
    obtain ⟨b, hb, hbx⟩ := exists_closest_closer htot hxB
    obtain ⟨hab, hba⟩ := hAB a₀ ha₀ b hb
    have hxa : sim.closer w x a₀ :=
      (hx'.2 a₀ (Finset.mem_union_left _ (sim.closestWorlds_subset w A ha₀))).elim id
        fun hn ↦ (hn (sim.closer_trans w a₀ b x hab hbx)).elim
    exact hba (sim.closer_trans w b x a₀ hbx hxa)
  · intro hx
    have hx' := hx
    rw [SimilarityOrdering.mem_closestWorlds] at hx' ⊢
    refine ⟨Finset.mem_union_left _ hx'.1, fun u hu ↦ Or.inl ?_⟩
    rcases Finset.mem_union.mp hu with huA | huB
    · exact (hx'.2 u huA).elim id fun hn ↦ (htot w x u).resolve_right hn
    · obtain ⟨b, hb, hbu⟩ := exists_closest_closer htot huB
      exact sim.closer_trans w x b u (hAB x hx b hb).1 hbu

/-- Case 1 of §2: when neither disjunct is more realistic than the other, the closest worlds of
the disjunction are the closest worlds of the disjuncts together. -/
theorem closestWorlds_union_of_equallyRealistic
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (hAB : ¬ MoreRealistic sim A B w) (hBA : ¬ MoreRealistic sim B A w) :
    sim.closestWorlds w (A ∪ B) = sim.closestWorlds w A ∪ sim.closestWorlds w B := by
  -- a closest world of one disjunct is a closest world of the union
  have key : ∀ {S T : Finset W}, ¬ MoreRealistic sim T S w →
      ∀ x ∈ sim.closestWorlds w S, x ∈ sim.closestWorlds w (S ∪ T) := by
    intro S T hTS x hx
    have hx' := hx
    rw [SimilarityOrdering.mem_closestWorlds] at hx' ⊢
    refine ⟨Finset.mem_union_left _ hx'.1, fun u hu ↦ ?_⟩
    rcases Finset.mem_union.mp hu with huS | huT
    · exact hx'.2 u huS
    · by_contra hcon
      rw [not_or, not_not] at hcon
      obtain ⟨b, hb, hbu⟩ := exists_closest_closer htot huT
      have hbx : sim.closer w b x := sim.closer_trans w b u x hbu hcon.2
      have hxb : ¬ sim.closer w x b := fun hxb ↦ hcon.1 (sim.closer_trans w x b u hxb hbu)
      refine hTS ⟨⟨b, hb⟩, fun b' hb' a ha ↦ ⟨?_, ?_⟩⟩
      · exact sim.closer_trans w b' x a
          (sim.closer_trans w b' b x (closer_of_mem_closest htot hb' hb) hbx)
          (closer_of_mem_closest htot hx ha)
      · intro hab'
        exact hxb (sim.closer_trans w x b' b (sim.closer_trans w x a b'
          (closer_of_mem_closest htot hx ha) hab') (closer_of_mem_closest htot hb' hb))
  ext x
  constructor
  · intro hx
    have hx' := hx
    rw [SimilarityOrdering.mem_closestWorlds, Finset.mem_union] at hx'
    rcases hx'.1 with hxA | hxB
    · exact Finset.mem_union_left _
        (sim.mem_closestWorlds_of_subset Finset.subset_union_left hx hxA)
    · exact Finset.mem_union_right _
        (sim.mem_closestWorlds_of_subset Finset.subset_union_right hx hxB)
  · intro hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact key hBA x hxA
    · rw [Finset.union_comm]
      exact key hAB x hxB

end Closest

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W)
  (A B : Finset W) (C : Set W) (w : W)

/-! ### The three readings (Table 2) -/

/-- The disjunctive conditional reading: some simplification holds. -/
def DCR : Prop := w ∈ closestImp sim ↑A C ∨ w ∈ closestImp sim ↑B C

private theorem filter_mem (S : Finset W) : Finset.univ.filter (· ∈ (S : Set W)) = S := by
  ext
  simp

/-- A counterfactual whose antecedent is a finset, on its closest worlds. -/
private theorem mem_closestImp_coe (S : Finset W) :
    w ∈ closestImp sim ↑S C ↔ ∀ v ∈ sim.closestWorlds w S, v ∈ C := by
  rw [mem_closestImp_iff_closestWorlds, filter_mem]

omit [Fintype W] in
private theorem would_eq (A B : Finset W) :
    would sim [A, B] C w = (w ∈ closestImp sim ↑(A ∪ B) C) := by
  simp only [would, disjunctiveClosure, List.foldr, Finset.union_empty]

/-- Lewis's truth condition for the DAC quantifies over the closest worlds of the union of the
disjuncts. -/
theorem would_pair :
    would sim [A, B] C w ↔ ∀ v ∈ sim.closestWorlds w (A ∪ B), v ∈ C := by
  rw [would_eq, mem_closestImp_coe]

variable {sim A B w}

/-- When neither disjunct is more realistic, Lewis's DAC is equivalent to SDA. -/
theorem would_iff_distributive_of_equallyRealistic
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (hAB : ¬ MoreRealistic sim A B w) (hBA : ¬ MoreRealistic sim B A w) :
    would sim [A, B] C w ↔ Distributive sim [A, B] C w := by
  rw [would_pair, closestWorlds_union_of_equallyRealistic htot hAB hBA, Finset.forall_mem_union]
  simp only [Distributive, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_closestImp_coe]

/-- When `A` is more realistic than `B`, Lewis's DAC is equivalent to the simplification with
the more realistic disjunct: the asymmetric reading. -/
theorem would_iff_of_moreRealistic
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (h : MoreRealistic sim A B w) :
    would sim [A, B] C w ↔ w ∈ closestImp sim ↑A C := by
  rw [would_pair, closestWorlds_union_of_moreRealistic htot h, mem_closestImp_coe]

omit [Fintype W] in
/-- SDA entails Lewis's DAC, and so the asymmetric reading. -/
theorem would_of_distributive (h : Distributive sim [A, B] C w) : would sim [A, B] C w := by
  rw [would_eq, Finset.coe_union]
  exact mem_closestImp_union (h A (by simp)) (h B (by simp))

omit [Fintype W] in
/-- Lewis's DAC, and so the asymmetric reading, entails DCR under a total ordering. -/
theorem dcr_of_would (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (h : would sim [A, B] C w) : DCR sim A B C w := by
  rw [would_eq, Finset.coe_union] at h
  exact mem_closestImp_or_of_mem_union htot h

/-! ### Homogeneity and exhaustification (§2, §3) -/

/-- On the homogeneity accounts, DCR is the existential resolution of the homogeneous
quantification over the disjuncts: the DAC is not false. SDA is its universal resolution,
`distributive_iff_homogeneity_eq_true`. -/
theorem dcr_iff_homogeneity_ne_false [DecidablePred (· ∈ C)] :
    DCR sim A B C w ↔ homogeneity sim [A, B] C w ≠ .false := by
  rw [Ne, homogeneity_eq_false_iff, DCR]
  constructor
  · rintro h ⟨-, hall⟩
    exact h.elim (hall A (by simp)) (hall B (by simp))
  · intro h
    by_contra hn
    rw [not_or] at hn
    refine h ⟨by simp, fun S hS ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl
    exacts [hn.1, hn.2]

open BarLevFox2020 in
omit [Fintype W] in
/-- The literal meaning of the DAC on the exhaustification account is Lewis's. -/
theorem literal_eq_would : closestImp sim (↑A ∪ ↑B) C = {v | would sim [A, B] C v} := by
  ext v
  rw [Set.mem_ofPred_eq, would_eq, Finset.coe_union]

omit [DecidableEq W] [Fintype W] in
open BarLevFox2020 in
/-- Exhaustification with innocent inclusion strengthens the literal DAC to SDA, under the
model conditions of [bar-lev-fox-2020]'s derivation. -/
theorem distributive_of_exh
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁)
    (h₁ : ∃ v ∈ closestImp sim (↑A ∪ ↑B) C,
      v ∉ closestImp sim ↑B C ∪ closestImp sim (↑A ∩ ↑B) C)
    (h₂ : ∃ v ∈ closestImp sim (↑A ∪ ↑B) C,
      v ∉ closestImp sim ↑A C ∪ closestImp sim (↑A ∩ ↑B) C)
    (h : ∃ v ∈ closestImp sim ↑A C ∩ closestImp sim ↑B C, v ∉ closestImp sim (↑A ∩ ↑B) C)
    (hw : w ∈ Exhaustification.exhIEII (sdaAlts sim ↑A ↑B C) (closestImp sim (↑A ∪ ↑B) C)) :
    Distributive sim [A, B] C w := by
  rw [sda htot h₁ h₂ h] at hw
  intro S hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl
  exacts [hw.1.1, hw.1.2]

/-! ### The closeness evaluation item (§4) -/

/-- Accepting *if not H, S* reveals that `S` is more realistic than any `T` disjoint from `S`
within the `H`-free worlds: every closest `H`-free world is an `S`-world, and a closest
`T`-world as close as a closest `S`-world would be one of them. -/
theorem moreRealistic_of_closeness
    (htot : ∀ w₀ w₁ w₂, sim.closer w₀ w₁ w₂ ∨ sim.closer w₀ w₂ w₁) {H S T : Finset W}
    (hclose : w ∈ closestImp sim (↑H)ᶜ ↑S) (hS : S.Nonempty)
    (hT : ∀ t ∈ T, t ∉ H) (hST : ∀ t ∈ T, t ∉ S) : MoreRealistic sim S T w := by
  rw [mem_closestImp_iff_closestWorlds] at hclose
  refine ⟨sim.closestWorlds_nonempty w hS, fun a ha b hb ↦ ?_⟩
  have hbN : b ∈ Finset.univ.filter (· ∈ (↑H : Set W)ᶜ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff, Finset.mem_coe]
    exact hT b (sim.closestWorlds_subset w T hb)
  obtain ⟨m, hm, hmb⟩ := exists_closest_closer htot hbN
  have hmS : m ∈ S := hclose m hm
  have ham : sim.closer w a m := by
    rw [SimilarityOrdering.mem_closestWorlds] at ha
    exact (ha.2 m hmS).elim id fun hn ↦ (htot w a m).resolve_right hn
  refine ⟨sim.closer_trans w a m b ham hmb, fun hba ↦ ?_⟩
  have hbm : sim.closer w b m := sim.closer_trans w b a m hba ham
  have hbN' : b ∈ sim.closestWorlds w (Finset.univ.filter (· ∈ (↑H : Set W)ᶜ)) := by
    rw [SimilarityOrdering.mem_closestWorlds] at hm ⊢
    refine ⟨hbN, fun u hu ↦ (hm.2 u hu).imp (sim.closer_trans w b m u hbm) ?_⟩
    exact fun hum hub ↦ hum (sim.closer_trans w u b m hub hbm)
  exact hST b (sim.closestWorlds_subset w T hb) (hclose b hbN')

/-! ### The race scenario and Table 3 -/

/-- The competitors of a scenario, in order of speed. -/
inductive Competitor
  | hare | squirrel | tortoise
  deriving DecidableEq, Fintype, Repr

/-- The prizes; each competitor's prize is fixed by the scenario. -/
inductive Prize
  | carrot | hazelnut | lettuce
  deriving DecidableEq, Repr

/-- Each competitor's prize. -/
def Competitor.prize : Competitor → Prize
  | .hare => .carrot
  | .squirrel => .hazelnut
  | .tortoise => .lettuce

/-- Speed rank, the hare fastest. -/
def Competitor.speed : Competitor → ℕ
  | .hare => 0
  | .squirrel => 1
  | .tortoise => 2

/-- Figure 3(a), the non-equally realistic condition: a faster competitor is a more realistic
winner. -/
def nonEqual : SimilarityOrdering Competitor := .ofRank fun _ v ↦ v.speed

/-- Figure 3(b), the equally realistic condition: the squirrel and the tortoise tie. -/
def equal : SimilarityOrdering Competitor := .ofRank fun _ v ↦ min v.speed 1

theorem nonEqual_total (w₀ w₁ w₂ : Competitor) :
    nonEqual.closer w₀ w₁ w₂ ∨ nonEqual.closer w₀ w₂ w₁ :=
  le_total _ _

/-- A target item (9): *if `first` or `second` wins, it will get `prize`*. -/
structure Item where
  first : Competitor
  second : Competitor
  prize : Prize

/-- The four target items (9a)–(9d). -/
def items : List Item :=
  [⟨.squirrel, .tortoise, .hazelnut⟩, ⟨.tortoise, .squirrel, .hazelnut⟩,
    ⟨.squirrel, .tortoise, .lettuce⟩, ⟨.tortoise, .squirrel, .lettuce⟩]

/-- The SDA verdict on an item in the actual world, where the hare won. -/
def Item.sda (it : Item) : Prop :=
  Distributive nonEqual [{it.first}, {it.second}] {v | v.prize = it.prize} .hare

/-- The DCR verdict on an item. -/
def Item.dcr (it : Item) : Prop :=
  DCR nonEqual {it.first} {it.second} {v | v.prize = it.prize} .hare

/-- Lewis's verdict on an item in the non-equally realistic condition: the asymmetric
reading. -/
def Item.ar (it : Item) : Prop :=
  would nonEqual [{it.first}, {it.second}] {v | v.prize = it.prize} .hare

instance (it : Item) : Decidable it.sda := inferInstanceAs (Decidable (Distributive _ _ _ _))
instance (it : Item) : Decidable it.dcr := inferInstanceAs (Decidable (_ ∨ _))
instance (it : Item) : Decidable it.ar := inferInstanceAs (Decidable (would _ _ _ _))

/-- Table 3, SDA: every target item is false, since one simplification always fails. -/
theorem table3_sda : items.map (fun it ↦ decide it.sda) = [false, false, false, false] := by
  decide

/-- Table 3, DCR: every target item is true, since one simplification always holds. -/
theorem table3_dcr : items.map (fun it ↦ decide it.dcr) = [true, true, true, true] := by
  decide

/-- Table 3, AR: the items naming the squirrel's prize are true and the others false. -/
theorem table3_ar : items.map (fun it ↦ decide it.ar) = [true, true, false, false] := by
  decide

/-- In the equally realistic condition, Lewis's verdicts coincide with SDA on every item. -/
theorem table3_equal :
    items.map (fun it ↦ decide (would equal [{it.first}, {it.second}]
      {v | v.prize = it.prize} .hare)) = [false, false, false, false] := by
  decide

/-- The closeness evaluation item *if the hare doesn't win, the squirrel will win* holds in
the non-equally realistic condition and fails in the equally realistic one. -/
theorem closeness_item :
    .hare ∈ closestImp nonEqual {.hare}ᶜ {.squirrel} ∧
      .hare ∉ closestImp equal {.hare}ᶜ {.squirrel} := by
  decide

/-- Accepting the closeness evaluation item makes the squirrel the more realistic winner,
which is what licenses the asymmetric pattern of Table 3. -/
theorem squirrel_moreRealistic : MoreRealistic nonEqual {.squirrel} {.tortoise} .hare :=
  moreRealistic_of_closeness nonEqual_total (H := {.hare})
    (by simpa using closeness_item.1) ⟨.squirrel, by simp⟩ (by decide) (by decide)

end ZaniCiardelliSanfelici2026
