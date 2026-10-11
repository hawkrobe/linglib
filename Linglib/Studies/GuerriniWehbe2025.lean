module

public import Linglib.Studies.BarLev2021
public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Data.Examples.GuerriniWehbe2025

/-!
# Guerrini and Wehbe (2025): Homogeneity as presuppositional exhaustification

Guerrini and Wehbe derive homogeneity by presuppositional exhaustification. A plural definite
contributes Bar-Lev's existential pluralization, and the operator `pex` of Del Pinal, Bassi and
Sauerland asserts it while presupposing that its subdomain alternatives are all true or all false.
Accommodating the presupposition yields the universal reading as long as no alternative for a
single atom is pruned (`holds_iff_forall`), and pruning those yields non-maximal readings, at
least two of three students for the pairs of (21) (`holds_pairs_iff`). Under negation the presupposition projects and the negated existential
already entails it, so pruning has no effect (`neg_holds_iff`). Non-maximality under negation
needs local accommodation below negation and a second `pex` over the negated universal, which is
the positive case for the negated predicate (`localAccommodation_nonMaximal`).

Homogeneity is thus a presupposition, which a constraint on accommodation detects: a sentence is
felicitous only if its assertion is informative once its presupposition is accommodated
(`Informative`, the paper's (8)). *She read the books* is infelicitous where Mary is known to have
read some of them, *the candidates lost* where at most one candidate can win, and their negations
where the universal is known to fail, while the quantified counterparts are fine
(`judgments_10`, `judgments_13`).

## Implementation notes

A plurality is the domain of Bar-Lev's existential pluralization, the disjunction of its atoms,
and the alternatives are his subdomain alternatives, the sub-disjunctions, all of which are
innocently includable (`Exhaustification.II_eq_self_of_subDisjs`).
The common ground is a set of worlds and accommodation intersects it with the presupposition.
The higher `pex` of (24) and (27) does not change the truth conditions of a negated plural and
is not modelled.

## TODO

* The comparison with Križ and Chemla's gap judgments (§5.1) and with Paillé (§5.2).
* Projection from non-monotonic quantifiers, free choice and the modal cases of §6.

## References

* [guerrini-wehbe-2025]
* [bar-lev-2021]
* [delpinal-bassi-sauerland-2024]
* [bar-lev-fox-2020]
* [crnic-chemla-fox-2015]
-/

@[expose] public section

namespace GuerriniWehbe2025

open Exhaustification Presupposition Homogeneity BarLev2021

/-! ### Presuppositional exhaustification of plural predication (§4) -/

section Plural

variable {Atom W : Type*} [DecidableEq Atom] {D x : Finset Atom} {P : Atom → W → Prop}
  {R : Set (Set W)} {w : W}

variable (D x P) in
/-- A plural predication under `pex`, (19), asserts Bar-Lev's existential pluralization and
presupposes that its relevant subdomain alternatives are homogeneous. -/
abbrev pexPlural (R : Set (Set W)) : PartialProp W :=
  pexIEII (subDisjs (x ∩ D) (atom P)) (disj (x ∩ D) (atom P)) R

/-- The presupposition (19b) is that the relevant subdomain alternatives are all true or all
false. -/
theorem presup_iff (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    (pexPlural D x P R).presup w ↔
      Homogeneous (subDisjs (x ∩ D) (atom P) \ {disj (x ∩ D) (atom P)} ∩ R) w := by
  simp only [pexIEII,
    II_eq_self_of_subDisjs (p := atom P) le_rfl hsplit_subDisjs h.single hne h.all]
  exact and_iff_right fun ψ hψ ↦
    absurd hψ (not_isInnocentlyExcludable_of_subDisjs le_rfl hsplit_subDisjs h.single ψ)

/-- In (20), after accommodation, a plural predication is universal as long as no alternative for
a single atom is pruned. -/
theorem holds_iff_forall (h : Separating D x P) (hcard : 1 < (x ∩ D).card)
    (hR : ∀ a ∈ x ∩ D, atom P a ∈ R) :
    (pexPlural D x P R).holds w ↔ ∀ a ∈ x, a ∈ D → P a w := by
  have hne : (x ∩ D).Nonempty := Finset.card_pos.1 (by omega)
  have hsing : ∀ a ∈ x ∩ D,
      atom P a ∈ subDisjs (x ∩ D) (atom P) \ {disj (x ∩ D) (atom P)} ∩ R := by
    intro a ha
    refine ⟨⟨mem_subDisjs_of_mem ha, fun heq ↦ ?_⟩, hR a ha⟩
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
    obtain ⟨wb, hwb⟩ := h.single b hb
    have hin : wb ∈ disj (x ∩ D) (atom P) := mem_subDisj.2 ⟨b, hb, (hwb b hb).2 rfl⟩
    rw [← Set.mem_singleton_iff.1 heq] at hin
    exact hba ((hwb a ha).1 hin).symm
  rw [PartialProp.holds, presup_iff h hne]
  constructor
  · rintro ⟨hhom | hhom, hw⟩
    · exact fun b hbx hbD ↦ hhom _ (hsing b (Finset.mem_inter.2 ⟨hbx, hbD⟩))
    · obtain ⟨a, ha, hPa⟩ := mem_subDisj.1 hw
      exact absurd hPa (hhom _ (hsing a ha))
  · intro hall
    have hall' (a) (ha : a ∈ x ∩ D) : P a w :=
      hall a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2
    refine ⟨.inl ?_, ?_⟩
    · rintro _ ⟨⟨⟨S, hS, ⟨c, hc⟩, rfl⟩, -⟩, -⟩
      exact mem_subDisj.2 ⟨c, hc, hall' c (hS hc)⟩
    · obtain ⟨a, ha⟩ := hne
      exact mem_subDisj.2 ⟨a, ha, hall' a ha⟩

/-- In (25) and (28), a negated plural predication is true exactly where no atom satisfies the
predicate, however the alternatives are pruned. -/
theorem neg_holds_iff : (pexPlural D x P R).neg.holds w ↔ ∀ a ∈ x, a ∈ D → ¬ P a w := by
  have hout (hnone : ∀ a ∈ x, a ∈ D → ¬ P a w) : ∀ q ∈ subDisjs (x ∩ D) (atom P), w ∉ q := by
    rintro _ ⟨S, hS, -, rfl⟩ hw
    obtain ⟨c, hc, hPc⟩ := mem_subDisj.1 hw
    exact hnone c (Finset.mem_inter.1 (hS hc)).1 (Finset.mem_inter.1 (hS hc)).2 hPc
  refine ⟨fun ⟨_, hna⟩ a hax haD hPa ↦ hna (mem_subDisj.2 ⟨a, Finset.mem_inter.2 ⟨hax, haD⟩, hPa⟩),
    fun hnone ↦ ⟨⟨fun ψ hψ _ ↦ hout hnone ψ hψ.1, .inr fun α hα ↦ hout hnone α hα.1.1.1⟩,
      fun hw ↦ ?_⟩⟩
  obtain ⟨a, ha, hPa⟩ := mem_subDisj.1 hw
  exact hnone a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2 hPa

end Plural

/-! ### Post-Accommodation Informativity (§3) -/

section Informativity

variable {W : Type*}

/-- A sentence is informative in the common ground `c` after accommodation, Post-Accommodation
Informativity (8), when it is false at some world of `c` where its presupposition holds. -/
def Informative (c : Set W) (S : PartialProp W) : Prop := ∃ w ∈ c, S.presup w ∧ ¬ S.assertion w

theorem Informative.mono {c c' : Set W} {S : PartialProp W} (h : Informative c S)
    (hcc' : c ⊆ c') : Informative c' S :=
  let ⟨w, hw, hS⟩ := h
  ⟨w, hcc' hw, hS⟩

variable {Atom : Type*} [DecidableEq Atom] {D x : Finset Atom} {P : Atom → W → Prop}
  {R : Set (Set W)}

/-- Where the existential is common ground, a plural predication asserts nothing new, (10a) and
(13d). -/
theorem not_informative_pexPlural : ¬ Informative (disj (x ∩ D) (atom P)) (pexPlural D x P R) :=
  fun ⟨_, hw, _, hna⟩ ↦ hna hw

/-- Where the universal is known to fail, the negated plural predication asserts nothing new once
homogeneity is accommodated, (10b), (12b), (13c) and (23). -/
theorem not_informative_neg (h : Separating D x P) (hcard : 1 < (x ∩ D).card)
    (hR : ∀ a ∈ x ∩ D, atom P a ∈ R) :
    ¬ Informative {w | ¬ ∀ a ∈ x, a ∈ D → P a w} (pexPlural D x P R).neg :=
  fun ⟨_, hw, hpre, hna⟩ ↦ hw ((holds_iff_forall h hcard hR).1 ⟨hpre, not_not.1 hna⟩)

end Informativity

/-! ### Three students (§4, §5)

Worlds record who smiled, and `holds a w` says that `a` smiled at `w`. -/

section Students

open Finset in
private theorem mem_pairs {α : Set (Finset (Fin 3))} :
    α ∈ subDisjs (univ ∩ univ) (atom holds) \ {disj (univ ∩ univ) (atom holds)} ∩
        subDisjsOfCard univ (atom holds) 2 ↔
      ∃ S : Finset (Fin 3), S.card = 2 ∧ α = subDisj (atom holds) S := by
  constructor
  · rintro ⟨⟨-, hne⟩, rfl | ⟨S, -, hcard, rfl⟩⟩
    · exact absurd (Set.mem_singleton _) hne
    · exact ⟨S, hcard, rfl⟩
  · rintro ⟨S, hcard, rfl⟩
    refine ⟨⟨⟨S, by simp, card_pos.1 (by omega), rfl⟩, fun heq ↦ ?_⟩,
      .inr ⟨S, subset_univ _, hcard, rfl⟩⟩
    obtain ⟨k, hk⟩ : ∃ k, k ∉ S := by
      by_contra! h
      have := card_le_card (fun a _ ↦ h a : (univ : Finset (Fin 3)) ⊆ S)
      simp [hcard] at this
    have hin : ({k} : Finset (Fin 3)) ∈ disj (univ ∩ univ) (atom holds) :=
      mem_subDisj.2 ⟨k, by simp, mem_singleton_self k⟩
    rw [← Set.mem_singleton_iff.1 heq] at hin
    obtain ⟨a, haS, ha⟩ := mem_subDisj.1 hin
    exact hk (mem_singleton.1 ha ▸ haS)

/-- In (21), pruning to the alternatives over pairs of the three students makes *the students
smiled* true after accommodation where at least two of them smiled. -/
theorem holds_pairs_iff (w : Finset (Fin 3)) :
    (pexPlural Finset.univ Finset.univ holds (subDisjsOfCard Finset.univ (atom holds) 2)).holds w ↔
      2 ≤ w.card := by
  rw [PartialProp.holds, presup_iff (separating_holds _ _) ⟨0, by simp⟩, Homogeneous]
  simp only [mem_pairs, forall_exists_index, and_imp]
  have key : ((∀ S : Finset (Fin 3), S.card = 2 → w ∈ subDisj (atom holds) S) ∨
      ∀ S : Finset (Fin 3), S.card = 2 → w ∉ subDisj (atom holds) S) ∧
      w ∈ disj (Finset.univ ∩ Finset.univ) (atom holds) ↔ 2 ≤ w.card := by
    simp only [mem_subDisj, atom, Set.mem_ofPred_eq]
    revert w; decide
  rw [← key]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    exacts [⟨.inl fun S hS ↦ h1 _ S hS rfl, h2⟩, ⟨.inr fun S hS ↦ h1 _ S hS rfl, h2⟩]
  · rintro ⟨h1 | h1, h2⟩
    exacts [⟨.inl fun _ S hS h ↦ h ▸ h1 S hS, h2⟩, ⟨.inr fun _ S hS h ↦ h ▸ h1 S hS, h2⟩]

/-- Student `a` did not smile at `w`. -/
abbrev notSmiled (a : Fin 3) (w : Finset (Fin 3)) : Prop := a ∉ w

private theorem separating_not : Separating Finset.univ Finset.univ notSmiled :=
  ⟨by decide, by decide⟩

/-- In (31), with homogeneity accommodated below negation and no pruning, *the students didn't
smile* is true where none of them smiled. -/
theorem localAccommodation_holds_iff (w : Finset (Fin 3)) :
    (pexPlural Finset.univ Finset.univ notSmiled (subDisjs Finset.univ (atom notSmiled))).holds w ↔
      w = ∅ := by
  rw [holds_iff_forall separating_not (by decide) fun a _ ↦
    mem_subDisjs_of_mem (Finset.mem_univ a), Finset.eq_empty_iff_forall_notMem]
  simp

/-- In (32)–(34), pruning the alternative for the third student makes *the students didn't smile*
true when only that student smiled, a non-maximal reading under negation. -/
theorem localAccommodation_nonMaximal :
    (pexPlural Finset.univ Finset.univ notSmiled
      (subDisjs Finset.univ (atom notSmiled) \ {atom notSmiled 2})).holds {2} := by
  rw [PartialProp.holds, presup_iff separating_not ⟨0, by simp⟩]
  refine ⟨.inl ?_, mem_subDisj.2 ⟨0, by simp, by decide⟩⟩
  rintro _ ⟨-, ⟨S, -, ⟨c, hc⟩, rfl⟩, hne⟩
  by_contra hout
  refine hne (Set.mem_singleton_iff.2 ((congrArg (subDisj _) ?_).trans (subDisj_singleton 2)))
  ext a
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · by_contra h2
    exact hout (mem_subDisj.2 ⟨a, ha, by simpa [atom, notSmiled] using h2⟩)
  · rw [Finset.mem_singleton.1 ha]
    by_contra h2
    have hc2 : c ≠ 2 := fun h ↦ h2 (h ▸ hc)
    exact hout (mem_subDisj.2 ⟨c, hc, by simpa [atom, notSmiled] using hc2⟩)

end Students

/-! ### The judgments of §3

Each sentence is judged against the common ground its context sets up. Worlds record which books
Mary read, which teammates John is married to, which candidates won, or which students smiled. -/

section Judgments

open Finset

/-- In (9), with John's kids known to be adopted, *all 10 of John's kids are adopted* asserts
nothing once its presupposition that he has 10 kids is accommodated, while *John has 10 adopted
kids* is informative. A world records how many kids John has and whether they are all adopted. -/
theorem judgments_9 :
    (Examples.ex_9a.judgment = .acceptable ↔ Informative {w : ℕ × Bool | w.2 = true}
      { presup := fun w ↦ w.1 = 10, assertion := fun w ↦ w.2 = true }) ∧
    (Examples.ex_9b.judgment = .acceptable ↔ Informative {w : ℕ × Bool | w.2 = true}
      (.ofProp fun w ↦ w.1 = 10 ∧ w.2 = true)) :=
  ⟨iff_of_false (by decide) fun ⟨_, hw, _, hna⟩ ↦ hna hw,
    iff_of_true (by decide) ⟨(3, true), rfl, trivial, by simp⟩⟩

private theorem subset_not_forall {n : ℕ} :
    {w : Finset (Fin n) | w ≠ univ} ⊆ {w | ¬ ∀ a ∈ univ, a ∈ univ → holds a w} :=
  fun _ hw hall ↦ hw (eq_univ_of_forall fun a ↦ hall a (mem_univ a) (mem_univ a))

/-- In (10), with Mary known to have read some of the books, *she read the books* asserts nothing
new, and with her known not to have read all of them, neither does *she didn't read the books*. -/
theorem judgments_10 :
    (Examples.ex_10a.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w.Nonempty}
      (pexPlural univ univ holds (subDisjs univ (atom holds)))) ∧
    (Examples.ex_10b.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w ≠ univ}
      (pexPlural univ univ holds (subDisjs univ (atom holds))).neg) :=
  ⟨iff_of_false (by decide) fun h ↦ not_informative_pexPlural
      (h.mono fun _ ⟨a, ha⟩ ↦ mem_subDisj.2 ⟨a, by simp, ha⟩),
    iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
      (fun a _ ↦ mem_subDisjs_of_mem (mem_univ a)) (h.mono subset_not_forall)⟩

/-- In (12), since John is not married to all of his teammates, *John isn't married to any of his
teammates* is informative, but *John isn't married to his teammates* asserts nothing new once
homogeneity is accommodated. -/
theorem judgments_12 :
    (Examples.ex_12a.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w ≠ univ}
      (.ofProp fun w ↦ w = ∅)) ∧
    (Examples.ex_12b.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w ≠ univ}
      (pexPlural univ univ holds (subDisjs univ (atom holds))).neg) :=
  ⟨iff_of_true (by decide) ⟨{0}, by decide, trivial, by simp⟩,
    iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
      (fun a _ ↦ mem_subDisjs_of_mem (mem_univ a)) (h.mono subset_not_forall)⟩

/-- In (13), where at most one candidate can win, *none of the candidates won* and *all of the
candidates lost* are informative, but *the candidates didn't win* and *the candidates lost*
assert nothing new once homogeneity is accommodated. -/
theorem judgments_13 :
    (Examples.ex_13a.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w.card ≤ 1}
      (.ofProp fun w ↦ w = ∅)) ∧
    (Examples.ex_13b.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w.card ≤ 1}
      (.ofProp fun w ↦ ∀ a, a ∉ w)) ∧
    (Examples.ex_13c.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w.card ≤ 1}
      (pexPlural univ univ holds (subDisjs univ (atom holds))).neg) ∧
    (Examples.ex_13d.judgment = .acceptable ↔ Informative {w : Finset (Fin 2) | w.card ≤ 1}
      (pexPlural univ univ (fun (a : Fin 2) (w : Finset (Fin 2)) ↦ a ∉ w)
        (subDisjs univ (atom fun a w ↦ a ∉ w)))) :=
  ⟨iff_of_true (by decide) ⟨{0}, by decide, trivial, by simp⟩,
    iff_of_true (by decide) ⟨{0}, by decide, trivial, by simp⟩,
    iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
      (fun a _ ↦ mem_subDisjs_of_mem (mem_univ a))
      (h.mono fun w hw hall ↦ by
        rw [eq_univ_of_forall fun a ↦ hall a (mem_univ a) (mem_univ a)] at hw
        exact absurd hw (by decide)),
    iff_of_false (by decide) fun h ↦ not_informative_pexPlural (h.mono fun w hw ↦ by
      obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card (s := w) (t := univ)
        (by simpa using hw.trans_lt (by decide))
      exact mem_subDisj.2 ⟨a, by simp, ha⟩)⟩

/-- In (23), with the students known not to have all smiled, *the students didn't smile* asserts
nothing new once homogeneity is accommodated. -/
theorem judgments_23 :
    Examples.ex_23.judgment = .acceptable ↔ Informative {w : Finset (Fin 3) | w ≠ univ}
      (pexPlural univ univ holds (subDisjs univ (atom holds))).neg :=
  iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
    (fun a _ ↦ mem_subDisjs_of_mem (mem_univ a)) (h.mono subset_not_forall)

end Judgments

end GuerriniWehbe2025
