import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Logic.Modal.Defs
import Linglib.Data.Examples.Fox2007
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.CompleteLattice.Finset

/-!
# Fox (2007): Free Choice and the Theory of Scalar Implicatures

This file formalizes [fox-2007]'s derivation of free-choice inferences by recursive
exhaustification. The exhaustivity operator denies the innocently excludable alternatives
(`Exhaustification.exhIE`); a second layer, `exh₂`, exhaustifies the result against the
exhaustified alternatives. The Appendix theorem `exh₂_eq_anEx` identifies the second layer
with the anti-exhaustivity reading `anEx` whenever that reading is consistent, and the theorem
of the paper's note on the diamond configuration, `IsDiamond.exh₂_eq` and
`IsDiamond.exh₂_vacuous_iff`, derives free choice for any four alternatives `w = s ∪ n ⊇ e`
exactly when `e` is stronger than `s ∩ n`. Disjunction under a possibility modal, under an
existential quantifier, and conjunction under a negated necessity modal instantiate the diamond
with `e` strictly stronger; unembedded disjunction has `e = s ∩ n`, so its second
exhaustification is vacuous. `exhIE_hamblin` is the paper's `some GIRL` computation: against
Hamblin alternatives, innocent exclusion yields *exactly one*.

## Implementation notes

Propositions are sets of worlds and alternative sets are `Set (Set W)`, so the theorems hold
over any model; the paper's four-member Sauerland sets are the literal `{w, s, n, e}`. The
negated-necessity instance uses the four alternatives of the necessity modal alone; the paper
notes that adding the possibility variants does not change the result. The Zimmermann sentence,
which the paper leaves unresolved, is a row with the `open` status and is outside the row
theorem. Example and note numbers follow the manuscript version of the paper.

## References

* [fox-2007]
* [sauerland-2004]
* [kratzer-shimoyama-2002]
* [simons-2005]
* [zimmermann-2000]
-/

namespace Fox2007

open Exhaustification Set ModalLogic Data.Examples

variable {W : Type*}

/-! ### Recursive exhaustification -/

section Recursive

variable (C : Set (Set W)) (p : Set W)

/-- The second layer of exhaustification: the exhaustified prejacent against the exhaustified
alternatives `{Exh(C)(q) : q ∈ C}`. -/
def exh₂ : Set W := exhIE (exhIE C '' C) (exhIE C p)

/-- The anti-exhaustivity reading of the Appendix: the exhaustified prejacent with the
exhaustification of every other alternative that is not innocently excludable denied. -/
def anEx : Set W :=
  exhIE C p ∩ ⋂ q ∈ (C \ {q | IsInnocentlyExcludable C p q}) \ {p}, (exhIE C q)ᶜ

/-- Exhaustifying the prejacent denies the exhaustification of an innocently excludable
alternative. -/
theorem exhIE_subset_compl_exhIE {q : Set W} (hq : IsInnocentlyExcludable C p q) :
    exhIE C p ⊆ (exhIE C q)ᶜ :=
  λ _ hu hq' => hu qᶜ hq.2 (hq' q (self_mem_IE C q))

/-- The anti-exhaustivity reading denies the exhaustification of every other alternative. -/
theorem anEx_eq : anEx C p = exhIE C p ∩ ⋂ q ∈ C \ {p}, (exhIE C q)ᶜ := by
  ext u
  simp only [anEx, mem_inter_iff, mem_iInter₂, mem_sdiff, mem_singleton_iff, mem_ofPred_eq,
    mem_compl_iff]
  refine and_congr_right λ hu => ⟨λ h q hq => ?_, λ h q hq => h q ⟨hq.1.1, hq.2⟩⟩
  by_cases hIE : IsInnocentlyExcludable C p q
  · exact exhIE_subset_compl_exhIE C p hIE hu
  · exact h q ⟨⟨hq.1, hIE⟩, hq.2⟩

/-- The anti-exhaustivity reading for alternatives listed apart from the prejacent. -/
theorem anEx_insert {C₀ : Set (Set W)} (hp : p ∉ C₀) :
    anEx (insert p C₀) p = exhIE (insert p C₀) p ∩ ⋂ q ∈ C₀, (exhIE (insert p C₀) q)ᶜ := by
  rw [anEx_eq]
  congr 1
  ext u
  simp only [mem_iInter₂, mem_sdiff, mem_insert_iff, mem_singleton_iff]
  exact ⟨λ h q hq => h q ⟨Or.inr hq, λ hqp => hp (hqp ▸ hq)⟩,
    λ h q hq => h q (hq.1.resolve_left hq.2)⟩

/-- The Appendix theorem: a consistent anti-exhaustivity reading is the second layer. -/
theorem exh₂_eq_anEx (hfin : C.Finite) (hp : p ∈ C) (h : (anEx C p).Nonempty) :
    exh₂ C p = anEx C p := by
  rw [anEx_eq] at h ⊢
  obtain ⟨w, hw, hw'⟩ := h
  have hw'' := mem_iInter₂.1 hw'
  have hfin' : (exhIE C '' C).Finite := hfin.image _
  ext u
  rw [exh₂, mem_exhIE_iff _ _ hfin', mem_inter_iff, mem_iInter₂]
  refine and_congr_right λ hu => ⟨λ h q hq => h _ ?_, λ h b hb => ?_⟩
  · refine .of_forall_subset_or_notMem (mem_image_of_mem _ hq.1) hw (hw'' q hq) ?_
    rintro _ ⟨q', hq', rfl⟩
    by_cases hqp : q' = p
    · exact Or.inl (hqp ▸ subset_rfl)
    · exact Or.inr (hw'' q' ⟨hq', hqp⟩)
  · obtain ⟨q, hq, rfl⟩ := hb.1
    by_cases hqp : q = p
    · subst hqp
      exact (not_isInnocentlyExcludable_of_phi_subset hfin' ⟨u, hu⟩ subset_rfl hb).elim
    · exact h q ⟨hq, hqp⟩

end Recursive

/-! ### Disjunction and its disjuncts -/

/-- A disjunction against its disjuncts and one further alternative: only the further
alternative is innocently excludable, when each disjunct can hold without the other and
without it. -/
theorem exhIE_pair {A B D : Set W} (hA : ((A \ B) \ D).Nonempty)
    (hB : ((B \ A) \ D).Nonempty) : exhIE {A ∪ B, A, B, D} (A ∪ B) = (A ∪ B) \ D := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have notIE : ∀ {A B : Set W} {a : W}, a ∈ (A \ B) \ D →
      ¬ IsInnocentlyExcludable {A ∪ B, A, B, D} (A ∪ B) A := by
    intro A B a ha
    rw [isInnocentlyExcludable_iff_exhMW_subset_compl {A ∪ B, A, B, D} (A ∪ B) A (by simp)]
    refine λ h => h ⟨Or.inl ha.1.1, ?_⟩ ha.1.1
    rintro ⟨v, hv, hva, hnav⟩
    rcases hv with hvA | hvB
    · refine hnav λ c hc hac => ?_
      simp only [mem_insert_iff, mem_singleton_iff] at hc
      obtain h1 | h1 | h1 | h1 := hc <;> subst c
      · exact Or.inl hvA
      · exact hvA
      · exact (ha.1.2 hac).elim
      · exact (ha.2 hac).elim
    · exact ha.1.2 (hva B (by simp) hvB)
  have hD : IsInnocentlyExcludable {A ∪ B, A, B, D} (A ∪ B) D := by
    refine .of_extension_consistent (by simp) λ E hE => ?_
    obtain ⟨v, hv⟩ := hE.1.2.2
    have key : ∀ {A B : Set W} {b : W}, b ∈ (B \ A) \ D → Bᶜ ∉ E → A ∪ B ∈ E →
        (∀ ψ ∈ E, ψ = A ∪ B ∨ ∃ c ∈ ({A ∪ B, A, B, D} : Set (Set W)), ψ = cᶜ) →
        b ∈ ⋂₀ (E ∪ {Dᶜ}) := by
      intro A B b hb hBE hPE hE'
      rintro ψ (hψ | hψ)
      · rcases hE' ψ hψ with rfl | ⟨c, hc, rfl⟩
        · exact Or.inr hb.1.1
        · simp only [mem_insert_iff, mem_singleton_iff] at hc
          obtain h1 | h1 | h1 | h1 := hc <;> subst c
          · exact (hv _ hψ (hv _ hPE)).elim
          · exact hb.1.2
          · exact (hBE hψ).elim
          · exact hb.2
      · rw [mem_singleton_iff] at hψ
        exact hψ ▸ hb.2
    by_cases hBE : Bᶜ ∈ E
    · have hAE : Aᶜ ∉ E := λ hAE =>
        (hv _ hE.1.1).elim (hv _ hAE) (hv _ hBE)
      have hE' : ∀ ψ ∈ E, ψ = B ∪ A ∨ ∃ c ∈ ({B ∪ A, B, A, D} : Set (Set W)), ψ = cᶜ := by
        rw [union_comm B A, insert_comm B A]
        exact hE.1.2.1
      exact ⟨a, key ha hAE (union_comm B A ▸ hE.1.1) hE'⟩
    · exact ⟨b, key hb hBE hE.1.1 hE.1.2.1⟩
  ext u
  rw [mem_exhIE_iff _ _ (toFinite _), mem_sdiff]
  refine and_congr_right λ hu => ⟨λ h => h D hD, λ h c hc => ?_⟩
  have hc1 := hc.1
  simp only [mem_insert_iff, mem_singleton_iff] at hc1
  obtain h1 | h1 | h1 | h1 := hc1 <;> subst c
  · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨u, hu⟩ subset_rfl hc).elim
  · exact (notIE ha hc).elim
  · have := notIE hb
    rw [union_comm B A, insert_comm B A] at this
    exact (this hc).elim
  · exact h

/-- Exclusive *or*: the Sauerland alternatives of a disjunction exclude only the conjunction. -/
theorem exhIE_or {p q : Set W} (hp : (p \ q).Nonempty) (hq : (q \ p).Nonempty) :
    exhIE {p ∪ q, p, q, p ∩ q} (p ∪ q) = (p ∪ q) \ (p ∩ q) :=
  exhIE_pair ⟨hp.some, hp.some_mem, λ h => hp.some_mem.2 h.2⟩
    ⟨hq.some, hq.some_mem, λ h => hq.some_mem.2 h.1⟩

/-! ### The diamond -/

/-- Four alternatives in the diamond configuration of the paper's note on §8: `w` is the
disjunction of the logically independent `s` and `n`, and `e` is stronger than both. -/
structure IsDiamond (w s n e : Set W) : Prop where
  union : w = s ∪ n
  le_s : e ⊆ s
  le_n : e ⊆ n
  sn : (s \ n).Nonempty
  ns : (n \ s).Nonempty

namespace IsDiamond

variable {w s n e : Set W} (h : IsDiamond w s n e)
include h

theorem symm : IsDiamond w n s e :=
  ⟨h.union.trans (union_comm _ _), h.le_n, h.le_s, h.ns, h.sn⟩

theorem notMem : w ∉ ({s, n, e} : Set (Set W)) := by
  obtain ⟨rfl, hs, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  rintro (h1 | h1 | h1)
  · exact hb.2 (h1 ▸ (Or.inr hb.1 : b ∈ s ∪ n))
  · exact ha.2 (h1 ▸ (Or.inl ha.1 : a ∈ s ∪ n))
  · exact ha.2 (hn (h1 ▸ (Or.inl ha.1 : a ∈ s ∪ n)))

/-- Only the strongest alternative is innocently excludable given the weakest. -/
theorem exhIE_w : exhIE {w, s, n, e} w = w \ e := by
  obtain ⟨rfl, hs, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  exact exhIE_pair ⟨a, ha, λ hae => ha.2 (hn hae)⟩ ⟨b, hb, λ hbe => hb.2 (hs hbe)⟩

/-- Given an independent alternative, the other and the strongest are innocently
excludable. -/
theorem exhIE_s : exhIE {w, s, n, e} s = s \ n := by
  obtain ⟨rfl, hs, hn, ⟨a, ha⟩, -⟩ := h
  ext u
  rw [mem_exhIE_iff _ _ (toFinite _), mem_sdiff]
  refine and_congr_right λ hu => ⟨λ h' => h' n ?_, λ hun c hc => ?_⟩
  · refine .of_forall_subset_or_notMem (by simp) ha.1 ha.2 ?_
    intro c hc
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    obtain h1 | h1 | h1 | h1 := hc <;> subst c
    · exact Or.inl subset_union_left
    · exact Or.inl subset_rfl
    · exact Or.inr ha.2
    · exact Or.inr λ hae => ha.2 (hn hae)
  · have hc1 := hc.1
    simp only [mem_insert_iff, mem_singleton_iff] at hc1
    obtain h1 | h1 | h1 | h1 := hc1 <;> subst c
    · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨u, hu⟩ subset_union_left
        hc).elim
    · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨u, hu⟩ subset_rfl hc).elim
    · exact hun
    · exact λ hue => hun (hn hue)

theorem exhIE_n : exhIE {w, s, n, e} n = n \ s := by
  have := h.symm.exhIE_s
  rwa [insert_comm n s] at this

/-- Nothing is innocently excludable given the strongest alternative. -/
theorem exhIE_e : exhIE {w, s, n, e} e = e := by
  obtain ⟨rfl, hs, hn, -, -⟩ := h
  refine Subset.antisymm (λ u hu => hu e (self_mem_IE _ _)) λ u hu => ?_
  rw [mem_exhIE_iff _ _ (toFinite _)]
  refine ⟨hu, λ c hc => ?_⟩
  have hc1 := hc.1
  simp only [mem_insert_iff, mem_singleton_iff] at hc1
  refine (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨u, hu⟩ ?_ hc).elim
  obtain h1 | h1 | h1 | h1 := hc1 <;> subst c
  · exact hs.trans subset_union_left
  · exact hs
  · exact hn
  · exact subset_rfl

/-- The second-layer alternatives. -/
theorem image_exhIE : exhIE {w, s, n, e} '' {w, s, n, e} = {w \ e, s \ n, n \ s, e} := by
  rw [image_insert_eq, image_insert_eq, image_pair, h.exhIE_w, h.exhIE_s, h.exhIE_n, h.exhIE_e]

/-- The anti-exhaustivity reading of the weakest alternative asserts both independent
alternatives and denies the strongest. -/
theorem anEx_w : anEx {w, s, n, e} w = (s ∩ n) \ e := by
  rw [anEx_insert _ h.notMem, biInter_insert, biInter_insert, biInter_singleton, h.exhIE_w,
    h.exhIE_s, h.exhIE_n, h.exhIE_e, h.union]
  ext u
  simp only [mem_inter_iff, mem_sdiff, mem_compl_iff, mem_union]
  tauto

/-- Free choice: when the strongest alternative is stronger than the conjunction of the
independent ones, the second layer asserts both and denies the strongest. -/
theorem exh₂_eq (hne : ((s ∩ n) \ e).Nonempty) : exh₂ {w, s, n, e} w = (s ∩ n) \ e := by
  rw [exh₂_eq_anEx _ _ (toFinite _) (mem_insert _ _) (h.anEx_w ▸ hne), h.anEx_w]

/-- When the strongest alternative is the conjunction of the independent ones, as for
unembedded disjunction, the second layer is vacuous. -/
theorem exh₂_eq_of_eq_inter (he : e = s ∩ n) : exh₂ {w, s, n, e} w = exhIE {w, s, n, e} w := by
  rw [exh₂, h.image_exhIE, h.exhIE_w]
  obtain ⟨rfl, -, -, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  subst he
  have hsd : (s ∪ n) \ (s ∩ n) = (s \ n) ∪ (n \ s) := by
    ext u
    simp only [mem_sdiff, mem_union, mem_inter_iff]
    tauto
  rw [hsd, exhIE_pair ⟨a, ⟨ha, λ h' => ha.2 h'.1⟩, λ h' => ha.2 h'.2⟩
    ⟨b, ⟨hb, λ h' => hb.2 h'.1⟩, λ h' => hb.2 h'.1⟩]
  ext u
  simp only [mem_sdiff, mem_union, mem_inter_iff]
  tauto

/-- The second layer is vacuous exactly when the strongest alternative is the conjunction of
the independent ones. -/
theorem exh₂_vacuous_iff : exh₂ {w, s, n, e} w = exhIE {w, s, n, e} w ↔ e = s ∩ n := by
  refine ⟨λ hv => by_contra λ hne => ?_, h.exh₂_eq_of_eq_inter⟩
  have hne' : ((s ∩ n) \ e).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty]
    exact λ hle => hne (subset_antisymm (subset_inter h.le_s h.le_n) hle)
  rw [h.exh₂_eq hne', h.exhIE_w, h.union] at hv
  obtain ⟨a, ha⟩ := h.sn
  have : a ∈ (s ∪ n) \ e := ⟨Or.inl ha.1, λ hae => ha.2 (h.le_n hae)⟩
  rw [← hv] at this
  exact ha.2 this.1.2

end IsDiamond

/-! ### Instances of the diamond -/

/-- Unembedded disjunction: the second layer adds nothing to exclusive *or*. -/
theorem exh₂_or {p q : Set W} (hp : (p \ q).Nonempty) (hq : (q \ p).Nonempty) :
    exh₂ {p ∪ q, p, q, p ∩ q} (p ∪ q) = (p ∪ q) \ (p ∩ q) :=
  (IsDiamond.exh₂_eq_of_eq_inter ⟨rfl, inter_subset_left, inter_subset_right, hp, hq⟩ rfl).trans
    (exhIE_or hp hq)

/-- Possibility as a proposition: the worlds from which some accessible world satisfies `p`. -/
def poss (R : W → W → Prop) (p : W → Prop) : Set W := {w | ◇[R] p w}

/-- Necessity as a proposition: the worlds from which every accessible world satisfies `p`. -/
def nec (R : W → W → Prop) (p : W → Prop) : Set W := {w | □[R] p w}

section Modal

variable {R : W → W → Prop} (p q : W → Prop)

/-- The Sauerland alternatives of `◇(p ∨ q)` form a diamond whenever each disjunct can be
permitted without the other. -/
theorem isDiamond_diamond (hp : (poss R p \ poss R q).Nonempty) (hq : (poss R q \ poss R p).Nonempty) :
    IsDiamond (poss R (λ v => p v ∨ q v)) (poss R p) (poss R q) (poss R (λ v => p v ∧ q v)) where
  union := by
    ext w
    show (∃ v, R w v ∧ (p v ∨ q v)) ↔ (∃ v, R w v ∧ p v) ∨ ∃ v, R w v ∧ q v
    simp only [and_or_left, exists_or]
  le_s := by
    rintro w ⟨v, hv, hpv, -⟩
    exact ⟨v, hv, hpv⟩
  le_n := by
    rintro w ⟨v, hv, -, hqv⟩
    exact ⟨v, hv, hqv⟩
  sn := hp
  ns := hq

/-- Free choice permission: with a world where each disjunct is permitted but not both, the
doubly exhaustified `◇(p ∨ q)` asserts both permissions and denies the joint one. -/
theorem free_choice (hp : (poss R p \ poss R q).Nonempty) (hq : (poss R q \ poss R p).Nonempty)
    (h : ((poss R p ∩ poss R q) \ poss R (λ v => p v ∧ q v)).Nonempty) :
    exh₂ {poss R (λ v => p v ∨ q v), poss R p, poss R q, poss R (λ v => p v ∧ q v)} (poss R (λ v => p v ∨ q v))
      = (poss R p ∩ poss R q) \ poss R (λ v => p v ∧ q v) :=
  (isDiamond_diamond p q hp hq).exh₂_eq h

/-- The Sauerland alternatives of `¬□(p ∧ q)` form a diamond whenever each conjunct can be
required without the other. -/
theorem isDiamond_not_box (hp : ((nec R p)ᶜ \ (nec R q)ᶜ).Nonempty)
    (hq : ((nec R q)ᶜ \ (nec R p)ᶜ).Nonempty) :
    IsDiamond (nec R (λ v => p v ∧ q v))ᶜ (nec R p)ᶜ (nec R q)ᶜ (nec R (λ v => p v ∨ q v))ᶜ where
  union := by
    ext w
    show ¬ box R _ w ↔ ¬ box R p w ∨ ¬ box R q w
    rw [box_and]
    exact not_and_or
  le_s := by
    intro w h hp
    exact h λ v hv => Or.inl (hp v hv)
  le_n := by
    intro w h hq
    exact h λ v hv => Or.inr (hq v hv)
  sn := hp
  ns := hq

/-- Free choice under a negated necessity modal: the doubly exhaustified `¬□(p ∧ q)` asserts
that neither conjunct is required and that their disjunction is. -/
theorem free_choice_not_box (hp : ((nec R p)ᶜ \ (nec R q)ᶜ).Nonempty)
    (hq : ((nec R q)ᶜ \ (nec R p)ᶜ).Nonempty)
    (h : (((nec R p)ᶜ ∩ (nec R q)ᶜ) \ (nec R (λ v => p v ∨ q v))ᶜ).Nonempty) :
    exh₂ {(nec R (λ v => p v ∧ q v))ᶜ, (nec R p)ᶜ, (nec R q)ᶜ, (nec R (λ v => p v ∨ q v))ᶜ} (nec R (λ v => p v ∧ q v))ᶜ
      = ((nec R p)ᶜ ∩ (nec R q)ᶜ) \ (nec R (λ v => p v ∨ q v))ᶜ :=
  (isDiamond_not_box p q hp hq).exh₂_eq h

/-- Simons's reading: with each disjunct exhaustified first, the joint alternative is empty, so
free choice arrives without the anti-conjunctive inference. -/
theorem free_choice_exhaustified_disjuncts
    (hp : (poss R (λ v => p v ∧ ¬ q v) \ poss R (λ v => q v ∧ ¬ p v)).Nonempty)
    (hq : (poss R (λ v => q v ∧ ¬ p v) \ poss R (λ v => p v ∧ ¬ q v)).Nonempty)
    (h : (poss R (λ v => p v ∧ ¬ q v) ∩ poss R (λ v => q v ∧ ¬ p v)).Nonempty) :
    exh₂ {poss R (λ v => (p v ∧ ¬ q v) ∨ (q v ∧ ¬ p v)), poss R (λ v => p v ∧ ¬ q v),
        poss R (λ v => q v ∧ ¬ p v), poss R (λ v => (p v ∧ ¬ q v) ∧ (q v ∧ ¬ p v))}
        (poss R (λ v => (p v ∧ ¬ q v) ∨ (q v ∧ ¬ p v)))
      = poss R (λ v => p v ∧ ¬ q v) ∩ poss R (λ v => q v ∧ ¬ p v) := by
  have he : poss R (λ v => (p v ∧ ¬ q v) ∧ (q v ∧ ¬ p v)) = (∅ : Set W) :=
    eq_empty_of_forall_notMem (by rintro w ⟨_, _, ⟨hpv, _⟩, _, hnp⟩; exact hnp hpv)
  rw [free_choice _ _ hp hq (by rw [he, sdiff_empty]; exact h), he, sdiff_empty]

end Modal

section Existential

variable {ι : Type*} (P Q : ι → Set W)

/-- The Sauerland alternatives of `∃x (P x ∨ Q x)` form a diamond whenever each disjunct can be
witnessed without the other. -/
theorem isDiamond_iUnion (hp : ((⋃ x, P x) \ ⋃ x, Q x).Nonempty)
    (hq : ((⋃ x, Q x) \ ⋃ x, P x).Nonempty) :
    IsDiamond (⋃ x, P x ∪ Q x) (⋃ x, P x) (⋃ x, Q x) (⋃ x, P x ∩ Q x) where
  union := iUnion_union_distrib P Q
  le_s := iUnion_mono λ _ => inter_subset_left
  le_n := iUnion_mono λ _ => inter_subset_right
  sn := hp
  ns := hq

/-- Existential free choice: with a witness for each disjunct but none for both, the doubly
exhaustified `∃x (P x ∨ Q x)` asserts witnesses for each and denies a joint one. -/
theorem free_choice_iUnion (hp : ((⋃ x, P x) \ ⋃ x, Q x).Nonempty)
    (hq : ((⋃ x, Q x) \ ⋃ x, P x).Nonempty)
    (h : (((⋃ x, P x) ∩ ⋃ x, Q x) \ ⋃ x, P x ∩ Q x).Nonempty) :
    exh₂ {⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, P x ∩ Q x} (⋃ x, P x ∪ Q x)
      = ((⋃ x, P x) ∩ ⋃ x, Q x) \ ⋃ x, P x ∩ Q x :=
  (isDiamond_iUnion P Q hp hq).exh₂_eq h

end Existential

/-! ### Hamblin alternatives -/

section Hamblin

variable {ι : Type*} (a : ι → Set W)

/-- The Hamblin alternative for a group: the answer holds of every member. -/
def hamblinAlt (S : Finset ι) : Set W := ⋂ i ∈ S, a i

/-- The Hamblin alternatives: one per non-empty group. -/
def hamblin : Set (Set W) := hamblinAlt a '' {S | S.Nonempty}

variable {a}

theorem mem_hamblinAlt {S : Finset ι} {u : W} : u ∈ hamblinAlt a S ↔ ∀ i ∈ S, u ∈ a i :=
  mem_iInter₂

theorem hamblinAlt_singleton (i : ι) : hamblinAlt a {i} = a i :=
  Finset.set_biInter_singleton i a

theorem hamblinAlt_mem_hamblin {S : Finset ι} (hS : S.Nonempty) : hamblinAlt a S ∈ hamblin a :=
  ⟨S, hS, rfl⟩

variable (hsolo : ∀ i, ∃ u, u ∈ a i ∧ ∀ j, j ≠ i → u ∉ a j)
include hsolo

/-- A group of two or more is innocently excludable given the existential answer. -/
theorem isInnocentlyExcludable_hamblinAlt {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) : IsInnocentlyExcludable (hamblin a) (⋃ i, a i) (hamblinAlt a S) := by
  refine .of_extension_consistent (hamblinAlt_mem_hamblin ⟨i, hi⟩) λ E hE => ?_
  obtain ⟨v, hv⟩ := hE.1.2.2
  by_cases hvS : v ∈ hamblinAlt a S
  · obtain ⟨u, hui, hu⟩ := hsolo i
    refine ⟨u, ?_⟩
    rintro ψ (hψ | hψ)
    · rcases hE.1.2.1 ψ hψ with rfl | ⟨c, ⟨T, -, rfl⟩, rfl⟩
      · exact mem_iUnion.2 ⟨i, hui⟩
      · intro huT
        have hTi : ∀ k ∈ T, k = i := λ k hk =>
          by_contra λ hki => hu k hki (mem_hamblinAlt.1 huT k hk)
        refine hv _ hψ (mem_hamblinAlt.2 λ k hk => ?_)
        rw [hTi k hk]
        exact mem_hamblinAlt.1 hvS i hi
    · rw [mem_singleton_iff] at hψ
      subst hψ
      exact λ huS => hu j hij.symm (mem_hamblinAlt.1 huS j hj)
  · refine ⟨v, ?_⟩
    rintro ψ (hψ | hψ)
    · exact hv ψ hψ
    · rw [mem_singleton_iff] at hψ
      exact hψ ▸ hvS

/-- A single individual is not innocently excludable given the existential answer. -/
theorem not_isInnocentlyExcludable_atom (i : ι) :
    ¬ IsInnocentlyExcludable (hamblin a) (⋃ i, a i) (a i) := by
  obtain ⟨u, hui, hu⟩ := hsolo i
  have hmem : ∀ k, a k ∈ hamblin a := λ k =>
    hamblinAlt_singleton (a := a) k ▸ hamblinAlt_mem_hamblin ⟨k, Finset.mem_singleton_self k⟩
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (hmem i)]
  refine λ h => h ⟨mem_iUnion.2 ⟨i, hui⟩, ?_⟩ hui
  rintro ⟨v, hv, hvu, hnuv⟩
  obtain ⟨k, hkv⟩ := mem_iUnion.1 hv
  have hki : k = i := by_contra λ hki => hu k hki (hvu _ (hmem k) hkv)
  subst k
  refine hnuv λ c hc huc => ?_
  obtain ⟨T, -, rfl⟩ := hc
  refine mem_hamblinAlt.2 λ m hm => ?_
  have hmi : m = i := by_contra λ hmi => hu m hmi (mem_hamblinAlt.1 huc m hm)
  rw [hmi]
  exact hkv

/-- Exhaustifying the existential answer against its Hamblin alternatives yields *exactly one*,
provided each individual can be the sole witness. -/
theorem exhIE_hamblin [Fintype ι] [DecidableEq ι] :
    exhIE (hamblin a) (⋃ i, a i) = {u | ∃! i, u ∈ a i} := by
  have hfin : (hamblin a).Finite := (toFinite {S : Finset ι | S.Nonempty}).image _
  ext u
  rw [mem_exhIE_iff _ _ hfin, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨i, hi, λ j hj => by_contra λ hji =>
      h (hamblinAlt a {i, j}) ?_ (mem_hamblinAlt.2 λ m hm => ?_)⟩
    · exact isInnocentlyExcludable_hamblinAlt hsolo (S := {i, j}) (Finset.mem_insert_self i _)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)) λ h' => hji h'.symm
    · rcases Finset.mem_insert.1 hm with h1 | h1
      · rw [h1]
        exact hi
      · rw [Finset.mem_singleton.1 h1]
        exact hj
  · rintro ⟨i, hi, huniq⟩
    refine ⟨⟨i, hi⟩, λ c hc huc => ?_⟩
    obtain ⟨S, hS, rfl⟩ := hc.1
    by_cases hSi : ∀ j ∈ S, j = i
    · obtain ⟨j, hj⟩ := hS
      have : S = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨hSi j hj ▸ hj, hSi⟩
      rw [this, hamblinAlt_singleton] at hc
      exact not_isInnocentlyExcludable_atom hsolo i hc
    · obtain ⟨j, hj⟩ := not_forall.1 hSi
      obtain ⟨hjS, hji⟩ := Classical.not_imp.1 hj
      exact hji (huniq j (mem_hamblinAlt.1 huc j hjS))

end Hamblin

/-! ### A finite model -/

instance {W : Type*} [Fintype W] {R : W → W → Prop} [DecidableRel R] {p : W → Prop}
    [DecidablePred p] (w : W) : Decidable (w ∈ poss R p) :=
  inferInstanceAs (Decidable (∃ v, R w v ∧ p v))

/-- The accessibility edges of a seven-world model: from `0` every option is permitted, from
`4` only the first, from `5` only the second, from `6` each but not both. -/
def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (4, 1), (5, 2), (6, 1), (6, 2)]

def R (w v : Fin 7) : Prop := (w.val, v.val) ∈ edges

instance : DecidableRel R := λ w v => inferInstanceAs (Decidable ((w.val, v.val) ∈ edges))

/-- The first option holds at worlds `1` and `3`. -/
def p (v : Fin 7) : Prop := v.val ∈ [1, 3]

/-- The second option holds at worlds `2` and `3`. -/
def q (v : Fin 7) : Prop := v.val ∈ [2, 3]

instance : DecidablePred p := λ v => inferInstanceAs (Decidable (v.val ∈ [1, 3]))
instance : DecidablePred q := λ v => inferInstanceAs (Decidable (v.val ∈ [2, 3]))

/-- From world `6`, where each option is permitted but not both, the doubly exhaustified
permission holds. -/
example : (6 : Fin 7) ∈ exh₂ {poss R (λ v => p v ∨ q v), poss R p, poss R q,
    poss R (λ v => p v ∧ q v)} (poss R (λ v => p v ∨ q v)) := by
  rw [free_choice p q ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩]
  decide

/-- From world `0`, where both options are jointly permitted, it fails: the anti-conjunctive
inference. -/
example : (0 : Fin 7) ∉ exh₂ {poss R (λ v => p v ∨ q v), poss R p, poss R q,
    poss R (λ v => p v ∧ q v)} (poss R (λ v => p v ∨ q v)) := by
  rw [free_choice p q ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩]
  decide

/-- With the disjuncts exhaustified first, world `0` verifies Simons's free-choice reading
together with the joint permission. -/
example : (0 : Fin 7) ∈ exh₂ {poss R (λ v => (p v ∧ ¬ q v) ∨ (q v ∧ ¬ p v)),
      poss R (λ v => p v ∧ ¬ q v), poss R (λ v => q v ∧ ¬ p v),
      poss R (λ v => (p v ∧ ¬ q v) ∧ (q v ∧ ¬ p v))}
      (poss R (λ v => (p v ∧ ¬ q v) ∨ (q v ∧ ¬ p v))) ∧ (0 : Fin 7) ∈ poss R (λ v => p v ∧ q v) := by
  rw [free_choice_exhaustified_disjuncts p q ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨0, by decide⟩]
  decide

/-! ### The distribution of free choice -/

/-- The operator taking scope over the connective. -/
inductive Operator
  | possibility
  | negatedPossibility
  | existential
  | negatedNecessity
  | negatedUniversal
  | negation
  deriving DecidableEq

/-- Number marking on an existential. -/
inductive Number
  | none
  | mass
  | plural
  | singular
  deriving DecidableEq

inductive Connective
  | or
  | and
  deriving DecidableEq

/-- A sentence of the data: its operator, number marking, connective, whether the connective
takes narrow scope, and whether it has the free-choice reading. -/
structure Row where
  operator : Operator
  number : Number
  connective : Connective
  narrow : Bool
  fc : Bool
  deriving DecidableEq

/-- Existential free choice: disjunction in the scope of a possibility modal or a non-singular
existential. -/
def Row.ExistentialFC (r : Row) : Prop :=
  r.connective = .or ∧ r.narrow = true ∧
    (r.operator = .possibility ∨ r.operator = .existential ∧ r.number ≠ .singular)

/-- Conjunctive free choice: conjunction in the scope of a negated universal. -/
def Row.ConjunctiveFC (r : Row) : Prop :=
  r.connective = .and ∧ (r.operator = .negatedNecessity ∨ r.operator = .negatedUniversal)

instance : DecidablePred Row.ExistentialFC := λ _ => by unfold Row.ExistentialFC; infer_instance
instance : DecidablePred Row.ConjunctiveFC := λ _ => by unfold Row.ConjunctiveFC; infer_instance

def operatorTable : List (String × Operator) :=
  [("possibility", .possibility), ("negatedPossibility", .negatedPossibility),
    ("existential", .existential), ("negatedNecessity", .negatedNecessity),
    ("negatedUniversal", .negatedUniversal), ("negation", .negation)]

def numberTable : List (String × Number) :=
  [("none", .none), ("mass", .mass), ("plural", .plural), ("singular", .singular)]

def yesNoTable : List (String × Bool) := [("yes", true), ("no", false)]

/-- The rows the paper accounts for; the sentence it leaves open is skipped. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let o ← ex.parse? "quantifier" operatorTable
  let n ← ex.parse? "number" numberTable
  let c ← ex.parse? "connective" [("or", Connective.or), ("and", Connective.and)]
  let s ← ex.parse? "scope" [("narrow", true), ("wide", false)]
  let f ← ex.parse? "fc" yesNoTable
  let st ← ex.feature? "status"
  if st = "accounted" then pure ⟨o, n, c, s, f⟩ else none

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The two generalizations of §3 fit the data: a sentence has the free-choice reading exactly
when it falls under existential or conjunctive free choice. -/
theorem rows_predicted : ∀ r ∈ rows, (r.fc = true ↔ r.ExistentialFC ∨ r.ConjunctiveFC) := by
  decide

end Fox2007
