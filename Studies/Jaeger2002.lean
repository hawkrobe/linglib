module

public import Linglib.Pragmatics.Bidirectional

/-!
# Jäger (2002): Some notes on the formal properties of bidirectional OT

[jaeger-2002] asks when [blutner-2000]'s weak bidirection is well defined. The paper's
Definition 1 is Blutner's mutual recursion between the Q- and the I-principle
(`BidirectionalOT.IsWeakSolution`), which it calls z-optimality after the zigzag of its
evaluation; Lemma 1 shows by the recursion theorem that a well-founded harmony ordering
makes the solution unique. Definition 3 is the paper's own x-optimality: a pair is x-optimal
iff it lies in the generator and no x-optimal pair blocks it along either axis, the fixed
point of `BidirectionalOT.unblockedSet`. Theorem 2 shows that for a transitive well-founded
ordering the x-optimality relation is unique and coincides with z-optimality. Lemma 2 notes
that ranked constraints induce such an ordering.

This file proves Lemma 1 and Theorem 2 for a finite generator, where the ordering restricted
to the generator is well founded, taking the transitivity from the preorder of profiles. The
paper's Lemma 1 gives existence and uniqueness together by the recursion theorem; here
existence is the substrate's hypothesis-free `BidirectionalOT.exists_isWeakSolution` and only
uniqueness needs the descent. The first part of Theorem 2 uses minimality alone; the second
part uses transitivity, as the paper does, where a form-axis blocker of a blocker is turned
into a blocker.

## Main results

* `isWeakSolution_unique` — Lemma 1: the weak version has at most one solution.
* `existsUnique_isFixedPt` — Theorem 2, first part: x-optimality is unique, and it is the
  substrate's `superoptimalSet`.
* `inter_eq_superoptimalSet` — Theorem 2, second part: the pairs satisfying both principles of
  a weak solution are exactly the x-optimal pairs.

## TODO

* The paper's hypotheses are well-foundedness and transitivity of the ordering on an
  arbitrary generator; the finite generator is the case every consumer uses. Generalize to
  `pairs.WellFoundedOn (f · < f ·)`.
* The paper's second part, bidirectional optimization by finite-state transducers, is not
  formalized.

## References

* [jaeger-2002] — the paper.
* [blutner-2000] — the definitions under study.
-/

public section

namespace Jaeger2002

open BidirectionalOT Function
open scoped symmDiff

variable {F M α : Type*} [Preorder α] {pairs : Set (F × M)} {f : F × M → α}

/-! ### Lemma 1: uniqueness of the weak solution -/

/-- A pair unblocked by `I` along the meaning axis but not by `I'` has a blocker in
`I' \ I`. -/
private theorem exists_lt_of_qUnblocked {I I' : Set (F × M)} {p : F × M}
    (hp : p ∈ qUnblockedSet pairs f I) (hp' : p ∉ qUnblockedSet pairs f I') :
    ∃ q ∈ I' \ I, f q < f p := by
  obtain ⟨q, hqI', hq, hlt⟩ : QBlocks f I' p := not_not.1 fun hb ↦ hp' ⟨hp.1, hb⟩
  exact ⟨q, ⟨hqI', fun hqI ↦ hp.2 ⟨q, hqI, hq, hlt⟩⟩, hlt⟩

/-- A pair unblocked by `Q` along the form axis but not by `Q'` has a blocker in `Q' \ Q`. -/
private theorem exists_lt_of_iUnblocked {Q Q' : Set (F × M)} {p : F × M}
    (hp : p ∈ iUnblockedSet pairs f Q) (hp' : p ∉ iUnblockedSet pairs f Q') :
    ∃ q ∈ Q' \ Q, f q < f p := by
  obtain ⟨q, hqQ', hq, hlt⟩ : IBlocks f Q' p := not_not.1 fun hb ↦ hp' ⟨hp.1, hb⟩
  exact ⟨q, ⟨hqQ', fun hqQ ↦ hp.2 ⟨q, hqQ, hq, hlt⟩⟩, hlt⟩

/-- Lemma 1: on a finite generator the weak version has at most one solution. A
profile-minimal pair on which two solutions disagree would have a blocker on which they
also disagree. -/
theorem isWeakSolution_unique (h : pairs.Finite) {Q I Q' I' : Set (F × M)}
    (hQI : IsWeakSolution pairs f Q I) (hQI' : IsWeakSolution pairs f Q' I') :
    Q = Q' ∧ I = I' := by
  obtain ⟨hQ, hI⟩ := hQI
  obtain ⟨hQ', hI'⟩ := hQI'
  by_contra hne
  have hDne : ((Q ∆ Q') ∪ (I ∆ I')).Nonempty := Set.nonempty_iff_ne_empty.2 fun hD ↦ hne <| by
    rwa [Set.union_empty_iff, ← Set.bot_eq_empty, symmDiff_eq_bot, symmDiff_eq_bot] at hD
  have hsub : ∀ {S T : Set (F × M)}, T = S → S ⊆ pairs → T ⊆ pairs := fun hTS hS ↦ hTS ▸ hS
  have hDfin : ((Q ∆ Q') ∪ (I ∆ I')).Finite := h.subset <| Set.union_subset
    (symmDiff_le_sup.trans (Set.union_subset (hsub hQ.symm fun _ hx ↦ hx.1)
      (hsub hQ'.symm fun _ hx ↦ hx.1)))
    (symmDiff_le_sup.trans (Set.union_subset (hsub hI.symm fun _ hx ↦ hx.1)
      (hsub hI'.symm fun _ hx ↦ hx.1)))
  obtain ⟨p, hpD, hmin⟩ := hDfin.exists_minimalFor f _ hDne
  rcases hpD with hp | hp <;> rcases Set.mem_symmDiff.1 hp with ⟨hp, hp'⟩ | ⟨hp, hp'⟩
  · rw [← hQ] at hp; rw [← hQ'] at hp'
    obtain ⟨q, hq, hlt⟩ := exists_lt_of_qUnblocked hp hp'
    exact hlt.not_ge (hmin (.inr (Set.mem_symmDiff.2 (.inr hq))) hlt.le)
  · rw [← hQ'] at hp; rw [← hQ] at hp'
    obtain ⟨q, hq, hlt⟩ := exists_lt_of_qUnblocked hp hp'
    exact hlt.not_ge (hmin (.inr (Set.mem_symmDiff.2 (.inl hq))) hlt.le)
  · rw [← hI] at hp; rw [← hI'] at hp'
    obtain ⟨q, hq, hlt⟩ := exists_lt_of_iUnblocked hp hp'
    exact hlt.not_ge (hmin (.inl (Set.mem_symmDiff.2 (.inr hq))) hlt.le)
  · rw [← hI'] at hp; rw [← hI] at hp'
    obtain ⟨q, hq, hlt⟩ := exists_lt_of_iUnblocked hp hp'
    exact hlt.not_ge (hmin (.inl (Set.mem_symmDiff.2 (.inl hq))) hlt.le)

/-! ### Theorem 2: x-optimality is unique and is z-optimality -/

/-- Theorem 2, first part: on a finite generator there is exactly one x-optimality relation,
the substrate's `superoptimalSet`. -/
theorem existsUnique_isFixedPt (h : pairs.Finite) :
    ∃! S : Set (F × M), IsFixedPt (unblockedSet pairs f) S :=
  ⟨superoptimalSet pairs f, (isFixedPt_superoptimalSet pairs f h).eq,
    fun _ hS ↦ eq_superoptimalSet_of_isFixedPt pairs f h hS⟩

/-- Every x-optimal pair satisfies the I-principle of a weak solution. A profile-minimal
x-optimal pair violating it is I-blocked by a pair of `Q`; that pair is not x-optimal, so
some x-optimal pair blocks it, along the form axis (then it blocks the minimal pair by
transitivity) or the meaning axis (then it is not in `I`, and is a smaller violator). -/
private theorem superoptimalSet_subset_right (h : pairs.Finite) {Q I : Set (F × M)}
    (hQI : IsWeakSolution pairs f Q I) : superoptimalSet pairs f ⊆ I := by
  obtain ⟨hQ, hI⟩ := hQI
  have hX := (isFixedPt_superoptimalSet pairs f h).eq
  by_contra hne
  obtain ⟨p, ⟨hpX, hpI⟩, hmin⟩ := (h.subset fun x hx ↦ superoptimalSet_subset pairs f hx.1)
    |>.exists_minimalFor f _ (Set.not_subset.1 hne)
  have hp : p ∈ unblockedSet pairs f (superoptimalSet pairs f) := hX.symm ▸ hpX
  rw [← hI] at hpI
  obtain ⟨q, hqQ, hq, hqp⟩ : IBlocks f Q p := not_not.1 fun hb ↦ hpI ⟨hp.1, hb⟩
  rw [← hQ] at hqQ
  have hqX : q ∉ superoptimalSet pairs f := fun hqX ↦ hp.2 ⟨q, hqX, .inl hq, hqp⟩
  obtain ⟨r, hrX, hr, hrq⟩ : Blocks f (superoptimalSet pairs f) q :=
    not_not.1 fun hb ↦ hqX (hX ▸ (⟨hqQ.1, hb⟩ : q ∈ unblockedSet pairs f (superoptimalSet pairs f)))
  rcases hr with hr | hr
  · exact hp.2 ⟨r, hrX, .inl (hr.trans hq), hrq.trans hqp⟩
  · exact (hrq.trans hqp).not_ge
      (hmin ⟨hrX, fun hrI ↦ hqQ.2 ⟨r, hrI, hr, hrq⟩⟩ (hrq.trans hqp).le)

/-- Every x-optimal pair satisfies the Q-principle of a weak solution; the mirror image of
`superoptimalSet_subset_right`. -/
private theorem superoptimalSet_subset_left (h : pairs.Finite) {Q I : Set (F × M)}
    (hQI : IsWeakSolution pairs f Q I) : superoptimalSet pairs f ⊆ Q := by
  obtain ⟨hQ, hI⟩ := hQI
  have hX := (isFixedPt_superoptimalSet pairs f h).eq
  by_contra hne
  obtain ⟨p, ⟨hpX, hpQ⟩, hmin⟩ := (h.subset fun x hx ↦ superoptimalSet_subset pairs f hx.1)
    |>.exists_minimalFor f _ (Set.not_subset.1 hne)
  have hp : p ∈ unblockedSet pairs f (superoptimalSet pairs f) := hX.symm ▸ hpX
  rw [← hQ] at hpQ
  obtain ⟨q, hqI, hq, hqp⟩ : QBlocks f I p := not_not.1 fun hb ↦ hpQ ⟨hp.1, hb⟩
  rw [← hI] at hqI
  have hqX : q ∉ superoptimalSet pairs f := fun hqX ↦ hp.2 ⟨q, hqX, .inr hq, hqp⟩
  obtain ⟨r, hrX, hr, hrq⟩ : Blocks f (superoptimalSet pairs f) q :=
    not_not.1 fun hb ↦ hqX (hX ▸ (⟨hqI.1, hb⟩ : q ∈ unblockedSet pairs f (superoptimalSet pairs f)))
  rcases hr with hr | hr
  · exact (hrq.trans hqp).not_ge
      (hmin ⟨hrX, fun hrQ ↦ hqI.2 ⟨r, hrQ, hr, hrq⟩⟩ (hrq.trans hqp).le)
  · exact hp.2 ⟨r, hrX, .inr (hr.trans hq), hrq.trans hqp⟩

/-- Theorem 2, second part: the pairs satisfying both principles of a weak solution are the
x-optimal pairs. -/
theorem inter_eq_superoptimalSet (h : pairs.Finite) {Q I : Set (F × M)}
    (hQI : IsWeakSolution pairs f Q I) : Q ∩ I = superoptimalSet pairs f := by
  refine Set.Subset.antisymm (fun p ⟨hpQ, hpI⟩ ↦ not_not.1 fun hpX ↦ ?_) (Set.subset_inter
    (superoptimalSet_subset_left h hQI) (superoptimalSet_subset_right h hQI))
  obtain ⟨hQ, hI⟩ := hQI
  have hX := (isFixedPt_superoptimalSet pairs f h).eq
  rw [← hQ] at hpQ
  rw [← hI] at hpI
  obtain ⟨q, hqX, hq, hqp⟩ : Blocks f (superoptimalSet pairs f) p :=
    not_not.1 fun hb ↦ hpX (hX ▸ (⟨hpQ.1, hb⟩ : p ∈ unblockedSet pairs f (superoptimalSet pairs f)))
  rcases hq with hq | hq
  · exact hpI.2 ⟨q, superoptimalSet_subset_left h ⟨hQ, hI⟩ hqX, hq, hqp⟩
  · exact hpQ.2 ⟨q, superoptimalSet_subset_right h ⟨hQ, hI⟩ hqX, hq, hqp⟩

end Jaeger2002
