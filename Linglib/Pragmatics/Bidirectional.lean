module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Preorder.Finite

/-!
# Bidirectional Optimality Theory

[blutner-2000]'s bidirectional OT evaluates a form-meaning pair from both the speaker's and
the hearer's side. A pair `⟨A, τ⟩` of the generator `Gen` competes along two axes of a
harmony ordering `<`: the **Q-principle** (production, [horn-1984]'s Q) rejects it when another
form expresses `τ` more harmonically, and the **I-principle** (comprehension, Horn's R) rejects
it when `A` has a more harmonic interpretation. Two versions differ in what a competitor must
be:

* **Strong** bidirection: a pair is optimal iff no pair of `Gen` at all Q- or I-blocks it.
  Here `strongOptimalSet`.
* **Weak** bidirection: the Q-competitors are only the pairs satisfying the I-principle and
  vice versa, a mutual recursion whose solutions are `IsWeakSolution`; a pair satisfying both
  principles is *super-optimal*. The paper's footnote credits Jäger (a 1999 handout, published
  as [jaeger-2002]) with the transparent reformulation that a pair is super-optimal iff it lies
  in `Gen` and no super-optimal pair blocks it, a fixed point of the blocking step
  `unblockedSet`; that fixed point is `superoptimalSet`.

The weak version derives Horn's division of pragmatic labour (unmarked forms take unmarked
meanings, marked forms marked meanings), which the strong version cannot: it blocks a marked
form in every interpretation.

## Main definitions

* `profile`: the violation profile of a ranking, compared lexicographically.
* `QBlocks`, `IBlocks`, `Blocks`: a witness set blocks a pair along the meaning axis, the form
  axis, or either.
* `unblockedSet pairs f S`: the pairs of `pairs` that `S` does not block, the antitone blocking
  step; `strongOptimalSet` is its value at `pairs`.
* `superoptimalSet`: the greatest fixed point of the square of the step.
* `IsWeakSolution`: a solution `(Q, I)` of the paper's mutual recursion.
* `unblocked`, `strongOptimal`, `superoptimal`: the `Finset` forms, computable and closed by
  `decide` on literal generators.

## Main results

* `lfp_eq_superoptimalSet`: for a finite generator the least and greatest fixed points of the
  squared step coincide, so `superoptimalSet` is a fixed point of the step itself
  (`isFixedPt_superoptimalSet`), the unique one (`eq_superoptimalSet_of_isFixedPt`), and
  membership is the footnote's recursion (`mem_superoptimalSet`).
* `strongOptimalSet_subset_inter`: the paper's remark that optimal pairs are super-optimal,
  for every weak solution; `strongOptimalSet_subset_superoptimalSet` is its fixed-point
  companion by coinduction. Neither needs finiteness.
* `exists_isWeakSolution`: the mutual recursion has a solution.
* `coe_superoptimal`: the `Finset` iteration computes `superoptimalSet` on every finite
  generator.

## Implementation notes

The harmony ordering is any preorder `α` reached through a profile `f`, so `profile` (the
lexicographic order on `List ℕ`) and the linear order `Lex (Fin n → ℕ)` both serve. The
paper's "other pair" clause in the principles is dropped: `f q < f p` already forces `q ≠ p`.

The step `unblockedSet pairs f` is antitone, so its square is monotone and mathlib's
`OrderHom.gfp` applies without further hypotheses. The step maps that greatest fixed point to
the least one; for a finite generator the two coincide by descent along a profile-minimal
element of their difference, which is where the well-foundedness of [jaeger-2002]'s Theorem 2
enters. Structurally, `superoptimalSet` is then the kernel of the acyclic digraph whose arcs run
from a pair to the pairs it blocks: no member blocks another, and every other pair of the
generator is blocked by a member.

The `Finset` form iterates the squared step from `pairs` until it is fixed, with `pairs.card`
as the fuel: the descending chain has stabilised by then, so the iteration needs no
convergence hypothesis, and the early exit keeps `decide` shallow. The pair
`(gfp (qUnblockedSet ∘ iUnblockedSet), iUnblockedSet (gfp …))` is a weak solution by
`OrderHom.map_gfp` alone; its uniqueness ([jaeger-2002]'s Lemma 1) and the equality of
`Q ∩ I` with `superoptimalSet` (Theorem 2) are that paper's results, in
`Studies/Jaeger2002.lean`.

## References

* [blutner-2000] — strong and weak bidirection, super-optimality, the division of labour.
* [jaeger-2002] — the fixed-point reformulation, well-definedness and its equivalence with
  the mutual recursion.
* [horn-1984], [atlas-levinson-1981] — the Q- and I-principles.
-/

@[expose] public section

namespace BidirectionalOT

open Function OrderHom

variable {F M α : Type*} [Preorder α]

/-- The violation profile of a ranking: a pair's violations listed from the dominant constraint
down, compared lexicographically. -/
def profile (ranking : List (F × M → ℕ)) (p : F × M) : List ℕ := ranking.map (· p)

/-! ### Blocking -/

section Blocks

variable (f : F × M → α) (S : Set (F × M)) (p : F × M)

/-- `QBlocks f S p`: a more harmonic pair of `S` expresses `p`'s meaning. -/
def QBlocks : Prop := ∃ q ∈ S, q.2 = p.2 ∧ f q < f p

/-- `IBlocks f S p`: a more harmonic pair of `S` interprets `p`'s form. -/
def IBlocks : Prop := ∃ q ∈ S, q.1 = p.1 ∧ f q < f p

/-- `Blocks f S p`: a more harmonic pair of `S` shares `p`'s form or meaning. -/
def Blocks : Prop := ∃ q ∈ S, (q.1 = p.1 ∨ q.2 = p.2) ∧ f q < f p

theorem blocks_iff : Blocks f S p ↔ IBlocks f S p ∨ QBlocks f S p := by
  simp only [Blocks, IBlocks, QBlocks, or_and_right, exists_or, and_or_left]

variable {f S p} {T : Set (F × M)}

theorem QBlocks.mono (hST : S ⊆ T) : QBlocks f S p → QBlocks f T p :=
  fun ⟨q, hq, h⟩ ↦ ⟨q, hST hq, h⟩

theorem IBlocks.mono (hST : S ⊆ T) : IBlocks f S p → IBlocks f T p :=
  fun ⟨q, hq, h⟩ ↦ ⟨q, hST hq, h⟩

theorem Blocks.mono (hST : S ⊆ T) : Blocks f S p → Blocks f T p :=
  fun ⟨q, hq, h⟩ ↦ ⟨q, hST hq, h⟩

variable [DecidableLT α] (f) (S : Finset (F × M)) (p)

instance [DecidableEq M] : Decidable (QBlocks f ↑S p) :=
  decidable_of_iff (∃ q ∈ S, q.2 = p.2 ∧ f q < f p) Iff.rfl

instance [DecidableEq F] : Decidable (IBlocks f ↑S p) :=
  decidable_of_iff (∃ q ∈ S, q.1 = p.1 ∧ f q < f p) Iff.rfl

instance [DecidableEq F] [DecidableEq M] : Decidable (Blocks f ↑S p) :=
  decidable_of_iff (∃ q ∈ S, (q.1 = p.1 ∨ q.2 = p.2) ∧ f q < f p) Iff.rfl

end Blocks

/-! ### The blocking step and its fixed points -/

section Step

variable (pairs : Set (F × M)) (f : F × M → α) {S : Set (F × M)} {p : F × M}

/-- The pairs of `pairs` that `S` does not block. Antitone in `S`. -/
def unblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ Blocks f S p}

@[simp] theorem mem_unblockedSet : p ∈ unblockedSet pairs f S ↔ p ∈ pairs ∧ ¬ Blocks f S p :=
  Iff.rfl

theorem unblockedSet_subset : unblockedSet pairs f S ⊆ pairs := fun _ hp ↦ hp.1

theorem unblockedSet_antitone : Antitone (unblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

/-- Strong bidirection: the pairs that no pair of `pairs` blocks. -/
def strongOptimalSet : Set (F × M) := unblockedSet pairs f pairs

/-- The square of the blocking step, monotone as the composite of two antitone maps. -/
def unblockedSq : Set (F × M) →o Set (F × M) :=
  ⟨unblockedSet pairs f ∘ unblockedSet pairs f,
    (unblockedSet_antitone pairs f).comp (unblockedSet_antitone pairs f)⟩

@[simp] theorem unblockedSq_apply (S : Set (F × M)) :
    unblockedSq pairs f S = unblockedSet pairs f (unblockedSet pairs f S) := rfl

/-- The super-optimal pairs: the greatest fixed point of the squared blocking step. On a
finite generator it is the unique fixed point of the step itself
(`isFixedPt_superoptimalSet`, `eq_superoptimalSet_of_isFixedPt`), the paper's footnote. -/
noncomputable def superoptimalSet : Set (F × M) := (unblockedSq pairs f).gfp

theorem superoptimalSet_subset : superoptimalSet pairs f ⊆ pairs := by
  rw [superoptimalSet, ← (unblockedSq pairs f).map_gfp]
  exact unblockedSet_subset _ _

/-- An optimal pair is a fixed point's member: `strongOptimalSet` is a post-fixed point of the
squared step, since the step is antitone and lands in `pairs`. -/
theorem strongOptimalSet_subset_superoptimalSet :
    strongOptimalSet pairs f ⊆ superoptimalSet pairs f :=
  le_gfp _ (unblockedSet_antitone pairs f (unblockedSet_subset pairs f))

/-- The step exchanges the greatest and least fixed points of its square. -/
theorem unblockedSet_superoptimalSet :
    unblockedSet pairs f (superoptimalSet pairs f) = (unblockedSq pairs f).lfp := by
  have hfix : ∀ S, unblockedSq pairs f S = S →
      unblockedSq pairs f (unblockedSet pairs f S) = unblockedSet pairs f S := fun S hS ↦ by
    change unblockedSet pairs f (unblockedSq pairs f S) = _
    rw [hS]
  refine le_antisymm ?_ (lfp_le_fixed _ (hfix _ (unblockedSq pairs f).map_gfp))
  calc unblockedSet pairs f (superoptimalSet pairs f)
      ≤ unblockedSet pairs f (unblockedSet pairs f (unblockedSq pairs f).lfp) :=
        unblockedSet_antitone pairs f (le_gfp _ (hfix _ (unblockedSq pairs f).map_lfp).ge)
    _ = (unblockedSq pairs f).lfp := (unblockedSq pairs f).map_lfp

/-- On a finite generator the least and greatest fixed points of the squared step coincide:
a profile-minimal pair of their difference would be blocked by a still smaller one. -/
theorem lfp_eq_superoptimalSet (h : pairs.Finite) :
    (unblockedSq pairs f).lfp = superoptimalSet pairs f := by
  set G := superoptimalSet pairs f
  set L := (unblockedSq pairs f).lfp
  have hGL : unblockedSet pairs f G = L := unblockedSet_superoptimalSet pairs f
  have hLG : unblockedSet pairs f L = G := by rw [← hGL]; exact (unblockedSq pairs f).map_gfp
  refine le_antisymm (lfp_le_gfp _) (not_not.1 fun hne ↦ ?_)
  obtain ⟨p, ⟨hpG, hpL⟩, hmin⟩ := (h.subset fun x hx ↦ superoptimalSet_subset pairs f hx.1)
    |>.exists_minimalFor f (G \ L) (Set.not_subset.1 hne)
  have hp : p ∈ unblockedSet pairs f L := hLG.symm ▸ hpG
  obtain ⟨q, hqG, hadj, hlt⟩ : Blocks f G p :=
    not_not.1 fun hb ↦ hpL (hGL ▸ (⟨hp.1, hb⟩ : p ∈ unblockedSet pairs f G))
  exact hlt.not_ge (hmin ⟨hqG, fun hqL ↦ hp.2 ⟨q, hqL, hadj, hlt⟩⟩ hlt.le)

theorem isFixedPt_superoptimalSet (h : pairs.Finite) :
    IsFixedPt (unblockedSet pairs f) (superoptimalSet pairs f) := by
  rw [IsFixedPt, unblockedSet_superoptimalSet, lfp_eq_superoptimalSet pairs f h]

/-- The footnote's recursion: a pair is super-optimal iff it lies in the generator and no
super-optimal pair blocks it. -/
theorem mem_superoptimalSet (h : pairs.Finite) :
    p ∈ superoptimalSet pairs f ↔ p ∈ pairs ∧ ¬ Blocks f (superoptimalSet pairs f) p := by
  conv_lhs => rw [← (isFixedPt_superoptimalSet pairs f h).eq]
  exact Iff.rfl

/-- On a finite generator the blocking step has no fixed point but the super-optimal set. -/
theorem eq_superoptimalSet_of_isFixedPt (h : pairs.Finite)
    (hS : IsFixedPt (unblockedSet pairs f) S) : S = superoptimalSet pairs f := by
  have hsq : unblockedSq pairs f S = S := by
    change unblockedSet pairs f (unblockedSet pairs f S) = S
    rw [hS.eq, hS.eq]
  exact le_antisymm (le_gfp _ hsq.ge)
    ((lfp_eq_superoptimalSet pairs f h).symm.trans_le (lfp_le_fixed _ hsq))

end Step

/-! ### The paper's mutual recursion -/

section Weak

variable (pairs : Set (F × M)) (f : F × M → α)

/-- The pairs of `pairs` that `S` does not Q-block. -/
def qUnblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ QBlocks f S p}

/-- The pairs of `pairs` that `S` does not I-block. -/
def iUnblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ IBlocks f S p}

theorem qUnblockedSet_antitone : Antitone (qUnblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

theorem iUnblockedSet_antitone : Antitone (iUnblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

theorem unblockedSet_eq_inter (S : Set (F × M)) :
    unblockedSet pairs f S = qUnblockedSet pairs f S ∩ iUnblockedSet pairs f S := by
  ext p
  simp only [mem_unblockedSet, blocks_iff, qUnblockedSet, iUnblockedSet, Set.mem_inter_iff,
    Set.mem_sep_iff, not_or]
  tauto

/-- The weak version of bidirection: `Q` collects the pairs no pair of `I` Q-blocks and `I`
the pairs no pair of `Q` I-blocks. A pair of both is super-optimal. -/
def IsWeakSolution (Q I : Set (F × M)) : Prop :=
  qUnblockedSet pairs f I = Q ∧ iUnblockedSet pairs f Q = I

/-- The mutual recursion has a solution: the greatest fixed point of the monotone composite
`qUnblockedSet ∘ iUnblockedSet` together with its image under `iUnblockedSet`. -/
theorem exists_isWeakSolution : ∃ Q I, IsWeakSolution pairs f Q I :=
  let Φ : Set (F × M) →o Set (F × M) :=
    ⟨qUnblockedSet pairs f ∘ iUnblockedSet pairs f,
      (qUnblockedSet_antitone pairs f).comp (iUnblockedSet_antitone pairs f)⟩
  ⟨Φ.gfp, iUnblockedSet pairs f Φ.gfp, Φ.map_gfp, rfl⟩

/-- The paper's remark that an optimal pair is super-optimal: a pair no pair of `pairs`
blocks is blocked by no pair of `I` or of `Q`, both subsets of `pairs`. -/
theorem strongOptimalSet_subset_inter {Q I : Set (F × M)} (h : IsWeakSolution pairs f Q I) :
    strongOptimalSet pairs f ⊆ Q ∩ I := fun p hp ↦ by
  obtain ⟨hQ, hI⟩ := h
  have hQp : Q ⊆ pairs := hQ ▸ fun _ hx ↦ hx.1
  have hIp : I ⊆ pairs := hI ▸ fun _ hx ↦ hx.1
  have hpQ : p ∈ qUnblockedSet pairs f I :=
    ⟨hp.1, fun hb ↦ hp.2 ((blocks_iff ..).2 (.inr (hb.mono hIp)))⟩
  have hpI : p ∈ iUnblockedSet pairs f Q :=
    ⟨hp.1, fun hb ↦ hp.2 ((blocks_iff ..).2 (.inl (hb.mono hQp)))⟩
  exact ⟨hQ ▸ hpQ, hI ▸ hpI⟩

end Weak

/-! ### Computable forms -/

section Finset

variable [DecidableEq F] [DecidableEq M] [DecidableLT α] (pairs : Finset (F × M))
  (f : F × M → α) {S : Finset (F × M)} {p : F × M}

/-- The pairs of `pairs` that `S` does not block. -/
def unblocked (S : Finset (F × M)) : Finset (F × M) := pairs.filter fun p ↦ ¬ Blocks f ↑S p

variable {pairs f} in
@[simp] theorem mem_unblocked : p ∈ unblocked pairs f S ↔ p ∈ pairs ∧ ¬ Blocks f ↑S p :=
  Finset.mem_filter

@[simp] theorem coe_unblocked : (↑(unblocked pairs f S) : Set (F × M)) = unblockedSet ↑pairs f ↑S :=
  Finset.coe_filter _ _

theorem unblocked_subset : unblocked pairs f S ⊆ pairs := Finset.filter_subset _ _

theorem unblocked_antitone : Antitone (unblocked pairs f) := fun _ _ hST _ hp ↦
  mem_unblocked.2 ⟨(mem_unblocked.1 hp).1,
    fun hb ↦ (mem_unblocked.1 hp).2 (hb.mono (Finset.coe_subset.2 hST))⟩

/-- Strong bidirection, computably. -/
def strongOptimal : Finset (F × M) := unblocked pairs f pairs

variable {pairs f} in
@[simp] theorem mem_strongOptimal : p ∈ strongOptimal pairs f ↔ p ∈ pairs ∧ ¬ Blocks f ↑pairs p :=
  mem_unblocked

theorem coe_strongOptimal : (↑(strongOptimal pairs f) : Set (F × M)) = strongOptimalSet ↑pairs f :=
  coe_unblocked pairs f

/-- The squared blocking step iterated from `S` until it is fixed, at most `n` times; the
computation behind `superoptimal`. -/
def superoptimalAux (S : Finset (F × M)) : ℕ → Finset (F × M)
  | 0 => S
  | n + 1 =>
    if unblocked pairs f (unblocked pairs f S) = S then S
    else superoptimalAux (unblocked pairs f (unblocked pairs f S)) n

private theorem superoptimalAux_spec (S : Finset (F × M)) (n : ℕ) :
    ∃ k ≤ n, superoptimalAux pairs f S n = (unblocked pairs f ∘ unblocked pairs f)^[k] S ∧
      (IsFixedPt (unblocked pairs f ∘ unblocked pairs f) (superoptimalAux pairs f S n) ∨
        k = n) := by
  induction n generalizing S with
  | zero => exact ⟨0, le_rfl, rfl, .inr rfl⟩
  | succ n ih =>
    by_cases h : unblocked pairs f (unblocked pairs f S) = S
    · exact ⟨0, Nat.zero_le _, by simp [superoptimalAux, h],
        .inl (by simp [superoptimalAux, h, IsFixedPt])⟩
    · obtain ⟨k, hk, hT, hfix⟩ := ih (unblocked pairs f (unblocked pairs f S))
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · rw [iterate_succ_apply, comp_apply, ← hT]; simp [superoptimalAux, h]
      · simpa [superoptimalAux, h] using hfix.imp_right fun hk ↦ by omega

/-- The super-optimal pairs, computably: the squared blocking step iterated from `pairs` until
fixed, which happens within `pairs.card` steps. Equality with a literal `Finset` is closed by
`decide`. -/
def superoptimal : Finset (F × M) := superoptimalAux pairs f pairs pairs.card

/-- A monotone self-map of finsets that shrinks `s` is fixed on `s` within `s.card` steps. -/
private theorem isFixedPt_iterate_card {β : Type*} {g : Finset β → Finset β} (hg : Monotone g)
    {s : Finset β} (hs : g s ⊆ s) : IsFixedPt g (g^[s.card] s) := by
  have hdesc : ∀ n, g^[n + 1] s ⊆ g^[n] s := fun n ↦ by
    induction n with
    | zero => exact hs
    | succ n ih =>
      have := hg ih
      rwa [← iterate_succ_apply' g, ← iterate_succ_apply' g] at this
  have key : ∀ n, IsFixedPt g (g^[n] s) ∨ (g^[n] s).card + n ≤ s.card := fun n ↦ by
    induction n with
    | zero => exact .inr (by simp)
    | succ n ih =>
      by_cases hfix : IsFixedPt g (g^[n] s)
      · exact .inl (by rw [iterate_succ_apply', hfix.eq]; exact hfix)
      · have hlt : (g^[n + 1] s).card < (g^[n] s).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hdesc n,
            fun h ↦ hfix (by show g (g^[n] s) = g^[n] s; rw [← iterate_succ_apply' g, h])⟩)
        exact .inr (by have := ih.resolve_left hfix; omega)
  rcases key s.card with h | h
  · exact h
  · have hempty : g^[s.card] s = ∅ := Finset.card_eq_zero.1 (by omega)
    have hsub := hdesc s.card
    rw [iterate_succ_apply', hempty] at hsub
    show g (g^[s.card] s) = g^[s.card] s
    rw [hempty]
    exact Finset.subset_empty.1 hsub

theorem coe_superoptimal : (↑(superoptimal pairs f) : Set (F × M)) = superoptimalSet ↑pairs f := by
  have hcoe : ∀ n, (↑((unblocked pairs f ∘ unblocked pairs f)^[n] pairs) : Set (F × M)) =
      (unblockedSq ↑pairs f)^[n] ↑pairs := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; simp
  have hle : ∀ n, (unblockedSq ↑pairs f).gfp ≤ (unblockedSq ↑pairs f)^[n] ↑pairs := fun n ↦ by
    induction n with
    | zero => exact superoptimalSet_subset _ _
    | succ n ih =>
      rw [iterate_succ_apply']
      exact (unblockedSq ↑pairs f).map_gfp.symm.le.trans ((unblockedSq ↑pairs f).monotone ih)
  obtain ⟨k, -, hT, hfix⟩ := superoptimalAux_spec pairs f pairs pairs.card
  have hfix : IsFixedPt (unblocked pairs f ∘ unblocked pairs f) (superoptimal pairs f) :=
    hfix.elim id fun hk ↦ by
      rw [superoptimal, hT, hk]
      exact isFixedPt_iterate_card ((unblocked_antitone pairs f).comp (unblocked_antitone pairs f))
        (unblocked_subset pairs f (S := unblocked pairs f pairs))
  have hΦ : unblockedSq ↑pairs f ↑(superoptimal pairs f) = ↑(superoptimal pairs f) := by
    simpa using congrArg (fun s : Finset (F × M) ↦ (↑s : Set (F × M))) hfix.eq
  refine le_antisymm (le_gfp _ hΦ.ge) ?_
  rw [superoptimal, hT, hcoe]
  exact hle k

/-- The footnote's recursion, computably. -/
theorem mem_superoptimal :
    p ∈ superoptimal pairs f ↔ p ∈ pairs ∧ ¬ Blocks f ↑(superoptimal pairs f) p := by
  rw [← Finset.mem_coe, coe_superoptimal, mem_superoptimalSet _ _ pairs.finite_toSet,
    Finset.mem_coe]

theorem superoptimal_subset : superoptimal pairs f ⊆ pairs :=
  fun _ hp ↦ ((mem_superoptimal pairs f).1 hp).1

theorem strongOptimal_subset_superoptimal : strongOptimal pairs f ⊆ superoptimal pairs f := by
  rw [← Finset.coe_subset, coe_strongOptimal, coe_superoptimal]
  exact strongOptimalSet_subset_superoptimalSet _ _

end Finset

end BidirectionalOT
