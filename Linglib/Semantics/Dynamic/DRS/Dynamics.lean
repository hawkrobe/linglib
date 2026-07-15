import Linglib.Semantics.Dynamic.DRS.Basic
import Linglib.Semantics.Dynamic.DRS.Reduction
import Linglib.Semantics.Dynamic.Update

/-!
# Relational (dynamic) semantics of DRSs, and its equivalence with verifying embeddings
[muskens-1996]

Muskens's reformulation of DRT. Conditions denote *sets* of embeddings (SEM1/2);
boxes denote *binary relations* between embeddings (SEM3, input → output, the
format of [groenendijk-stokhof-1991]); a box is true under an input embedding
`a` iff some output `a'` is related to it (p. 148). This is the dynamic / CCP
face of DRT, dual to the static verifying-embedding semantics `DRS.Realize` —
the total-assignment rendering of [kamp-reyle-1993]'s verification (see the
deviation note in `DRS/Semantics.lean`).

The two semantics are *defined independently* and proved equivalent — Muskens's
remark that the relational interpretation "is in fact equivalent" to the
verifying-embedding one (his fn. 4 scopes the remark: both sides here are the
total-assignment variant). The equivalence is a theorem, not a definitional
identification:

* `DRS.toRel_iff_realize` — the relation `toRel K a a'` holds iff `a'` extends `a`
  over `K`'s universe and verifies `K` (the keystone bridge).
* `DRS.trueRel_iff_realize_toFormula` — the dynamic truth of a DRS equals its
  first-order translation's `Realize`, closing the triangle with `Reduction`
  (`Realize` — `toFormula` — `toRel`, each pair related by a proven theorem).

## Main declarations

* `DRS.toRel` / `Condition.holds` — the relational (SEM3) and set (SEM1/2)
  denotations.
* `DRS.trueRel` — relational truth: some output embedding is related to the input.
* `DRS.toRel_iff_realize` / `Condition.holds_iff_realize` — equivalence with the
  static `DRS.Realize` semantics.
* `DRS.trueRel_congr` — the coincidence lemma: denotation depends only on the
  occurring referents (`DRS.occ`, from `DRS/Basic.lean`).
* `DRS.toRel_merge` — the Merging Lemma: under freshness, `merge` denotes the
  spine sequencing `⨟` (relational composition) of the two box relations.

## Implementation notes

Naming: the dynamic face (`toRel`, `holds`, `trueRel`) follows the spine's
lowerCamel operation names (`dneg`, `dseq`, `closure`); the static face
(`DRS.Realize`, `DRS/Semantics.lean`) follows mathlib's `Formula.Realize`.
-/

open FirstOrder FirstOrder.Language
open DynamicSemantics (Update dneg dimpl ddisj closure dseq)

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-! ### The relational denotation -/

mutual
/-- The relational (dynamic) denotation of a DRS ([muskens-1996], SEM3): the
input-output relation `⟨a, a'⟩` where `a'` differs from `a` at most on the
universe and verifies every condition. -/
def DRS.toRel : DRS L V → Update (V → M)
  | .mk U conds => fun a a' => (∀ x, x ∉ U → a' x = a x) ∧ Condition.holdsAll conds a'
/-- The set denotation of a condition ([muskens-1996], SEM1/2): the set of
embeddings at which it holds. Complex conditions apply the spine connectives
`dneg`/`dimpl`/`ddisj` to the box relations of their sub-DRSs. -/
def Condition.holds : Condition L V → (V → M) → Prop
  | .rel R args => fun a => Structure.RelMap R (fun i => a (args i))
  | .eq u v => fun a => a u = a v
  | .neg K => dneg (DRS.toRel K)
  | .imp ante cons => dimpl (DRS.toRel ante) (DRS.toRel cons)
  | .dis l r => ddisj (DRS.toRel l) (DRS.toRel r)
/-- Every condition in the list holds at `a`. A `List` helper — the higher-order
form fails the nested-inductive structural-recursion checker. -/
def Condition.holdsAll : List (Condition L V) → (V → M) → Prop
  | [] => fun _ => True
  | c :: cs => fun a => Condition.holds c a ∧ Condition.holdsAll cs a
end

/-- A DRS is *true* under an input embedding `a` iff some output embedding is
related to it ([muskens-1996], p. 148) — the spine's anaphoric `closure`. -/
def DRS.trueRel (K : DRS L V) (a : V → M) : Prop := closure (DRS.toRel K) a

/-! ### Structural simp API -/

@[simp] theorem DRS.toRel_mk (U : Finset V) (conds : List (Condition L V)) (a a' : V → M) :
    DRS.toRel (.mk U conds) a a' ↔
      (∀ x, x ∉ U → a' x = a x) ∧ Condition.holdsAll conds a' := Iff.rfl

@[simp] theorem Condition.holds_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) (a : V → M) :
    (Condition.rel R args).holds a ↔ Structure.RelMap R (fun i => a (args i)) := Iff.rfl

@[simp] theorem Condition.holds_eq (u v : V) (a : V → M) :
    (Condition.eq u v : Condition L V).holds a ↔ a u = a v := Iff.rfl

@[simp] theorem Condition.holds_neg (K : DRS L V) (a : V → M) :
    (Condition.neg K).holds a ↔ ¬ ∃ a', DRS.toRel K a a' := Iff.rfl

@[simp] theorem Condition.holds_imp (ante cons : DRS L V) (a : V → M) :
    (Condition.imp ante cons).holds a ↔
      ∀ a', DRS.toRel ante a a' → ∃ a'', DRS.toRel cons a' a'' := Iff.rfl

@[simp] theorem Condition.holds_dis (l r : DRS L V) (a : V → M) :
    (Condition.dis l r).holds a ↔ ∃ a', DRS.toRel l a a' ∨ DRS.toRel r a a' := Iff.rfl

@[simp] theorem Condition.holdsAll_nil (a : V → M) :
    Condition.holdsAll ([] : List (Condition L V)) a := trivial

@[simp] theorem Condition.holdsAll_cons (c : Condition L V) (cs : List (Condition L V))
    (a : V → M) :
    Condition.holdsAll (c :: cs) a ↔ Condition.holds c a ∧ Condition.holdsAll cs a := Iff.rfl

/-- `trueRel` unfolded: some output embedding is related to the input. -/
theorem DRS.trueRel_iff (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ ∃ a', DRS.toRel K a a' := Iff.rfl

/-! ### Equivalence with the verifying-embedding semantics -/

mutual
/-- **SEM3 ≡ verification semantics** ([muskens-1996]): the relational denotation
agrees with the static verifying-embedding semantics — `toRel K a a'` holds iff
the output `a'` extends the input `a` over `K`'s universe and verifies `K`.
(Both sides are the total-assignment variant; see `DRS/Semantics.lean`.) -/
theorem DRS.toRel_iff_realize (K : DRS L V) (a a' : V → M) :
    DRS.toRel K a a' ↔ (∀ x, x ∉ K.referents → a' x = a x) ∧ DRS.Realize a' K := by
  match K with
  | .mk U conds =>
    simp only [DRS.toRel, DRS.referents_mk, DRS.Realize]
    exact and_congr_right (fun _ => Condition.holdsAll_iff_realizeAll conds a')
/-- A condition's set denotation agrees with its static `Realize`. -/
theorem Condition.holds_iff_realize (c : Condition L V) (a : V → M) :
    Condition.holds c a ↔ Condition.Realize a c := by
  match c with
  | .rel R args => exact Iff.rfl
  | .eq u v => exact Iff.rfl
  | .neg K =>
    simp only [Condition.holds_neg, Condition.Realize]
    exact not_congr (exists_congr (fun a' => DRS.toRel_iff_realize K a a'))
  | .imp ante cons =>
    simp only [Condition.holds_imp, Condition.Realize]
    refine forall_congr' (fun a' => ?_)
    rw [DRS.toRel_iff_realize ante a a', and_imp]
    refine imp_congr_right (fun _ => imp_congr_right (fun _ => ?_))
    exact exists_congr (fun a'' => DRS.toRel_iff_realize cons a' a'')
  | .dis l r =>
    simp only [Condition.holds_dis, Condition.Realize, exists_or]
    exact or_congr (exists_congr (fun a' => DRS.toRel_iff_realize l a a'))
      (exists_congr (fun a' => DRS.toRel_iff_realize r a a'))
/-- The list analogue of `Condition.holds_iff_realize`. -/
theorem Condition.holdsAll_iff_realizeAll (cs : List (Condition L V)) (a : V → M) :
    Condition.holdsAll cs a ↔ Condition.RealizeAll a cs := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    simp only [Condition.holdsAll, Condition.RealizeAll]
    exact and_congr (Condition.holds_iff_realize c a) (Condition.holdsAll_iff_realizeAll cs a)
end

/-- The dynamic truth of a DRS equals its first-order translation's `Realize`
([muskens-1996]; [kamp-reyle-1993] §1.5) — the third edge of the
`Realize`/`toFormula`/`toRel` triangle. -/
theorem DRS.trueRel_iff_realize_toFormula [DecidableEq V] (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ (K.toFormula).Realize a := by
  rw [DRS.trueRel_iff, DRS.realize_toFormula K a]
  exact exists_congr (fun a' => DRS.toRel_iff_realize K a a')

/-! ### The coincidence lemma -/

mutual
/-- **Coincidence**: a DRS's relational truth depends only on the input
embedding's values at its occurring referents. Proved by surgery on the output
witness, the load-bearing case being the `imp` clause of `Condition.holds_congr`. -/
theorem DRS.trueRel_congr [DecidableEq V] (K : DRS L V) (a₁ a₂ : V → M)
    (h : Set.EqOn a₁ a₂ ↑(DRS.occ K)) : DRS.trueRel K a₁ ↔ DRS.trueRel K a₂ := by
  match K with
  | .mk U conds =>
    simp only [DRS.trueRel_iff, DRS.toRel_mk]
    have key : ∀ (b₁ b₂ : V → M), Set.EqOn b₁ b₂ ↑(DRS.occ (DRS.mk U conds)) →
        (∃ a', (∀ x, x ∉ U → a' x = b₁ x) ∧ Condition.holdsAll conds a') →
        (∃ a', (∀ x, x ∉ U → a' x = b₂ x) ∧ Condition.holdsAll conds a') := by
      rintro b₁ b₂ hb ⟨a', hag, hh⟩
      refine ⟨(Condition.occL conds).piecewise a' b₂, ?_, ?_⟩
      · intro x hx
        by_cases hxc : x ∈ Condition.occL conds
        · rw [Finset.piecewise_eq_of_mem _ _ _ hxc, hag x hx]
          refine hb ?_
          simp only [DRS.occ, Finset.coe_union]
          exact Or.inr (Finset.mem_coe.mpr hxc)
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hxc]
      · refine (Condition.holdsAll_congr conds _ a' ?_).mpr hh
        intro x hx
        exact Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_coe.mp hx)
    exact ⟨key a₁ a₂ h, key a₂ a₁ h.symm⟩
/-- A condition's set denotation depends only on its occurring referents. -/
theorem Condition.holds_congr [DecidableEq V] (c : Condition L V) (a₁ a₂ : V → M)
    (h : Set.EqOn a₁ a₂ ↑(Condition.occ c)) : Condition.holds c a₁ ↔ Condition.holds c a₂ := by
  match c with
  | .rel R args =>
    simp only [Condition.holds]
    have : (fun i => a₁ (args i)) = (fun i => a₂ (args i)) := by
      funext i; refine h ?_; simp [Condition.occ]
    rw [this]
  | .eq u v =>
    simp only [Condition.holds]
    rw [h (show u ∈ ↑(Condition.occ (Condition.eq u v)) by simp [Condition.occ]),
      h (show v ∈ ↑(Condition.occ (Condition.eq u v)) by simp [Condition.occ])]
  | .neg K =>
    simp only [Condition.holds_neg]
    have hk := DRS.trueRel_congr K a₁ a₂ h
    simp only [DRS.trueRel_iff] at hk
    rw [hk]
  | .imp ante cons =>
    simp only [Condition.holds_imp]
    have hante : ∀ (b₁ b₂ : V → M), Set.EqOn b₁ b₂ ↑(Condition.occ (Condition.imp ante cons)) →
        (∀ a', DRS.toRel ante b₁ a' → ∃ a'', DRS.toRel cons a' a'') →
        (∀ a', DRS.toRel ante b₂ a' → ∃ a'', DRS.toRel cons a' a'') := by
      rintro b₁ b₂ hb hL a' ha'
      cases ante with
      | mk Ua condsa =>
        obtain ⟨hag, hh⟩ := ha'
        have hset : DRS.occ (DRS.mk Ua condsa) ∪ DRS.occ cons =
            Condition.occ (Condition.imp (DRS.mk Ua condsa) cons) := by
          simp [Condition.occ]
        have hagree : Set.EqOn
            ((DRS.occ (DRS.mk Ua condsa) ∪ DRS.occ cons).piecewise a' b₁) a'
            ↑(DRS.occ cons) := by
          intro x hx
          exact Finset.piecewise_eq_of_mem _ _ _
            (Finset.mem_union_right _ (Finset.mem_coe.mp hx))
        have hr₁ : DRS.toRel (DRS.mk Ua condsa) b₁
            ((DRS.occ (DRS.mk Ua condsa) ∪ DRS.occ cons).piecewise a' b₁) := by
          refine ⟨?_, ?_⟩
          · intro x hx
            by_cases hxS : x ∈ DRS.occ (DRS.mk Ua condsa) ∪ DRS.occ cons
            · rw [Finset.piecewise_eq_of_mem _ _ _ hxS, hag x hx]
              exact (hb (Finset.mem_coe.mpr (hset ▸ hxS))).symm
            · rw [Finset.piecewise_eq_of_notMem _ _ _ hxS]
          · refine (Condition.holdsAll_congr condsa _ a' ?_).mpr hh
            intro x hx
            refine Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_union_left _ ?_)
            simp only [DRS.occ]
            exact Finset.mem_union_right _ (Finset.mem_coe.mp hx)
        obtain ⟨a₄, ha₄⟩ := hL _ hr₁
        have hcc := DRS.trueRel_congr cons _ a' hagree
        simp only [DRS.trueRel_iff] at hcc
        exact hcc.mp ⟨a₄, ha₄⟩
    exact ⟨hante a₁ a₂ h, hante a₂ a₁ h.symm⟩
  | .dis l r =>
    simp only [Condition.holds_dis, exists_or]
    have hsub : ↑(DRS.occ l) ⊆ ↑(Condition.occ (Condition.dis l r)) :=
      Finset.coe_subset.mpr Finset.subset_union_left
    have hsubr : ↑(DRS.occ r) ⊆ ↑(Condition.occ (Condition.dis l r)) :=
      Finset.coe_subset.mpr Finset.subset_union_right
    have hl := DRS.trueRel_congr l a₁ a₂ (h.mono hsub)
    have hr := DRS.trueRel_congr r a₁ a₂ (h.mono hsubr)
    simp only [DRS.trueRel_iff] at hl hr
    rw [hl, hr]
/-- The list analogue of `Condition.holds_congr`. -/
theorem Condition.holdsAll_congr [DecidableEq V] (cs : List (Condition L V)) (a₁ a₂ : V → M)
    (h : Set.EqOn a₁ a₂ ↑(Condition.occL cs)) :
    Condition.holdsAll cs a₁ ↔ Condition.holdsAll cs a₂ := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    simp only [Condition.holdsAll_cons]
    have hsub : ↑(Condition.occ c) ⊆ ↑(Condition.occL (c :: cs)) :=
      Finset.coe_subset.mpr Finset.subset_union_left
    have hsubr : ↑(Condition.occL cs) ⊆ ↑(Condition.occL (c :: cs)) :=
      Finset.coe_subset.mpr Finset.subset_union_right
    exact and_congr (Condition.holds_congr c a₁ a₂ (h.mono hsub))
      (Condition.holdsAll_congr cs a₁ a₂ (h.mono hsubr))
end

/-! ### The merging lemma: sequencing is merge, under freshness -/

/-- The conjunction of conditions distributes over list append. -/
@[simp] theorem Condition.holdsAll_append (cs ds : List (Condition L V)) (a : V → M) :
    Condition.holdsAll (cs ++ ds) a ↔ Condition.holdsAll cs a ∧ Condition.holdsAll ds a := by
  induction cs with
  | nil => simp [Condition.holdsAll]
  | cons c cs ih => simp only [List.cons_append, Condition.holdsAll, ih, and_assoc]

/-- **Merging Lemma** ([muskens-1996], §II.2): when `K₂`'s universe is fresh
for `K₁`'s conditions, the merge `K₁ ⊕ K₂` denotes the spine sequencing
(relational composition) of the two box relations — `‖K₁ ⊕ K₂‖ = ‖K₁‖ ⨟ ‖K₂‖`.
This is what gives `merge` its dynamic meaning. -/
theorem DRS.toRel_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.occL K₁.conditions)) :
    (DRS.toRel (K₁.merge K₂) : Update (V → M)) = DRS.toRel K₁ ⨟ DRS.toRel K₂ := by
  obtain ⟨U₁, conds₁⟩ := K₁
  obtain ⟨U₂, conds₂⟩ := K₂
  simp only [DRS.referents_mk, DRS.conditions_mk, Finset.disjoint_left] at hfresh
  funext a a'
  apply propext
  simp only [DRS.merge, DRS.referents_mk, DRS.conditions_mk, DRS.toRel,
    Condition.holdsAll_append, dseq, Relation.Comp]
  constructor
  · rintro ⟨hag, hh₁, hh₂⟩
    refine ⟨U₂.piecewise a a', ⟨?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      by_cases hxU2 : x ∈ U₂
      · rw [Finset.piecewise_eq_of_mem _ _ _ hxU2]
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hxU2]
        refine hag x ?_
        rw [Finset.mem_union, not_or]
        exact ⟨hx, hxU2⟩
    · refine (Condition.holdsAll_congr conds₁ _ a' ?_).mpr hh₁
      intro x hx
      exact Finset.piecewise_eq_of_notMem _ _ _
        (fun h => hfresh h (Finset.mem_coe.mp hx))
    · intro x hx
      exact (Finset.piecewise_eq_of_notMem _ _ _ hx).symm
    · exact hh₂
  · rintro ⟨a'', ⟨hag1, hh1⟩, hag2, hh2⟩
    refine ⟨?_, ?_, hh2⟩
    · intro x hx
      rw [Finset.mem_union, not_or] at hx
      rw [hag2 x hx.2, hag1 x hx.1]
    · exact (Condition.holdsAll_congr conds₁ a' a''
        (fun x hx => hag2 x (fun hu => hfresh hu (Finset.mem_coe.mp hx)))).mpr hh1

end DRT
