import Linglib.Theories.Discourse.Boxes.Syntax
import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Discourse.Connectives.WeakestPrecondition
import Linglib.Theories.Discourse.Connectives.CCP
import Linglib.Core.CylindricAlgebra
import Mathlib.Tactic.SimpRw

/-!
# DRS Interpretation and Accessibility
@cite{muskens-1996}

Semantic interpretation bridge: maps `DRSExpr` syntax (from `Core.DRSExpr`)
to `DRS (Assignment E)` semantics, connecting the pure syntactic representation
to the dynamic semantic algebra.

## Key Results

- `interp`: maps `DRSExpr → DRS (Assignment E)` (ABB1–ABB4)
- `mergingLemma`: sequenced boxes with fresh drefs merge into one box
- `reduce`/`reduce_sound`: iterative reduction to canonical form
- Proposition 1 (@cite{muskens-1996}, p. 174): proper DRS ↔ closed wp
-/

namespace Semantics.Dynamic.Core.Accessibility

export Semantics.Dynamic.Core.DRSExpr (DRSExpr adr occurs acc allOccurring isFree isProper
  exManAdoresWoman exDonkey exFree)
open Semantics.Dynamic.Core.DRSExpr

-- ════════════════════════════════════════════════════════════════
-- § 1. Semantic Interpretation
-- ════════════════════════════════════════════════════════════════

/-- Interpretation of relation symbols. -/
abbrev RelInterp (E : Type*) := Nat → List E → Prop

/-- Semantic interpretation: maps DRS syntax to DRS semantics.

Each syntactic DRS expression denotes a binary relation on assignments
(type `DRS (Assignment E)`), following the abbreviation clauses
ABB1–ABB4 (@cite{muskens-1996}, p. 157). -/
def interp {E : Type*} (rels : RelInterp E) : DRSExpr → DRS (Assignment E)
  | .atom rel drefs =>
    test (λ g => rels rel (drefs.map (λ i => g i)))
  | .is u v =>
    test (λ g => g u = g v)
  | .neg K =>
    test (dneg (interp rels K))
  | .disj K₁ K₂ =>
    test (ddisj (interp rels K₁) (interp rels K₂))
  | .impl K₁ K₂ =>
    test (dimpl (interp rels K₁) (interp rels K₂))
  | .box newDrefs conds =>
    let introduce := newDrefs.foldl
      (λ D n => dseq D (λ i j => ∃ e : E, j = i.update n e)) (λ i j => i = j)
    dseq introduce (interpConds rels conds)
  | .seq K₁ K₂ =>
    dseq (interp rels K₁) (interp rels K₂)
where
  interpConds (rels : RelInterp E) : List DRSExpr → DRS (Assignment E)
    | [] => λ i j => i = j
    | c :: cs => dseq (interp rels c) (interpConds rels cs)

-- ════════════════════════════════════════════════════════════════
-- § 2. Projection Drefs and Assignment Properties
-- ════════════════════════════════════════════════════════════════

/-- Projection dref: the n-th register value.

In @cite{muskens-1996}'s terminology, `projDref n` is the *variable register*
`uₙ` — the function that reads the n-th slot of an assignment. -/
def projDref {E : Type*} (n : Nat) : Dref (Assignment E) E := λ g => g n

/-- Updating at index n assigns the new value to the n-th projection dref.

This is the concrete version of `AssignmentStructure.extend_at` for
`Assignment E`: `uₙ(g[n ↦ e]) = e`. -/
theorem update_projDref_eq {E : Type*} (g : Assignment E) (n : Nat) (e : E) :
    projDref n (g.update n e) = e := by
  simp [projDref, Assignment.update]

/-- Updating at index n preserves other projection drefs.

Concrete version of `AssignmentStructure.extend_other`:
`uₘ(g[n ↦ e]) = uₘ(g)` when `n ≠ m`. -/
theorem update_projDref_ne {E : Type*} (g : Assignment E) (n m : Nat) (e : E) (h : n ≠ m) :
    projDref m (g.update n e) = projDref m g := by
  simp [projDref, Assignment.update, h.symm]

-- ════════════════════════════════════════════════════════════════
-- § 3. Structural Lemmas for DRS Composition
-- ════════════════════════════════════════════════════════════════

private theorem dseq_id_right {S : Type*} (D : DRS S) :
    dseq D (λ i j => i = j) = D := by
  funext i j; simp only [dseq, eq_iff_iff]
  exact ⟨λ ⟨_, h, rfl⟩ => h, λ h => ⟨j, h, rfl⟩⟩

private theorem id_dseq {S : Type*} (D : DRS S) :
    dseq (λ i j => i = j) D = D := by
  funext i j; simp only [dseq, eq_iff_iff]
  exact ⟨λ ⟨_, rfl, h⟩ => h, λ h => ⟨i, rfl, h⟩⟩

/-- `interpConds` distributes over list concatenation. -/
theorem interpConds_append {E : Type*} (rels : RelInterp E)
    (cs1 cs2 : List DRSExpr) :
    interp.interpConds rels (cs1 ++ cs2) =
    dseq (interp.interpConds rels cs1) (interp.interpConds rels cs2) := by
  induction cs1 with
  | nil => simp only [List.nil_append, interp.interpConds]; rw [id_dseq]
  | cons c cs1 ih => simp only [List.cons_append, interp.interpConds]; rw [ih, dseq_assoc]

/-- The dref introduction foldl distributes through `dseq`:
`foldl f A drefs = dseq A (foldl f id drefs)`. -/
private theorem foldl_dseq_shift {E : Type*} (A : DRS (Assignment E)) (drefs : List Nat) :
    List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e)) A drefs =
    dseq A (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
      (λ i j => i = j) drefs) := by
  induction drefs generalizing A with
  | nil => simp only [List.foldl]; rw [dseq_id_right]
  | cons d ds ih =>
    simp only [List.foldl]; rw [ih]
    conv_rhs => rw [ih]
    rw [dseq_assoc, id_dseq]

/-- Dref introduction over concatenation = sequencing of introductions. -/
theorem foldl_append_introduce {E : Type*} (drefs1 drefs2 : List Nat) :
    List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
      (λ i j => i = j) (drefs1 ++ drefs2) =
    dseq
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
        (λ i j => i = j) drefs1)
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
        (λ i j => i = j) drefs2) := by
  rw [List.foldl_append, foldl_dseq_shift]

-- ════════════════════════════════════════════════════════════════
-- § 3b. Freshness Invariance (FreshInv)
-- ════════════════════════════════════════════════════════════════

/-! When dref `n` does not occur in expression `K`, the DRS
`interp rels K` is semantically invariant under `Assignment.update` at
slot `n`: updating slot `n` in both input and output preserves the
relation (FreshFwd), and any output from an updated input factors
through an un-updated intermediate (FreshBack). -/

section FreshInv

variable {E : Type*}

private theorem update_comm (g : Assignment E) (n m : Nat) (e₁ e₂ : E) (h : n ≠ m) :
    (g.update n e₁).update m e₂ = (g.update m e₂).update n e₁ := by
  funext k; simp only [Assignment.update]; split <;> split <;> simp_all

private theorem occursAny_false (n : Nat) (cs : List DRSExpr)
    (h : occurs.occursAny n cs = false) : ∀ c ∈ cs, occurs n c = false := by
  induction cs with
  | nil => intro c hc; nomatch hc
  | cons c cs ih =>
    simp only [occurs.occursAny, Bool.or_eq_false_iff] at h
    intro c' hc'
    cases hc' with
    | head => exact h.1
    | tail _ hm => exact ih h.2 c' hm

private theorem freshFwd_dseq {D₁ D₂ : DRS (Assignment E)} {n : Nat}
    (h₁ : ∀ g k e, D₁ g k → D₁ (g.update n e) (k.update n e))
    (h₂ : ∀ g k e, D₂ g k → D₂ (g.update n e) (k.update n e)) :
    ∀ g k : Assignment E, ∀ e : E,
    dseq D₁ D₂ g k → dseq D₁ D₂ (g.update n e) (k.update n e) :=
  fun _ _ e ⟨m, hD₁, hD₂⟩ => ⟨m.update n e, h₁ _ m e hD₁, h₂ m _ e hD₂⟩

private theorem freshBack_dseq {D₁ D₂ : DRS (Assignment E)} {n : Nat}
    (h₁ : ∀ g k e, D₁ (g.update n e) k → ∃ k', D₁ g k' ∧ k = k'.update n e)
    (h₂ : ∀ g k e, D₂ (g.update n e) k → ∃ k', D₂ g k' ∧ k = k'.update n e) :
    ∀ g k : Assignment E, ∀ e : E,
    dseq D₁ D₂ (g.update n e) k →
    ∃ k', dseq D₁ D₂ g k' ∧ k = k'.update n e := by
  intro g k e ⟨m, hD₁, hD₂⟩
  obtain ⟨m', hD₁', rfl⟩ := h₁ g m e hD₁
  obtain ⟨k', hD₂', rfl⟩ := h₂ m' k e hD₂
  exact ⟨k', ⟨m', hD₁', hD₂'⟩, rfl⟩

private theorem freshInvConds (rels : RelInterp E) (cs : List DRSExpr) (n : Nat)
    (hfwd : ∀ c ∈ cs, ∀ g k : Assignment E, ∀ e,
      interp rels c g k → interp rels c (g.update n e) (k.update n e))
    (hback : ∀ c ∈ cs, ∀ g k : Assignment E, ∀ e,
      interp rels c (g.update n e) k →
      ∃ k', interp rels c g k' ∧ k = k'.update n e) :
    (∀ g k : Assignment E, ∀ e,
      interp.interpConds rels cs g k →
      interp.interpConds rels cs (g.update n e) (k.update n e)) ∧
    (∀ g k : Assignment E, ∀ e,
      interp.interpConds rels cs (g.update n e) k →
      ∃ k', interp.interpConds rels cs g k' ∧ k = k'.update n e) := by
  induction cs with
  | nil =>
    simp only [interp.interpConds]
    constructor
    · intro g k e h; subst h; rfl
    · intro g k e h; exact ⟨g, rfl, h.symm⟩
  | cons c cs ih =>
    simp only [interp.interpConds]
    obtain ⟨ihf, ihb⟩ := ih
      (fun c' hc' => hfwd c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hback c' (List.mem_cons_of_mem _ hc'))
    exact ⟨freshFwd_dseq (hfwd c List.mem_cons_self) ihf,
           freshBack_dseq (hback c List.mem_cons_self) ihb⟩

private theorem freshFwd_assign (n d : Nat) (hnd : n ≠ d)
    (g k : Assignment E) (e : E)
    (h : ∃ v : E, k = g.update d v) :
    ∃ v : E, k.update n e = (g.update n e).update d v := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨v, update_comm g d n v e hnd.symm⟩

private theorem freshBack_assign (n d : Nat) (hnd : n ≠ d)
    (g k : Assignment E) (e : E)
    (h : ∃ v : E, k = (g.update n e).update d v) :
    ∃ k', (∃ v : E, k' = g.update d v) ∧ k = k'.update n e := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨g.update d v, ⟨v, rfl⟩, (update_comm g d n v e hnd.symm).symm⟩

private theorem introChain_cons (d : Nat) (ds : List Nat) :
    List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
      (λ i j => i = j) (d :: ds) =
    dseq (λ i j => ∃ e : E, j = Assignment.update i d e)
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
        (λ i j => i = j) ds) := by
  simp only [List.foldl]; rw [foldl_dseq_shift, id_dseq]

private theorem introFreshInv (n : Nat) (drefs : List Nat)
    (h : ∀ d ∈ drefs, n ≠ d) :
    (∀ g k : Assignment E, ∀ e,
      List.foldl (λ D m => dseq D (λ i j => ∃ v : E, j = i.update m v))
        (λ i j => i = j) drefs g k →
      List.foldl (λ D m => dseq D (λ i j => ∃ v : E, j = i.update m v))
        (λ i j => i = j) drefs (g.update n e) (k.update n e)) ∧
    (∀ g k : Assignment E, ∀ e,
      List.foldl (λ D m => dseq D (λ i j => ∃ v : E, j = i.update m v))
        (λ i j => i = j) drefs (g.update n e) k →
      ∃ k', List.foldl (λ D m => dseq D (λ i j => ∃ v : E, j = i.update m v))
        (λ i j => i = j) drefs g k' ∧ k = k'.update n e) := by
  induction drefs with
  | nil =>
    simp only [List.foldl]
    exact ⟨fun _ _ _ h => by subst h; rfl,
           fun g _ _ h => ⟨g, rfl, h.symm⟩⟩
  | cons d ds ih =>
    have hd := h d List.mem_cons_self
    have hds := fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    obtain ⟨ihf, ihb⟩ := ih hds
    simp_rw [introChain_cons]
    exact ⟨freshFwd_dseq (fun g k e h => freshFwd_assign n d hd g k e h) ihf,
           freshBack_dseq (fun g k e h => freshBack_assign n d hd g k e h) ihb⟩

set_option maxHeartbeats 800000 in
private theorem freshInv (rels : RelInterp E) (K : DRSExpr) (n : Nat)
    (h : occurs n K = false) :
    (∀ g k : Assignment E, ∀ e, interp rels K g k →
      interp rels K (g.update n e) (k.update n e)) ∧
    (∀ g k : Assignment E, ∀ e, interp rels K (g.update n e) k →
      ∃ k', interp rels K g k' ∧ k = k'.update n e) := by
  match K with
  | .atom rel drefs =>
    simp only [occurs] at h
    have hmem : n ∉ drefs := fun hm =>
      absurd (List.contains_iff_mem.mpr hm) (Bool.eq_false_iff.mp h)
    have mapInv : ∀ g : Assignment E, ∀ e,
        List.map (fun i => (g.update n e) i) drefs = List.map (fun i => g i) drefs :=
      fun g e => List.map_congr_left fun i hi => by
        simp [Assignment.update]; intro heq; subst heq; exact absurd hi hmem
    constructor
    · intro g k e hgk
      simp only [interp, test] at hgk ⊢
      obtain ⟨rfl, hR⟩ := hgk
      exact ⟨rfl, by rwa [mapInv g e]⟩
    · intro g k e hgk
      simp only [interp, test] at hgk ⊢
      obtain ⟨rfl, hR⟩ := hgk
      exact ⟨g, ⟨rfl, by rwa [← mapInv g e]⟩, rfl⟩
  | .is u v =>
    simp only [occurs, Bool.or_eq_false_iff] at h
    have hu : u ≠ n := Ne.symm (by simpa using h.1)
    have hv : v ≠ n := Ne.symm (by simpa using h.2)
    constructor
    · intro g k e hgk
      simp only [interp, test] at hgk ⊢
      obtain ⟨rfl, hR⟩ := hgk
      exact ⟨rfl, show (g.update n e) u = (g.update n e) v by
        simp only [Assignment.update, if_neg hu, if_neg hv]; exact hR⟩
    · intro g k e hgk
      simp only [interp, test] at hgk ⊢
      obtain ⟨rfl, hR⟩ := hgk
      exact ⟨g, ⟨rfl, show g u = g v by
        have : (g.update n e) u = (g.update n e) v := hR
        simp only [Assignment.update, if_neg hu, if_neg hv] at this; exact this⟩, rfl⟩
  | .neg K' =>
    simp only [occurs] at h
    obtain ⟨fwd, back⟩ := freshInv rels K' n h
    constructor
    · intro g k e hgk
      simp only [interp, test, dneg] at hgk ⊢
      obtain ⟨rfl, hNeg⟩ := hgk
      exact ⟨rfl, fun ⟨k, hK⟩ => hNeg ⟨_, (back g k e hK).choose_spec.1⟩⟩
    · intro g k e hgk
      simp only [interp, test, dneg] at hgk ⊢
      obtain ⟨rfl, hNeg⟩ := hgk
      exact ⟨g, ⟨rfl, fun ⟨k, hK⟩ => hNeg ⟨_, fwd g k e hK⟩⟩, rfl⟩
  | .disj K₁ K₂ =>
    simp only [occurs, Bool.or_eq_false_iff] at h
    obtain ⟨fwd₁, back₁⟩ := freshInv rels K₁ n h.1
    obtain ⟨fwd₂, back₂⟩ := freshInv rels K₂ n h.2
    constructor
    · intro g k e hgk
      simp only [interp, test, ddisj] at hgk ⊢
      obtain ⟨rfl, k, hk⟩ := hgk
      refine ⟨rfl, ?_⟩
      cases hk with
      | inl hk => exact ⟨k.update n e, Or.inl (fwd₁ g k e hk)⟩
      | inr hk => exact ⟨k.update n e, Or.inr (fwd₂ g k e hk)⟩
    · intro g k e hgk
      simp only [interp, test, ddisj] at hgk ⊢
      obtain ⟨rfl, k, hk⟩ := hgk
      refine ⟨g, ⟨rfl, ?_⟩, rfl⟩
      cases hk with
      | inl hk => obtain ⟨k', hk', _⟩ := back₁ g k e hk; exact ⟨k', Or.inl hk'⟩
      | inr hk => obtain ⟨k', hk', _⟩ := back₂ g k e hk; exact ⟨k', Or.inr hk'⟩
  | .impl K₁ K₂ =>
    simp only [occurs, Bool.or_eq_false_iff] at h
    obtain ⟨fwd₁, back₁⟩ := freshInv rels K₁ n h.1
    obtain ⟨fwd₂, back₂⟩ := freshInv rels K₂ n h.2
    constructor
    · intro g k e hgk
      simp only [interp, test, dimpl] at hgk ⊢
      obtain ⟨rfl, himpl⟩ := hgk
      refine ⟨rfl, fun h' hK₁ => ?_⟩
      obtain ⟨h'', hK₁', rfl⟩ := back₁ g h' e hK₁
      obtain ⟨k, hK₂⟩ := himpl h'' hK₁'
      exact ⟨k.update n e, fwd₂ h'' k e hK₂⟩
    · intro g k e hgk
      simp only [interp, test, dimpl] at hgk ⊢
      obtain ⟨rfl, himpl⟩ := hgk
      refine ⟨g, ⟨rfl, fun h' hK₁ => ?_⟩, rfl⟩
      obtain ⟨k, hK₂⟩ := himpl (h'.update n e) (fwd₁ g h' e hK₁)
      obtain ⟨k', hK₂', _⟩ := back₂ h' k e hK₂
      exact ⟨k', hK₂'⟩
  | .seq K₁ K₂ =>
    simp only [occurs, Bool.or_eq_false_iff] at h
    obtain ⟨fwd₁, back₁⟩ := freshInv rels K₁ n h.1
    obtain ⟨fwd₂, back₂⟩ := freshInv rels K₂ n h.2
    constructor
    · intro g k e hgk
      simp only [interp] at hgk ⊢
      exact freshFwd_dseq fwd₁ fwd₂ g k e hgk
    · intro g k e hgk
      simp only [interp] at hgk ⊢
      exact freshBack_dseq back₁ back₂ g k e hgk
  | .box drefs conds =>
    simp only [occurs, Bool.or_eq_false_iff] at h
    have hcondsList := occursAny_false n conds h.2
    have hcFresh := fun c hc => freshInv rels c n (hcondsList c hc)
    obtain ⟨cfwd, cback⟩ := freshInvConds rels conds n
      (fun c hc => (hcFresh c hc).1) (fun c hc => (hcFresh c hc).2)
    have hdrefsList : ∀ d ∈ drefs, n ≠ d := by
      intro d hd heq; subst heq
      exact absurd (List.contains_iff_mem.mpr hd) (Bool.eq_false_iff.mp h.1)
    have ⟨ifwd, iback⟩ := @introFreshInv E n drefs hdrefsList
    constructor
    · intro g k e hgk
      simp only [interp] at hgk ⊢
      exact freshFwd_dseq ifwd cfwd g k e hgk
    · intro g k e hgk
      simp only [interp] at hgk ⊢
      exact freshBack_dseq iback cback g k e hgk
termination_by sizeOf K

-- ════════════════════════════════════════════════════════════════
-- § 3c. Commuting Lemma
-- ════════════════════════════════════════════════════════════════

/-- A DRS commutes with a single random assignment when FreshFwd
and FreshBack hold for the assigned slot. -/
private theorem drs_comm_assign (D : DRS (Assignment E)) (d : Nat)
    (hfwd : ∀ g k : Assignment E, ∀ e, D g k → D (g.update d e) (k.update d e))
    (hback : ∀ g k : Assignment E, ∀ e, D (g.update d e) k →
      ∃ k', D g k' ∧ k = k'.update d e) :
    dseq D (λ i j => ∃ e : E, j = i.update d e) =
    dseq (λ i j => ∃ e : E, j = i.update d e) D := by
  funext i j; apply propext; constructor
  · rintro ⟨h, hD, e, rfl⟩
    exact ⟨i.update d e, ⟨e, rfl⟩, hfwd i h e hD⟩
  · rintro ⟨h, ⟨e, rfl⟩, hD⟩
    obtain ⟨k', hD', rfl⟩ := hback i j e hD
    exact ⟨k', hD', e, rfl⟩

private theorem interpConds_comm_assign (rels : RelInterp E)
    (conds : List DRSExpr) (d : Nat)
    (hfresh : ∀ c ∈ conds, occurs d c = false) :
    dseq (interp.interpConds rels conds) (λ i j => ∃ e : E, j = i.update d e) =
    dseq (λ i j => ∃ e : E, j = i.update d e) (interp.interpConds rels conds) := by
  have hcFresh := fun c hc => freshInv rels c d (hfresh c hc)
  have ⟨cfwd, cback⟩ := freshInvConds rels conds d
    (fun c hc => (hcFresh c hc).1) (fun c hc => (hcFresh c hc).2)
  exact drs_comm_assign _ d cfwd cback

/-- `interpConds` commutes with a full dref introduction chain when
the introduced drefs do not occur in any condition. -/
private theorem interpConds_comm_introChain (rels : RelInterp E)
    (conds : List DRSExpr) (drefs : List Nat)
    (hfresh : ∀ n ∈ drefs, ∀ c ∈ conds, occurs n c = false) :
    dseq (interp.interpConds rels conds)
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = i.update n e))
        (λ i j => i = j) drefs) =
    dseq (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = i.update n e))
        (λ i j => i = j) drefs)
      (interp.interpConds rels conds) := by
  induction drefs with
  | nil => simp only [List.foldl]; rw [dseq_id_right, id_dseq]
  | cons d ds ih =>
    have hd : ∀ c ∈ conds, occurs d c = false := fun c hc => hfresh d List.mem_cons_self c hc
    have hds := fun n hn c hc => hfresh n (List.mem_cons_of_mem _ hn) c hc
    rw [introChain_cons]
    calc dseq (interp.interpConds rels conds)
            (dseq (λ i j => ∃ e : E, j = Assignment.update i d e)
              (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
                (λ i j => i = j) ds))
        = dseq (dseq (interp.interpConds rels conds)
            (λ i j => ∃ e : E, j = Assignment.update i d e))
            (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
              (λ i j => i = j) ds) := (dseq_assoc _ _ _).symm
      _ = dseq (dseq (λ i j => ∃ e : E, j = Assignment.update i d e)
            (interp.interpConds rels conds))
            (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
              (λ i j => i = j) ds) := by rw [interpConds_comm_assign rels conds d hd]
      _ = dseq (λ i j => ∃ e : E, j = Assignment.update i d e)
            (dseq (interp.interpConds rels conds)
              (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
                (λ i j => i = j) ds)) := dseq_assoc _ _ _
      _ = dseq (λ i j => ∃ e : E, j = Assignment.update i d e)
            (dseq (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
                (λ i j => i = j) ds)
              (interp.interpConds rels conds)) := by rw [ih hds]
      _ = dseq (dseq (λ i j => ∃ e : E, j = Assignment.update i d e)
            (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assignment.update i n e))
              (λ i j => i = j) ds))
            (interp.interpConds rels conds) := (dseq_assoc _ _ _).symm

end FreshInv

-- ════════════════════════════════════════════════════════════════
-- § 4. Merging Lemma
-- ════════════════════════════════════════════════════════════════

/-- Merging Lemma (@cite{muskens-1996}, p. 150).

If drefs `x'₁,...,x'ₖ` do not occur in any condition `γ₁,...,γₘ`, then
sequencing two boxes equals a single merged box:

  `⟦[x₁...xₙ|γ₁,...,γₘ]; [x'₁...x'ₖ|δ₁,...,δq]⟧`
  `= ⟦[x₁...xₙx'₁...x'ₖ|γ₁,...,γₘ,δ₁,...,δq]⟧`

This is used throughout §III.4 to simplify compositional derivations.

The proof reduces (via `foldl_append_introduce`, `interpConds_append`,
and `dseq_assoc`) to showing that condition tests commute with fresh
dref introductions. This commuting step requires a mutual induction
on `DRSExpr` proving that `interp rels c` is semantically invariant
under `Assignment.update` at slots not mentioned in `c`. -/
theorem mergingLemma {E : Type*} (rels : RelInterp E)
    (drefs1 drefs2 : List Nat) (conds1 conds2 : List DRSExpr)
    (hfresh : ∀ n ∈ drefs2, ∀ c ∈ conds1, occurs n c = false) :
    interp rels (.seq (.box drefs1 conds1) (.box drefs2 conds2)) =
    interp rels (.box (drefs1 ++ drefs2) (conds1 ++ conds2)) := by
  simp only [interp]
  rw [foldl_append_introduce, interpConds_append, dseq_assoc, dseq_assoc]
  congr 1
  rw [← dseq_assoc, interpConds_comm_introChain rels conds1 drefs2 hfresh, dseq_assoc]

-- ════════════════════════════════════════════════════════════════
-- § 4b. DRS Reduction (Merging to Canonical Form)
-- ════════════════════════════════════════════════════════════════

/-! Kamp & Reyle's *DRS reduction* — the operation that collapses
compositional `.seq (.box …) (.box …)` derivations into canonical
single-box form. This is Muskens's T₅ rule applied iteratively.

`reduce K` walks the `.seq` spine bottom-up: whenever two adjacent
boxes satisfy the freshness precondition of the merging lemma, they
are fused into one box. The soundness theorem says interpretation is
invariant: `interp rels (reduce K) = interp rels K`. -/

/-- Try to merge two DRS expressions. If both are boxes and the
freshness condition is met, fuse them; otherwise leave as `.seq`. -/
private def tryMerge : DRSExpr → DRSExpr → DRSExpr
  | .box d1 c1, .box d2 c2 =>
      if d2.all (fun n => c1.all (fun c => !occurs n c))
      then .box (d1 ++ d2) (c1 ++ c2)
      else .seq (.box d1 c1) (.box d2 c2)
  | r1, r2 => .seq r1 r2

/-- Reduce a DRS expression by iteratively merging sequential boxes.

Only reduces `.seq` chains (the discourse-composition spine).
Conditions inside boxes are left structurally intact — they don't
contain `.seq` in well-formed DRT derivations. -/
def reduce : DRSExpr → DRSExpr
  | .seq K₁ K₂ => tryMerge (reduce K₁) (reduce K₂)
  | K => K

private theorem tryMerge_sound {E : Type*} (rels : RelInterp E)
    (K₁ K₂ : DRSExpr) :
    interp rels (tryMerge K₁ K₂) = interp rels (.seq K₁ K₂) := by
  unfold tryMerge
  split
  · rename_i d1 c1 d2 c2
    split
    · rename_i hfresh
      have hf : ∀ n ∈ d2, ∀ c ∈ c1, occurs n c = false := by
        simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hfresh
        exact fun n hn c hc => hfresh n hn c hc
      exact (mergingLemma rels d1 d2 c1 c2 hf).symm
    · rfl
  · rfl

/-- DRS reduction preserves interpretation. -/
theorem reduce_sound {E : Type*} (rels : RelInterp E) :
    ∀ K : DRSExpr, interp rels (reduce K) = interp rels K
  | .atom _ _ | .is _ _ | .neg _ | .disj _ _ | .impl _ _ | .box _ _ => rfl
  | .seq K₁ K₂ => by
      show interp rels (tryMerge (reduce K₁) (reduce K₂)) = _
      rw [tryMerge_sound rels (reduce K₁) (reduce K₂)]
      show dseq (interp rels (reduce K₁)) (interp rels (reduce K₂)) =
           dseq (interp rels K₁) (interp rels K₂)
      rw [reduce_sound rels K₁, reduce_sound rels K₂]

-- ════════════════════════════════════════════════════════════════
-- § 5. Proposition 1
-- ════════════════════════════════════════════════════════════════

/-! ### Contextual properness

The syntactic `isProper` function (from `DRSExpr.lean`) has a soundness
gap: it conflates accessibility across disjunction branches, allowing
expressions like `[u₁|P(u₁)] ∨ [|Q(u₁)]` to pass even though `u₁` is
free in the second disjunct. The `allBound` check defined here tracks
bound drefs contextually and requires each disjunct to be independently
well-bound. -/

/-- Context-sensitive properness: every dref used in `K` must appear
in the bound set `B`. -/
def allBound : List Nat → DRSExpr → Bool
  | bound, .atom _ drefs => drefs.all (bound.contains ·)
  | bound, .is u v => bound.contains u && bound.contains v
  | bound, .neg K => allBound bound K
  | bound, .disj K₁ K₂ => allBound bound K₁ && allBound bound K₂
  | bound, .impl K₁ K₂ => allBound bound K₁ && allBound (bound ++ adr K₁) K₂
  | bound, .box drefs conds => allBoundConds (bound ++ drefs) conds
  | bound, .seq K₁ K₂ => allBound bound K₁ && allBound (bound ++ adr K₁) K₂
where
  allBoundConds : List Nat → List DRSExpr → Bool
    | _, [] => true
    | bound, c :: cs => allBound bound c && allBoundConds (bound ++ adr c) cs

example : allBound [] exManAdoresWoman = true := by decide
example : allBound [] exDonkey = true := by decide
example : allBound [] exFree = false := by decide

section Proposition1

variable {E : Type*} [Nonempty E]

/-- Two assignments agree on a set of slots. -/
private abbrev Agree (g₁ g₂ : Assignment E) (B : List Nat) : Prop :=
  ∀ n ∈ B, g₁ n = g₂ n

omit [Nonempty E] in
private theorem agree_symm {g₁ g₂ : Assignment E} {B : List Nat}
    (h : Agree g₁ g₂ B) : Agree g₂ g₁ B :=
  fun n hn => (h n hn).symm

omit [Nonempty E] in
private theorem agree_of_append_left {g₁ g₂ : Assignment E} {B₁ B₂ : List Nat}
    (h : Agree g₁ g₂ (B₁ ++ B₂)) : Agree g₁ g₂ B₁ :=
  fun n hn => h n (List.mem_append_left _ hn)

omit [Nonempty E] in
private theorem agree_update_same {g₁ g₂ : Assignment E} {B : List Nat} {n : Nat} {e : E}
    (h : Agree g₁ g₂ B) :
    Agree (g₁.update n e) (g₂.update n e) (B ++ [n]) := by
  intro m hm
  simp only [Assignment.update]
  split
  · rfl
  · rename_i hne
    exact h m (by
      rcases List.mem_append.mp hm with h | h
      · exact h
      · simp at h; exact absurd h hne)

omit [Nonempty E] in
/-- Introduction chain rebase: if two assignments agree on `B` and
a dref introduction chain from `g₁` produces `mid₁`, then the same
fresh values produce `mid₂` from `g₂` with agreement on `B ++ drefs`. -/
private theorem intro_rebase (drefs : List Nat) (B : List Nat)
    (g₁ g₂ : Assignment E) (mid₁ : Assignment E)
    (hagree : Agree g₁ g₂ B)
    (hintro : List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = i.update n e))
      (λ i j => i = j) drefs g₁ mid₁) :
    ∃ mid₂, List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = i.update n e))
      (λ i j => i = j) drefs g₂ mid₂ ∧ Agree mid₁ mid₂ (B ++ drefs) := by
  induction drefs generalizing B g₁ g₂ mid₁ with
  | nil =>
    simp only [List.foldl] at hintro ⊢
    subst hintro
    exact ⟨g₂, rfl, fun n hn => hagree n (by simpa using hn)⟩
  | cons d ds ih =>
    rw [introChain_cons] at hintro ⊢
    simp only [dseq] at hintro ⊢
    obtain ⟨mid₁', ⟨e₁, rfl⟩, hds₁⟩ := hintro
    have hagree' := agree_update_same (n := d) (e := e₁) hagree
    obtain ⟨mid₂, hds₂, hagree_out⟩ := ih (B ++ [d]) (g₁.update d e₁) (g₂.update d e₁)
      mid₁ hagree' hds₁
    refine ⟨mid₂, ⟨g₂.update d e₁, ⟨e₁, rfl⟩, hds₂⟩, fun n hn => ?_⟩
    exact hagree_out n (by rw [List.append_assoc]; exact hn)

omit [Nonempty E] in
/-- Condition list rebase: if a per-condition rebase hypothesis holds,
then `interpConds` transfers from `g₁` to `g₂` preserving agreement on `B`. -/
private theorem rebaseConds (rels : RelInterp E) (conds : List DRSExpr)
    (hRebase : ∀ c ∈ conds, ∀ (B : List Nat), allBound B c = true →
      ∀ g₁ g₂ : Assignment E, Agree g₁ g₂ B →
      ∀ j₁, interp rels c g₁ j₁ →
      ∃ j₂, interp rels c g₂ j₂ ∧ Agree j₁ j₂ (B ++ adr c)) :
    ∀ (B : List Nat),
    allBound.allBoundConds B conds = true →
    ∀ g₁ g₂ : Assignment E, Agree g₁ g₂ B →
    ∀ j₁, interp.interpConds rels conds g₁ j₁ →
    ∃ j₂, interp.interpConds rels conds g₂ j₂ ∧ Agree j₁ j₂ B := by
  induction conds with
  | nil =>
    intro B _ g₁ g₂ hagree j₁ hinterp
    simp only [interp.interpConds] at hinterp ⊢
    subst hinterp
    exact ⟨g₂, rfl, hagree⟩
  | cons c₀ cs ih =>
    intro B hB g₁ g₂ hagree j₁ hinterp
    simp only [allBound.allBoundConds, Bool.and_eq_true] at hB
    simp only [interp.interpConds, dseq] at hinterp ⊢
    obtain ⟨mid₁, hc₁, hcs₁⟩ := hinterp
    obtain ⟨mid₂, hc₂, hagree_mid⟩ := hRebase c₀ List.mem_cons_self B hB.1
      g₁ g₂ hagree mid₁ hc₁
    obtain ⟨j₂, hcs₂, hagree_j⟩ := ih
      (fun c' hc' => hRebase c' (List.mem_cons_of_mem c₀ hc'))
      (B ++ adr c₀) hB.2 mid₁ mid₂ hagree_mid j₁ hcs₁
    exact ⟨j₂, ⟨mid₂, hc₂, hcs₂⟩, agree_of_append_left hagree_j⟩

omit [Nonempty E] in
private theorem rebase_main (rels : RelInterp E) (K : DRSExpr) (B : List Nat)
    (hB : allBound B K = true) (g₁ g₂ : Assignment E) (hagree : Agree g₁ g₂ B)
    (j₁ : Assignment E) (hinterp : interp rels K g₁ j₁) :
    ∃ j₂, interp rels K g₂ j₂ ∧ Agree j₁ j₂ (B ++ adr K) := by
  match K with
  | .atom rel drefs =>
    simp only [interp, test] at hinterp ⊢
    obtain ⟨rfl, hR⟩ := hinterp
    simp only [allBound, List.all_eq_true, List.contains_iff_mem] at hB
    have : drefs.map g₁ = drefs.map g₂ :=
      List.map_congr_left (fun n hn => hagree n (hB n hn))
    exact ⟨g₂, ⟨rfl, this ▸ hR⟩, fun n hn => hagree n (by simpa [adr] using hn)⟩
  | .is u v =>
    simp only [interp, test] at hinterp ⊢
    obtain ⟨rfl, hR⟩ := hinterp
    simp only [allBound, Bool.and_eq_true, List.contains_iff_mem] at hB
    exact ⟨g₂, ⟨rfl, by rw [← hagree u hB.1, ← hagree v hB.2]; exact hR⟩,
      fun n hn => hagree n (by simpa [adr] using hn)⟩
  | .neg K' =>
    simp only [interp, test, dneg] at hinterp ⊢
    obtain ⟨rfl, hNeg⟩ := hinterp
    simp only [allBound] at hB
    refine ⟨g₂, ⟨rfl, fun ⟨k, hk⟩ => ?_⟩, fun n hn => hagree n (by simpa [adr] using hn)⟩
    obtain ⟨k', hk', _⟩ := rebase_main rels K' B hB g₂ g₁ (agree_symm hagree) k hk
    exact hNeg ⟨k', hk'⟩
  | .disj K₁ K₂ =>
    simp only [interp, test, ddisj] at hinterp ⊢
    obtain ⟨rfl, k, hk⟩ := hinterp
    simp only [allBound, Bool.and_eq_true] at hB
    refine ⟨g₂, ⟨rfl, ?_⟩, fun n hn => hagree n (by simpa [adr] using hn)⟩
    cases hk with
    | inl h =>
      obtain ⟨k', hk', _⟩ := rebase_main rels K₁ B hB.1 g₁ g₂ hagree k h
      exact ⟨k', Or.inl hk'⟩
    | inr h =>
      obtain ⟨k', hk', _⟩ := rebase_main rels K₂ B hB.2 g₁ g₂ hagree k h
      exact ⟨k', Or.inr hk'⟩
  | .impl K₁ K₂ =>
    simp only [interp, test, dimpl] at hinterp ⊢
    obtain ⟨rfl, himpl⟩ := hinterp
    simp only [allBound, Bool.and_eq_true] at hB
    refine ⟨g₂, ⟨rfl, fun h' hK₁h' => ?_⟩, fun n hn => hagree n (by simpa [adr] using hn)⟩
    obtain ⟨h, hK₁h, hagree_h⟩ := rebase_main rels K₁ B hB.1 g₂ g₁
      (agree_symm hagree) h' hK₁h'
    obtain ⟨k, hK₂k⟩ := himpl h hK₁h
    obtain ⟨k', hK₂k', _⟩ := rebase_main rels K₂ (B ++ adr K₁) hB.2 h h'
      (agree_symm hagree_h) k hK₂k
    exact ⟨k', hK₂k'⟩
  | .seq K₁ K₂ =>
    simp only [interp, dseq] at hinterp ⊢
    obtain ⟨mid₁, hK₁, hK₂⟩ := hinterp
    simp only [allBound, Bool.and_eq_true] at hB
    obtain ⟨mid₂, hK₁', hagree_mid⟩ := rebase_main rels K₁ B hB.1 g₁ g₂ hagree mid₁ hK₁
    obtain ⟨j₂, hK₂', hagree_j⟩ := rebase_main rels K₂ (B ++ adr K₁) hB.2 mid₁ mid₂
      hagree_mid j₁ hK₂
    refine ⟨j₂, ⟨mid₂, hK₁', hK₂'⟩, fun n hn => ?_⟩
    rcases List.mem_append.mp hn with hB' | hadr
    · exact hagree_j n (List.mem_append_left _ (List.mem_append_left _ hB'))
    · simp [adr] at hadr
      rcases hadr with h1 | h2
      · exact hagree_j n (List.mem_append_left _ (List.mem_append_right _ h1))
      · exact hagree_j n (List.mem_append_right _ h2)
  | .box drefs conds =>
    simp only [interp, dseq] at hinterp ⊢
    obtain ⟨mid₁, hintro₁, hconds₁⟩ := hinterp
    simp only [allBound] at hB
    obtain ⟨mid₂, hintro₂, hagree_mid⟩ := intro_rebase drefs B g₁ g₂ mid₁ hagree hintro₁
    have hPerCond : ∀ c ∈ conds, ∀ B' : List Nat, allBound B' c = true →
        ∀ g₁' g₂' : Assignment E, Agree g₁' g₂' B' →
        ∀ j₁', interp rels c g₁' j₁' →
        ∃ j₂', interp rels c g₂' j₂' ∧ Agree j₁' j₂' (B' ++ adr c) :=
      fun c _hc => rebase_main rels c
    obtain ⟨j₂, hconds₂, hagree_j⟩ := rebaseConds rels conds hPerCond (B ++ drefs) hB
      mid₁ mid₂ hagree_mid j₁ hconds₁
    exact ⟨j₂, ⟨mid₂, hintro₂, hconds₂⟩, fun n hn => by
      simp [adr] at hn
      rcases hn with hB' | hdrefs
      · exact hagree_j n (List.mem_append_left _ hB')
      · exact hagree_j n (List.mem_append_right _ hdrefs)⟩
termination_by K

end Proposition1

/-- Proposition 1 (@cite{muskens-1996}, p. 174).

A syntactically proper DRS (no free discourse referents) has
state-independent truth conditions: `wp(⟦K⟧, ⊤)` doesn't depend
on the input assignment.

This bridges syntactic properness (`allBound`) with semantic
properness (`WeakestPrecondition.isProper`). The proof uses a
rebase lemma: if all drefs in `K` are bound, then satisfaction
can be transferred between any two assignments. -/
theorem proposition_1 {E : Type*} [Nonempty E] (rels : RelInterp E) (K : DRSExpr)
    (hproper : allBound [] K = true) :
    WeakestPrecondition.isProper (interp rels K) := by
  intro g₁ g₂
  constructor
  · rintro ⟨j₁, hinterp⟩
    obtain ⟨j₂, hinterp₂, _⟩ := rebase_main rels K [] hproper g₁ g₂
      (fun _ h => nomatch h) j₁ hinterp
    exact ⟨j₂, hinterp₂⟩
  · rintro ⟨j₂, hinterp⟩
    obtain ⟨j₁, hinterp₁, _⟩ := rebase_main rels K [] hproper g₂ g₁
      (fun _ h => nomatch h) j₂ hinterp
    exact ⟨j₁, hinterp₁⟩

-- ════════════════════════════════════════════════════════════════
-- § 6. Cylindric Algebra Bridge
-- ════════════════════════════════════════════════════════════════

/-! ### Connection to cylindric algebras

The algebraic definitions (`cylindrify`, `invariantOn`, `cylClosed`,
`diagonal`, axioms C1–C7, substitution, derived theorems) live in
`CylindricAlgebra.lean`. This section re-exports them and adds the
DRT-specific bridge theorems that depend on `interp`/`closure`. -/

-- Re-export cylindric algebra definitions for backward compatibility
open _root_.Core.CylindricAlgebra

section CylindricBridge

variable {E : Type*}

/-- The truth condition of a DRS with `allBound B K` is invariant on
`B`: it only depends on the registers that `K` is allowed to read.

This is the support theorem: syntactic bound-checking (`allBound`)
correctly over-approximates semantic support. -/
theorem allBound_invariantOn [Nonempty E] (rels : RelInterp E) (K : DRSExpr)
    (B : List Nat) (hB : allBound B K = true) :
    invariantOn (closure (interp rels K)) B := by
  intro g₁ g₂ hagree
  constructor
  · rintro ⟨j₁, hinterp⟩
    obtain ⟨j₂, hinterp₂, _⟩ := rebase_main rels K B hB g₁ g₂ hagree j₁ hinterp
    exact ⟨j₂, hinterp₂⟩
  · rintro ⟨j₂, hinterp⟩
    obtain ⟨j₁, hinterp₁, _⟩ := rebase_main rels K B hB g₂ g₁
      (fun n hn => (hagree n hn).symm) j₂ hinterp
    exact ⟨j₁, hinterp₁⟩

private theorem update_self' (g : Assignment E) (n : Nat) : g.update n (g n) = g := by
  funext m; by_cases h : m = n <;> simp [Assignment.update, h]

/-- Per-register support theorem: if dref `n` does not occur in `K`,
then the truth condition of `K` is cylindrification-closed at `n`.

This connects `freshInv` (§3b) to the cylindric algebra vocabulary.
`occurs` is the per-register support checker, and `allBound` is
the global version. -/
theorem cylClosed_of_not_occurs [Nonempty E] (rels : RelInterp E) (K : DRSExpr)
    (n : Nat) (h : occurs n K = false) :
    cylClosed n (closure (interp rels K)) := by
  obtain ⟨fwd, back⟩ := freshInv rels K n h
  ext g; simp only [cylindrify, closure]; constructor
  · rintro ⟨e, k, hk⟩
    obtain ⟨k', hk', _⟩ := back g k e hk
    exact ⟨k', hk'⟩
  · rintro ⟨k, hk⟩
    exact ⟨g n, k, by rw [update_self']; exact hk⟩

/-- The DRS identity condition `is u v` denotes the diagonal element. -/
theorem interp_is_eq_diagonal (rels : RelInterp E) (u v : Nat) :
    closure (interp rels (.is u v)) = @diagonal E u v := by
  ext g; simp only [closure, interp, test, diagonal]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

/-- **Register introduction + D under closure = cylindrification.**

The DRS `[n]; D` (introduce dref `n` then continue with `D`),
under `closure`, equals `cₙ(closure(D))`: cylindrification at `n`.

This is the DRS-level analog of the DPL theorem
`closure(∃x.φ) = cₓ(closure(φ))`. -/
theorem closure_introReg_seq (n : Nat) (D : DRS (Assignment E)) :
    closure (dseq (fun g h => ∃ e : E, h = g.update n e) D) =
    cylindrify n (closure D) := by
  ext g; simp only [closure, dseq, cylindrify]; constructor
  · rintro ⟨h, ⟨k, ⟨e, rfl⟩, hD⟩⟩
    exact ⟨e, h, hD⟩
  · rintro ⟨e, h, hD⟩
    exact ⟨h, g.update n e, ⟨e, rfl⟩, hD⟩

/-- Register introduction alone under closure is trivially true
(given a nonempty entity type). `closure([n]) = ⊤`. -/
theorem closure_introReg [Nonempty E] (n : Nat) :
    closure (fun (g h : Assignment E) => ∃ e : E, h = g.update n e) =
    fun _ => True := by
  ext g; simp only [closure]; constructor
  · intro _; trivial
  · intro _; exact ⟨g.update n (Classical.arbitrary E), Classical.arbitrary E, rfl⟩

end CylindricBridge

end Semantics.Dynamic.Core.Accessibility
