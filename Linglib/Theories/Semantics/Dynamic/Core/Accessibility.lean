import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.Core.WeakestPrecondition

/-!
# DRS Syntax and Accessibility
@cite{muskens-1996}

§III.5 (pp. 170–171): Accessibility determines which discourse referents
can be anaphorically resolved. A dref `u` occurring in condition `γ`
within DRS `K` is *accessible* from `u`'s position if an earlier part
of `K` introduced `u`. A DRS with no *free* (inaccessible) referents
is called *proper*.

## Definitions

- `adr K`: active discourse referents (drefs introduced by `K`)
- `occurs u K`: whether dref `u` occurs in `K`
- `acc u K`: drefs accessible from `u`'s occurrence in `K`
- `isFree u K`: `u` occurs in `K` but is not accessible
- `isProper K`: no free referents

## Key Result

Proposition 1 (@cite{muskens-1996}, p. 174): A DRS `K` is proper
iff `wp(K, ⊤)` is a closed formula.
-/

namespace Semantics.Dynamic.Core.Accessibility

-- ════════════════════════════════════════════════════════════════
-- § 1. DRS Syntax
-- ════════════════════════════════════════════════════════════════

/-- Syntactic representation of DRS expressions.

Dref indices are natural numbers. Relation symbols are identified
by natural number indices; their arity is implicit in the dref list. -/
inductive DRSExpr where
  /-- Atomic condition: relation R applied to drefs -/
  | atom (rel : Nat) (drefs : List Nat) : DRSExpr
  /-- Identity condition: u₁ is u₂ -/
  | is (u v : Nat) : DRSExpr
  /-- Negation: not K -/
  | neg (K : DRSExpr) : DRSExpr
  /-- Disjunction: K₁ or K₂ -/
  | disj (K₁ K₂ : DRSExpr) : DRSExpr
  /-- Implication: K₁ ⇒ K₂ -/
  | impl (K₁ K₂ : DRSExpr) : DRSExpr
  /-- Box: [u₁,...,uₙ | γ₁,...,γₘ] -/
  | box (newDrefs : List Nat) (conds : List DRSExpr) : DRSExpr
  /-- Sequencing: K₁ ; K₂ -/
  | seq (K₁ K₂ : DRSExpr) : DRSExpr
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Active Discourse Referents
-- ════════════════════════════════════════════════════════════════

/-- Active discourse referents: the drefs *introduced* by `K`.

`adr([u₁,...,uₙ | γ₁,...,γₘ]) = {u₁,...,uₙ}`
`adr(K₁ ; K₂) = adr(K₁) ∪ adr(K₂)`

Conditions (atoms, negation, disjunction, implication) introduce no drefs. -/
def adr : DRSExpr → List Nat
  | .atom _ _ => []
  | .is _ _ => []
  | .neg _ => []
  | .disj _ _ => []
  | .impl _ _ => []
  | .box newDrefs _ => newDrefs
  | .seq K₁ K₂ => adr K₁ ++ adr K₂

-- ════════════════════════════════════════════════════════════════
-- § 3. Occurrence and Accessibility
-- ════════════════════════════════════════════════════════════════

/-- Whether dref `u` occurs anywhere in expression `K`. -/
def occurs (u : Nat) : DRSExpr → Bool
  | .atom _ drefs => drefs.contains u
  | .is v w => u == v || u == w
  | .neg K => occurs u K
  | .disj K₁ K₂ => occurs u K₁ || occurs u K₂
  | .impl K₁ K₂ => occurs u K₁ || occurs u K₂
  | .box newDrefs conds => newDrefs.contains u || occursAny u conds
  | .seq K₁ K₂ => occurs u K₁ || occurs u K₂
where
  occursAny (u : Nat) : List DRSExpr → Bool
    | [] => false
    | c :: cs => occurs u c || occursAny u cs

/-- Accessible drefs from an occurrence of `u` in `K`.

Defined by structural recursion following @cite{muskens-1996} pp. 170–171:
- Atomic: no drefs are accessible
- Negation: accessibility passes through
- Disjunction/implication: accessibility from the branch containing `u`,
  with antecedent drefs accessible in the consequent
- Box: new drefs are accessible, plus accessibility from the condition containing `u`
- Sequencing: drefs from `K₁` are accessible in `K₂` -/
def acc (u : Nat) : DRSExpr → List Nat
  | .atom _ _ => []
  | .is _ _ => []
  | .neg K => acc u K
  | .disj K₁ K₂ =>
    if occurs u K₁ then acc u K₁ else acc u K₂
  | .impl K₁ K₂ =>
    if occurs u K₁ then acc u K₁
    else acc u K₂ ++ adr K₁
  | .box newDrefs conds =>
    match accFind u conds with
    | some r => r ++ newDrefs
    | none => newDrefs
  | .seq K₁ K₂ =>
    if occurs u K₁ then acc u K₁
    else acc u K₂ ++ adr K₁
where
  /-- Find the first condition containing `u` and return its accessible drefs. -/
  accFind (u : Nat) : List DRSExpr → Option (List Nat)
    | [] => none
    | c :: cs => if occurs u c then some (acc u c) else accFind u cs

/-- Collect all dref indices mentioned anywhere in `K`. -/
def allOccurring : DRSExpr → List Nat
  | .atom _ drefs => drefs
  | .is v w => [v, w]
  | .neg K => allOccurring K
  | .disj K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
  | .impl K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
  | .box newDrefs conds => newDrefs ++ allOccurringList conds
  | .seq K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
where
  allOccurringList : List DRSExpr → List Nat
    | [] => []
    | c :: cs => allOccurring c ++ allOccurringList cs

/-- A dref `u` is *free* in `K` if it occurs in `K` but is not
among the drefs accessible from its position. -/
def isFree (u : Nat) (K : DRSExpr) : Bool :=
  occurs u K && !(acc u K).contains u

/-- A DRS is *proper* if it contains no free referents
(@cite{muskens-1996}, p. 171). -/
def isProper (K : DRSExpr) : Bool :=
  (allOccurring K).all (λ u => !(isFree u K))

-- ════════════════════════════════════════════════════════════════
-- § 4. Semantic Interpretation
-- ════════════════════════════════════════════════════════════════

open DynamicTy2

/-- Assignment type: dref indices map to entities. -/
abbrev Assign (E : Type*) := Nat → E

/-- Update an assignment at index `n`. -/
def Assign.update {E : Type*} (g : Assign E) (n : Nat) (e : E) : Assign E :=
  λ m => if m = n then e else g m

/-- Interpretation of relation symbols. -/
abbrev RelInterp (E : Type*) := Nat → List E → Prop

/-- Semantic interpretation: maps DRS syntax to DRS semantics.

Each syntactic DRS expression denotes a binary relation on assignments
(type `DRS (Assign E)`), following the abbreviation clauses
ABB1–ABB4 (@cite{muskens-1996}, p. 157). -/
def interp {E : Type*} (rels : RelInterp E) : DRSExpr → DRS (Assign E)
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
  interpConds (rels : RelInterp E) : List DRSExpr → DRS (Assign E)
    | [] => λ i j => i = j
    | c :: cs => dseq (interp rels c) (interpConds rels cs)

-- ════════════════════════════════════════════════════════════════
-- § 5. Verification Examples
-- ════════════════════════════════════════════════════════════════

/-- "A man adores a woman" as a syntactic DRS.

`[u₁ u₂ | man u₁, woman u₂, u₁ adores u₂]`

Using relation indices: 0 = man, 1 = woman, 2 = adores. -/
def exManAdoresWoman : DRSExpr :=
  .box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]]

/-- The example DRS is proper: all drefs (1, 2) are introduced by the box. -/
example : isProper exManAdoresWoman = true := by native_decide

/-- "If a farmer owns a donkey, he beats it" as a syntactic DRS.

`[u₁ u₂ | farmer u₁, donkey u₂, u₁ owns u₂] ⇒ [| u₁ beats u₂]`

Using relation indices: 0 = farmer, 1 = donkey, 2 = owns, 3 = beats. -/
def exDonkey : DRSExpr :=
  .impl
    (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
    (.box [] [.atom 3 [1, 2]])

/-- The donkey sentence is proper: drefs 1, 2 are introduced in the
antecedent and accessible in the consequent. -/
example : isProper exDonkey = true := by native_decide

/-- "He₁ stinks" (with no antecedent) is NOT proper: dref 1 is free. -/
def exFree : DRSExpr := .box [] [.atom 0 [1]]

example : isProper exFree = false := by native_decide

-- ════════════════════════════════════════════════════════════════
-- § 6. Projection Drefs and Assignment Properties
-- ════════════════════════════════════════════════════════════════

/-- Projection dref: the n-th register value.

In @cite{muskens-1996}'s terminology, `projDref n` is the *variable register*
`uₙ` — the function that reads the n-th slot of an assignment. -/
def projDref {E : Type*} (n : Nat) : Dref (Assign E) E := λ g => g n

/-- Updating at index n assigns the new value to the n-th projection dref.

This is the concrete version of `AssignmentStructure.extend_at` for
`Assign E`: `uₙ(g[n ↦ e]) = e`. -/
theorem update_projDref_eq {E : Type*} (g : Assign E) (n : Nat) (e : E) :
    projDref n (g.update n e) = e := by
  simp [projDref, Assign.update]

/-- Updating at index n preserves other projection drefs.

Concrete version of `AssignmentStructure.extend_other`:
`uₘ(g[n ↦ e]) = uₘ(g)` when `n ≠ m`. -/
theorem update_projDref_ne {E : Type*} (g : Assign E) (n m : Nat) (e : E) (h : n ≠ m) :
    projDref m (g.update n e) = projDref m g := by
  simp [projDref, Assign.update, h.symm]

-- ════════════════════════════════════════════════════════════════
-- § 7. Structural Lemmas for DRS Composition
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
private theorem foldl_dseq_shift {E : Type*} (A : DRS (Assign E)) (drefs : List Nat) :
    List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e)) A drefs =
    dseq A (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
      (λ i j => i = j) drefs) := by
  induction drefs generalizing A with
  | nil => simp only [List.foldl]; rw [dseq_id_right]
  | cons d ds ih =>
    simp only [List.foldl]; rw [ih]
    conv_rhs => rw [ih]
    rw [dseq_assoc, id_dseq]

/-- Dref introduction over concatenation = sequencing of introductions. -/
theorem foldl_append_introduce {E : Type*} (drefs1 drefs2 : List Nat) :
    List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
      (λ i j => i = j) (drefs1 ++ drefs2) =
    dseq
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
        (λ i j => i = j) drefs1)
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
        (λ i j => i = j) drefs2) := by
  rw [List.foldl_append, foldl_dseq_shift]

-- ════════════════════════════════════════════════════════════════
-- § 7b. Freshness Invariance (FreshInv)
-- ════════════════════════════════════════════════════════════════

/-! When dref `n` does not occur in expression `K`, the DRS
`interp rels K` is semantically invariant under `Assign.update` at
slot `n`: updating slot `n` in both input and output preserves the
relation (FreshFwd), and any output from an updated input factors
through an un-updated intermediate (FreshBack). -/

section FreshInv

variable {E : Type*}

private theorem update_comm (g : Assign E) (n m : Nat) (e₁ e₂ : E) (h : n ≠ m) :
    (g.update n e₁).update m e₂ = (g.update m e₂).update n e₁ := by
  funext k; simp only [Assign.update]; split <;> split <;> simp_all

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

private theorem freshFwd_dseq {D₁ D₂ : DRS (Assign E)} {n : Nat}
    (h₁ : ∀ g k e, D₁ g k → D₁ (g.update n e) (k.update n e))
    (h₂ : ∀ g k e, D₂ g k → D₂ (g.update n e) (k.update n e)) :
    ∀ g k : Assign E, ∀ e : E,
    dseq D₁ D₂ g k → dseq D₁ D₂ (g.update n e) (k.update n e) :=
  fun _ _ e ⟨m, hD₁, hD₂⟩ => ⟨m.update n e, h₁ _ m e hD₁, h₂ m _ e hD₂⟩

private theorem freshBack_dseq {D₁ D₂ : DRS (Assign E)} {n : Nat}
    (h₁ : ∀ g k e, D₁ (g.update n e) k → ∃ k', D₁ g k' ∧ k = k'.update n e)
    (h₂ : ∀ g k e, D₂ (g.update n e) k → ∃ k', D₂ g k' ∧ k = k'.update n e) :
    ∀ g k : Assign E, ∀ e : E,
    dseq D₁ D₂ (g.update n e) k →
    ∃ k', dseq D₁ D₂ g k' ∧ k = k'.update n e := by
  intro g k e ⟨m, hD₁, hD₂⟩
  obtain ⟨m', hD₁', rfl⟩ := h₁ g m e hD₁
  obtain ⟨k', hD₂', rfl⟩ := h₂ m' k e hD₂
  exact ⟨k', ⟨m', hD₁', hD₂'⟩, rfl⟩

private theorem freshInvConds (rels : RelInterp E) (cs : List DRSExpr) (n : Nat)
    (hfwd : ∀ c ∈ cs, ∀ g k : Assign E, ∀ e,
      interp rels c g k → interp rels c (g.update n e) (k.update n e))
    (hback : ∀ c ∈ cs, ∀ g k : Assign E, ∀ e,
      interp rels c (g.update n e) k →
      ∃ k', interp rels c g k' ∧ k = k'.update n e) :
    (∀ g k : Assign E, ∀ e,
      interp.interpConds rels cs g k →
      interp.interpConds rels cs (g.update n e) (k.update n e)) ∧
    (∀ g k : Assign E, ∀ e,
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
    (g k : Assign E) (e : E)
    (h : ∃ v : E, k = g.update d v) :
    ∃ v : E, k.update n e = (g.update n e).update d v := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨v, update_comm g d n v e hnd.symm⟩

private theorem freshBack_assign (n d : Nat) (hnd : n ≠ d)
    (g k : Assign E) (e : E)
    (h : ∃ v : E, k = (g.update n e).update d v) :
    ∃ k', (∃ v : E, k' = g.update d v) ∧ k = k'.update n e := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨g.update d v, ⟨v, rfl⟩, (update_comm g d n v e hnd.symm).symm⟩

private theorem introChain_cons (d : Nat) (ds : List Nat) :
    List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
      (λ i j => i = j) (d :: ds) =
    dseq (λ i j => ∃ e : E, j = Assign.update i d e)
      (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
        (λ i j => i = j) ds) := by
  simp only [List.foldl]; rw [foldl_dseq_shift, id_dseq]

private theorem introFreshInv (n : Nat) (drefs : List Nat)
    (h : ∀ d ∈ drefs, n ≠ d) :
    (∀ g k : Assign E, ∀ e,
      List.foldl (λ D m => dseq D (λ i j => ∃ v : E, j = i.update m v))
        (λ i j => i = j) drefs g k →
      List.foldl (λ D m => dseq D (λ i j => ∃ v : E, j = i.update m v))
        (λ i j => i = j) drefs (g.update n e) (k.update n e)) ∧
    (∀ g k : Assign E, ∀ e,
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
    (∀ g k : Assign E, ∀ e, interp rels K g k →
      interp rels K (g.update n e) (k.update n e)) ∧
    (∀ g k : Assign E, ∀ e, interp rels K (g.update n e) k →
      ∃ k', interp rels K g k' ∧ k = k'.update n e) := by
  match K with
  | .atom rel drefs =>
    simp only [occurs] at h
    have hmem : n ∉ drefs := fun hm =>
      absurd (List.contains_iff_mem.mpr hm) (Bool.eq_false_iff.mp h)
    have mapInv : ∀ g : Assign E, ∀ e,
        List.map (fun i => (g.update n e) i) drefs = List.map (fun i => g i) drefs :=
      fun g e => List.map_congr_left fun i hi => by
        simp [Assign.update]; intro heq; subst heq; exact absurd hi hmem
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
        simp only [Assign.update, if_neg hu, if_neg hv]; exact hR⟩
    · intro g k e hgk
      simp only [interp, test] at hgk ⊢
      obtain ⟨rfl, hR⟩ := hgk
      exact ⟨g, ⟨rfl, show g u = g v by
        have : (g.update n e) u = (g.update n e) v := hR
        simp only [Assign.update, if_neg hu, if_neg hv] at this; exact this⟩, rfl⟩
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
-- § 7c. Commuting Lemma
-- ════════════════════════════════════════════════════════════════

/-- A DRS commutes with a single random assignment when FreshFwd
and FreshBack hold for the assigned slot. -/
private theorem drs_comm_assign (D : DRS (Assign E)) (d : Nat)
    (hfwd : ∀ g k : Assign E, ∀ e, D g k → D (g.update d e) (k.update d e))
    (hback : ∀ g k : Assign E, ∀ e, D (g.update d e) k →
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
            (dseq (λ i j => ∃ e : E, j = Assign.update i d e)
              (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
                (λ i j => i = j) ds))
        = dseq (dseq (interp.interpConds rels conds)
            (λ i j => ∃ e : E, j = Assign.update i d e))
            (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
              (λ i j => i = j) ds) := (dseq_assoc _ _ _).symm
      _ = dseq (dseq (λ i j => ∃ e : E, j = Assign.update i d e)
            (interp.interpConds rels conds))
            (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
              (λ i j => i = j) ds) := by rw [interpConds_comm_assign rels conds d hd]
      _ = dseq (λ i j => ∃ e : E, j = Assign.update i d e)
            (dseq (interp.interpConds rels conds)
              (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
                (λ i j => i = j) ds)) := dseq_assoc _ _ _
      _ = dseq (λ i j => ∃ e : E, j = Assign.update i d e)
            (dseq (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
                (λ i j => i = j) ds)
              (interp.interpConds rels conds)) := by rw [ih hds]
      _ = dseq (dseq (λ i j => ∃ e : E, j = Assign.update i d e)
            (List.foldl (λ D n => dseq D (λ i j => ∃ e : E, j = Assign.update i n e))
              (λ i j => i = j) ds))
            (interp.interpConds rels conds) := (dseq_assoc _ _ _).symm

end FreshInv

-- ════════════════════════════════════════════════════════════════
-- § 8. Merging Lemma
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
under `Assign.update` at slots not mentioned in `c`. -/
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
-- § 9. Proposition 1
-- ════════════════════════════════════════════════════════════════

/-- Proposition 1 (@cite{muskens-1996}, p. 174).

A syntactically proper DRS (no free discourse referents) has
state-independent truth conditions: `wp(⟦K⟧, ⊤)` doesn't depend
on the input assignment.

This bridges syntactic properness (`Accessibility.isProper`) with
semantic properness (`WeakestPrecondition.isProper`).

The proof requires induction on `DRSExpr`, showing that `interp`
only reads registers through drefs that are either (1) introduced
by enclosing boxes or (2) universally quantified over by the wp
calculus. When all occurring drefs are accessible (properness),
the wp truth condition is closed and hence state-independent. -/
theorem proposition_1 {E : Type*} [Nonempty E] (rels : RelInterp E) (K : DRSExpr)
    (hproper : isProper K = true) :
    WeakestPrecondition.isProper (interp rels K) := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- § 10. Compositional Derivation and Truth-Condition Extraction
-- ════════════════════════════════════════════════════════════════

/-- Compositional derivation of "a¹ man adores a² woman".

The T₀–T₅ rules (@cite{muskens-1996}, pp. 165–167) produce a sequence
of two boxes. The derivation tree (39) yields:

  `[u₁ | man u₁] ; [u₂ | woman u₂, u₁ adores u₂]`

The first box introduces the subject's dref and checks the restrictor;
the second introduces the object's dref and checks both the object
restrictor and the VP relation. This is the pre-merge form — what
falls out of function application (T₂) and sequencing (T₃) before
T₅ REDUCTION collapses the boxes. -/
def exManAdoresWoman_compositional : DRSExpr :=
  .seq (.box [1] [.atom 0 [1]])
       (.box [2] [.atom 1 [2], .atom 2 [1, 2]])

/-- T₅ REDUCTION: the merging lemma collapses the compositional
derivation into the standard single-box DRS.

The sequenced boxes merge because dref 2 (introduced by the second
box) does not occur free in any condition of the first box (`man u₁`
only mentions dref 1). -/
theorem exManAdoresWoman_merge {E : Type*} (rels : RelInterp E) :
    interp rels exManAdoresWoman_compositional = interp rels exManAdoresWoman :=
  mergingLemma rels [1] [2] [.atom 0 [1]] [.atom 1 [2], .atom 2 [1, 2]]
    (by intro n hn c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn hc
        subst hn; subst hc; native_decide)

/-- Truth conditions via the compositional route.

Full pipeline: compositional derivation (T₀–T₄) → T₅ REDUCTION
(merging lemma) → wp truth-condition extraction, yielding the
expected first-order formula from @cite{muskens-1996}:

  `∃ e₁ e₂, man(e₁) ∧ woman(e₂) ∧ adores(e₁, e₂)` -/
theorem exManAdoresWoman_truthConditions {E : Type*} (rels : RelInterp E)
    (g : Assign E) :
    WeakestPrecondition.wp (interp rels exManAdoresWoman_compositional) (λ _ => True) g ↔
    ∃ e₁ e₂ : E, rels 0 [e₁] ∧ rels 1 [e₂] ∧ rels 2 [e₁, e₂] := by
  rw [exManAdoresWoman_merge]
  simp only [exManAdoresWoman, interp, interp.interpConds,
    WeakestPrecondition.wp, dseq, test, List.foldl, and_true, List.map]
  constructor
  · intro h
    obtain ⟨j, g₁, hintro, hconds⟩ := h
    obtain ⟨g₂, hg₂, e₂, rfl⟩ := hintro
    obtain ⟨g₃, rfl, e₁, rfl⟩ := hg₂
    obtain ⟨g₄, ⟨rfl, hR₁⟩, hrest⟩ := hconds
    obtain ⟨g₅, ⟨rfl, hR₂⟩, hrest2⟩ := hrest
    obtain ⟨g₆, ⟨rfl, hR₃⟩, rfl⟩ := hrest2
    simp [Assign.update] at hR₁ hR₂ hR₃
    exact ⟨e₁, e₂, hR₁, hR₂, hR₃⟩
  · intro ⟨e₁, e₂, hR₁, hR₂, hR₃⟩
    let g' := (g.update 1 e₁).update 2 e₂
    use g', g'
    exact ⟨⟨g.update 1 e₁, ⟨g, rfl, e₁, rfl⟩, e₂, rfl⟩,
      g', ⟨rfl, by simp [g', Assign.update]; exact hR₁⟩,
      g', ⟨rfl, by simp [g', Assign.update]; exact hR₂⟩,
      g', ⟨rfl, by simp [g', Assign.update]; exact hR₃⟩, rfl⟩

end Semantics.Dynamic.Core.Accessibility
