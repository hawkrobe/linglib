import Linglib.Theories.Syntax.Minimalism.Formal.HopfAlgebra

/-!
# Coassociativity of the Connes-Kreimer coproduct

Proves coassociativity `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` on H^c by reducing to the
**double-cut identity**: `Σ assoc(δ(P) ⊗ R) = Σ P ⊗ cutTermsSum(R)` summed over
admissible cuts `(P, R)` of a node.

The double-cut identity is proved combinatorially: both sides enumerate
**nested admissible cut pairs** `C₁ ⊆ C₂` in the subtree poset, grouped
differently. We show the two lists of triples `(F, G, Q)` are
**permutations** of each other (`List.Perm`), hence their mapped sums
into `Hc ⊗ (Hc ⊗ Hc)` are equal.

The proof factors into:
1. **Product-to-sum expansion**: `comulAlgHom(ofForest P)` = sum over
   `forestTerms P` (all ways to distribute trees in `P` between left and
   right tensor factors), proved by induction on `P`.
2. **Per-child permutation** (`childLHS c ~ childRHS c`): structural
   induction on `c` shows the LHS and RHS per-child triple lists are
   permutations. The key insight: `forestTerms(P_c)` choices for the LHS
   correspond to `extOptions(R_c)` inner cuts for the RHS.
3. **Factorization**: both `lhsTriples` and `nestedCutTriples` factor as
   filtered Cartesian products of per-child lists (up to `flatMap`
   reordering via `flatMap_comm_perm`).
4. **Assembly**: `lhsTriples ~ nestedCutTriples` by composing per-child
   perms through the factored product.

@cite{connes-marcolli-2008} Theorem 1.27,
@cite{marcolli-chomsky-berwick-2025} Lemma 1.2.10.
-/

set_option autoImplicit false
open scoped TensorProduct List
namespace Minimalism
open Hc

/-! ## §1. Forest splitting

A `TreeChoice` for tree `v` in a forest `P` selects one of three options
from `comulGen(v) = v⊗1 + 1⊗v + cutTermsSum(v)`:
- **left**: `v` goes to the left tensor factor
- **right**: `v` goes to the right tensor factor
- **cut `(F,Q)`**: forest `F` goes left, singleton `[Q]` goes right

`forestTerms P` enumerates all Cartesian products of per-tree choices. -/

def treeTerms (v : SyntacticObject) : List (Forest × Forest) :=
  [([v], []), ([], [v])] ++
  (cutTerms v).map fun ⟨F, Q⟩ => (F, [Q])

def forestTerms : Forest → List (Forest × Forest)
  | [] => [([], [])]
  | v :: rest =>
    (treeTerms v).flatMap fun ⟨lv, rv⟩ =>
      (forestTerms rest).map fun ⟨lr, rr⟩ => (lv ++ lr, rv ++ rr)

def nontrivialTerms (P : Forest) : List (Forest × Forest) :=
  (forestTerms P).filter fun ⟨l, r⟩ => !l.isEmpty && !r.isEmpty

theorem forestTerms_append (P₁ P₂ : Forest) :
    forestTerms (P₁ ++ P₂) =
    (forestTerms P₁).flatMap fun ⟨l₁, r₁⟩ =>
      (forestTerms P₂).map fun ⟨l₂, r₂⟩ => (l₁ ++ l₂, r₁ ++ r₂) := by
  induction P₁ with
  | nil =>
    simp only [List.nil_append, forestTerms, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact (List.map_id _).symm
  | cons v rest ih =>
    simp only [List.cons_append, forestTerms, ih]
    simp only [List.map_flatMap, List.map_map, Function.comp_def,
      List.flatMap_assoc, List.flatMap_map, List.append_assoc]

/-! ## §2. Algebraic bridge: comulAlgHom = sum of forestTerms

This section proves that the coproduct of a forest decomposes as
a sum over `forestTerms`, and that the reduced coproduct `δ(P)` equals
the sum over `nontrivialTerms` (excluding all-left and all-right). -/

private theorem allLeft_mem (P : Forest) : (P, []) ∈ forestTerms P := by
  induction P with
  | nil => simp [forestTerms]
  | cons v rest ih =>
    simp only [forestTerms, List.mem_flatMap, List.mem_map, Prod.exists]
    exact ⟨[v], [], by simp [treeTerms], rest, [], ih, by simp⟩

private theorem allRight_mem (P : Forest) : ([], P) ∈ forestTerms P := by
  induction P with
  | nil => simp [forestTerms]
  | cons v rest ih =>
    simp only [forestTerms, List.mem_flatMap, List.mem_map, Prod.exists]
    exact ⟨[], [v], by simp [treeTerms], [], rest, ih, by simp⟩

private theorem cutTerms_fst_ne_nil (v : SyntacticObject)
    (F : Forest) (Q : SyntacticObject) (h : (F, Q) ∈ cutTerms v) :
    F ≠ [] := by
  unfold cutTerms at h
  simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  intro heq; subst heq; simp at h

private theorem treeTerms_mem (v : SyntacticObject) (lv rv : Forest)
    (h : (lv, rv) ∈ treeTerms v) :
    (lv = [v] ∧ rv = []) ∨ (lv = [] ∧ rv = [v]) ∨
    (∃ F Q, (F, Q) ∈ cutTerms v ∧ lv = F ∧ rv = [Q]) := by
  unfold treeTerms at h
  rcases List.mem_append.mp h with h1 | h2
  · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h1
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (.inl ⟨rfl, rfl⟩)
  · simp only [List.mem_map, Prod.exists, Prod.mk.injEq] at h2
    obtain ⟨F, Q, hFQ, rfl, rfl⟩ := h2
    exact .inr (.inr ⟨F, Q, hFQ, rfl, rfl⟩)

private theorem right_nil_iff (P : Forest) (l : Forest)
    (h : (l, []) ∈ forestTerms P) : l = P := by
  induction P generalizing l with
  | nil => simp [forestTerms] at h; exact h
  | cons v rest ih =>
    simp only [forestTerms, List.mem_flatMap, List.mem_map, Prod.exists] at h
    obtain ⟨lv, rv, hlv, lr, rr, hlr, heq⟩ := h
    have ⟨hl, hr⟩ := Prod.mk.inj heq
    rw [List.append_eq_nil_iff] at hr
    obtain ⟨hrv, hrr⟩ := hr; subst hrv; subst hrr
    rcases treeTerms_mem v lv [] hlv with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨_, _, _, _, h⟩
    · rw [← hl, ih _ hlr]; simp
    · exact absurd h.symm (List.cons_ne_nil _ _)
    · exact absurd h.symm (List.cons_ne_nil _ _)

private theorem left_nil_iff (P : Forest) (r : Forest)
    (h : ([], r) ∈ forestTerms P) : r = P := by
  induction P generalizing r with
  | nil => simp [forestTerms] at h; exact h
  | cons v rest ih =>
    simp only [forestTerms, List.mem_flatMap, List.mem_map, Prod.exists] at h
    obtain ⟨lv, rv, hlv, lr, rr, hlr, heq⟩ := h
    have ⟨hl, hr⟩ := Prod.mk.inj heq
    rw [List.append_eq_nil_iff] at hl
    obtain ⟨hlv_nil, hlr_nil⟩ := hl; subst hlv_nil; subst hlr_nil
    rcases treeTerms_mem v [] rv hlv with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨F, Q, hFQ, h, _⟩
    · exact absurd h.symm (List.cons_ne_nil _ _)
    · rw [← hr, ih _ hlr]; simp
    · exact absurd h.symm (cutTerms_fst_ne_nil _ _ _ hFQ)

private theorem treeTerms_sum (v : SyntacticObject) :
    comulGen v = ((treeTerms v).map fun ⟨l, r⟩ =>
      ofForest l ⊗ₜ[ℤ] ofForest r).sum := by
  have ofTree_eq : ∀ T : SyntacticObject, ofTree T = ofForest [T] := fun _ => rfl
  unfold treeTerms
  rw [comulGen_eq_parts, cutTermsSum_eq_map_sum]
  simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append,
    List.map_map, Function.comp_def, List.map_nil, List.sum_nil, add_zero,
    ofForest_nil, ofTree_eq]

private theorem mul_list_sum_right (x : Hc ⊗[ℤ] Hc) (L : List (Hc ⊗[ℤ] Hc)) :
    x * L.sum = (L.map (x * ·)).sum := by
  induction L with
  | nil => simp [mul_zero]
  | cons hd tl ih => simp [mul_add, ih]

private theorem mul_list_sum_left (L : List (Hc ⊗[ℤ] Hc)) (x : Hc ⊗[ℤ] Hc) :
    L.sum * x = (L.map (· * x)).sum := by
  induction L with
  | nil => simp [zero_mul]
  | cons hd tl ih => simp [add_mul, ih]

private theorem sum_map_flatMap {M : Type*} [AddCommMonoid M] {α β : Type*}
    (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

set_option maxHeartbeats 1600000 in
theorem comul_forest_eq_terms (P : Forest) :
    comulAlgHom (ofForest P) =
    ((forestTerms P).map fun ⟨l, r⟩ => ofForest l ⊗ₜ[ℤ] ofForest r).sum := by
  induction P with
  | nil =>
    simp only [forestTerms, List.map, List.sum_cons, List.sum_nil, add_zero]
    rw [comulAlgHom_ofForest_nil, ofForest_nil]
    show (1 : Hc ⊗[ℤ] Hc) = (1 : Hc) ⊗ₜ[ℤ] (1 : Hc); rfl
  | cons v rest ih =>
    rw [comulAlgHom_ofForest_cons, treeTerms_sum v, ih, mul_list_sum_left]
    simp only [List.map_map, Function.comp_def, mul_list_sum_right]
    conv_rhs =>
      rw [show forestTerms (v :: rest) = (treeTerms v).flatMap fun ⟨lv, rv⟩ =>
        (forestTerms rest).map fun ⟨lr, rr⟩ => (lv ++ lr, rv ++ rr) from rfl]
    rw [sum_map_flatMap]
    simp only [List.map_map, Function.comp_def,
      Algebra.TensorProduct.tmul_mul_tmul, ← ofForest_append]

/-! ### Reduced coproduct and nontrivial terms -/

noncomputable def forestDelta (P : Forest) : Hc ⊗[ℤ] Hc :=
  comulAlgHom (ofForest P) - ofForest P ⊗ₜ[ℤ] 1 - 1 ⊗ₜ[ℤ] ofForest P

-- Filter helpers for the partition argument
private theorem filter_flatMap_map {α β : Type*} (L : List α) (f : α → List β)
    (P : β → Bool) :
    (L.flatMap f).filter P = L.flatMap fun a => (f a).filter P := by
  induction L with
  | nil => simp
  | cons hd tl ih => simp [List.filter_append, ih]

private theorem treeTerms_filter_right_nil (v : SyntacticObject) :
    (treeTerms v).filter (fun x => x.2 == ([] : Forest)) = [([v], [])] := by
  simp only [treeTerms, List.filter_append, List.filter_cons, List.filter_map]
  simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq, List.cons_ne_nil, ↓reduceCtorEq]
  simp only [List.filter_nil, List.append_nil]
  suffices ((cutTerms v).map fun ⟨F, Q⟩ => (F, [Q])).filter
      (fun x => x.2 == ([] : Forest)) = [] by simp [this]
  apply List.filter_eq_nil_iff.mpr
  intro ⟨F, r⟩ hmem
  simp only [List.mem_map, Prod.exists] at hmem
  obtain ⟨F', Q', _, rfl, rfl⟩ := hmem; simp

private theorem filter_map_snd_comm (L : List (Forest × Forest)) (f : Forest → Forest) :
    (L.map fun ⟨lr, rr⟩ => (f lr, rr)).filter (fun x => x.2 == ([] : Forest)) =
    (L.filter (fun x => x.2 == ([] : Forest))).map fun ⟨lr, rr⟩ => (f lr, rr) := by
  induction L with
  | nil => simp
  | cons hd tl ih => obtain ⟨lr, rr⟩ := hd; simp only [List.map_cons, List.filter_cons]; split <;> simp_all

private theorem flatMap_ite_filter_map (L : List (Forest × Forest))
    (f : Forest × Forest → Forest × Forest) :
    L.flatMap (fun x => if x.2 == ([] : Forest) then [f x] else []) =
    (L.filter (fun x => x.2 == ([] : Forest))).map f := by
  induction L with
  | nil => simp
  | cons hd tl ih => simp only [List.flatMap_cons, List.filter_cons]; split <;> simp_all

private theorem inner_filter_snd (lv rv : Forest) (rest : Forest)
    (ih : (forestTerms rest).filter (fun x => x.2 == ([] : Forest)) = [(rest, [])]) :
    ((forestTerms rest).map fun ⟨lr, rr⟩ => (lv ++ lr, rv ++ rr)).filter
      (fun x => x.2 == ([] : Forest)) =
    if rv == ([] : Forest) then [(lv ++ rest, ([] : Forest))] else [] := by
  split
  · next h =>
    rw [beq_iff_eq] at h; subst h
    simp only [List.nil_append, filter_map_snd_comm (forestTerms rest) (lv ++ ·), ih]
    simp
  · next h =>
    apply List.filter_eq_nil_iff.mpr
    intro ⟨a, b⟩ hmem
    simp only [List.mem_map, Prod.exists] at hmem
    obtain ⟨lr, rr, _, rfl, rfl⟩ := hmem
    simp only [beq_iff_eq, List.append_eq_nil_iff]
    intro ⟨_, _⟩; exact absurd (beq_iff_eq.mpr ‹rv = []›) h

private theorem forestTerms_filter_snd_nil (P : Forest) :
    (forestTerms P).filter (fun x => x.2 == ([] : Forest)) = [(P, [])] := by
  induction P with
  | nil => simp [forestTerms]
  | cons v rest ih =>
    simp only [forestTerms, filter_flatMap_map]
    have step : (treeTerms v).flatMap (fun x =>
        ((forestTerms rest).map fun ⟨lr, rr⟩ => (x.1 ++ lr, x.2 ++ rr)).filter
          (fun z => z.2 == ([] : Forest))) =
      (treeTerms v).flatMap (fun x =>
        if x.2 == ([] : Forest) then [(x.1 ++ rest, ([] : Forest))] else []) := by
      congr 1; funext ⟨lv, rv⟩; exact inner_filter_snd lv rv rest ih
    rw [step, flatMap_ite_filter_map, treeTerms_filter_right_nil]; simp

private theorem treeTerms_filter_left_nil' (v : SyntacticObject) :
    (treeTerms v).filter (fun x => x.1 == ([] : Forest)) = [([], [v])] := by
  simp only [treeTerms, List.filter_append, List.filter_cons]
  simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq, List.cons_ne_nil, ↓reduceCtorEq]
  simp only [List.filter_nil, List.append_nil, List.nil_append]
  suffices h : ((cutTerms v).map fun ⟨F, Q⟩ => (F, [Q])).filter
      (fun x => x.1 == ([] : Forest)) = [] by rw [h, List.append_nil]
  apply List.filter_eq_nil_iff.mpr
  intro ⟨F, r⟩ hmem
  simp only [List.mem_map, Prod.exists] at hmem
  obtain ⟨F', Q', hF', rfl, rfl⟩ := hmem
  simp only [beq_iff_eq]; exact cutTerms_fst_ne_nil _ _ _ hF'

private theorem filter_map_fst_comm (L : List (Forest × Forest)) (f : Forest → Forest) :
    (L.map fun ⟨lr, rr⟩ => (lr, f rr)).filter (fun x => x.1 == ([] : Forest)) =
    (L.filter (fun x => x.1 == ([] : Forest))).map fun ⟨lr, rr⟩ => (lr, f rr) := by
  induction L with
  | nil => simp
  | cons hd tl ih => obtain ⟨lr, rr⟩ := hd; simp only [List.map_cons, List.filter_cons]; split <;> simp_all

private theorem flatMap_ite_filter_map_fst (L : List (Forest × Forest))
    (f : Forest × Forest → Forest × Forest) :
    L.flatMap (fun x => if x.1 == ([] : Forest) then [f x] else []) =
    (L.filter (fun x => x.1 == ([] : Forest))).map f := by
  induction L with
  | nil => simp
  | cons hd tl ih => simp only [List.flatMap_cons, List.filter_cons]; split <;> simp_all

private theorem inner_filter_fst (lv rv : Forest) (rest : Forest)
    (ih : (forestTerms rest).filter (fun x => x.1 == ([] : Forest)) = [([], rest)]) :
    ((forestTerms rest).map fun ⟨lr, rr⟩ => (lv ++ lr, rv ++ rr)).filter
      (fun x => x.1 == ([] : Forest)) =
    if lv == ([] : Forest) then [(([] : Forest), rv ++ rest)] else [] := by
  split
  · next h =>
    rw [beq_iff_eq] at h; subst h
    simp only [List.nil_append, filter_map_fst_comm (forestTerms rest) (rv ++ ·), ih]
    simp
  · next h =>
    apply List.filter_eq_nil_iff.mpr
    intro ⟨a, b⟩ hmem
    simp only [List.mem_map, Prod.exists] at hmem
    obtain ⟨lr, rr, _, rfl, rfl⟩ := hmem
    simp only [beq_iff_eq, List.append_eq_nil_iff]
    intro ⟨_, _⟩; exact absurd (beq_iff_eq.mpr ‹lv = []›) h

private theorem forestTerms_filter_fst_nil (P : Forest) :
    (forestTerms P).filter (fun x => x.1 == ([] : Forest)) = [([], P)] := by
  induction P with
  | nil => simp [forestTerms]
  | cons v rest ih =>
    simp only [forestTerms, filter_flatMap_map]
    have step : (treeTerms v).flatMap (fun x =>
        ((forestTerms rest).map fun ⟨lr, rr⟩ => (x.1 ++ lr, x.2 ++ rr)).filter
          (fun z => z.1 == ([] : Forest))) =
      (treeTerms v).flatMap (fun x =>
        if x.1 == ([] : Forest) then [(([] : Forest), x.2 ++ rest)] else []) := by
      congr 1; funext ⟨lv, rv⟩; exact inner_filter_fst lv rv rest ih
    rw [step, flatMap_ite_filter_map_fst, treeTerms_filter_left_nil']; simp

private theorem sum_filter_add_not {M : Type*} [AddCommMonoid M] {α : Type*}
    (L : List α) (p : α → Bool) (f : α → M) :
    (L.map f).sum =
    ((L.filter p).map f).sum + ((L.filter (fun a => !p a)).map f).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    cases hp : p hd <;> simp [hp, ih] <;> abel

/-- `forestDelta P = Σ nontrivialTerms(P)` for nonempty forests. -/
theorem forestDelta_eq_nontrivial (P : Forest) (hP : P ≠ []) :
    forestDelta P =
    ((nontrivialTerms P).map fun ⟨l, r⟩ =>
      ofForest l ⊗ₜ[ℤ] ofForest r).sum := by
  unfold forestDelta nontrivialTerms
  rw [comul_forest_eq_terms]
  let f : Forest × Forest → Hc ⊗[ℤ] Hc := fun ⟨l, r⟩ => ofForest l ⊗ₜ[ℤ] ofForest r
  let p : Forest × Forest → Bool := fun ⟨l, r⟩ => !l.isEmpty && !r.isEmpty
  have partition := sum_filter_add_not (forestTerms P) p f
  suffices trivial_eq :
      (((forestTerms P).filter (fun a => !p a)).map f).sum =
      ofForest P ⊗ₜ[ℤ] (1 : Hc) + (1 : Hc) ⊗ₜ[ℤ] ofForest P by
    rw [partition]; rw [trivial_eq]; abel
  have trivial_split := sum_filter_add_not
    ((forestTerms P).filter (fun a => !p a))
    (fun x => x.2 == ([] : Forest)) f
  rw [trivial_split]
  have isEmpty_beq (l : Forest) : l.isEmpty = (l == ([] : Forest)) := by
    cases l <;> simp [List.isEmpty]
  have h1 : ((forestTerms P).filter (fun a => !p a)).filter
      (fun x => x.2 == ([] : Forest)) = [(P, [])] := by
    rw [List.filter_filter]
    have : (forestTerms P).filter (fun a => (a.2 == ([] : Forest)) && !p a) =
        (forestTerms P).filter (fun x => x.2 == ([] : Forest)) :=
      List.filter_congr (fun ⟨l, r⟩ _ => by
        simp only [p, isEmpty_beq]; cases (l == ([] : Forest)) <;> cases (r == ([] : Forest)) <;> simp)
    rw [this]; exact forestTerms_filter_snd_nil P
  have h2 : ((forestTerms P).filter (fun a => !p a)).filter
      (fun x => !(x.2 == ([] : Forest))) = [([], P)] := by
    rw [List.filter_filter]
    have : (forestTerms P).filter (fun a => !(a.2 == ([] : Forest)) && !p a) =
        (forestTerms P).filter (fun x => x.1 == ([] : Forest)) :=
      List.filter_congr (fun ⟨l, r⟩ hmem => by
        simp only [p, isEmpty_beq]
        cases hl : (l == ([] : Forest)) <;> cases hr : (r == ([] : Forest)) <;>
          simp [hl, hr]
        rw [beq_iff_eq] at hl hr; subst hl; subst hr
        exact absurd (right_nil_iff P [] hmem).symm hP)
    rw [this]; exact forestTerms_filter_fst_nil P
  rw [h1, h2]; simp [f, ofForest_nil]

/-! ## §3. LHS triples and the algebraic bridge

Connect `forestDeltaTmul P R` (the non-structural coproduct part tensored
with `R`, reassociated) to a sum over `lhsTriples`. -/

/-- Distribute `assoc ∘ (· ⊗ₜ R)` over sums. -/
private theorem assoc_tmul_list_sum (L : List (Hc ⊗[ℤ] Hc)) (R : SyntacticObject) :
    (TensorProduct.assoc ℤ Hc Hc Hc) (L.sum ⊗ₜ[ℤ] ofTree R) =
    (L.map fun t => (TensorProduct.assoc ℤ Hc Hc Hc) (t ⊗ₜ[ℤ] ofTree R)).sum := by
  induction L with
  | nil => simp [TensorProduct.zero_tmul, map_zero]
  | cons hd tl ih => simp [TensorProduct.add_tmul, map_add, ih]

/-- All LHS triples `(l, r, R)` of `node a b`:
    outer cut gives `(P, R)`, nontrivial forest term of `P` gives `(l, r)`. -/
def lhsTriples (a b : SyntacticObject) :
    List (Forest × Forest × SyntacticObject) :=
  (cutTerms (.node a b)).flatMap fun ⟨P, R⟩ =>
    (nontrivialTerms P).map fun ⟨l, r⟩ => (l, r, R)

private theorem cutTerms_nonempty (T : SyntacticObject) (P : Forest)
    (R : SyntacticObject) (h : (P, R) ∈ cutTerms T) : P ≠ [] := by
  unfold cutTerms at h
  simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  intro heq; subst heq; simp at h

namespace Hc

/-- Non-structural part of `Δ(ofForest P)` tensored with `R`, reassociated.
    `forestDeltaTmul P R = assoc((Δ(P) - P⊗1 - 1⊗P) ⊗ R)`. -/
private noncomputable def forestDeltaTmul (P : Forest) (R : SyntacticObject) :
    Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc) :=
  (TensorProduct.assoc ℤ Hc Hc Hc) (forestDelta P ⊗ₜ[ℤ] ofTree R)

private theorem forestDeltaTmul_eq_nontrivial_sum (P : Forest) (hP : P ≠ [])
    (R : SyntacticObject) :
    forestDeltaTmul P R =
    ((nontrivialTerms P).map fun ⟨l, r⟩ =>
      ofForest l ⊗ₜ[ℤ] (ofForest r ⊗ₜ[ℤ] ofTree R)).sum := by
  unfold forestDeltaTmul
  rw [forestDelta_eq_nontrivial P hP, assoc_tmul_list_sum, List.map_map]; rfl

/-- LHS of double-cut identity = sum of lhsTriples mapped to tensors. -/
theorem lhs_eq_lhsTriples (a b : SyntacticObject) :
    ((cutTerms (.node a b)).map fun ⟨P, R⟩ => forestDeltaTmul P R).sum =
    ((lhsTriples a b).map fun t =>
      ofForest t.1 ⊗ₜ[ℤ] (ofForest t.2.1 ⊗ₜ[ℤ] ofTree t.2.2)).sum := by
  unfold lhsTriples
  rw [sum_map_flatMap]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_eq_map_iff.mpr
  intro ⟨P, R⟩ hPR
  exact forestDeltaTmul_eq_nontrivial_sum P (cutTerms_nonempty _ P R hPR) R

end Hc

/-! ## §4. Nested cut triples (RHS)

Both sides of the double-cut identity enumerate **nested admissible cut pairs**
`C₁ ⊆ C₂` in the subtree poset, producing triples `(F₁, F₂, Q)`. The
RHS groups by the outer cut `C₁`; the LHS groups by the outer cut `C₂`.
We define the common flattened sum and prove both sides equal it. -/

namespace Hc

/-- All nested cut triples `(P, F₂, Q)` of `node a b`:
    outer cut gives `(P, R)`, inner cut of `R` gives `(F₂, Q)`. -/
def nestedCutTriples (a b : SyntacticObject) :
    List (Forest × Forest × SyntacticObject) :=
  (cutTerms (.node a b)).flatMap fun ⟨P, R⟩ =>
    (cutTerms R).map fun ⟨F₂, Q⟩ => (P, F₂, Q)

/-- Sum over nested cut triples. -/
noncomputable def nestedCutSum (a b : SyntacticObject) :
    Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc) :=
  ((nestedCutTriples a b).map fun t =>
    ofForest t.1 ⊗ₜ[ℤ] (ofForest t.2.1 ⊗ₜ[ℤ] ofTree t.2.2)).sum

/-- RHS of double-cut identity equals nestedCutSum. -/
theorem rhs_eq_nestedCutSum (a b : SyntacticObject) :
    doubleCutSum a b = nestedCutSum a b := by
  rw [doubleCutSum_eq_map_sum]
  unfold nestedCutSum nestedCutTriples
  suffices h : ∀ L : List (Forest × SyntacticObject),
      (L.map fun x => ofForest x.1 ⊗ₜ[ℤ] cutTermsSum x.2).sum =
      ((L.flatMap fun x =>
        (cutTerms x.2).map fun y => (x.1, y.1, y.2)).map fun t =>
        ofForest t.1 ⊗ₜ[ℤ] (ofForest t.2.1 ⊗ₜ[ℤ] ofTree t.2.2)).sum by
    exact h _
  intro L
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
      List.map_append, List.sum_append]
    rw [cutTermsSum_eq_map_sum, tmul_list_sum]
    simp only [List.map_map, Function.comp_def, ih]

end Hc

/-! ## §5. Permutation machinery

The core combinatorial engine: swapping nested `flatMap` iteration order
preserves the list up to permutation. -/

theorem flatMap_comm_perm {α β γ : Type*}
    (M : List α) (N : List β) (f : α → β → List γ) :
    M.flatMap (fun a => N.flatMap (fun b => f a b))
    ~ N.flatMap (fun b => M.flatMap (fun a => f a b)) := by
  induction M with
  | nil => simp
  | cons a M' ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left (N.flatMap (f a))).trans
      (List.flatMap_append_perm N (f a)
        (fun b => M'.flatMap (fun a' => f a' b)))

/-! ## §6. Per-child triple lists

For each child `c`, define:
- `childLHS c`: outer cut of `c` + forest splitting of the cut forest
- `childRHS c`: outer cut of `c` + inner cut of the residual -/

def childLHS (c : SyntacticObject) :
    List (Forest × Forest × SyntacticObject) :=
  (extOptions c).flatMap fun ⟨Pc, Rc⟩ =>
    (forestTerms Pc).map fun ⟨lc, rc⟩ => (lc, rc, Rc)

def childRHS (c : SyntacticObject) :
    List (Forest × Forest × SyntacticObject) :=
  (extOptions c).flatMap fun ⟨Pc, Rc⟩ =>
    (extOptions Rc).map fun ⟨F₂c, Qc⟩ => (Pc, F₂c, Qc)

/-! ## §7. Structural lemmas for per-child decomposition -/

private abbrev qLeaf : SyntacticObject := .leaf quotientLeafToken

theorem extOptions_leaf' (tok : LIToken) :
    extOptions (.leaf tok) = [([], .leaf tok)] := by
  unfold extOptions cutOptions; simp

theorem childLHS_leaf (tok : LIToken) :
    childLHS (.leaf tok) = [([], [], .leaf tok)] := by
  unfold childLHS; rw [extOptions_leaf']; simp [forestTerms]

theorem childRHS_leaf (tok : LIToken) :
    childRHS (.leaf tok) = [([], [], .leaf tok)] := by
  unfold childRHS; rw [extOptions_leaf']; simp [extOptions_leaf']

/-! ## §8. Node decomposition into A/B parts

`childLHS(node c₁ c₂) = A_L ++ B_L` and `childRHS(node c₁ c₂) = prod_R ++ B_R`,
where:
- `A_L`/`A_R1`: entries from `cutOptions` (proper cuts of `c`)
- `B_L`/`B_R`: entry from `([c], qLeaf)` (cut-entirely)
- `A_R2`: extra entries from `extOptions(node Ra Rb)` vs `cutOptions`
- `prod_R ~ A_R1 ++ A_R2` -/

private def A_L (c₁ c₂ : SyntacticObject) :=
  (extOptions c₁).flatMap fun ⟨Pa, Ra⟩ =>
    (extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
      (forestTerms (Pa ++ Pb)).map fun ⟨l, r⟩ =>
        (l, r, SyntacticObject.node Ra Rb)

private def B_L (c₁ c₂ : SyntacticObject) :=
  (forestTerms [SyntacticObject.node c₁ c₂]).map fun ⟨l, r⟩ => (l, r, qLeaf)

private def prod_R (c₁ c₂ : SyntacticObject) :=
  (extOptions c₁).flatMap fun ⟨Pa, Ra⟩ =>
    (extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
      (extOptions (SyntacticObject.node Ra Rb)).map fun ⟨F₂, Q⟩ =>
        (Pa ++ Pb, F₂, Q)

private def A_R1 (c₁ c₂ : SyntacticObject) :=
  (extOptions c₁).flatMap fun ⟨Pa, Ra⟩ =>
    (extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
      (cutOptions (SyntacticObject.node Ra Rb)).map fun ⟨F₂, Q⟩ =>
        (Pa ++ Pb, F₂, Q)

private def A_R2 (c₁ c₂ : SyntacticObject) :=
  (extOptions c₁).flatMap fun ⟨Pa, Ra⟩ =>
    (extOptions c₂).map fun ⟨Pb, Rb⟩ =>
      (Pa ++ Pb, [SyntacticObject.node Ra Rb], qLeaf)

private def B_R (c₁ c₂ : SyntacticObject) :=
  [([SyntacticObject.node c₁ c₂], ([] : Forest), qLeaf)]

theorem childLHS_node_eq (c₁ c₂ : SyntacticObject) :
    childLHS (.node c₁ c₂) = A_L c₁ c₂ ++ B_L c₁ c₂ := by
  unfold childLHS A_L B_L
  show (extOptions (.node c₁ c₂)).flatMap _ = _
  rw [show extOptions (.node c₁ c₂) =
      cutOptions (.node c₁ c₂) ++ [([.node c₁ c₂], qLeaf)] from rfl]
  rw [List.flatMap_append]
  congr 1
  · rw [cutOptions_node c₁ c₂, List.flatMap_assoc]
    congr 1; funext ⟨Pa, Ra⟩; rw [List.flatMap_map]
  · simp

theorem childRHS_node_eq (c₁ c₂ : SyntacticObject) :
    childRHS (.node c₁ c₂) = prod_R c₁ c₂ ++ B_R c₁ c₂ := by
  unfold childRHS prod_R B_R
  show (extOptions (.node c₁ c₂)).flatMap _ = _
  rw [show extOptions (.node c₁ c₂) =
      cutOptions (.node c₁ c₂) ++ [([.node c₁ c₂], qLeaf)] from rfl]
  rw [List.flatMap_append]
  congr 1
  rw [cutOptions_node c₁ c₂, List.flatMap_assoc]
  congr 1; funext ⟨Pa, Ra⟩; rw [List.flatMap_map]

private theorem extOptions_node_map_split (Ra Rb : SyntacticObject)
    {γ : Type*} (f : Forest × SyntacticObject → γ) :
    (extOptions (.node Ra Rb)).map f =
    (cutOptions (.node Ra Rb)).map f ++ [f ([.node Ra Rb], qLeaf)] := by
  show (cutOptions _ ++ _).map _ = _; rw [List.map_append]; rfl

theorem prod_R_perm_A_R1_A_R2 (c₁ c₂ : SyntacticObject) :
    prod_R c₁ c₂ ~ A_R1 c₁ c₂ ++ A_R2 c₁ c₂ := by
  unfold prod_R A_R1 A_R2
  have inner_split : ∀ Pa (Ra : SyntacticObject),
      ((extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
        (extOptions (.node Ra Rb)).map fun ⟨F₂, Q⟩ => (Pa ++ Pb, F₂, Q))
      ~ ((extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
          (cutOptions (.node Ra Rb)).map fun ⟨F₂, Q⟩ => (Pa ++ Pb, F₂, Q))
        ++ ((extOptions c₂).map fun ⟨Pb, Rb⟩ =>
          (Pa ++ Pb, [SyntacticObject.node Ra Rb], qLeaf)) := by
    intro Pa Ra
    calc (extOptions c₂).flatMap (fun ⟨Pb, Rb⟩ =>
          (extOptions (.node Ra Rb)).map fun ⟨F₂, Q⟩ => (Pa ++ Pb, F₂, Q))
      _ = (extOptions c₂).flatMap (fun ⟨Pb, Rb⟩ =>
            ((cutOptions (.node Ra Rb)).map fun ⟨F₂, Q⟩ => (Pa ++ Pb, F₂, Q))
            ++ [(Pa ++ Pb, [SyntacticObject.node Ra Rb], qLeaf)]) := by
          congr 1; funext ⟨Pb, Rb⟩; exact extOptions_node_map_split Ra Rb _
      _ ~ ((extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
            (cutOptions (.node Ra Rb)).map fun ⟨F₂, Q⟩ => (Pa ++ Pb, F₂, Q))
          ++ ((extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
            [(Pa ++ Pb, [SyntacticObject.node Ra Rb], qLeaf)]) :=
          (List.flatMap_append_perm _ _ _).symm
      _ = _ := by congr 1; exact List.map_eq_flatMap.symm
  exact (List.Perm.flatMap_left (l := extOptions c₁)
      fun ⟨Pa, Ra⟩ _ => inner_split Pa Ra).trans
    (List.flatMap_append_perm (extOptions c₁) _ _).symm

/-! ## §9. A_L ~ A_R1 via canonical 4-deep form

Both `A_L` and `A_R1` can be rewritten into a 4-deep nested `flatMap`
over the same index sets (extOptions of both children × inner choices).
The only difference is iteration order of the middle two levels, which
`flatMap_comm_perm` handles. -/

private def unfilteredTripleProduct
    (L₁ L₂ : List (Forest × Forest × SyntacticObject)) :=
  L₁.flatMap fun ⟨l₁, r₁, R₁⟩ =>
    L₂.map fun ⟨l₂, r₂, R₂⟩ =>
      (l₁ ++ l₂, r₁ ++ r₂, SyntacticObject.node R₁ R₂)

private theorem unfilteredTripleProduct_perm
    {L₁ L₁' L₂ L₂' : List (Forest × Forest × SyntacticObject)}
    (h₁ : L₁ ~ L₁') (h₂ : L₂ ~ L₂') :
    unfilteredTripleProduct L₁ L₂ ~ unfilteredTripleProduct L₁' L₂' := by
  unfold unfilteredTripleProduct
  exact List.Perm.flatMap h₁ (fun ⟨_, _, _⟩ _ => h₂.map _)

private def canonical_L (c₁ c₂ : SyntacticObject) :=
  (extOptions c₁).flatMap fun ⟨Pa, Ra⟩ =>
    (forestTerms Pa).flatMap fun ⟨la, ra⟩ =>
      (extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
        (forestTerms Pb).map fun ⟨lb, rb⟩ =>
          (la ++ lb, ra ++ rb, SyntacticObject.node Ra Rb)

private theorem A_L_perm_canonical (c₁ c₂ : SyntacticObject) :
    A_L c₁ c₂ ~ canonical_L c₁ c₂ := by
  unfold A_L canonical_L
  apply List.Perm.flatMap_left
  intro ⟨Pa, Ra⟩ _
  simp_rw [forestTerms_append]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  exact flatMap_comm_perm (extOptions c₂) (forestTerms Pa)
    (fun ⟨Pb, Rb⟩ ⟨la, ra⟩ =>
      (forestTerms Pb).map fun ⟨lb, rb⟩ =>
        (la ++ lb, ra ++ rb, SyntacticObject.node Ra Rb))

private theorem product_eq_canonical (c₁ c₂ : SyntacticObject) :
    unfilteredTripleProduct (childLHS c₁) (childLHS c₂) = canonical_L c₁ c₂ := by
  unfold unfilteredTripleProduct childLHS canonical_L
  simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem A_L_perm_product (c₁ c₂ : SyntacticObject) :
    A_L c₁ c₂ ~ unfilteredTripleProduct (childLHS c₁) (childLHS c₂) := by
  rw [product_eq_canonical]; exact A_L_perm_canonical c₁ c₂

private def canonical_R (c₁ c₂ : SyntacticObject) :=
  (extOptions c₁).flatMap fun ⟨Pa, Ra⟩ =>
    (extOptions Ra).flatMap fun ⟨F2a, Qa⟩ =>
      (extOptions c₂).flatMap fun ⟨Pb, Rb⟩ =>
        (extOptions Rb).map fun ⟨F2b, Qb⟩ =>
          (Pa ++ Pb, F2a ++ F2b, SyntacticObject.node Qa Qb)

private theorem A_R1_perm_canonical (c₁ c₂ : SyntacticObject) :
    A_R1 c₁ c₂ ~ canonical_R c₁ c₂ := by
  unfold A_R1 canonical_R
  apply List.Perm.flatMap_left
  intro ⟨Pa, Ra⟩ _
  simp_rw [cutOptions_node]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  exact flatMap_comm_perm (extOptions c₂) (extOptions Ra)
    (fun ⟨Pb, Rb⟩ ⟨F2a, Qa⟩ =>
      (extOptions Rb).map fun ⟨F2b, Qb⟩ =>
        (Pa ++ Pb, F2a ++ F2b, SyntacticObject.node Qa Qb))

private theorem product_R_eq_canonical (c₁ c₂ : SyntacticObject) :
    unfilteredTripleProduct (childRHS c₁) (childRHS c₂) = canonical_R c₁ c₂ := by
  unfold unfilteredTripleProduct childRHS canonical_R
  simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem A_R1_perm_product (c₁ c₂ : SyntacticObject) :
    A_R1 c₁ c₂ ~ unfilteredTripleProduct (childRHS c₁) (childRHS c₂) := by
  rw [product_R_eq_canonical]; exact A_R1_perm_canonical c₁ c₂

/-! ## §10. B_L ~ A_R2 ++ B_R -/

private theorem flatMap_eq_flatMap_filter {α β : Type*}
    (f : α → List β) (p : α → Bool) (L : List α)
    (h : ∀ x ∈ L, p x = false → f x = []) :
    L.flatMap f = (L.filter p).flatMap f := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.flatMap_cons, List.filter_cons]
    rcases Bool.eq_false_or_eq_true (p x) with hp | hp <;> simp [hp]
    · exact ih'
    · rw [h x (.head _) hp, List.nil_append, ih']

private theorem filter_eq_nil_of {α : Type*} {p : α → Bool} {L : List α}
    (h : ∀ x ∈ L, p x = false) : L.filter p = [] := by
  rw [List.filter_eq_nil_iff]; exact fun x hx => by simp [h x hx]

private theorem extOptions_filter_empty (c : SyntacticObject) :
    (extOptions c).filter (fun x => x.1.isEmpty) = [([], c)] := by
  induction c with
  | leaf tok => simp [extOptions, cutOptions]
  | node c₁ c₂ ih₁ ih₂ =>
    show (cutOptions (SyntacticObject.node c₁ c₂) ++
      [([SyntacticObject.node c₁ c₂], qLeaf)]).filter _ = _
    rw [List.filter_append]
    have : List.filter (fun x => x.1.isEmpty)
        [([SyntacticObject.node c₁ c₂], qLeaf)] = [] := rfl
    rw [this, List.append_nil, cutOptions_node, List.filter_flatMap]
    simp only [List.filter_map, Function.comp_def]
    rw [flatMap_eq_flatMap_filter _ (fun x => x.1.isEmpty) _ (by
      intro ⟨Pa, Ra⟩ _ hne
      rw [List.map_eq_nil_iff, filter_eq_nil_of]
      intro ⟨Pb, Rb⟩ _
      cases Pa with | nil => simp at hne | cons _ _ => rfl)]
    rw [ih₁]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
    rw [ih₂]; rfl

private theorem forestTerms_singleton (v : SyntacticObject) :
    forestTerms [v] = treeTerms v := by
  unfold forestTerms
  simp only [forestTerms, List.map_cons, List.map_nil, List.append_nil]; simp

private theorem B_L_expand (c₁ c₂ : SyntacticObject) :
    B_L c₁ c₂ =
    [([SyntacticObject.node c₁ c₂], [], qLeaf),
     ([], [SyntacticObject.node c₁ c₂], qLeaf)] ++
    (cutTerms (SyntacticObject.node c₁ c₂)).map fun ⟨F, Q⟩ => (F, [Q], qLeaf) := by
  unfold B_L; rw [forestTerms_singleton]; unfold treeTerms
  simp [List.map_map, Function.comp_def]

private theorem A_R2_eq (c₁ c₂ : SyntacticObject) :
    A_R2 c₁ c₂ = (cutOptions (SyntacticObject.node c₁ c₂)).map
      fun ⟨P, R⟩ => (P, [R], qLeaf) := by
  unfold A_R2; rw [cutOptions_node]
  simp [List.map_flatMap, List.map_map, Function.comp_def]

private theorem cutOptions_map_perm (c₁ c₂ : SyntacticObject) :
    (cutOptions (SyntacticObject.node c₁ c₂)).map (fun ⟨P, R⟩ => (P, [R], qLeaf)) ~
    (cutTerms (SyntacticObject.node c₁ c₂)).map (fun ⟨F, Q⟩ => (F, [Q], qLeaf)) ++
    [([], [SyntacticObject.node c₁ c₂], qLeaf)] := by
  have h_filter : (cutOptions (SyntacticObject.node c₁ c₂)).filter
      (fun x => x.1.isEmpty) = [([], SyntacticObject.node c₁ c₂)] := by
    rw [cutOptions_node, List.filter_flatMap]
    simp only [List.filter_map, Function.comp_def]
    rw [flatMap_eq_flatMap_filter _ (fun x => x.1.isEmpty) _ (by
      intro ⟨Pa, Ra⟩ _ hne
      rw [List.map_eq_nil_iff, filter_eq_nil_of]
      intro ⟨Pb, Rb⟩ _
      cases Pa with | nil => simp at hne | cons _ _ => rfl)]
    rw [extOptions_filter_empty c₁]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
    rw [extOptions_filter_empty c₂]; rfl
  set L := cutOptions (SyntacticObject.node c₁ c₂)
  set g : Forest × SyntacticObject → Forest × Forest × SyntacticObject :=
    fun ⟨P, R⟩ => (P, [R], qLeaf)
  have h_neg : (L.filter (fun x => !(fun x => !x.1.isEmpty) x)) =
      [([], SyntacticObject.node c₁ c₂)] := by
    convert h_filter using 1; congr 1; ext ⟨P, _⟩; simp [Bool.not_not]
  have h_perm : L ~ (cutTerms (SyntacticObject.node c₁ c₂)) ++
      [([], SyntacticObject.node c₁ c₂)] := by
    have h := (List.filter_append_perm (fun (x : Forest × SyntacticObject) =>
      !x.1.isEmpty) L).symm
    rwa [h_neg] at h
  calc L.map g
      ~ ((cutTerms (SyntacticObject.node c₁ c₂)) ++
          [([], SyntacticObject.node c₁ c₂)]).map g := h_perm.map g
    _ = (cutTerms (SyntacticObject.node c₁ c₂)).map g ++
        [([], [SyntacticObject.node c₁ c₂], qLeaf)] := by
      rw [List.map_append]; rfl

theorem B_L_perm_A_R2_B_R (c₁ c₂ : SyntacticObject) :
    B_L c₁ c₂ ~ A_R2 c₁ c₂ ++ B_R c₁ c₂ := by
  rw [B_L_expand, A_R2_eq]
  set c := SyntacticObject.node c₁ c₂
  set g : Forest × SyntacticObject → Forest × Forest × SyntacticObject :=
    fun ⟨P, R⟩ => (P, [R], qLeaf)
  set a : Forest × Forest × SyntacticObject := ([c], [], qLeaf)
  set b : Forest × Forest × SyntacticObject := ([], [c], qLeaf)
  show [a, b] ++ (cutTerms c).map g ~ (cutOptions c).map g ++ [a]
  calc [a, b] ++ (cutTerms c).map g
      ~ (cutTerms c).map g ++ [a, b] := List.perm_append_comm
    _ ~ (cutTerms c).map g ++ [b, a] :=
        List.Perm.append_left _ (List.Perm.swap b a [])
    _ = ((cutTerms c).map g ++ [b]) ++ [a] := by
        rw [show [b, a] = [b] ++ [a] from rfl, List.append_assoc]
    _ ~ (cutOptions c).map g ++ [a] :=
        (cutOptions_map_perm c₁ c₂).symm.append_right [a]

/-! ## §11. Core per-child permutation (structural induction) -/

theorem childLHS_perm_childRHS (c : SyntacticObject) :
    childLHS c ~ childRHS c := by
  induction c with
  | leaf tok => rw [childLHS_leaf, childRHS_leaf]
  | node c₁ c₂ ih₁ ih₂ =>
    rw [childLHS_node_eq, childRHS_node_eq]
    have hA : A_L c₁ c₂ ~ A_R1 c₁ c₂ :=
      (A_L_perm_product c₁ c₂).trans
        ((unfilteredTripleProduct_perm ih₁ ih₂).trans
          (A_R1_perm_product c₁ c₂).symm)
    have hB : B_L c₁ c₂ ~ A_R2 c₁ c₂ ++ B_R c₁ c₂ := B_L_perm_A_R2_B_R c₁ c₂
    calc A_L c₁ c₂ ++ B_L c₁ c₂
        ~ A_R1 c₁ c₂ ++ (A_R2 c₁ c₂ ++ B_R c₁ c₂) := hA.append hB
      _ ~ (A_R1 c₁ c₂ ++ A_R2 c₁ c₂) ++ B_R c₁ c₂ := by
            rw [List.append_assoc]
      _ ~ prod_R c₁ c₂ ++ B_R c₁ c₂ :=
            (prod_R_perm_A_R1_A_R2 c₁ c₂).symm.append_right _

/-! ## §12. Factorization into filtered Cartesian products

Both `lhsTriples` and `nestedCutTriples` factor as filtered products of
per-child lists. The factorization rewrites each into a 4-deep form,
then `flatMap_comm_perm` swaps the middle two iteration levels. -/

def filteredTripleProduct
    (L₁ L₂ : List (Forest × Forest × SyntacticObject)) :=
  L₁.flatMap fun ⟨l₁, r₁, R₁⟩ =>
    L₂.flatMap fun ⟨l₂, r₂, R₂⟩ =>
      if !(l₁ ++ l₂).isEmpty && !(r₁ ++ r₂).isEmpty
      then [(l₁ ++ l₂, r₁ ++ r₂, SyntacticObject.node R₁ R₂)]
      else []

private theorem filteredTripleProduct_perm
    {L₁ L₁' L₂ L₂' : List (Forest × Forest × SyntacticObject)}
    (h₁ : L₁ ~ L₁') (h₂ : L₂ ~ L₂') :
    filteredTripleProduct L₁ L₂ ~ filteredTripleProduct L₁' L₂' := by
  unfold filteredTripleProduct
  exact List.Perm.flatMap h₁ (fun ⟨_, _, _⟩ _ => h₂.flatMap_right _)

-- Helpers for controlled unfolding of cutTerms
private theorem filter_flatMap_eq' {α β : Type*} (L : List α) (p : α → Bool)
    (f : α → List β) :
    (L.filter p).flatMap f = L.flatMap (fun x => if p x then f x else []) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    cases p x <;> simp [ih]

private theorem filter_map_eq_flatMap {α β : Type*} (L : List α) (p : α → Bool)
    (f : α → β) :
    (L.filter p).map f = L.flatMap (fun x => if p x then [f x] else []) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    cases p x <;> simp [ih]

-- Inner lemma for LHS factorization: gated forestTerms
private theorem gated_eq_ungated (Pa Pb : Forest) (Ra Rb : SyntacticObject) :
    (if !(Pa ++ Pb).isEmpty then
      ((forestTerms (Pa ++ Pb)).filter fun ⟨l, r⟩ =>
        !l.isEmpty && !r.isEmpty).map
        fun ⟨l, r⟩ => (l, r, SyntacticObject.node Ra Rb)
    else []) =
    (forestTerms Pa).flatMap fun ⟨la, ra⟩ =>
      (forestTerms Pb).flatMap fun ⟨lb, rb⟩ =>
        if !(la ++ lb).isEmpty && !(ra ++ rb).isEmpty
        then [(la ++ lb, ra ++ rb, SyntacticObject.node Ra Rb)]
        else [] := by
  rw [forestTerms_append, filter_map_eq_flatMap]
  simp only [List.flatMap_assoc, List.flatMap_map, Function.comp_def]
  cases hPab : (Pa ++ Pb).isEmpty
  · simp [hPab]
  · have hPa : Pa = [] := by cases Pa <;> simp_all
    have hPb : Pb = [] := by subst hPa; simpa using hPab
    subst hPa; subst hPb; simp [forestTerms]

-- Inner lemma for RHS factorization: gated cutTerms
private theorem gated_eq_ungated_R (Pa Pb : Forest) (Ra Rb : SyntacticObject) :
    (if !(Pa ++ Pb).isEmpty then
      (cutTerms (SyntacticObject.node Ra Rb)).map fun ⟨F₂, Q⟩ =>
        (Pa ++ Pb, F₂, Q)
    else []) =
    (extOptions Ra).flatMap fun ⟨F₂a, Qa⟩ =>
      (extOptions Rb).flatMap fun ⟨F₂b, Qb⟩ =>
        if !(Pa ++ Pb).isEmpty && !(F₂a ++ F₂b).isEmpty
        then [(Pa ++ Pb, F₂a ++ F₂b, SyntacticObject.node Qa Qb)]
        else [] := by
  cases hPab : (Pa ++ Pb).isEmpty
  · simp only [hPab, Bool.not_false, Bool.true_and, ↓reduceIte]
    show (cutTerms (SyntacticObject.node Ra Rb)).map _ = _
    unfold cutTerms
    rw [filter_map_eq_flatMap, cutOptions_node]
    simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
      List.map_map, Function.comp_def]
  · simp [hPab]

theorem lhsTriples_perm_filteredProduct (a b : SyntacticObject) :
    lhsTriples a b ~ filteredTripleProduct (childLHS a) (childLHS b) := by
  have h_lhs : lhsTriples a b =
      (extOptions a).flatMap fun ⟨Pa, Ra⟩ =>
        (extOptions b).flatMap fun ⟨Pb, Rb⟩ =>
          (forestTerms Pa).flatMap fun ⟨la, ra⟩ =>
            (forestTerms Pb).flatMap fun ⟨lb, rb⟩ =>
              if !(la ++ lb).isEmpty && !(ra ++ rb).isEmpty
              then [(la ++ lb, ra ++ rb, SyntacticObject.node Ra Rb)]
              else [] := by
    unfold lhsTriples nontrivialTerms
    have hct : cutTerms (.node a b) =
        (cutOptions (.node a b)).filter (fun x => !x.1.isEmpty) := rfl
    rw [hct, filter_flatMap_eq', cutOptions_node]
    simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
      List.map_map, Function.comp_def]
    simp_rw [gated_eq_ungated]
  have h_rhs : filteredTripleProduct (childLHS a) (childLHS b) =
      (extOptions a).flatMap fun ⟨Pa, Ra⟩ =>
        (forestTerms Pa).flatMap fun ⟨la, ra⟩ =>
          (extOptions b).flatMap fun ⟨Pb, Rb⟩ =>
            (forestTerms Pb).flatMap fun ⟨lb, rb⟩ =>
              if !(la ++ lb).isEmpty && !(ra ++ rb).isEmpty
              then [(la ++ lb, ra ++ rb, SyntacticObject.node Ra Rb)]
              else [] := by
    unfold filteredTripleProduct childLHS
    simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
      List.map_map, Function.comp_def]
  rw [h_lhs, h_rhs]
  apply List.Perm.flatMap_left; intro ⟨Pa, Ra⟩ _
  exact flatMap_comm_perm (extOptions b) (forestTerms Pa) _

theorem nestedCutTriples_perm_filteredProduct (a b : SyntacticObject) :
    Hc.nestedCutTriples a b ~ filteredTripleProduct (childRHS a) (childRHS b) := by
  have h_lhs : Hc.nestedCutTriples a b =
      (extOptions a).flatMap fun ⟨Pa, Ra⟩ =>
        (extOptions b).flatMap fun ⟨Pb, Rb⟩ =>
          (extOptions Ra).flatMap fun ⟨F₂a, Qa⟩ =>
            (extOptions Rb).flatMap fun ⟨F₂b, Qb⟩ =>
              if !(Pa ++ Pb).isEmpty && !(F₂a ++ F₂b).isEmpty
              then [(Pa ++ Pb, F₂a ++ F₂b, SyntacticObject.node Qa Qb)]
              else [] := by
    unfold Hc.nestedCutTriples
    have hct : cutTerms (.node a b) =
        (cutOptions (.node a b)).filter (fun x => !x.1.isEmpty) := rfl
    rw [hct, filter_flatMap_eq', cutOptions_node]
    simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap]
    simp_rw [gated_eq_ungated_R]
  have h_rhs : filteredTripleProduct (childRHS a) (childRHS b) =
      (extOptions a).flatMap fun ⟨Pa, Ra⟩ =>
        (extOptions Ra).flatMap fun ⟨F₂a, Qa⟩ =>
          (extOptions b).flatMap fun ⟨Pb, Rb⟩ =>
            (extOptions Rb).flatMap fun ⟨F₂b, Qb⟩ =>
              if !(Pa ++ Pb).isEmpty && !(F₂a ++ F₂b).isEmpty
              then [(Pa ++ Pb, F₂a ++ F₂b, SyntacticObject.node Qa Qb)]
              else [] := by
    unfold filteredTripleProduct childRHS
    simp only [List.flatMap_assoc, List.flatMap_map]
  rw [h_lhs, h_rhs]
  apply List.Perm.flatMap_left; intro ⟨Pa, Ra⟩ _
  exact flatMap_comm_perm (extOptions b) (extOptions Ra) _

/-! ## §13. Main permutation and sum equality -/

theorem lhsTriples_perm_nestedCutTriples (a b : SyntacticObject) :
    lhsTriples a b ~ Hc.nestedCutTriples a b :=
  (lhsTriples_perm_filteredProduct a b).trans
    ((filteredTripleProduct_perm
        (childLHS_perm_childRHS a)
        (childLHS_perm_childRHS b)).trans
      (nestedCutTriples_perm_filteredProduct a b).symm)

private noncomputable def tripleToTensor (t : Forest × Forest × SyntacticObject) :
    Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc) :=
  ofForest t.1 ⊗ₜ[ℤ] (ofForest t.2.1 ⊗ₜ[ℤ] ofTree t.2.2)

theorem lhsTriples_sum_eq_nestedCutTriples_sum (a b : SyntacticObject) :
    ((lhsTriples a b).map tripleToTensor).sum =
    ((Hc.nestedCutTriples a b).map tripleToTensor).sum :=
  ((lhsTriples_perm_nestedCutTriples a b).map tripleToTensor).sum_eq

/-! ## §14. Core identity machinery

The core identity decomposes both sides of coassociativity into
structural terms (which cancel) plus the double-cut sum. -/

namespace Hc

-- Per-term RHS identity: 1⊗(P⊗R) + P⊗Δ(R) = structural(P,R) + P⊗cutTermsSum(R)
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
private theorem rhs_per_term (P : Forest) (R : SyntacticObject) :
    Add.add
      ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R))
      (ofForest P ⊗ₜ[ℤ] (comulAlgHom (ofTree R) : Hc ⊗[ℤ] Hc))
    =
    Add.add
      (Add.add (Add.add
        (ofForest P ⊗ₜ[ℤ] (ofTree R ⊗ₜ[ℤ] (1 : Hc)))
        (ofForest P ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree R)))
        ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R)))
      (ofForest P ⊗ₜ[ℤ] cutTermsSum R) := by
  rw [comulAlgHom_ofTree, comulGen_eq_parts]
  simp only [TensorProduct.tmul_add]
  have h_eq : ∀ (x y : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)), Add.add x y = x + y := fun _ _ => rfl
  simp only [h_eq]
  abel_nf

/-- `lTensor` on a pure tensor. -/
private theorem lTensor_tmul_eq (P : Forest) (R : SyntacticObject) :
    (LinearMap.lTensor Hc comulAlgHom.toLinearMap) (ofForest P ⊗ₜ[ℤ] ofTree R) =
    ofForest P ⊗ₜ[ℤ] (comulAlgHom (ofTree R) : Hc ⊗[ℤ] Hc) := by
  rw [LinearMap.lTensor_tmul]; rfl

-- RHS sum induction: lifts rhs_per_term over a list of (Forest × SyntacticObject)
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000 in
private theorem rhs_sum_induction
    (L : List (Forest × SyntacticObject)) :
    Add.add
      ((1 : Hc) ⊗ₜ[ℤ] (L.map fun x => ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum)
      ((LinearMap.lTensor Hc comulAlgHom.toLinearMap)
        (L.map fun x => ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum)
    =
    Add.add
      ((L.map fun x =>
        Add.add (Add.add
          (ofForest x.1 ⊗ₜ[ℤ] (ofTree x.2 ⊗ₜ[ℤ] (1 : Hc)))
          (ofForest x.1 ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree x.2)))
          ((1 : Hc) ⊗ₜ[ℤ] (ofForest x.1 ⊗ₜ[ℤ] ofTree x.2))).sum)
      ((L.map fun x => ofForest x.1 ⊗ₜ[ℤ] cutTermsSum x.2).sum) := by
  have h_eq : ∀ (x y : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)), Add.add x y = x + y := fun _ _ => rfl
  simp only [h_eq]
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, TensorProduct.tmul_zero, map_zero]
    exact rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, TensorProduct.tmul_add, map_add]
    rw [lTensor_tmul_eq]
    have head_eq := rhs_per_term hd.1 hd.2
    suffices ∀ (a b c d e f : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)),
        Add.add a c = Add.add e f →
        Add.add b d = Add.add
          ((tl.map fun x =>
            Add.add (Add.add
              (ofForest x.1 ⊗ₜ[ℤ] (ofTree x.2 ⊗ₜ[ℤ] (1 : Hc)))
              (ofForest x.1 ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree x.2)))
              ((1 : Hc) ⊗ₜ[ℤ] (ofForest x.1 ⊗ₜ[ℤ] ofTree x.2))).sum)
          ((tl.map fun x => ofForest x.1 ⊗ₜ[ℤ] cutTermsSum x.2).sum) →
        Add.add (a + b) (c + d) = Add.add (e +
          (tl.map fun x =>
            Add.add (Add.add
              (ofForest x.1 ⊗ₜ[ℤ] (ofTree x.2 ⊗ₜ[ℤ] (1 : Hc)))
              (ofForest x.1 ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree x.2)))
              ((1 : Hc) ⊗ₜ[ℤ] (ofForest x.1 ⊗ₜ[ℤ] ofTree x.2))).sum)
          (f + (tl.map fun x => ofForest x.1 ⊗ₜ[ℤ] cutTermsSum x.2).sum) from
      this _ _ _ _ _ _ head_eq ih
    intro a b c d e f hac hbd
    simp only [h_eq] at hac hbd ⊢
    have step1 : a + b + (c + d) = (a + c) + (b + d) := by abel
    rw [step1, hac, hbd]
    abel_nf

/-! ### LHS per-term decomposition -/

private theorem rTensor_tmul_eq (P : Forest) (R : SyntacticObject) :
    (LinearMap.rTensor Hc comulAlgHom.toLinearMap) (ofForest P ⊗ₜ[ℤ] ofTree R) =
    (comulAlgHom (ofForest P) : Hc ⊗[ℤ] Hc) ⊗ₜ[ℤ] ofTree R := by
  rw [LinearMap.rTensor_tmul]; rfl

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000 in
private theorem lhs_per_term (P : Forest) (R : SyntacticObject) :
    Add.add
      ((TensorProduct.assoc ℤ Hc Hc Hc) ((ofForest P ⊗ₜ[ℤ] ofTree R) ⊗ₜ[ℤ] (1 : Hc)))
      ((TensorProduct.assoc ℤ Hc Hc Hc)
        ((comulAlgHom (ofForest P) : Hc ⊗[ℤ] Hc) ⊗ₜ[ℤ] ofTree R))
    =
    Add.add
      (Add.add (Add.add
        (ofForest P ⊗ₜ[ℤ] (ofTree R ⊗ₜ[ℤ] (1 : Hc)))
        (ofForest P ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree R)))
        ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R)))
      ((TensorProduct.assoc ℤ Hc Hc Hc)
        ((comulAlgHom (ofForest P) - ofForest P ⊗ₜ[ℤ] 1 -
          1 ⊗ₜ[ℤ] ofForest P) ⊗ₜ[ℤ] ofTree R)) := by
  rw [TensorProduct.assoc_tmul]
  have h_decomp : (comulAlgHom (ofForest P) : Hc ⊗[ℤ] Hc) =
      ofForest P ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] ofForest P +
      (comulAlgHom (ofForest P) - ofForest P ⊗ₜ[ℤ] 1 -
        1 ⊗ₜ[ℤ] ofForest P) := by abel
  have h2 : (TensorProduct.assoc ℤ Hc Hc Hc)
      ((comulAlgHom (ofForest P) : Hc ⊗[ℤ] Hc) ⊗ₜ[ℤ] ofTree R) =
      Add.add (Add.add
        (ofForest P ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree R))
        ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R)))
      ((TensorProduct.assoc ℤ Hc Hc Hc)
        ((comulAlgHom (ofForest P) - ofForest P ⊗ₜ[ℤ] 1 -
          1 ⊗ₜ[ℤ] ofForest P) ⊗ₜ[ℤ] ofTree R)) := by
    conv_lhs => rw [show (comulAlgHom (ofForest P) : Hc ⊗[ℤ] Hc) = _ from h_decomp]
    simp only [TensorProduct.add_tmul, map_add, TensorProduct.assoc_tmul]
    rfl
  rw [h2]
  suffices ∀ (a b c d : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)),
      Add.add a (Add.add (Add.add b c) d) =
      Add.add (Add.add (Add.add a b) c) d by exact this _ _ _ _
  intro a b c d
  have h_eq : ∀ (x y : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)), Add.add x y = x + y := fun _ _ => rfl
  simp only [h_eq]
  abel

private theorem lhs_per_term' (P : Forest) (R : SyntacticObject) :
    Add.add
      ((TensorProduct.assoc ℤ Hc Hc Hc) ((ofForest P ⊗ₜ[ℤ] ofTree R) ⊗ₜ[ℤ] (1 : Hc)))
      ((TensorProduct.assoc ℤ Hc Hc Hc)
        ((comulAlgHom (ofForest P) : Hc ⊗[ℤ] Hc) ⊗ₜ[ℤ] ofTree R))
    =
    Add.add
      (Add.add (Add.add
        (ofForest P ⊗ₜ[ℤ] (ofTree R ⊗ₜ[ℤ] (1 : Hc)))
        (ofForest P ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree R)))
        ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R)))
      (forestDeltaTmul P R) :=
  lhs_per_term P R

-- LHS sum induction: lifts lhs_per_term over a list of (Forest × SyntacticObject)
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000 in
private theorem lhs_sum_induction
    (L : List (Forest × SyntacticObject)) :
    Add.add
      ((TensorProduct.assoc ℤ Hc Hc Hc)
        ((L.map fun x => ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum ⊗ₜ[ℤ] (1 : Hc)))
      ((TensorProduct.assoc ℤ Hc Hc Hc)
        ((LinearMap.rTensor Hc comulAlgHom.toLinearMap)
          (L.map fun x => ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum))
    =
    Add.add
      ((L.map fun x =>
        Add.add (Add.add
          (ofForest x.1 ⊗ₜ[ℤ] (ofTree x.2 ⊗ₜ[ℤ] (1 : Hc)))
          (ofForest x.1 ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree x.2)))
          ((1 : Hc) ⊗ₜ[ℤ] (ofForest x.1 ⊗ₜ[ℤ] ofTree x.2))).sum)
      ((L.map fun x => forestDeltaTmul x.1 x.2).sum) := by
  have h_eq : ∀ (x y : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)), Add.add x y = x + y := fun _ _ => rfl
  simp only [h_eq]
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, TensorProduct.zero_tmul, map_zero]
    exact rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, TensorProduct.add_tmul, map_add]
    rw [rTensor_tmul_eq]
    have head_eq := lhs_per_term' hd.1 hd.2
    suffices ∀ (a b c d e f : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)),
        Add.add a c = Add.add e f →
        Add.add b d = Add.add
          ((tl.map fun x =>
            Add.add (Add.add
              (ofForest x.1 ⊗ₜ[ℤ] (ofTree x.2 ⊗ₜ[ℤ] (1 : Hc)))
              (ofForest x.1 ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree x.2)))
              ((1 : Hc) ⊗ₜ[ℤ] (ofForest x.1 ⊗ₜ[ℤ] ofTree x.2))).sum)
          ((tl.map fun x => forestDeltaTmul x.1 x.2).sum) →
        Add.add (a + b) (c + d) = Add.add (e +
          (tl.map fun x =>
            Add.add (Add.add
              (ofForest x.1 ⊗ₜ[ℤ] (ofTree x.2 ⊗ₜ[ℤ] (1 : Hc)))
              (ofForest x.1 ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree x.2)))
              ((1 : Hc) ⊗ₜ[ℤ] (ofForest x.1 ⊗ₜ[ℤ] ofTree x.2))).sum)
          (f + (tl.map fun x => forestDeltaTmul x.1 x.2).sum) from
      this _ _ _ _ _ _ head_eq ih
    intro a b c d e f hac hbd
    simp only [h_eq] at hac hbd ⊢
    have step1 : a + b + (c + d) = (a + c) + (b + d) := by abel
    rw [step1, hac, hbd]
    abel_nf

-- LHS of the core identity = structural terms + forest delta sum
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000 in
private theorem lhs_decomposition (a b : SyntacticObject) :
    let S := (cutTerms (.node a b)).foldl
      (fun acc x => acc + ofForest x.1 ⊗ₜ[ℤ] ofTree x.2) (0 : Hc ⊗[ℤ] Hc)
    Add.add
      ((TensorProduct.assoc ℤ Hc Hc Hc) (S ⊗ₜ[ℤ] (1 : Hc)))
      ((TensorProduct.assoc ℤ Hc Hc Hc) ((LinearMap.rTensor Hc comulAlgHom.toLinearMap) S))
    =
    Add.add
      (((cutTerms (.node a b)).map fun ⟨P, R⟩ =>
        Add.add (Add.add
          (ofForest P ⊗ₜ[ℤ] (ofTree R ⊗ₜ[ℤ] (1 : Hc)))
          (ofForest P ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree R)))
          ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R))).sum)
      (((cutTerms (.node a b)).map fun ⟨P, R⟩ =>
        forestDeltaTmul P R).sum) := by
  intro S
  have hS : S = ((cutTerms (.node a b)).map
      fun x => ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum :=
    foldl_add_eq_sum _ _
  rw [hS]
  exact lhs_sum_induction _

-- RHS of the core identity = structural terms + doubleCutSum
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000 in
private theorem rhs_decomposition (a b : SyntacticObject) :
    let S := (cutTerms (.node a b)).foldl
      (fun acc x => acc + ofForest x.1 ⊗ₜ[ℤ] ofTree x.2) (0 : Hc ⊗[ℤ] Hc)
    Add.add
      ((1 : Hc) ⊗ₜ[ℤ] S)
      ((LinearMap.lTensor Hc comulAlgHom.toLinearMap) S)
    =
    Add.add
      (((cutTerms (.node a b)).map fun ⟨P, R⟩ =>
        Add.add (Add.add
          (ofForest P ⊗ₜ[ℤ] (ofTree R ⊗ₜ[ℤ] (1 : Hc)))
          (ofForest P ⊗ₜ[ℤ] ((1 : Hc) ⊗ₜ[ℤ] ofTree R)))
          ((1 : Hc) ⊗ₜ[ℤ] (ofForest P ⊗ₜ[ℤ] ofTree R))).sum)
      (doubleCutSum a b) := by
  intro S
  have hS : S = ((cutTerms (.node a b)).map
      fun x => ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum :=
    foldl_add_eq_sum _ _
  have hDCS : doubleCutSum a b = ((cutTerms (.node a b)).map
      fun x => ofForest x.1 ⊗ₜ[ℤ] cutTermsSum x.2).sum :=
    foldl_add_eq_sum _ _
  rw [hS, hDCS]
  exact rhs_sum_induction _

/-! ## §15. Double-cut identity — CLOSED

The key identity: `Σ assoc(δ(P) ⊗ R) = doubleCutSum a b`, proved by:
1. LHS = Σ lhsTriples (via `lhs_eq_lhsTriples`)
2. RHS = nestedCutSum (via `rhs_eq_nestedCutSum`)
3. lhsTriples ~ nestedCutTriples (via `lhsTriples_perm_nestedCutTriples`)
4. Permuted lists have equal sums -/

private theorem double_cut_identity (a b : SyntacticObject) :
    ((cutTerms (.node a b)).map fun ⟨P, R⟩ =>
      forestDeltaTmul P R).sum =
    doubleCutSum a b := by
  rw [rhs_eq_nestedCutSum]
  exact (lhs_eq_lhsTriples a b).trans (lhsTriples_sum_eq_nestedCutTriples_sum a b)

-- Core identity: both sides of coassociativity equal after structural
-- cancellation, via lhs_decomposition + double_cut_identity + rhs_decomposition
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000 in
private theorem core_identity (a b : SyntacticObject) :
    let S := (cutTerms (.node a b)).foldl
      (fun acc x => acc + ofForest x.1 ⊗ₜ[ℤ] ofTree x.2) (0 : Hc ⊗[ℤ] Hc)
    Add.add
      ((TensorProduct.assoc ℤ Hc Hc Hc) (S ⊗ₜ[ℤ] (1 : Hc)))
      ((TensorProduct.assoc ℤ Hc Hc Hc) ((LinearMap.rTensor Hc comulAlgHom.toLinearMap) S))
    =
    Add.add
      ((1 : Hc) ⊗ₜ[ℤ] S)
      ((LinearMap.lTensor Hc comulAlgHom.toLinearMap) S) := by
  intro S
  rw [lhs_decomposition]
  rw [rhs_decomposition]
  congr 1
  exact double_cut_identity a b

/-! ## §16. Coassociativity on generators -/

set_option maxHeartbeats 800000 in
/-- Coassociativity for primitive elements: trees T with
    `cutTerms T = []` (leaves and bushes). -/
theorem coassoc_gen_primitive (T : SyntacticObject)
    (h : cutTerms T = []) :
    TensorProduct.assoc ℤ Hc Hc Hc
      (comulAlgHom.toLinearMap.rTensor Hc (comulAlgHom (ofTree T))) =
    comulAlgHom.toLinearMap.lTensor Hc (comulAlgHom (ofTree T)) := by
  rw [comulAlgHom_ofTree, comulGen_primitive T h]
  simp only [map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  rw [show comulAlgHom.toLinearMap (ofTree T) = comulGen T from comulAlgHom_ofTree _,
      comulAlgHom_toLinearMap_one, comulGen_primitive T h]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
             map_add, TensorProduct.assoc_tmul]
  abel

/-- Coassociativity on a single tree: the generator-level statement
    that, together with `MonoidAlgebra.algHom_ext`, implies `Coalgebra.coassoc`. -/
theorem coassoc_gen (T : SyntacticObject) :
    TensorProduct.assoc ℤ Hc Hc Hc
      (comulAlgHom.toLinearMap.rTensor Hc (comulAlgHom (ofTree T))) =
    comulAlgHom.toLinearMap.lTensor Hc (comulAlgHom (ofTree T)) := by
  cases T with
  | leaf tok => exact coassoc_gen_primitive _ (cutTerms_leaf tok)
  | node a b =>
    rw [comulAlgHom_ofTree]
    simp only [comulGen, map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    rw [comulAlgHom_toLinearMap_one,
        show comulAlgHom.toLinearMap (ofTree (.node a b)) = comulGen (.node a b)
          from comulAlgHom_ofTree _]
    set S := (cutTerms (.node a b)).foldl
      (fun acc x => acc + ofForest x.1 ⊗ₜ[ℤ] ofTree x.2) (0 : Hc ⊗[ℤ] Hc) with hS
    rw [show comulGen (.node a b) =
        ofTree (.node a b) ⊗ₜ[ℤ] (1 : Hc) + (1 : Hc) ⊗ₜ[ℤ] ofTree (.node a b) + S from rfl]
    simp only [TensorProduct.add_tmul, map_add, TensorProduct.assoc_tmul,
               TensorProduct.tmul_add]
    set X := (TensorProduct.assoc ℤ Hc Hc Hc) (S ⊗ₜ[ℤ] (1 : Hc))
    set Y := (TensorProduct.assoc ℤ Hc Hc Hc) ((LinearMap.rTensor Hc comulAlgHom.toLinearMap) S)
    have h : Add.add X Y =
        Add.add ((1 : Hc) ⊗ₜ[ℤ] S) ((LinearMap.lTensor Hc comulAlgHom.toLinearMap) S) :=
      core_identity a b
    suffices ∀ (p q r s t u v : Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)),
        Add.add s t = Add.add u v →
        p + q + s + r + t = p + (q + r + u) + v from this _ _ _ _ _ _ _ h
    intro p q r s t u v heq
    have lhs : p + q + s + r + t = p + q + r + (s + t) := by abel
    have rhs : p + (q + r + u) + v = p + q + r + (u + v) := by abel
    rw [lhs, rhs]; congr 1

/-! ## §17. Coassociativity lifting

Lift from generators to all of `Hc` via `MonoidAlgebra.algHom_ext`. -/

set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance : Semiring (Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)) :=
  Algebra.TensorProduct.instSemiring
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance : Algebra ℤ (Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc)) :=
  Algebra.TensorProduct.instAlgebra

/-- RHS of coassociativity as an AlgHom: `(id ⊗ Δ) ∘ Δ`. -/
noncomputable def coassocRHSAlg : Hc →ₐ[ℤ] Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) comulAlgHom).comp comulAlgHom

/-- LHS of coassociativity as an AlgHom: `assoc ∘ (Δ ⊗ id) ∘ Δ`. -/
noncomputable def coassocLHSAlg : Hc →ₐ[ℤ] Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc) :=
  ((Algebra.TensorProduct.assoc (R := ℤ) (S := ℤ) (A := Hc) ℤ Hc Hc).toAlgHom.comp
    (Algebra.TensorProduct.map comulAlgHom (AlgHom.id ℤ Hc))).comp comulAlgHom

private theorem map_rTensor_apply (x : Hc ⊗[ℤ] Hc) :
    (Algebra.TensorProduct.map comulAlgHom (AlgHom.id ℤ Hc) : _ →ₐ[ℤ] _) x =
    comulAlgHom.toLinearMap.rTensor Hc x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add _ _ h1 h2 => simp only [map_add, h1, h2]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
               LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]

private theorem map_lTensor_apply (x : Hc ⊗[ℤ] Hc) :
    (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) comulAlgHom : _ →ₐ[ℤ] _) x =
    comulAlgHom.toLinearMap.lTensor Hc x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add _ _ h1 h2 => simp only [map_add, h1, h2]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
               LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply]

private theorem algAssoc_toLinearMap :
    (Algebra.TensorProduct.assoc (R := ℤ) (S := ℤ) (A := Hc) ℤ Hc Hc).toAlgHom.toLinearMap =
    (TensorProduct.assoc ℤ Hc Hc Hc).toLinearMap := by
  apply TensorProduct.ext'
  intro ab c
  induction ab using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | tmul a b => rfl
  | add x y h1 h2 =>
    simp only [TensorProduct.add_tmul, map_add, h1, h2]

private theorem algAssoc_apply (x : (Hc ⊗[ℤ] Hc) ⊗[ℤ] Hc) :
    (Algebra.TensorProduct.assoc (R := ℤ) (S := ℤ) (A := Hc) ℤ Hc Hc : _ ≃ₐ[ℤ] _) x =
    TensorProduct.assoc ℤ Hc Hc Hc x := LinearMap.congr_fun algAssoc_toLinearMap x

set_option maxHeartbeats 800000 in
private theorem coassocAlg_ofTree (T : SyntacticObject) :
    coassocLHSAlg (ofTree T) = coassocRHSAlg (ofTree T) := by
  change (Algebra.TensorProduct.assoc (R := ℤ) (S := ℤ) (A := Hc) ℤ Hc Hc)
    ((Algebra.TensorProduct.map comulAlgHom (AlgHom.id ℤ Hc)) (comulAlgHom (ofTree T))) =
    (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) comulAlgHom) (comulAlgHom (ofTree T))
  rw [map_rTensor_apply, algAssoc_apply, map_lTensor_apply]
  exact coassoc_gen T

set_option maxHeartbeats 1600000 in
private theorem coassocLHSAlg_eq_coassocRHSAlg :
    coassocLHSAlg = coassocRHSAlg := by
  apply MonoidAlgebra.algHom_ext
  intro m
  induction m using FreeMonoid.recOn with
  | h0 => exact coassocLHSAlg.map_one'.trans coassocRHSAlg.map_one'.symm
  | ih T ts ih =>
    let a : Hc := MonoidAlgebra.single (FreeMonoid.of T) 1
    let b : Hc := MonoidAlgebra.single ts 1
    have hsplit : (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc) = a * b :=
      (MonoidAlgebra.single_mul_single (R := ℤ) (FreeMonoid.of T) ts 1 1).symm
    have hih : coassocLHSAlg b = coassocRHSAlg b := ih
    calc coassocLHSAlg (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc)
        = coassocLHSAlg (a * b) := by rw [hsplit]
      _ = coassocLHSAlg a * coassocLHSAlg b := map_mul coassocLHSAlg a b
      _ = coassocLHSAlg a * coassocRHSAlg b := by rw [hih]
      _ = coassocRHSAlg a * coassocRHSAlg b := by
          congr 1; exact coassocAlg_ofTree T
      _ = coassocRHSAlg (a * b) := (map_mul coassocRHSAlg a b).symm
      _ = coassocRHSAlg (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc) :=
          congr_arg _ hsplit.symm

private theorem coassocLHS_eq_linLHS (x : Hc) :
    coassocLHSAlg x =
    TensorProduct.assoc ℤ Hc Hc Hc
      (comulAlgHom.toLinearMap.rTensor Hc (comulAlgHom.toLinearMap x)) := by
  change (Algebra.TensorProduct.assoc (R := ℤ) (S := ℤ) (A := Hc) ℤ Hc Hc)
    ((Algebra.TensorProduct.map comulAlgHom (AlgHom.id ℤ Hc)) (comulAlgHom x)) = _
  rw [map_rTensor_apply, algAssoc_apply]; rfl

private theorem coassocRHS_eq_linRHS (x : Hc) :
    coassocRHSAlg x =
    comulAlgHom.toLinearMap.lTensor Hc (comulAlgHom.toLinearMap x) := by
  change (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) comulAlgHom) (comulAlgHom x) = _
  rw [map_lTensor_apply]; rfl

/-- Coassociativity of the CK coproduct as a `LinearMap` equation:
    `assoc ∘ (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. -/
private theorem coassoc_proof :
    TensorProduct.assoc ℤ Hc Hc Hc ∘ₗ
      comulAlgHom.toLinearMap.rTensor Hc ∘ₗ comulAlgHom.toLinearMap =
    comulAlgHom.toLinearMap.lTensor Hc ∘ₗ comulAlgHom.toLinearMap := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← coassocLHS_eq_linLHS, ← coassocRHS_eq_linRHS]
  exact DFunLike.congr_fun coassocLHSAlg_eq_coassocRHSAlg x

/-! ## §18. Coalgebra instance -/

/-- The Connes-Kreimer coalgebra structure on H^c.

    `comul` is constructed as an `AlgHom` (via `comulAlgHom`), then
    the `AlgHom.toLinearMap` is extracted for the `Coalgebra` instance.
    Coassociativity is proved by lifting from generators via
    `MonoidAlgebra.algHom_ext`. -/
noncomputable instance instCoalgebra : Coalgebra ℤ Hc where
  comul := comulAlgHom.toLinearMap
  counit := hcCounit
  coassoc := coassoc_proof
  rTensor_counit_comp_comul := rTensor_counit_comp_comul_proof
  lTensor_counit_comp_comul := lTensor_counit_comp_comul_proof

end Hc

end Minimalism
