/-
# No Complexity Loss (Proposition 1.6.10)

Formalizes §1.6.3 of @cite{marcolli-chomsky-berwick-2025}: the No Complexity
Loss constraint on Merge operations. Only External Merge and Internal Merge
satisfy nondecreasing component degree (= leafCount, the Hopf algebra
grading); all forms of Sideward Merge violate it by producing quotient
components of lower degree.

## Main definitions

- `deg`: degree of a syntactic object (= leafCount, the Hopf algebra grading)
- `satisfiesNCL`: No Complexity Loss predicate for workspace transformations

## Main results

- `merge_deg_ge_left` / `merge_deg_ge_right`: Merge is degree-nondecreasing
- `em_satisfies_ncl`: External Merge satisfies NCL
- `im_satisfies_ncl`: Internal Merge satisfies NCL
- `contains_leafCount_lt`: containment implies strict leafCount inequality
- `quotient_deg_lt`: quotient tree has strictly lower degree
- `sideward_2b_violates_ncl`: Sideward Merge type 2(b) violates NCL

-/

import Linglib.Theories.Syntax.Minimalist.Counting

namespace Minimalist

/-! ## Degree = leafCount (Hopf algebra grading)

In the Hopf algebra of rooted forests, the degree of a tree T is the
number of leaves #L(T) = T.leafCount. This is the grading that makes
the bialgebra connected and graded (Lemma 1.2.10). -/

/-- Degree of a syntactic object in the Hopf algebra of forests
    (Definition 1.6.2). -/
abbrev deg := SyntacticObject.leafCount

/-! ## Merge monotonicity

The fundamental property: Merge (= free magma multiplication) is
degree-nondecreasing. This is what makes EM and IM satisfy NCL. -/

/-- merge(T₁, T₂) has degree ≥ T₁ -/
theorem merge_deg_ge_left (T₁ T₂ : SyntacticObject) :
    deg (merge T₁ T₂) ≥ deg T₁ := by
  simp only [deg, merge, SyntacticObject.leafCount]; omega

/-- merge(T₁, T₂) has degree ≥ T₂ -/
theorem merge_deg_ge_right (T₁ T₂ : SyntacticObject) :
    deg (merge T₁ T₂) ≥ deg T₂ := by
  simp only [deg, merge, SyntacticObject.leafCount]; omega

/-- merge(T₁, T₂) has degree = deg T₁ + deg T₂ -/
theorem merge_deg_sum (T₁ T₂ : SyntacticObject) :
    deg (merge T₁ T₂) = deg T₁ + deg T₂ := rfl

/-! ## Containment and degree

Containment (dominance) strictly decreases degree. This is used to
show that quotient trees have lower degree than the original. -/

/-- Containment implies strict leafCount inequality.
    If T contains v, then v has strictly fewer leaves than T.
    Derived from `contains_lt_nodeCount` and `leaf_node_relation`. -/
theorem contains_leafCount_lt {T v : SyntacticObject}
    (h : contains T v) : v.leafCount < T.leafCount := by
  have hlt := contains_lt_nodeCount h
  have h1 := leaf_node_relation T
  have h2 := leaf_node_relation v
  omega

/-! ## No Complexity Loss (Definition 1.6.2)

A workspace transformation F → F' satisfies No Complexity Loss if every
component of F maps to some component of F' with nondecreasing degree.

The book's definition tracks the component map Φ₀ explicitly via root
vertices. Our formulation uses the existential: for every old component,
there exists a new component with ≥ degree. This is equivalent when the
component map is injective (which it is for EM and IM). -/

/-- No Complexity Loss: every component of the original workspace has
    a corresponding component in the new workspace with at least as
    high degree (leafCount). -/
def satisfiesNCL (F F' : List SyntacticObject) : Prop :=
  ∀ x ∈ F, ∃ y ∈ F', deg y ≥ deg x

/-! ## EM satisfies NCL (Proposition 1.6.10, positive direction)

For External Merge, the two merged components T₁ and T₂ both map to
merge(T₁, T₂) with strictly higher degree. All other components are
unchanged. -/

/-- External Merge satisfies No Complexity Loss. -/
theorem em_satisfies_ncl (T₁ T₂ : SyntacticObject)
    (F : List SyntacticObject) :
    satisfiesNCL F (emWorkspace T₁ T₂ F) := by
  intro x hx
  by_cases h₁ : x = T₁
  · refine ⟨merge T₁ T₂, em_contains_merge T₁ T₂ F, ?_⟩
    rw [h₁]; exact merge_deg_ge_left T₁ T₂
  · by_cases h₂ : x = T₂
    · refine ⟨merge T₁ T₂, em_contains_merge T₁ T₂ F, ?_⟩
      rw [h₂]; exact merge_deg_ge_right T₁ T₂
    · -- x ≠ T₁, x ≠ T₂: x passes both filters and stays in the workspace
      refine ⟨x, ?_, le_refl _⟩
      simp only [emWorkspace]
      apply List.mem_filter.mpr
      exact ⟨List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
        ⟨hx, by simp [bne_iff_ne, h₁]⟩)), by simp [bne_iff_ne, h₂]⟩

/-! ## IM satisfies NCL (Proposition 1.6.10, positive direction)

For Internal Merge, the component T maps to merge(β, T) with higher degree
(since merge adds β's leaves). All other components are unchanged. -/

/-- Internal Merge satisfies No Complexity Loss. -/
theorem im_satisfies_ncl (T β : SyntacticObject)
    (F : List SyntacticObject) :
    satisfiesNCL F (imWorkspace T β F) := by
  intro x hx
  by_cases h : x = T
  · refine ⟨merge β T, im_contains_merge T β F, ?_⟩
    rw [h]; exact merge_deg_ge_right β T
  · refine ⟨x, ?_, le_refl _⟩
    simp only [imWorkspace]
    exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
      ⟨hx, by simp [bne_iff_ne, h]⟩))

/-! ## Quotient degree loss

The key negative result: extracting a non-trivial subtree produces a
quotient with strictly lower degree. This is why Sideward Merge violates
No Complexity Loss — the component T₁ maps to its quotient T₁/β with
deg(T₁/β) < deg(T₁). -/

/-- Quotient tree has strictly lower degree when the extracted subtree
    has at least 2 leaves (i.e., is a non-trivial internal node).

    The hypothesis `hq : q.leafCount = T.leafCount - v.leafCount + 1`
    abstracts the contraction-quotient leaf-count identity (M-C-B Def
    1.2.4: replacing v with a single trace leaf reduces leafCount by
    `v.leafCount - 1`). Any quotient operation that respects this
    identity — including the general `Hopf/AdmissibleCut.lean`
    `CutShape.remainder` for the single-cut case — discharges the
    hypothesis. -/
theorem quotient_deg_lt (T v q : SyntacticObject)
    (hc : contains T v)
    (hq : q.leafCount = T.leafCount - v.leafCount + 1)
    (hv : v.leafCount ≥ 2) :
    deg q < deg T := by
  simp only [deg]
  have hle : v.leafCount ≤ T.leafCount :=
    Nat.le_of_lt (contains_leafCount_lt hc)
  omega

/-! ## Sideward Merge violates NCL (Proposition 1.6.10, negative direction)

Sideward Merge type 2(b): β is contained in workspace component T₁,
T₂ is a different component. The operation extracts β from T₁ and merges
it with T₂, producing workspace [merge(β, T₂), T₁/β, ...].

The component T₁ maps to quotient T₁/β, losing degree. When T₁ is
sufficiently large (deg T₁ > deg β + deg T₂), no component in the
new workspace can compensate. -/

/-- Sideward Merge type 2(b) violates No Complexity Loss.

    When T₁.leafCount > β.leafCount + T₂.leafCount, the merge component
    merge(β, T₂) is too small and the quotient T₁/β is too small to
    match T₁'s degree. The hypothesis `hq` abstracts the quotient leaf-
    count identity (see `quotient_deg_lt`'s docstring). -/
theorem sideward_2b_violates_ncl (T₁ T₂ β q : SyntacticObject)
    (hc : contains T₁ β)
    (hq : q.leafCount = T₁.leafCount - β.leafCount + 1)
    (hv : β.leafCount ≥ 2)
    (hbig : T₁.leafCount > β.leafCount + T₂.leafCount) :
    ¬satisfiesNCL [T₁, T₂] [merge β T₂, q] := by
  intro hncl
  obtain ⟨y, hy_mem, hy_deg⟩ := hncl T₁ (List.mem_cons.mpr (Or.inl rfl))
  have hq_lt := quotient_deg_lt T₁ β q hc hq hv
  rcases List.mem_cons.mp hy_mem with rfl | hy'
  · -- y = merge β T₂: degree = β.leafCount + T₂.leafCount < T₁.leafCount
    simp only [deg, merge, SyntacticObject.leafCount] at hy_deg
    omega
  · rcases List.mem_cons.mp hy' with rfl | hy''
    · -- y = q: degree < T₁.leafCount by quotient_deg_lt
      simp only [deg] at hy_deg hq_lt
      omega
    · contradiction

/-! ## Proposition 1.6.10: NCL characterizes EM and IM

Combining the positive and negative results: External Merge and Internal
Merge are the only Merge operations that satisfy No Complexity Loss.

The proof structure:
- EM: merge(T₁, T₂).leafCount = T₁.leafCount + T₂.leafCount ≥ both
  inputs. All other components unchanged. NCL satisfied.
- IM: merge(β, T).leafCount = β.leafCount + T.leafCount ≥ T.leafCount.
  All other components unchanged. NCL satisfied.
- Sideward 2(b): T₁ maps to T₁/β with deg(T₁/β) < deg(T₁). NCL violated.
- Sideward 3(a), 3(b): similarly produce quotient components. NCL violated.
- 𝔐_{S,1}: produces T_v ⊔ T/T_v, and deg(T/T_v) < deg(T). NCL violated.

The characterization is precise: NCL distinguishes IM from Sideward Merge
type 2(b), which cannot be distinguished by the size measures b₀, α, σ
alone (Remark 1.6.9). -/

end Minimalist
