import Linglib.Core.Logic.OT
import Linglib.Theories.Phonology.Constraints

/-!
# Correspondence Theory
@cite{mccarthy-prince-1995}

Correspondence Theory replaces the PARSE/FILL approach to faithfulness
(@cite{prince-smolensky-1993}) with a general relation ℛ between two
strings S₁ and S₂. Faithfulness constraints are defined as structural
properties of ℛ — completeness of mapping (MAX, DEP), featural identity
of correspondents (IDENT), linear order preservation (LINEARITY),
contiguity of mapped regions (CONTIGUITY), and edge alignment (ANCHOR).

The same constraint *schema* generates distinct, separately-rankable
constraints for each correspondence domain: Input-Output (I-O),
Base-Reduplicant (B-R), Input-Reduplicant (I-R), and Output-Output
(O-O). This unification is the paper's central theoretical move:
reduplicative identity and phonological faithfulness are governed by
the same formal apparatus.

## Connection to `Constraints.lean`

The `mkMax`, `mkDep`, `mkIdent` constructors in `Constraints.lean` are
ad-hoc boolean wrappers. The definitions here give them structural
content: MAX counts uncovered S₁ elements, DEP counts uncovered S₂
elements, IDENT counts featural mismatches between correspondents.

## Parallel implementations

Two domain-specific violation counters in the codebase are instances
of `Corr.identViol` specialized to particular tiers:

- `basemapViolations` in `Autosegmental/BasemapCorrespondence.lean`:
  IDENT over tonal tiers (OO correspondence, @cite{rolle-2018}).
- `identViolations` in `Harmony/OT.lean`: IDENT over harmonic
  feature values (IO correspondence on a single feature dimension).
-/

namespace Phonology.Correspondence

open Core.OT

-- ============================================================================
-- § 1: Correspondence Domains
-- ============================================================================

/-- The domain over which a correspondence relation holds.

    Each domain produces a separately rankable constraint family.
    @cite{mccarthy-prince-1995} §2 introduces I-O and B-R; §6 adds I-R;
    @cite{benua-1997} extends to O-O. -/
inductive CorrDomain where
  | io   -- Input → Output
  | br   -- Base → Reduplicant
  | ir   -- Input → Reduplicant (Full Model, §6)
  | oo   -- Output → Output (transderivational, Benua 1997)
  deriving DecidableEq, Repr

/-- Display name for a correspondence domain (used in constraint names). -/
def CorrDomain.label : CorrDomain → String
  | .io => "IO"
  | .br => "BR"
  | .ir => "IR"
  | .oo => "OO"

-- ============================================================================
-- § 2: Correspondence Relation (Definition 10)
-- ============================================================================

/-- A correspondence relation between two strings S₁ and S₂.

    @cite{mccarthy-prince-1995} Definition 10: "Given two strings S₁, S₂,
    **correspondence** is a relation ℛ from the elements of S₁ to those
    of S₂."

    `pairs` encodes ℛ as index pairs: `(i, j) ∈ pairs` means S₁[i] ℛ S₂[j].
    The relation need not be a function — one-to-many (INTEGRITY violations)
    and many-to-one (UNIFORMITY violations) are both permitted.

    The `wf` field ensures all index pairs refer to valid positions in S₁
    and S₂. This eliminates the partiality of `s₁[i]?` lookups in proofs —
    for any `(i, j) ∈ pairs`, both `s₁[i]` and `s₂[j]` are guaranteed
    to succeed. -/
structure Corr (α : Type*) where
  s₁ : List α
  s₂ : List α
  pairs : List (Nat × Nat)
  wf : ∀ p ∈ pairs, p.1 < s₁.length ∧ p.2 < s₂.length

section ConstraintFamilies
variable {α : Type*}

-- ============================================================================
-- § 3: Constraint Families (Appendix A)
-- ============================================================================

/-- **(A.1) MAX** — "Every element of S₁ has a correspondent in S₂."

    Counts S₁ positions with no correspondent in S₂. MAX-IO prohibits
    deletion; MAX-BR demands total reduplication. -/
def Corr.maxViol (c : Corr α) : Nat :=
  (List.range c.s₁.length).filter (λ i =>
    !c.pairs.any (λ (a, _) => a == i)) |>.length

/-- **(A.2) DEP** — "Every element of S₂ has a correspondent in S₁."

    Counts S₂ positions with no correspondent in S₁. DEP-IO prohibits
    epenthesis; DEP-BR prohibits fixed default segmentism. -/
def Corr.depViol (c : Corr α) : Nat :=
  (List.range c.s₂.length).filter (λ j =>
    !c.pairs.any (λ (_, b) => b == j)) |>.length

/-- **(A.3) IDENT(F)** — "Correspondent segments have identical feature values."

    Counts pairs (i, j) ∈ ℛ where S₁[i] ≠ S₂[j]. IDENT-IO penalizes
    featural unfaithfulness; IDENT-BR penalizes featural mismatch
    between base and reduplicant.

    For well-formed correspondences (`Corr.wf`), the `| _, _ => false`
    branch is unreachable — both lookups always succeed. -/
def Corr.identViol [BEq α] (c : Corr α) : Nat :=
  c.pairs.filter (λ (i, j) =>
    match c.s₁[i]?, c.s₂[j]? with
    | some a, some b => !(a == b)
    | _, _ => false
  ) |>.length

/-- A sorted list of natural numbers is contiguous (no gaps). -/
def isContiguous : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => b == a + 1 && isContiguous (b :: rest)

/-- Propositional version of contiguity: a sorted list of natural numbers
    has no gaps between consecutive elements. -/
def IsContiguous : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b = a + 1 ∧ IsContiguous (b :: rest)

/-- Decidability of `IsContiguous`. -/
def decIsContiguous : (l : List Nat) → Decidable (IsContiguous l)
  | [] => .isTrue trivial
  | [_] => .isTrue trivial
  | a :: b :: rest =>
    if h₁ : b = a + 1 then
      match decIsContiguous (b :: rest) with
      | .isTrue h₂ => .isTrue ⟨h₁, h₂⟩
      | .isFalse h₂ => .isFalse (λ ⟨_, h⟩ => h₂ h)
    else .isFalse (λ ⟨h, _⟩ => h₁ h)

instance (l : List Nat) : Decidable (IsContiguous l) := decIsContiguous l

/-- **(A.4a) I-CONTIGUITY** — "No Skipping."

    The portion of S₁ standing in correspondence forms a contiguous string.
    Domain(ℛ) is a single contiguous substring of S₁. Violated by internal
    deletion: the map **xyz** → **xz** skips y. -/
def Corr.contigIViol (c : Corr α) : Nat :=
  let dom := (c.pairs.map Prod.fst).mergeSort (· ≤ ·) |>.eraseDups
  if isContiguous dom then 0 else 1

/-- **(A.4b) O-CONTIGUITY** — "No Intrusion."

    The portion of S₂ standing in correspondence forms a contiguous string.
    Range(ℛ) is a single contiguous substring of S₂. Violated by internal
    epenthesis: the map **xy** → **xyz** intrudes z. -/
def Corr.contigOViol (c : Corr α) : Nat :=
  let rng := (c.pairs.map Prod.snd).mergeSort (· ≤ ·) |>.eraseDups
  if isContiguous rng then 0 else 1

/-- **(A.5) LEFT-ANCHOR** — left-edge correspondence.

    The leftmost element of S₁ has a correspondent at the left edge of S₂.
    In prefixing reduplication, L-ANCHOR-BR >> R-ANCHOR-BR. -/
def Corr.anchorLViol (c : Corr α) : Nat :=
  if c.s₁.length == 0 || c.s₂.length == 0 then 0
  else if c.pairs.any (λ (i, j) => i == 0 && j == 0) then 0 else 1

/-- **(A.5) RIGHT-ANCHOR** — right-edge correspondence. -/
def Corr.anchorRViol (c : Corr α) : Nat :=
  if c.s₁.length == 0 || c.s₂.length == 0 then 0
  else if c.pairs.any (λ (i, j) =>
    i == c.s₁.length - 1 && j == c.s₂.length - 1) then 0 else 1

/-- **(A.6) LINEARITY** — "No Metathesis."

    S₁ is consistent with the precedence structure of S₂. Counts
    order reversals: pairs (i₁, j₁), (i₂, j₂) where i₁ < i₂ but j₁ > j₂. -/
def Corr.linearityViol (c : Corr α) : Nat :=
  (c.pairs.map (λ (i₁, j₁) =>
    (c.pairs.filter (λ (i₂, j₂) => i₁ < i₂ && j₂ < j₁)).length
  )).sum

/-- **(A.7) UNIFORMITY** — "No Coalescence."

    No element of S₂ has multiple correspondents in S₁. Counts S₂
    positions j with |{i : (i,j) ∈ ℛ}| > 1. -/
def Corr.uniformityViol (c : Corr α) : Nat :=
  (List.range c.s₂.length).filter (λ j =>
    (c.pairs.filter (λ (_, b) => b == j)).length > 1
  ) |>.length

/-- **(A.8) INTEGRITY** — "No Breaking."

    No element of S₁ has multiple correspondents in S₂. Counts S₁
    positions i with |{j : (i,j) ∈ ℛ}| > 1. -/
def Corr.integrityViol (c : Corr α) : Nat :=
  (List.range c.s₁.length).filter (λ i =>
    (c.pairs.filter (λ (a, _) => a == i)).length > 1
  ) |>.length

-- ============================================================================
-- § 4: Identity Correspondence
-- ============================================================================

/-- The identity correspondence: S₁ = S₂ with each element mapped to itself.
    This is the fully faithful candidate — perfect I-O correspondence. -/
def Corr.identity (s : List α) : Corr α :=
  { s₁ := s
    s₂ := s
    pairs := List.range s.length |>.map (λ i => (i, i))
    wf := by
      intro ⟨a, b⟩ hmem
      simp only [List.mem_map, List.mem_range] at hmem
      obtain ⟨k, hk, rfl, rfl⟩ := hmem
      exact ⟨hk, hk⟩ }

end ConstraintFamilies

-- ============================================================================
-- § 5: Structural Theorems — Identity
-- ============================================================================

/-- Identity correspondence has zero MAX violations: every S₁ element
    has a correspondent. -/
theorem identity_max_zero {α : Type*} (s : List α) :
    (Corr.identity s).maxViol = 0 := by
  simp [Corr.identity, Corr.maxViol, List.filter_eq_nil_iff, List.mem_range]

/-- Identity correspondence has zero DEP violations: every S₂ element
    has a correspondent. -/
theorem identity_dep_zero {α : Type*} (s : List α) :
    (Corr.identity s).depViol = 0 := by
  simp [Corr.identity, Corr.depViol, List.filter_eq_nil_iff, List.mem_range]

/-- Identity correspondence has zero IDENT violations: correspondent
    elements are identical (they are the same element). -/
theorem identity_ident_zero {α : Type*} [BEq α] [LawfulBEq α] (s : List α) :
    (Corr.identity s).identViol = 0 := by
  simp [Corr.identity, Corr.identViol, List.filter_eq_nil_iff, List.mem_map, List.mem_range]
  intro i hi
  simp [List.getElem?_eq_getElem hi]

/-- No pair in the identity correspondence exhibits an order reversal:
    for diagonal pairs (i,i) and (j,j), i < j ∧ j < i is impossible. -/
private theorem identity_filter_diag_empty (n i : Nat) :
    ((List.range n).map (λ k => (k, k))).filter
      (λ (i₂, j₂) => i < i₂ && j₂ < i) = [] := by
  rw [List.filter_eq_nil_iff]
  intro ⟨i₂, j₂⟩ hmem
  simp only [List.mem_map, List.mem_range] at hmem
  obtain ⟨k, _, rfl, rfl⟩ := hmem
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  omega

/-- Identity correspondence has zero LINEARITY violations: the identity
    map preserves order. For any two pairs (a,a) and (b,b) in the
    identity correspondence, the condition a < b ∧ b < a is impossible. -/
theorem identity_linearity_zero {α : Type*} (s : List α) :
    (Corr.identity s).linearityViol = 0 := by
  unfold Corr.identity Corr.linearityViol
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨i₁, j₁⟩, hmem, hval⟩ := hx
  simp only [List.mem_map, List.mem_range] at hmem
  obtain ⟨k, _, rfl, rfl⟩ := hmem
  simp only at hval ⊢
  rw [identity_filter_diag_empty] at hval
  simp at hval
  exact hval.symm

/-- Filtering identity pairs `[(0,0), ..., (n-1,n-1)]` by second
    component `== j` gives the empty list when `j ≥ n`. -/
private theorem filter_identity_snd_empty (n j : Nat) (hj : ¬ j < n) :
    ((List.range n).map (λ k => (k, k))).filter (λ p => p.2 == j) = [] := by
  rw [List.filter_eq_nil_iff]
  intro ⟨a, b⟩ hmem
  simp only [List.mem_map, List.mem_range] at hmem
  obtain ⟨k, hk, rfl, rfl⟩ := hmem
  simp only [beq_iff_eq]; omega

/-- Filtering identity pairs by second component `== j` gives `[(j,j)]`
    when `j < n`. -/
private theorem filter_identity_snd_eq (n j : Nat) (hj : j < n) :
    ((List.range n).map (λ k => (k, k))).filter (λ p => p.2 == j) = [(j, j)] := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.filter_append]
    simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
    by_cases hjm : j < m
    · have := ih hjm
      simp only [beq_iff_eq] at this ⊢
      simp only [show m ≠ j from by omega, ite_false, List.append_nil]; exact this
    · have heq : j = m := by omega
      subst heq
      simp only [beq_iff_eq, ite_true]
      rw [filter_identity_snd_empty j j (by omega)]; simp

/-- Each position has at most one identity correspondent (second component). -/
private theorem filter_identity_snd_le_one (n j : Nat) :
    (((List.range n).map (λ k => (k, k))).filter (λ p => p.2 == j)).length ≤ 1 := by
  by_cases hj : j < n
  · rw [filter_identity_snd_eq n j hj]; simp
  · rw [filter_identity_snd_empty n j hj]; simp

/-- Filtering identity pairs by first component `== i` gives the empty
    list when `i ≥ n`. -/
private theorem filter_identity_fst_empty (n i : Nat) (hi : ¬ i < n) :
    ((List.range n).map (λ k => (k, k))).filter (λ p => p.1 == i) = [] := by
  rw [List.filter_eq_nil_iff]
  intro ⟨a, b⟩ hmem
  simp only [List.mem_map, List.mem_range] at hmem
  obtain ⟨k, hk, rfl, rfl⟩ := hmem
  simp only [beq_iff_eq]; omega

/-- Filtering identity pairs by first component `== i` gives `[(i,i)]`
    when `i < n`. -/
private theorem filter_identity_fst_eq (n i : Nat) (hi : i < n) :
    ((List.range n).map (λ k => (k, k))).filter (λ p => p.1 == i) = [(i, i)] := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.filter_append]
    simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
    by_cases him : i < m
    · have := ih him
      simp only [beq_iff_eq] at this ⊢
      simp only [show m ≠ i from by omega, ite_false, List.append_nil]; exact this
    · have heq : i = m := by omega
      subst heq
      simp only [beq_iff_eq, ite_true]
      rw [filter_identity_fst_empty i i (by omega)]; simp

/-- Each position has at most one identity correspondent (first component). -/
private theorem filter_identity_fst_le_one (n i : Nat) :
    (((List.range n).map (λ k => (k, k))).filter (λ p => p.1 == i)).length ≤ 1 := by
  by_cases hi : i < n
  · rw [filter_identity_fst_eq n i hi]; simp
  · rw [filter_identity_fst_empty n i hi]; simp

/-- If `f j ≤ 1` for all `j`, filtering for `f j > 1` produces the empty list. -/
private theorem filter_gt_one_empty {l : List Nat} {f : Nat → Nat}
    (h : ∀ j, f j ≤ 1) :
    l.filter (λ j => decide (f j > 1)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro j _
  simp only [decide_eq_true_eq, not_lt]
  exact h j

/-- Identity correspondence has zero UNIFORMITY violations: each S₂
    position has exactly one S₁ correspondent (itself). -/
theorem identity_uniformity_zero {α : Type*} (s : List α) :
    (Corr.identity s).uniformityViol = 0 := by
  simp only [Corr.identity, Corr.uniformityViol]
  change ((List.range s.length).filter (λ j => decide (
    (((List.range s.length).map (λ i => (i, i))).filter
      (λ x : Nat × Nat => x.2 == j)).length > 1))).length = 0
  simp [filter_gt_one_empty (λ j => filter_identity_snd_le_one s.length j)]

/-- Identity correspondence has zero INTEGRITY violations: each S₁
    position has exactly one S₂ correspondent (itself). -/
theorem identity_integrity_zero {α : Type*} (s : List α) :
    (Corr.identity s).integrityViol = 0 := by
  simp only [Corr.identity, Corr.integrityViol]
  change ((List.range s.length).filter (λ i => decide (
    (((List.range s.length).map (λ k => (k, k))).filter
      (λ x : Nat × Nat => x.1 == i)).length > 1))).length = 0
  simp [filter_gt_one_empty (λ i => filter_identity_fst_le_one s.length i)]

-- ============================================================================
-- § 6: Structural Theorems — Bounds
-- ============================================================================

/-- MAX violations cannot exceed the length of S₁: at most every
    position lacks a correspondent. -/
theorem maxViol_le_length {α : Type*} (c : Corr α) :
    c.maxViol ≤ c.s₁.length := by
  simp only [Corr.maxViol]
  exact le_of_le_of_eq (List.length_filter_le _ _) List.length_range

/-- DEP violations cannot exceed the length of S₂. -/
theorem depViol_le_length {α : Type*} (c : Corr α) :
    c.depViol ≤ c.s₂.length := by
  simp only [Corr.depViol]
  exact le_of_le_of_eq (List.length_filter_le _ _) List.length_range

/-- UNIFORMITY violations cannot exceed the length of S₂. -/
theorem uniformityViol_le_length {α : Type*} (c : Corr α) :
    c.uniformityViol ≤ c.s₂.length := by
  simp only [Corr.uniformityViol]
  exact le_of_le_of_eq (List.length_filter_le _ _) List.length_range

/-- INTEGRITY violations cannot exceed the length of S₁. -/
theorem integrityViol_le_length {α : Type*} (c : Corr α) :
    c.integrityViol ≤ c.s₁.length := by
  simp only [Corr.integrityViol]
  exact le_of_le_of_eq (List.length_filter_le _ _) List.length_range

-- ============================================================================
-- § 7: Correspondence → NamedConstraint Bridge
-- ============================================================================

/-- Build a MAX `NamedConstraint` from the structural `Corr.maxViol`.
    Ties the schema-level definition (§3) to the OT evaluation
    machinery in `Core.OT`. -/
def Corr.toMaxConstraint (α : Type) (domain : CorrDomain) :
    NamedConstraint (Corr α) :=
  { name := "MAX-" ++ domain.label
    family := .faithfulness
    eval := Corr.maxViol }

/-- Build a DEP `NamedConstraint` from `Corr.depViol`. -/
def Corr.toDepConstraint (α : Type) (domain : CorrDomain) :
    NamedConstraint (Corr α) :=
  { name := "DEP-" ++ domain.label
    family := .faithfulness
    eval := Corr.depViol }

/-- Build an IDENT `NamedConstraint` from `Corr.identViol`. -/
def Corr.toIdentConstraint (α : Type) [BEq α] (domain : CorrDomain) :
    NamedConstraint (Corr α) :=
  { name := "IDENT-" ++ domain.label
    family := .faithfulness
    eval := Corr.identViol }

/-- Build a LINEARITY `NamedConstraint` from `Corr.linearityViol`. -/
def Corr.toLinearityConstraint (α : Type) (domain : CorrDomain) :
    NamedConstraint (Corr α) :=
  { name := "LINEARITY-" ++ domain.label
    family := .faithfulness
    eval := Corr.linearityViol }

/-- Build a UNIFORMITY `NamedConstraint` from `Corr.uniformityViol`. -/
def Corr.toUniformityConstraint (α : Type) (domain : CorrDomain) :
    NamedConstraint (Corr α) :=
  { name := "UNIFORMITY-" ++ domain.label
    family := .faithfulness
    eval := Corr.uniformityViol }

/-- Build an INTEGRITY `NamedConstraint` from `Corr.integrityViol`. -/
def Corr.toIntegrityConstraint (α : Type) (domain : CorrDomain) :
    NamedConstraint (Corr α) :=
  { name := "INTEGRITY-" ++ domain.label
    family := .faithfulness
    eval := Corr.integrityViol }

end Phonology.Correspondence
