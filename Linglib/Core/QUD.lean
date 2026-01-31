/-
# Core/QUD.lean

QUD (Question Under Discussion) infrastructure for semantics and pragmatics.

## Key Concept

A QUD partitions the meaning space into equivalence classes. Two meanings are
equivalent under a QUD if they "answer the question the same way."

This is general semantics machinery used in:
- Information structure (Roberts 2012)
- RSA pragmatic models (Kao et al. 2014)
- Focus semantics
- Discourse coherence

## Example

For meaning space `Price × Affect`:
- QUD "price": (p1, a1) ≡ (p2, a2) iff p1 = p2
- QUD "affect": (p1, a1) ≡ (p2, a2) iff a1 = a2
- QUD "both": (p1, a1) ≡ (p2, a2) iff p1 = p2 ∧ a1 = a2

## References

- Roberts (2012). Information structure in discourse.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
-/

import Mathlib.Data.Set.Basic

-- ============================================================================
-- QUD: Question Under Discussion
-- ============================================================================

/--
A QUD (Question Under Discussion) partitions the meaning space.

Two meanings are equivalent under a QUD if they "answer the question the same way."
Speakers optimize informativity only within equivalence classes.

A well-formed QUD is an equivalence relation (reflexive, symmetric, transitive).
All three properties are bundled in the structure to guarantee well-formedness.
-/
structure QUD (M : Type*) where
  /-- Are two meanings equivalent under this QUD? -/
  sameAnswer : M → M → Bool
  /-- Equivalence must be reflexive -/
  refl : ∀ m, sameAnswer m m = true
  /-- Equivalence must be symmetric -/
  symm : ∀ m1 m2, sameAnswer m1 m2 = sameAnswer m2 m1
  /-- Equivalence must be transitive -/
  trans : ∀ m1 m2 m3, sameAnswer m1 m2 = true → sameAnswer m2 m3 = true → sameAnswer m1 m3 = true
  /-- Name for display/debugging -/
  name : String := ""

namespace QUD

variable {M : Type*}

-- ============================================================================
-- QUD as Equivalence Relation / Partition
-- ============================================================================

/-!
## QUD = Partition

A well-formed QUD defines an equivalence relation on meanings.
This equivalence relation partitions the meaning space into cells,
where each cell contains meanings that "answer the question the same way."

### Key Theorem

For any QUD built via `ofProject f`:
- `sameAnswer m1 m2 ↔ f m1 = f m2`
- This is trivially an equivalence relation
- The partition cells are exactly the fibers of f

This is the formal content of "QUD = partition projection."
-/

section EquivalenceProperties

variable (q : QUD M)

/-- Reflexivity is guaranteed by construction -/
theorem isReflexive : ∀ m, q.sameAnswer m m = true := q.refl

/-- Symmetry is guaranteed by construction -/
theorem isSymmetric : ∀ m1 m2, q.sameAnswer m1 m2 = q.sameAnswer m2 m1 := q.symm

/-- Transitivity is guaranteed by construction -/
theorem isTransitive : ∀ m1 m2 m3,
    q.sameAnswer m1 m2 = true → q.sameAnswer m2 m3 = true → q.sameAnswer m1 m3 = true := q.trans

end EquivalenceProperties

-- ============================================================================
-- Projection QUDs are always equivalences
-- ============================================================================

variable [BEq M]

/-- The identity QUD: speaker wants to convey exact meaning -/
def exact [LawfulBEq M] : QUD M where
  sameAnswer m1 m2 := m1 == m2
  refl m := beq_self_eq_true m
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := "exact"

/-- Trivial QUD: all meanings are equivalent (speaker doesn't care about this dimension) -/
def trivial : QUD M where
  sameAnswer _ _ := true
  refl _ := rfl
  symm _ _ := rfl
  trans _ _ _ _ _ := rfl
  name := "trivial"

/-- Build QUD from a projection function -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (name : String := "") : QUD M where
  sameAnswer m1 m2 := f m1 == f m2
  refl m := beq_self_eq_true (f m)
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := name

/-- Compose two QUDs: equivalent iff equivalent under both -/
def compose (q1 q2 : QUD M) : QUD M where
  sameAnswer m1 m2 := q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2
  refl m := by simp [q1.refl, q2.refl]
  symm m1 m2 := by rw [q1.symm, q2.symm, Bool.and_comm]
  trans m1 m2 m3 h12 h23 := by
    simp only [Bool.and_eq_true] at *
    exact ⟨q1.trans m1 m2 m3 h12.1 h23.1, q2.trans m1 m2 m3 h12.2 h23.2⟩
  name := s!"{q1.name}∧{q2.name}"

instance : Mul (QUD M) where
  mul := compose

-- ============================================================================
-- Key Theorems about Projection QUDs
-- ============================================================================

section ProjectionTheorems

variable {A : Type} [BEq A] [LawfulBEq A]

/-- **THEOREM**: sameAnswer for projection QUD iff same image under f -/
theorem ofProject_sameAnswer_iff (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = true ↔ f m1 = f m2 := by
  simp only [ofProject, beq_iff_eq]

end ProjectionTheorems

-- ============================================================================
-- Partition Cells
-- ============================================================================

/--
The equivalence class (partition cell) of a meaning under a QUD.

This is the set of all meanings that "answer the question the same way."
-/
def cell (q : QUD M) (m : M) : Set M :=
  {m' : M | q.sameAnswer m m' = true}

/-- **THEOREM**: For projection QUDs, cells are exactly fibers of the projection -/
theorem ofProject_cell_eq_fiber {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (m : M) :
    (ofProject f).cell m = {m' : M | f m' = f m} := by
  ext m'
  simp only [cell, Set.mem_setOf_eq, ofProject, beq_iff_eq]
  exact eq_comm

/-- Two meanings are in the same cell iff they have the same answer -/
theorem mem_cell_iff (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.sameAnswer m m' = true := by
  simp only [cell, Set.mem_setOf_eq]

end QUD

-- ============================================================================
-- Product QUDs: Common pattern for multi-dimensional meaning spaces
-- ============================================================================

-- For product meaning spaces M = A × B, common QUD patterns:
-- - Project to first component (care about A only)
-- - Project to second component (care about B only)
-- - Identity (care about both)

namespace ProductQUD

variable {A B : Type} [BEq A] [BEq B] [LawfulBEq A] [LawfulBEq B]

/-- QUD that cares only about first component -/
def fst : QUD (A × B) :=
  QUD.ofProject Prod.fst "fst"

/-- QUD that cares only about second component -/
def snd : QUD (A × B) :=
  QUD.ofProject Prod.snd "snd"

/-- QUD that cares about both components (exact) -/
def both : QUD (A × B) :=
  QUD.exact (M := A × B)

end ProductQUD

-- ============================================================================
-- Precision Projections: For approximate communication
-- ============================================================================

/--
Precision projection for numeric meanings.

Allows modeling "approximate" vs "exact" communication:
- Exact: speaker cares about precise value
- Approximate: speaker cares about rounded value

Used in Kao et al. (2014) to model pragmatic halo effect.
-/
structure PrecisionProjection (N : Type) where
  /-- Round/approximate the value -/
  round : N → N
  /-- Name -/
  name : String := ""

namespace PrecisionProjection

/-- Exact precision: no rounding -/
def exact {N : Type} : PrecisionProjection N where
  round := id
  name := "exact"

/-- Round to nearest multiple of k -/
def roundTo (k : Nat) : PrecisionProjection Nat where
  round n := (n / k) * k
  name := s!"round{k}"

/-- Compose precision with a QUD -/
def applyToQUD {M N : Type} [BEq N] [LawfulBEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M where
  sameAnswer m1 m2 := prec.round (proj m1) == prec.round (proj m2)
  refl m := beq_self_eq_true (prec.round (proj m))
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := prec.name

end PrecisionProjection

-- ============================================================================
-- QUD Goal Projection = Partition Projection
-- ============================================================================

/-!
## The Main Theorem: QUD = Partition

In RSA models with QUDs (e.g., Kao et al. 2014), the speaker's utility
depends on whether the listener recovers the "correct answer" to the QUD,
not the exact meaning.

**Goal Projection**: Two meanings m1, m2 are QUD-equivalent iff
the speaker would be equally satisfied with the listener inferring either.

**Partition Projection**: Project a distribution onto partition cells,
collapsing all meanings in the same cell.

**THE KEY INSIGHT**: These are the same operation!

```
goalProject q m1 m2 = true
  ↔ q.sameAnswer m1 m2 = true
  ↔ m1 and m2 are in the same partition cell
  ↔ f m1 = f m2  (for projection QUD via f)
```

This means ALL QUD-sensitive RSA models (Kao et al. 2014, hyperbole,
metaphor, politeness, etc.) are doing partition projection.
-/

namespace QUD

variable {M : Type*}

/-- Goal projection: are two meanings equivalent for the speaker's purpose? -/
def goalEquiv (q : QUD M) (m1 m2 : M) : Bool := q.sameAnswer m1 m2

/-- **THEOREM (QUD = Partition)**: Goal equivalence IS partition membership -/
theorem goalEquiv_iff_same_cell (q : QUD M) (m1 m2 : M) :
    q.goalEquiv m1 m2 = true ↔ m2 ∈ q.cell m1 := by
  simp only [goalEquiv, cell, Set.mem_setOf_eq]

/-- **COROLLARY**: For projection QUDs, goal equivalence iff same projection -/
theorem goalEquiv_ofProject_iff {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (m1 m2 : M) :
    (ofProject f).goalEquiv m1 m2 = true ↔ f m1 = f m2 := by
  simp only [goalEquiv, ofProject, beq_iff_eq]

/-!
### Application to RSA

In QUD-sensitive RSA, the speaker's utility is:
```
U(u, m, q) = log P_L(m' | u) where q.sameAnswer m m' = true
           = log Σ_{m' ∈ cell(m)} P_L(m' | u)
```

This is exactly "sum over the partition cell containing m."

The theorems above guarantee this is well-defined because:
1. `cell` forms a proper partition (equivalence classes)
2. `goalEquiv` correctly identifies cell membership
3. For projection QUDs, cells are fibers of the projection function
-/

/-!
### Connection to Decision Theory (Sumers et al. 2023)

**Key Insight**: A QUD induces a decision problem where:
- Actions = partition cells (encoded as cell indices)
- Utility(m, i) = 1 if m is in cell i, else 0

Under this induced DP:
- Correctly identifying the cell = decision-theoretic optimality
- Goal equivalence = same optimal action
- Partition refinement = Blackwell dominance (more info never hurts)

This is **Sumers et al. Theorem 2**: Any QUD is some decision problem.

The converse is NOT true (Theorem 3): Decision-theoretic relevance is
strictly more expressive than QUD partitions. Continuous utility gradations
cannot be captured by discrete cells.

### The Deep Connection

The QUD goal projection (goalEquiv) and decision-theoretic utility are two
perspectives on the same mathematical object:

```
         QUD Partition
             ↓
    {cell₁, cell₂, ..., cellₙ}
             ↓
    Decision Problem:
    - Actions = {1, 2, ..., n}
    - U(m, i) = 1 iff m ∈ cellᵢ
             ↓
    Optimal action = identify correct cell
             ↓
    DT utility = partition utility
```

This explains why RSA with QUDs is coherent: the pragmatic goal (answer the
QUD correctly) IS a decision problem, and the speaker optimizes for it.

For the formal proofs, see:
- `Theories/Montague/Questions/GSVanRooyBridge.lean` (Blackwell's theorem)
- `Theories/Comparisons/RelevanceTheories.lean` (Sumers theorems 1-3)
-/

end QUD
