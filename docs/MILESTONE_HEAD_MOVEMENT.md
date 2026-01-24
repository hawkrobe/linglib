# Milestone: Harizanov's Syntactic Head Movement

Formalization of Boris Harizanov's "Syntactic Head Movement" paper, which argues for two distinct types of syntactic head movement.

## Core Thesis

Head movement comes in two varieties:
1. **Head-to-specifier**: Moved head is maximal (+max, -min) in derived position
2. **Head-to-head**: Moved head reprojects (is minimal: +min, -max) in derived position

Both violate the Head Movement Constraint (HMC), distinguishing them from **Amalgamation** (post-syntactic PF operation that respects HMC).

## Phase 1: Core Data Structures

### 1.1 Lexical Items (Definition 10, 88)

```lean
-- Categorial features
inductive Cat where | V | N | A | P | C | T | D | ...

-- Selectional stack (what the LI selects)
abbrev SelStack := List Cat

-- Simple LI: single ⟨CAT, SEL⟩ pair
structure SimpleLI where
  cat : Cat
  sel : SelStack

-- Complex LI: list of ⟨CAT, SEL⟩ pairs (for head-to-head movement)
-- When X moves to Y via head-to-head, Y becomes complex: [Y's features, X's features]
structure LexicalItem where
  features : List SimpleLI
  deriving DecidableEq

-- An LI "token" is a specific instance in a derivation
structure LIToken where
  item : LexicalItem
  id : Nat  -- unique identifier
```

### 1.2 Syntactic Objects (Definition 11)

```lean
-- SO is either an LI token or a set of SOs
inductive SyntacticObject where
  | leaf : LIToken → SyntacticObject
  | set : SyntacticObject → SyntacticObject → SyntacticObject
```

### 1.3 Merge (Definition 12)

```lean
-- Merge is the structure-building operation
def merge (x y : SyntacticObject) : SyntacticObject :=
  .set x y

-- Constraint: X and Y must be distinct (not identical)
def validMerge (x y : SyntacticObject) : Prop :=
  x ≠ y
```

## Phase 2: Structural Relations

### 2.1 Containment (Definition 13-14)

```lean
-- Immediate containment: X ∈ Y
def immediatelyContains (container contained : SyntacticObject) : Prop :=
  match container with
  | .leaf _ => False
  | .set a b => contained = a ∨ contained = b

-- Transitive containment (dominance)
def contains (container contained : SyntacticObject) : Prop :=
  immediatelyContains container contained ∨
  ∃ z, immediatelyContains container z ∧ contains z contained
```

### 2.2 Labeling and Projection (Definition 16-17, 20)

```lean
-- The label of an SO
def label : SyntacticObject → Option LexicalItem

-- X projects in Y iff X's label = Y's label and X immediately contained in Y
def projects (x y : SyntacticObject) : Prop :=
  immediatelyContains y x ∧ label x = label y

-- Selection determines projection:
-- If X selects Y, then X projects (X is the "selector")
```

### 2.3 Maximality and Minimality (Definition 21)

```lean
-- These are RELATIONAL properties, not intrinsic

-- X is minimal in Y iff X is contained in Y and doesn't project in anything in Y
def isMinimalIn (x y : SyntacticObject) : Prop :=
  contains y x ∧ ¬∃ z, contains y z ∧ projects x z

-- X is maximal in Y iff X is contained in Y and nothing in Y projects into X
def isMaximalIn (x y : SyntacticObject) : Prop :=
  contains y x ∧ ¬∃ z, contains y z ∧ projects z x ∧ z ≠ x
```

### 2.4 Heads and Phrases (Definition 22)

```lean
-- A head in Y: +minimal, -maximal
def isHeadIn (x y : SyntacticObject) : Prop :=
  isMinimalIn x y ∧ ¬isMaximalIn x y

-- A phrase in Y: +maximal (minimality can vary)
def isPhraseIn (x y : SyntacticObject) : Prop :=
  isMaximalIn x y
```

## Phase 3: Head Movement Types

### 3.1 Head-to-Specifier Movement

The moved head X:
- Starts as head in its base position (+min, -max)
- Ends as **specifier** in derived position (+max, -min)
- The target Y projects (Y's label becomes the label of the merged structure)

Example: Bulgarian Long Head Movement, Irish VSO

```lean
-- After head-to-spec movement of X to YP:
-- X is maximal in the resulting structure
-- Y still projects (is the label)
```

### 3.2 Head-to-Head Movement (Reprojection)

The moved head X:
- Starts as head in base position (+min, -max)
- Ends as **head** in derived position (+min, -max) — X **reprojects**
- Requires X to be a **complex LI** that can "absorb" features

Example: Germanic V2 (V-to-C), verb-to-T movement

```lean
-- Complex LI formation:
-- When V moves to T, T becomes a complex LI: [T-features, V-features]
-- The V part is still minimal (it's projecting!)

-- Key insight: head-to-head movement = Internal Merge + reprojection
```

### 3.3 Key Distinction

| Property | Head-to-Spec | Head-to-Head |
|----------|--------------|--------------|
| X in derived position | +max, -min | +min, -max |
| What projects | Target Y | Moved X (reprojects) |
| LI complexity | Simple | Complex (absorbs features) |
| Locality | Can be long-distance | Phase-bound |

## Phase 4: Constraints and Theorems

### 4.1 Head Movement Constraint (HMC)

```lean
-- HMC: Head movement cannot skip an intervening head
-- BOTH types of syntactic head movement violate HMC
-- This distinguishes them from Amalgamation (PF operation)

theorem head_to_spec_violates_hmc : ...
theorem head_to_head_violates_hmc : ...
```

### 4.2 Phase Impenetrability Condition (PIC)

```lean
-- Head-to-head movement is phase-bound
-- Once a phase is complete, only the edge is accessible

-- This explains why head-to-head is local while head-to-spec can be long-distance
theorem head_to_head_phase_bound : ...
```

### 4.3 Interpretive Effects

```lean
-- Head-to-head: single complex predicate (V+T interpreted together)
-- Head-to-spec: two separate predicates

theorem head_to_head_single_predicate : ...
theorem head_to_spec_separate_predicates : ...
```

## Phase 5: Phenomena

### 5.1 Germanic V2 (Head-to-Head)

```
[CP C [TP T [VP V ... ]]]
→ V moves to T (head-to-head, T becomes [T, V])
→ V+T moves to C (head-to-head, C becomes [C, T, V])
```

### 5.2 Bulgarian Long Head Movement (Head-to-Spec)

```
[CP ... [TP ... [VP V ... ]]]
→ V moves to Spec-CP (head-to-spec)
→ V is maximal in derived position
→ Long-distance, violates HMC
```

### 5.3 Predicate Fronting (Amalgamation, not Head Movement)

```
[CP Pred-XP C [TP ... ]]
→ XP moves to Spec-CP (phrasal movement)
→ Predicate amalgamates with C at PF
→ Respects HMC (it's post-syntactic)
```

## File Structure

```
Theories/Minimalism/
├── Basic.lean              -- (existing, minimal)
├── Structure.lean          -- (existing, minimal)
├── SyntacticObjects.lean   -- Phase 1: SOs, LIs, Merge
├── Containment.lean        -- Phase 2.1: containment relations
├── Labeling.lean           -- Phase 2.2-2.4: projection, max/min, heads
├── HeadMovement/
│   ├── Basic.lean          -- Movement operations
│   ├── HeadToSpec.lean     -- Head-to-specifier analysis
│   ├── HeadToHead.lean     -- Head-to-head with complex LIs
│   └── Amalgamation.lean   -- PF operation (for contrast)
└── Constraints/
    ├── HMC.lean            -- Head Movement Constraint
    └── PIC.lean            -- Phase Impenetrability

Phenomena/HeadMovement/
├── GermanicV2.lean         -- V-to-T-to-C
├── BulgarianLHM.lean       -- Long head movement
└── PredicateFronting.lean  -- Amalgamation cases
```

## Implementation Order

1. **SyntacticObjects.lean** - Core types (LI, SO, Merge)
2. **Containment.lean** - Structural relations
3. **Labeling.lean** - Projection, maximality, heads
4. **HeadMovement/Basic.lean** - Movement operation types
5. **HeadMovement/HeadToSpec.lean** - First movement type
6. **HeadMovement/HeadToHead.lean** - Second movement type with complex LIs
7. **Constraints/HMC.lean** - HMC and its violations
8. **Phenomena/** - Concrete examples

## Key Theorems to Prove

1. `complex_li_enables_reprojection`: Complex LIs are necessary for head-to-head
2. `head_to_spec_yields_maximal`: Moved head is maximal after head-to-spec
3. `head_to_head_yields_minimal`: Moved head stays minimal after head-to-head
4. `both_violate_hmc`: Both movement types violate HMC
5. `head_to_head_is_local`: Head-to-head is phase-bound (PIC)
6. `head_to_spec_can_be_long`: Head-to-spec can cross phase boundaries
7. `amalgamation_respects_hmc`: Amalgamation (PF) respects HMC

## Connection to Existing Linglib

- Extends `Theories/Minimalism/` which currently has only basic structure
- Will need to refactor existing `Structure.lean` to align with Harizanov's definitions
- Eventually connect to `Montague/` for interpretation (predicate formation)
