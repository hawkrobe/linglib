/-
# Verb Position Phenomena

Concrete syntactic structures demonstrating verb position patterns.

## Examples

1. **Germanic V2**: V-to-T-to-C movement
2. **Simple VP**: Baseline structure for comparison
3. **Long Head Movement**: V moves to specifier position (Bulgarian)

## References

- Carnie, A. (2021). "Syntax: A Generative Introduction", 4th ed., Chapter 14 (V2)
- Adger, D. (2003). "Core Syntax", Chapters 5-6 (Verb Movement)
-/

import Linglib.Theories.Minimalism.Labeling

namespace Phenomena.WordOrderAlternations.VerbPosition

open Minimalism

-- ============================================================================
-- Part 1: Lexical Items
-- ============================================================================

-- Verbs
def verbSleep : LIToken := ⟨.simple .V [], 101⟩           -- intransitive
def verbEat : LIToken := ⟨.simple .V [.D], 102⟩           -- transitive
def verbSay : LIToken := ⟨.simple .V [.C], 103⟩           -- takes CP complement

-- Nouns
def nounJohn : LIToken := ⟨.simple .N [], 201⟩
def nounPizza : LIToken := ⟨.simple .N [], 202⟩
def nounBook : LIToken := ⟨.simple .N [], 203⟩

-- Determiners
def detThe : LIToken := ⟨.simple .D [.N], 301⟩
def detA : LIToken := ⟨.simple .D [.N], 302⟩

-- Functional heads
def tenseT : LIToken := ⟨.simple .T [.V], 401⟩            -- T selects V
def compC : LIToken := ⟨.simple .C [.T], 501⟩             -- C selects T

-- Complex LI: T that has incorporated V (for head-to-head)
def tensePlusV : LIToken := ⟨(LexicalItem.simple .T [.V]).combine (LexicalItem.simple .V [.D]), 402⟩

-- ============================================================================
-- Part 2: Basic Phrase Structure
-- ============================================================================

/-- DP: "the pizza" -/
def dpThePizza : SyntacticObject :=
  .node (.leaf detThe) (.leaf nounPizza)

/-- DP: "John" (bare NP as DP) -/
def dpJohn : SyntacticObject :=
  .node (.leaf detThe) (.leaf nounJohn)  -- simplified: "the John"

/-- VP: "eat the pizza" - V merges with DP complement -/
def vpEatPizza : SyntacticObject :=
  .node (.leaf verbEat) dpThePizza

/-- VP: "sleep" - intransitive -/
def vpSleep : SyntacticObject :=
  .leaf verbSleep  -- Just the verb (no complement needed for intransitive)

-- ============================================================================
-- Part 3: Clause Structure (Base Position)
-- ============================================================================

/-- T': T merges with VP -/
def tBarEatPizza : SyntacticObject :=
  .node (.leaf tenseT) vpEatPizza

/-- TP: Subject in Spec-TP (simplified - DP merges with T') -/
def tpJohnEatPizza : SyntacticObject :=
  .node dpJohn tBarEatPizza

/-- C': C merges with TP -/
def cBarJohnEatPizza : SyntacticObject :=
  .node (.leaf compC) tpJohnEatPizza

/-- CP: Full clause -/
def cpJohnEatPizza : SyntacticObject :=
  cBarJohnEatPizza  -- No Spec-CP in declarative

-- ============================================================================
-- Part 4: Head-to-Head Movement (V-to-T)
-- ============================================================================

/-
In V-to-T movement:
- V moves from VP to T
- T becomes a complex head [T + V]
- The V features are "inside" T

Structure after V-to-T:
  TP
 /  \
DP   T'
    /  \
  T+V   VP
        |
       tV (trace)
-/

/-- T+V: Complex head after V-to-T movement -/
def tPlusV : SyntacticObject :=
  .leaf tensePlusV  -- T with incorporated V features

/-- VP with V "moved out" (represented as just the complement) -/
def vpTrace : SyntacticObject :=
  dpThePizza  -- The object remains; V has moved

/-- T' after V-to-T: [T+V] merges with remnant VP -/
def tBarAfterVtoT : SyntacticObject :=
  .node tPlusV vpTrace

/-- TP after V-to-T -/
def tpAfterVtoT : SyntacticObject :=
  .node dpJohn tBarAfterVtoT

-- ============================================================================
-- Part 5: Verifying Selection and Projection
-- ============================================================================

-- Check that our structures have correct labels
#eval labelCat dpThePizza       -- some .D (determiner projects)
#eval labelCat vpEatPizza       -- some .V (verb projects)
#eval labelCat tBarEatPizza     -- some .T (tense projects)

-- Check selection
#eval selectsB (.leaf detThe) (.leaf nounPizza)  -- true: D selects N
#eval selectsB (.leaf verbEat) dpThePizza        -- true: V selects D
#eval selectsB (.leaf tenseT) vpEatPizza         -- true: T selects V
#eval selectsB (.leaf compC) tpJohnEatPizza      -- true: C selects T

-- ============================================================================
-- Part 6: Verifying Projection Relations
-- ============================================================================

-- In VP = {V, DP}:
-- V projects in VP (V is the head)
#eval projectsInB (.leaf verbEat) vpEatPizza  -- true

-- DP does NOT project in VP
#eval projectsInB dpThePizza vpEatPizza  -- false

-- In DP = {D, N}:
-- D projects in DP
#eval projectsInB (.leaf detThe) dpThePizza  -- true

-- ============================================================================
-- Part 7: Movement Structures for Proofs
-- ============================================================================

/-- Structure BEFORE movement: Full CP with V in base position -/
def beforeMovement : SyntacticObject := cpJohnEatPizza

/-- Structure showing V's projection chain in base position -/
def vInBasePosition : SyntacticObject := vpEatPizza

/-- The verb leaf -/
def theVerb : SyntacticObject := .leaf verbEat

-- Verify V projects in VP
#eval projectsInB theVerb vInBasePosition  -- should be true

-- Verify V is contained in CP
#eval match beforeMovement with
  | .node a _ => match a with
    | .node b _ => match b with
      | .node c _ => match c with
        | .node _ vp => match vp with
          | .node v _ => v == theVerb
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

-- ============================================================================
-- Part 8: Head-to-Specifier Example (Simplified)
-- ============================================================================

/-
In head-to-specifier movement:
- A head X moves to a specifier position
- X becomes maximal in the new position (it's a phrase now)
- The target Y still projects

Example: V moves to Spec-CP (as in Bulgarian long head movement)
-/

/-- Spec-CP filled by moved V -/
def cpWithVInSpec : SyntacticObject :=
  .node theVerb cBarJohnEatPizza  -- V in Spec, C' as complement

-- In this structure, V is a specifier (sister to C')
-- C projects (since C selects T, not V)
#eval labelCat cpWithVInSpec  -- Should be .C if C projects

-- V does NOT project in the new structure (different label)
#eval projectsInB theVerb cpWithVInSpec  -- false (V doesn't project here)

-- ============================================================================
-- Part 9: Summary
-- ============================================================================

/-
## Key Observations

1. **Selection determines projection**: The element that selects projects.
   - V[D] + DP → VP (V projects because V selects D)
   - T[V] + VP → T' (T projects because T selects V)

2. **Projection determines minimality**:
   - If X projects in Y, X is -minimal in Y
   - If X doesn't project in anything, X is +minimal

3. **Containment determines maximality**:
   - If something projects IN X, X is -maximal
   - If nothing projects in X, X is +maximal (X is a "phrase")

4. **Movement changes projection relations**:
   - Head-to-head: mover reprojects (stays -minimal)
   - Head-to-spec: mover stops projecting (becomes +minimal)

5. **Terminological inversion**:
   - Lexical items are "phrases" in Def 22 sense (+max)
   - Maximal projections are "heads" in Def 22 sense (+min, -max)
-/

end Phenomena.WordOrderAlternations.VerbPosition
