import Linglib.Fragments.Mayan.Params

/-!
# Shared Tseltalan Infrastructure
@cite{aissen-polian-2025} @cite{polian-2013}

Types shared across the Tseltalan subgroup (Tsotsil, Tseltal). Both
languages share agreement paradigm assignment, clause types, and
grammatical function classification. They differ in agreement exponents
and Set B marker position (Tsotsil: prefixal/suffixal; Tseltal:
consistently suffixal).

## Clause Structure (@cite{aissen-polian-2025}, (9))

- **Transitive**: vP layer introduces external argument (A) in Spec,vP.
  Set A indexes A; Set B indexes O.
- **Unergative**: vP layer introduces external argument (S_A) in Spec,vP.
  Set B indexes S_A.
- **Unaccusative**: no vP layer; internal argument (S_O) is complement of V.
  Set B indexes S_O.
-/

namespace Fragments.Mayan.Tseltalan

open Fragments.Mayan (MarkerSet)

-- ============================================================================
-- § 1: Grammatical Functions
-- ============================================================================

/-- Grammatical functions in Tseltalan, determining which agreement
    marker set cross-references each argument.

    | Function                       | Marker Set |
    |--------------------------------|------------|
    | A (transitive agent)           | Set A      |
    | S_A (unergative subject)       | Set B      |
    | S_O (unaccusative subject)     | Set B      |
    | O (transitive/ditransitive obj)| Set B      |
    | G (applied argument)           | Set B      |
    | Possessor (genitive)           | Set A      | -/
inductive GramFunction where
  | A    -- external argument of transitive
  | S_A  -- external argument of intransitive (unergative)
  | S_O  -- internal argument of intransitive (unaccusative)
  | O    -- internal argument of (di)transitive
  | G    -- applied argument of ditransitive
  | psr  -- possessor (genitive)
  deriving DecidableEq, Repr

/-- The marker set that cross-references each grammatical function.
    Set A = ergative/genitive; Set B = absolutive.
    Shared across Tseltalan (@cite{aissen-polian-2025}, @cite{polian-2013}). -/
def GramFunction.markerSet : GramFunction → MarkerSet
  | .A   => .setA
  | .S_A => .setB
  | .S_O => .setB
  | .O   => .setB
  | .G   => .setB
  | .psr => .setA

-- ============================================================================
-- § 2: Clause Types
-- ============================================================================

/-- Clause types in Tseltalan, determining the functional structure
    above VP (@cite{aissen-polian-2025}, (9)). -/
inductive ClauseType where
  /-- Transitive: vP introduces A in Spec,vP; V takes O as complement. -/
  | transitive
  /-- Unergative: vP introduces S_A in Spec,vP; no internal argument. -/
  | unergative
  /-- Unaccusative: no vP; S_O is complement of V. -/
  | unaccusative
  deriving DecidableEq, Repr

/-- Whether a clause type has a vP layer (little-v projection).
    Transitive and unergative clauses introduce an external argument
    in Spec,vP; unaccusative clauses do not. -/
def ClauseType.hasVP : ClauseType → Bool
  | .transitive   => true
  | .unergative   => true
  | .unaccusative => false

-- ============================================================================
-- § 3: Shared Theorems
-- ============================================================================

/-- Ergative-genitive homophony: Set A cross-references both transitive
    agents and possessors. A pan-Mayan pattern. -/
theorem erg_gen_homophonous :
    GramFunction.A.markerSet = GramFunction.psr.markerSet := rfl

/-- All absolutive arguments (S_A, S_O, O, G) use Set B. -/
theorem abs_uniform :
    GramFunction.S_A.markerSet = .setB ∧
    GramFunction.S_O.markerSet = .setB ∧
    GramFunction.O.markerSet = .setB ∧
    GramFunction.G.markerSet = .setB := ⟨rfl, rfl, rfl, rfl⟩

/-- Transitive and unergative clauses have a vP layer;
    unaccusative clauses do not. -/
theorem vp_distribution :
    ClauseType.transitive.hasVP = true ∧
    ClauseType.unergative.hasVP = true ∧
    ClauseType.unaccusative.hasVP = false := ⟨rfl, rfl, rfl⟩

end Fragments.Mayan.Tseltalan
