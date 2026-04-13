import Linglib.Fragments.Mayan.Params

/-!
# Shared Tseltalan Infrastructure
@cite{aissen-polian-2025} @cite{polian-2013}

Descriptive types shared across the Tseltalan subgroup (Tsotsil, Tseltal).
Both languages share agreement paradigm assignment and grammatical function
classification. They differ in agreement exponents and Set B marker
position (Tsotsil: prefixal/suffixal; Tseltal: consistently suffixal).

## Agreement System (Table 1 of @cite{aissen-polian-2025})

| Form   | Function | Tseltal  | Tsotsil          |
|--------|----------|----------|------------------|
| Set A  | A, Psr   | prefixal | prefixal         |
| Set B  | S and O  | suffixal | prefixal/suffixal|
-/

namespace Fragments.Mayan.Tseltalan

open Fragments.Mayan (MarkerSet)

-- ============================================================================
-- § 1: Grammatical Functions
-- ============================================================================

/-- Grammatical functions in Tseltalan, determining which agreement
    marker set cross-references each argument.

    These are traditional Mayanist descriptive categories
    (footnote 9 of @cite{aissen-polian-2025}).

    | Function                           | Marker Set |
    |------------------------------------|------------|
    | A (transitive subject)             | Set A      |
    | S_A (agentive intransitive subject)| Set B      |
    | S_O (patientive intransitive subj) | Set B      |
    | O (transitive/ditransitive object) | Set B      |
    | G (applied argument)               | Set B      |
    | Possessor (genitive)               | Set A      | -/
inductive GramFunction where
  | A    -- transitive subject (agent)
  | S_A  -- intransitive subject (agentive)
  | S_O  -- intransitive subject (patientive)
  | O    -- transitive/ditransitive object
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
-- § 2: Shared Theorems
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

end Fragments.Mayan.Tseltalan
