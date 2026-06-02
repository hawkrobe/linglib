import Linglib.Fragments.Mayan.Params
import Linglib.Features.Prominence

/-!
# Shared Tseltalan Infrastructure
[aissen-polian-2025] [polian-2013]

Descriptive types shared across the Tseltalan subgroup (Tsotsil, Tseltal).
Both languages share agreement paradigm assignment and grammatical function
classification. They differ in agreement exponents and Set B marker
position (Tsotsil: prefixal/suffixal; Tseltal: consistently suffixal).

## Agreement System (Table 1 of [aissen-polian-2025])

| Form   | Function | Tseltal  | Tsotsil          |
|--------|----------|----------|------------------|
| Set A  | A, Psr   | prefixal | prefixal         |
| Set B  | S and O  | suffixal | prefixal/suffixal|
-/

namespace Mayan.Tseltalan

open Mayan (MarkerSet)

-- ============================================================================
-- § 1: Grammatical Functions
-- ============================================================================

/-- Grammatical functions in Tseltalan, determining which agreement
    marker set cross-references each argument.

    These are traditional Mayanist descriptive categories
    (footnote 9 of [aissen-polian-2025]).

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
    Shared across Tseltalan ([aissen-polian-2025], [polian-2013]). -/
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

-- ============================================================================
-- § 3: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Tseltalan absolutive morphemes appear in low (post-stem) position.
    Both Tsotsil and Tseltal share this LOW-ABS classification — see
    `Tsotsil.absPosition` and `Tseltal.absPosition`
    for the per-language definitions, which are definitionally equal to this
    subgroup-level constant. The LOW-ABS classification refers to the
    structural position of the licensing head, not the linear position
    of every Set B exponent (which varies by language and context).
    [aissen-polian-2025] p. 97; [polian-2013]. -/
def absPosition : Mayan.ABSPosition := .low

-- ============================================================================
-- § 4: Projection to Canonical ArgumentRole
-- ============================================================================

/-- Project the Tseltalan-specific Split-S grammatical function down to
    the canonical pan-linguistic `ArgumentRole` (S/A/P/R/T) used across
    linglib. The projection is **partial** (`Option`-valued):

    - `.A → .A`, `.O → .P`, `.G → .R`: verbal arguments map cleanly.
    - `.S_A`, `.S_O → .S`: agentivity distinction is collapsed (lossy
      but expected for cross-Mayan typology theorems that don't track
      Split-S granularity).
    - `.psr → none`: possessors are DP-internal, with no `ArgumentRole`
      analog. Cross-Mayan typology theorems quantify over verbal
      arguments only.

    Tseltal/Tsotsil consumers of cross-Mayan theorems use this projection
    to feed Tseltalan agreement data into the canonical inventory; the
    Aissen-Polian possessor-extraction analysis continues to use
    `GramFunction` directly for its DP-internal claims. -/
def GramFunction.toArgumentRole? : GramFunction → Option Features.Prominence.ArgumentRole
  | .A   => some .A
  | .S_A => some .S
  | .S_O => some .S
  | .O   => some .P
  | .G   => some .R
  | .psr => none

end Mayan.Tseltalan
