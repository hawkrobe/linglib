import Linglib.Fragments.Mayan.Params
import Linglib.Features.Prominence

/-!
# Shared Tseltalan Infrastructure

Descriptive types shared across the Tseltalan subgroup, Tsotsil and Tseltal
([aissen-polian-2025]; [polian-2013]). Both languages share agreement
paradigm assignment and grammatical-function classification; they differ in
agreement exponents and Set B marker position (Tsotsil prefixal or suffixal,
Tseltal consistently suffixal).

## Main declarations

* `Mayan.Tseltalan.GramFunction` with `.markerSet` and `.toArgumentRole?`:
  the shared Split-S grammatical functions, their Set A / Set B assignment,
  and projection to the canonical `ArgumentRole`.
* `Mayan.Tseltalan.absPosition`: the subgroup-level LOW-ABS constant.

## Implementation notes

Agreement system ([aissen-polian-2025] Table 1):

| Form   | Function | Tseltal  | Tsotsil          |
|--------|----------|----------|------------------|
| Set A  | A, Psr   | prefixal | prefixal         |
| Set B  | S and O  | suffixal | prefixal/suffixal|
-/

namespace Mayan.Tseltalan

open Mayan (MarkerSet)

/-! ### Grammatical functions -/

/-- Grammatical functions in Tseltalan — traditional Mayanist descriptive
    categories (footnote 9 of [aissen-polian-2025]) — determining which
    agreement marker set cross-references each argument. -/
inductive GramFunction where
  | A    -- transitive subject (agent)
  | S_A  -- intransitive subject (agentive)
  | S_O  -- intransitive subject (patientive)
  | O    -- transitive/ditransitive object
  | G    -- applied argument of ditransitive
  | psr  -- possessor (genitive)
  deriving DecidableEq, Repr

/-- The marker set cross-referencing each grammatical function (Set A =
    ergative/genitive, Set B = absolutive); shared across Tseltalan
    ([aissen-polian-2025], [polian-2013]). -/
def GramFunction.markerSet : GramFunction → MarkerSet
  | .A   => .setA
  | .S_A => .setB
  | .S_O => .setB
  | .O   => .setB
  | .G   => .setB
  | .psr => .setA

/-! ### Shared theorems -/

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

/-! ### Absolutive position (LOW-ABS) -/

/-- Tseltalan absolutive morphemes appear in low (post-stem) position; both
    Tsotsil and Tseltal inherit this LOW-ABS constant. LOW-ABS refers to the
    structural position of the licensing head, not the linear position of
    every Set B exponent (which varies by language and context).
    [aissen-polian-2025] p. 97; [polian-2013]. -/
def absPosition : Mayan.ABSPosition := .low

/-! ### Projection to canonical ArgumentRole -/

/-- Project the Tseltalan Split-S grammatical function to the canonical
    `ArgumentRole` (S/A/P/R/T). Partial (`Option`-valued): `.A → .A`,
    `.O → .P`, `.G → .R` map cleanly; `.S_A`, `.S_O → .S` collapses the
    agentivity distinction (lossy but expected for cross-Mayan theorems that
    don't track Split-S); `.psr → none`, since possessors are DP-internal
    with no `ArgumentRole` analog. Cross-Mayan consumers use this projection;
    the Aissen-Polian possessor-extraction analysis uses `GramFunction`
    directly for its DP-internal claims. -/
def GramFunction.toArgumentRole? : GramFunction → Option Features.Prominence.ArgumentRole
  | .A   => some .A
  | .S_A => some .S
  | .S_O => some .S
  | .O   => some .P
  | .G   => some .R
  | .psr => none

end Mayan.Tseltalan
