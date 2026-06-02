import Linglib.Features.Case
import Linglib.Features.Case
/-!
# Dargwa (Tanti) Case Inventory [sumbatova-2021]

Dargwa (Tanti dialect; Nakh-Dagestanian) has a **consistently ergative**
alignment system — unlike Georgian's tense-conditioned split. All transitive
verbs mark the A-argument with ergative *-li* and leave the P-argument
unmarked (absolutive). There is no split conditioning.

## Grammatical Cases (Table 4.3 of [sumbatova-2021])

| Case        | Morpheme | Function                                |
|-------------|----------|-----------------------------------------|
| absolutive  | ∅        | S-argument, P-argument, nominal pred.   |
| ergative    | -li      | A-argument, instrument                  |
| genitive    | -la, -lla | nominal modifier, possessor            |
| dative      | -ž       | experiencer, recipient, benefactive     |
| comitative  | -c:ele   | comitative, instrument                  |
| adverbial   | -le      | nominal predicate, secondary predicate  |

The rich locative system (8 localizations × 4 orientations × 4 directions)
is in `Dargwa/Locatives.lean`.
-/

namespace Dargwa.Case

-- ============================================================================
-- § 1: Grammatical Case Inventory
-- ============================================================================

/-- Dargwa grammatical case inventory: ABS(∅), ERG(-li), GEN(-la, -lla),
    DAT(-ž), COM(-c:ele), ADV(-le).

    We use `Features.Case` values. The adverbial case is mapped to `ess`
    (essive) as the closest typological equivalent — it marks
    "being-in-a-state" predicates, analogous to the Finnish essive.

    Genitive has two allomorphs: -la and -lla. -/
def caseInventory : Finset Features.Case :=
  {.abs, .erg, .gen, .dat, .com, .ess}

/-- Dargwa's grammatical case inventory violates strict contiguity
    on Blake's hierarchy: COM (rank 1) and ESS (rank 0) are present
    without LOC (rank 3) or ABL/INST (rank 2). This is expected:
    Dargwa's rich *locative system* (8 localizations × 4 orientations)
    functionally covers spatial and source meanings that LOC and ABL
    encode in other languages. The grammatical vs. locative split is
    a structural feature of Nakh-Dagestanian languages. -/
theorem inventory_not_strictly_contiguous :
    ¬ Features.Case.IsValidInventory caseInventory := by decide

-- ============================================================================
-- § 2: Consistent Ergative Alignment
-- ============================================================================

/-- Dargwa alignment: consistently ergative — no tense/aspect split.
    Transitive A-arguments always take ergative *-li*;
    S and P arguments take unmarked absolutive. -/
def alignment : Features.AlignmentFamily := .ergative

/-- Case of the transitive agent (A-argument): always ergative. -/
def agentCase : Features.Case := .erg

/-- Case of the S-argument and P-argument: always absolutive. -/
def patientCase : Features.Case := .abs

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- The inventory contains both core ergative cases. -/
theorem has_core_ergative :
    .abs ∈ caseInventory ∧ .erg ∈ caseInventory := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Dargwa is consistently ergative (no split). -/
theorem consistently_ergative :
    alignment = .ergative := rfl

end Dargwa.Case
