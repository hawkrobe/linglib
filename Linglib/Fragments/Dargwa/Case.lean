module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Case.Alignment
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

@[expose] public section

namespace Dargwa.Case

-- ============================================================================
-- § 1: Grammatical Case Inventory
-- ============================================================================

/-- Dargwa grammatical case inventory: ABS(∅), ERG(-li), GEN(-la, -lla),
    DAT(-ž), COM(-c:ele), ADV(-le).

    We use `Case` values. The adverbial case is mapped to `ess`
    (essive) as the closest typological equivalent — it marks
    "being-in-a-state" predicates, analogous to the Finnish essive.

    Genitive has two allomorphs: -la and -lla. -/
def inventory : Finset Case :=
  {.abs, .erg, .gen, .dat, .com, .ess}

-- ============================================================================
-- § 2: Consistent Ergative Alignment
-- ============================================================================

/-- Dargwa alignment: consistently ergative — no tense/aspect split.
    Transitive A-arguments always take ergative *-li*;
    S and P arguments take unmarked absolutive. -/
def alignment : Alignment.AlignmentType := .ergative

/-- Case of the transitive agent (A-argument): always ergative. -/
def agentCase : Case := .erg

/-- Case of the S-argument and P-argument: always absolutive. -/
def patientCase : Case := .abs

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- The inventory contains both core ergative cases. -/
theorem has_core_ergative :
    .abs ∈ inventory ∧ .erg ∈ inventory := by
  refine ⟨?_, ?_⟩ <;> decide

end Dargwa.Case
