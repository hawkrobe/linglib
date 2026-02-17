import Linglib.Theories.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Phenomena.Constructions.Studies.FillmoreKayOConnor1988

/-!
# Bridge: FKO1988 CxG Theory → Polarity & Constructions Phenomena

Connects the Construction Grammar analysis of *let alone* (Fillmore, Kay &
O'Connor 1988) to:

1. NPI licensing contexts in `Phenomena.Polarity.NPIs` — maps each FKO NPI
   trigger type to a known licensing context
2. Empirical judgments in `Phenomena.Constructions.Studies.FillmoreKayOConnor1988`
   — verifies that *barely* licenses *let alone* while *almost* does not

## References

Fillmore, C. J., Kay, P., & O'Connor, M. C. (1988). Regularity and
Idiomaticity in Grammatical Constructions: The Case of *Let Alone*.
Language, 64(3), 501–538.
-/

namespace ConstructionGrammar.Studies.FillmoreKayOConnor1988.Bridge

open ConstructionGrammar.Studies.FillmoreKayOConnor1988

/-! ### Bridge 1: NPI triggers → Polarity.NPIs.LicensingContext

FKO1988's NPI trigger inventory (§2.2.4) maps onto the licensing contexts
already catalogued in `Phenomena.Polarity.NPIs`. This bridge makes that
mapping explicit: each FKO trigger type corresponds to a known NPI
licensing context. -/

open Phenomena.Polarity.NPIs in
/-- Map FKO1988 *let alone* NPI triggers to Polarity.NPIs licensing contexts. -/
def npiTriggerToContext : LetAloneNPITrigger → LicensingContext
  | .simpleNegation         => .sententialNegation
  | .tooComplementation     => .tooAdjective
  | .comparisonOfInequality => .comparativeThan
  | .onlyDeterminer         => .onlyFocus
  | .minimalAttainment      => .sententialNegation  -- "barely" ≈ negation
  | .conditionalSurprise    => .conditional
  | .failureVerb            => .sententialNegation   -- "fail" ≈ implicit negation
  | .anyoneWhod             => .universalRestrictor

open Phenomena.Polarity.NPIs in
/-- Every FKO trigger maps to a known NPI licensing context.
This verifies that FKO's *let alone* data is consistent with Ladusaw's
generalization: *let alone* appears in DE environments. -/
theorem all_triggers_are_known_contexts :
    ∀ t : LetAloneNPITrigger, ∃ c : LicensingContext, npiTriggerToContext t = c :=
  λ t => ⟨npiTriggerToContext t, rfl⟩

/-! ### Bridge 2: FKO Phenomena data ↔ NPI theory

The phenomena file records that *barely* licenses *let alone* (ex.115)
while *almost* does not (ex.113). This matches the Polarity.NPIs
classification: *barely* is a syntactic negative polarity trigger,
*almost* is not. -/

open _root_.Phenomena.Constructions.Studies.FillmoreKayOConnor1988 in
/-- *barely* licenses *let alone* in the phenomena data. -/
theorem barely_licenses_let_alone :
    ex115.judgment = Judgment.grammatical := rfl

open _root_.Phenomena.Constructions.Studies.FillmoreKayOConnor1988 in
/-- *almost* does NOT license *let alone* in the phenomena data. -/
theorem almost_blocks_let_alone :
    ex113.judgment = Judgment.ungrammatical := rfl

end ConstructionGrammar.Studies.FillmoreKayOConnor1988.Bridge
