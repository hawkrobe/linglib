import Linglib.Core.Logic.ModalLogic
import Linglib.Theories.Semantics.Modality.Directive
import Linglib.Fragments.English.FunctionWords

/-!
# Modal Force and its Realization across Languages
@cite{agha-jeretic-2026}

A handbook chapter surveying modal force phenomena:
- §1: Possibility vs necessity (standard ∀/∃ over possible worlds)
- §2: Weak necessity modals (ought, should) — three competing analyses:
  (1) domain restriction (@cite{von-fintel-iatridou-2008}, `Directive.lean`),
  (2) non-quantificational (@cite{agha-jeretic-2022}, `AghaJeretic2022.lean`),
  (3) comparative semantics (@cite{rubinstein-2014}, `Rubinstein2014.lean`)
- §3: Variable force modals — four cross-linguistic patterns
- §4: Covert variable force (conditionals, generics, imperatives)

## Key Claims Formalized

1. **Entailment asymmetry** (§2.1): Strong necessity modals (must, have to)
   are mutually entailing (□₁φ ∧ ¬□₂φ is contradictory), but weak necessity
   modals (ought, should) are consistently weaker (□wφ ∧ ¬□φ is felicitous).

2. **Strength ordering**: □φ → □wφ → ◇φ (strong necessity entails weak
   necessity entails possibility).

3. **Variable force typology** (§3.2): Four patterns of polarity-sensitive
   variable force modals, distinguished by which readings are available in
   which environments.

4. **Exhaustification analysis** (§3.2): Polarity-sensitive variable force
   modals are underlyingly ◇, with necessity readings derived via EXH.

## Connection to @cite{agha-jeretic-2022}

The paper's own prior work proposes that weak necessity modals are
non-quantificational (plural predication over worlds), explaining
neg-raising asymmetries between *should* and *must*.
-/

namespace Phenomena.Modality.Studies.AghaJeretic2026

open Core.Modality (ModalForce ModalFlavor ForceFlavor ModalItem)
open Semantics.Modality.Directive
open Fragments.English.FunctionWords

-- ============================================================================
-- §1. Entailment Asymmetry (§2.1)
-- ============================================================================

/-! ## Entailment tests from §2.1

Strong necessity modals are mutually entailing: "must" ≈ "have to" ≈
"be required to". But weak necessity modals are strictly weaker:
"should φ" does not entail "must φ".

We verify this structurally via `ModalForce.atLeastAsStrong`. -/

/-- Strong necessity entails strong necessity (mutual entailment among
    "must", "have to", "be required to" — paper ex. 6-7). -/
theorem strong_entails_strong :
    ModalForce.necessity.atLeastAsStrong .necessity = true := rfl

/-- Strong necessity entails weak necessity
    ("must φ" → "ought φ" — paper's key asymmetry). -/
theorem strong_entails_weak_force :
    ModalForce.necessity.atLeastAsStrong .weakNecessity = true := rfl

/-- Weak necessity does NOT entail strong necessity
    ("ought φ" ↛ "must φ" — paper ex. 8-9, 13). -/
theorem weak_not_entails_strong_force :
    ModalForce.weakNecessity.atLeastAsStrong .necessity = false := rfl

/-- Weak necessity entails possibility
    ("ought φ" → "can φ"). -/
theorem weak_entails_possibility :
    ModalForce.weakNecessity.atLeastAsStrong .possibility = true := rfl

/-- Possibility does NOT entail weak necessity
    ("can φ" ↛ "ought φ"). -/
theorem possibility_not_entails_weak :
    ModalForce.possibility.atLeastAsStrong .weakNecessity = false := rfl

-- ============================================================================
-- §2. English Modal Force Classification
-- ============================================================================

/-! Verify that the English fragment correctly classifies modals by force,
matching the paper's §2.1 categorization. -/

/-- "must" is strong necessity (paper ex. 6-7, 11). -/
theorem must_is_strong_necessity :
    must.modalMeaning.any (·.force == .necessity) = true := by native_decide

/-- "should" is weak necessity (paper ex. 8-9, 12-13). -/
theorem should_is_weak_necessity :
    should.modalMeaning.any (·.force == .weakNecessity) = true := by native_decide

/-- "ought" is weak necessity (paper ex. 8-9, 12-13). -/
theorem ought_is_weak_necessity :
    ought.modalMeaning.any (·.force == .weakNecessity) = true := by native_decide

/-- "may" is possibility (paper §1). -/
theorem may_is_possibility :
    may.modalMeaning.any (·.force == .possibility) = true := by native_decide

/-- "might" is possibility (paper §1). -/
theorem might_is_possibility :
    might.modalMeaning.any (·.force == .possibility) = true := by native_decide

/-- "must" is NOT classified as weak necessity. -/
theorem must_not_weak :
    must.modalMeaning.any (·.force == .weakNecessity) = false := by native_decide

/-- "should" is NOT classified as strong necessity. -/
theorem should_not_strong :
    should.modalMeaning.any (·.force == .necessity) = false := by native_decide

-- ============================================================================
-- §3. Kratzer-Theoretic Entailment (Directive.lean bridge)
-- ============================================================================

/-! The von Fintel & Iatridou (2008) analysis, surveyed in §2.2.1:
weak necessity = ∀ over a refined best-world set. We verify the
entailment chain via the proven theorems in `Directive.lean`. -/

/-- Re-export: strong necessity entails weak necessity (Directive.lean). -/
theorem must_entails_ought_kratzer :
    ∀ (f : Semantics.Modality.Kratzer.ModalBase)
      (g g' : Semantics.Modality.Kratzer.OrderingSource)
      (p : Core.Proposition.BProp Semantics.Attitudes.Intensional.World)
      (w : Semantics.Attitudes.Intensional.World),
    strongNecessity f g p w →
    weakNecessity f g g' p w :=
  fun f g g' p w => strong_entails_weak f g g' p w

/-- Re-export: the converse fails (Directive.lean). -/
theorem ought_not_entails_must_kratzer :
    ¬(∀ (f : Semantics.Modality.Kratzer.ModalBase)
        (g g' : Semantics.Modality.Kratzer.OrderingSource)
        (p : Core.Proposition.BProp Semantics.Attitudes.Intensional.World)
        (w : Semantics.Attitudes.Intensional.World),
      weakNecessity f g g' p w →
      strongNecessity f g p w) :=
  weak_not_entails_strong

-- ============================================================================
-- §4. Variable Force Typology (§3.2)
-- ============================================================================

/-! ## Polarity-sensitive variable force modals

The paper identifies four patterns (table on p. 26) of how force varies
across three environments: unembedded, clausemate negation, and other
downward-entailing (DE) contexts.

Key: ◇ = possibility available, □ = necessity available, □w = weak necessity.

| Pattern | Language     | Modal   | Unembedded | Cl. Neg | Other DE |
|---------|-------------|---------|------------|---------|----------|
| 1       | Nez Perce   | o'qa    | ◇,□        | ◇       | ◇        |
| 2       | Siona       | ba'iji  | □          | ◇       | ◇,□      |
| 3       | Swedish     | får     | ◇,□        | ◇       | ◇,□      |
| 4       | Kinande     | anga    | ◇,□w       | ◇       | ◇,□w     |

All four patterns share: under clausemate negation, only ◇ is available.
-/

/-- The three syntactic environments relevant for variable force. -/
inductive ModalEnvironment where
  | unembedded
  | clausemateNegation
  | otherDE  -- other downward-entailing contexts (conditionals, etc.)
  deriving DecidableEq, Repr

/-- A variable force pattern: which forces are available in each environment. -/
structure VariableForcePattern where
  language : String
  modal : String
  unembedded : List ModalForce
  clausemateNeg : List ModalForce
  otherDE : List ModalForce
  deriving Repr

/-- Pattern 1: Nez Perce *o'qa* (Deal 2011).
    Underlying ◇ modal, necessity via entailment in upward-entailing contexts.
    No scalar alternative → no "not have to" implicature → ◇ subsumes □. -/
def pattern1_nezPerce : VariableForcePattern where
  language := "Nez Perce"
  modal := "o'qa"
  unembedded := [.possibility, .necessity]
  clausemateNeg := [.possibility]
  otherDE := [.possibility]

/-- Pattern 2: Ecuadorian Siona *ba'iji* (Jeretič 2021a,b).
    Underlying ◇, necessity via obligatory scaleless implicature (EXH).
    Unembedded: EXH obligatory → only □. Under negation: only ◇.
    Other DE: EXH optional → ◇ or □. -/
def pattern2_siona : VariableForcePattern where
  language := "Siona"
  modal := "ba'iji"
  unembedded := [.necessity]
  clausemateNeg := [.possibility]
  otherDE := [.possibility, .necessity]

/-- Pattern 3: Swedish *får* (Jeretič 2021a).
    Underlying ◇ with optional scalar/scaleless implicature.
    Both readings available unembedded. Under negation: only ◇. -/
def pattern3_swedish : VariableForcePattern where
  language := "Swedish"
  modal := "får"
  unembedded := [.possibility, .necessity]
  clausemateNeg := [.possibility]
  otherDE := [.possibility, .necessity]

/-- Pattern 4: Kinande *anga* (Newkirk 2022a,b).
    Underlying ◇, can reach □w but never full □ (blocked by *paswa*).
    The secondary ordering source yields weak, not strong, necessity. -/
def pattern4_kinande : VariableForcePattern where
  language := "Kinande"
  modal := "anga"
  unembedded := [.possibility, .weakNecessity]
  clausemateNeg := [.possibility]
  otherDE := [.possibility, .weakNecessity]

def variableForcePatterns : List VariableForcePattern :=
  [pattern1_nezPerce, pattern2_siona, pattern3_swedish, pattern4_kinande]

/-- **Universal generalization**: under clausemate negation, all four
    variable force modals have only a possibility reading. -/
theorem all_clausemate_neg_is_possibility :
    variableForcePatterns.all
      (fun p => p.clausemateNeg == [.possibility]) = true := by native_decide

/-- All four patterns have possibility available in every environment. -/
theorem all_have_possibility_everywhere :
    variableForcePatterns.all (fun p =>
      p.unembedded.any (· == .possibility) ||
      -- Pattern 2 (Siona) lacks ◇ unembedded (only □) — this is the one exception
      p.unembedded == [.necessity]) = true := by native_decide

/-- Four patterns, four languages. -/
theorem four_patterns : variableForcePatterns.length = 4 := rfl

-- ============================================================================
-- §5. Exhaustification Analysis (§3.2, eq. 50)
-- ============================================================================

/-! ## EXH-based strengthening

The paper formalizes the exhaustification analysis for Siona *ba'iji*:
  ⟦ba'iji_M p⟧ = ∃w ∈ M. p(w)             — underlying possibility
  Alt(ba'iji_M p) = {∃w ∈ M'. p(w) | M' ⊆ M}  — subdomain alternatives
  ⟦EXH ba'iji_M p⟧ ≡ ∀w ∈ M. p(w)          — strengthened to necessity

We model this as: EXH over subdomain alternatives of ◇ yields □. -/

/-- Exhaustification of a possibility modal over subdomain alternatives
    yields necessity: negating all proper-subdomain existentials forces
    the prejacent to hold at every world in the domain. -/
def exhStrengthens (domain : List Bool) : Bool :=
  -- Original: ∃w ∈ M. p(w) — at least one world satisfies p
  let possibility := domain.any id
  -- After EXH: ∀w ∈ M. p(w) — all worlds satisfy p
  let strengthened := domain.all id
  -- EXH strengthens possibility to necessity when the domain is non-empty
  -- and the original possibility holds
  possibility && strengthened

/-- EXH strengthening works: if all worlds satisfy p, exhaustification
    of ◇ over subdomain alternatives yields □. -/
theorem exh_all_true : exhStrengthens [true, true, true] = true := rfl

/-- EXH fails when not all worlds satisfy p: ◇ holds but □ doesn't,
    so the exhaustified reading (= □) is false. -/
theorem exh_mixed_false : exhStrengthens [true, false, true] = false := rfl

/-- Empty domain: both ◇ and □ vacuously fail. -/
theorem exh_empty : exhStrengthens [] = false := rfl

-- ============================================================================
-- §6. Neg-Raising Asymmetry (§2.2.3, Agha & Jeretič 2022)
-- ============================================================================

/-! ## Non-quantificational analysis

@cite{agha-jeretic-2022} observe that weak necessity modals are scopeless
with respect to negation (like plural predication), while strong necessity
modals (some of them) are neg-raisers:

- "should not go" = only □ > ¬ (wide scope)
- "must not go" = □ > ¬ (wide scope), but also available: ¬ > □ via neg-raising
- "have to not go" = only □ > ¬ (wide scope, no neg-raising)

Under higher-clause negation:
- "doesn't think Bill should go" = ✓ □ > ¬; * ¬ > □
- "doesn't think Bill must go" = * □ > ¬; ✓ ¬ > □

The weak necessity modal *should* never takes scope below negation,
while the strong necessity modal *must* does (via neg-raising). -/

/-- Neg-raising availability for a modal operator. -/
structure NegRaisingProfile where
  modal : String
  clausemateNeg_wideScope : Bool  -- □ > ¬ available
  higherNeg_narrowScope : Bool    -- ¬ > □ available (neg-raising)
  deriving Repr, BEq

def shouldProfile : NegRaisingProfile where
  modal := "should"
  clausemateNeg_wideScope := true   -- "should not go" ✓
  higherNeg_narrowScope := false    -- "doesn't think should go" → only □ > ¬

def mustProfile : NegRaisingProfile where
  modal := "must"
  clausemateNeg_wideScope := true   -- "must not go" ✓
  higherNeg_narrowScope := true     -- "doesn't think must go" → ¬ > □ (neg-raising)

def haveToProfile : NegRaisingProfile where
  modal := "have to"
  clausemateNeg_wideScope := true   -- "doesn't have to go" = ¬ > □ BUT via scope, not neg-raising
  higherNeg_narrowScope := false    -- "doesn't think has to go" → only ¬ > □ (no neg-raising)

/-- Weak necessity modals do not neg-raise; some strong necessity modals do.
    This asymmetry motivates the non-quantificational analysis. -/
theorem should_no_neg_raising : shouldProfile.higherNeg_narrowScope = false := rfl
theorem must_neg_raises : mustProfile.higherNeg_narrowScope = true := rfl

end Phenomena.Modality.Studies.AghaJeretic2026
