/-!
# Indefinite Type Classification
@cite{degano-aloni-2025} @cite{haspelmath-1997} @cite{farkas-brasoveanu-2020}

Cross-linguistic classification of indefinite pronouns based on the
semantic dimensions of **variation** and **constancy** from team semantics
(@cite{hodges-1997}, @cite{vaananen-2007}).

Seven types arise from Boolean combinations of `var(y,x)` (variation)
and `dep(y,x)` (constancy/dependence) with two parameter choices:
within-world (`v`) and across-all-worlds (`∅`).

| Type | SK | SU | NS | Requirement | Example |
|------|----|----|-----|-------------|---------|
| (i)   unmarked         | ✓ | ✓ | ✓ | none                   | Italian *qualcuno*  |
| (ii)  specific         | ✓ | ✓ | ✗ | dep(v,x)               | Georgian *-ghats*   |
| (iii) non-specific     | ✗ | ✗ | ✓ | var(v,x)               | Russian *-nibud'*   |
| (iv)  epistemic        | ✗ | ✓ | ✓ | var(∅,x)               | German *irgend-*    |
| (v)   specific known   | ✓ | ✗ | ✗ | dep(∅,x)               | Russian *koe-*      |
| (vi)  SK + NS          | ✓ | ✗ | ✓ | dep(∅,x) ∧ var(v,x)   | *unattested*        |
| (vii) specific unknown | ✗ | ✓ | ✗ | dep(v,x) ∧ var(∅,x)   | Kannada *-oo*       |

The profile columns (SK/SU/NS) indicate which Haspelmath map functions
each type's semantics PERMITS. Actual distribution in a paradigm may
be narrower due to competition with more specific forms.

Used by:
- `Fragments/Russian/Indefinites.lean` (Russian ABC paradigm)
- `Phenomena/Reference/Studies/Bubnov2026.lean` (nanosyntax critique)
-/

set_option autoImplicit false

namespace Core.IndefiniteType

-- ============================================================================
-- §1. Indefinite Type Classification (@cite{degano-aloni-2025})
-- ============================================================================

/-- Degano & Aloni's seven-type classification of indefinites, based on
    team-semantic variation and constancy predicates.

    @cite{bubnov-2026} Table 3, adapted from @cite{degano-aloni-2025}. -/
inductive IndefiniteSpecType where
  /-- (i) No restriction on denotation. All three functions available.
      Example: Italian *qualcuno*, English *some-*. -/
  | unmarked
  /-- (ii) dep(v,x): constant denotation within each epistemic world.
      Specific (known or unknown). Example: Georgian *-ghats*. -/
  | specific
  /-- (iii) var(v,x): varying denotation within some epistemic world.
      Non-specific. Example: Russian *-nibud'*. -/
  | nonSpecific
  /-- (iv) var(∅,x): varying denotation across all epistemic worlds.
      Epistemic. Example: German *irgend-*, Russian *-to*
      (@cite{bubnov-2026} §7: `-to` ⟺ ∃_epistemic). -/
  | epistemic
  /-- (v) dep(∅,x): constant denotation across all worlds.
      Specific known. Example: Russian *koe-*. -/
  | specificKnown
  /-- (vi) dep(∅,x) ∧ var(v,x): contradictory, unattested.
      See `type_vi_contradictory` in `Bubnov2026.lean`. -/
  | skPlusNS
  /-- (vii) dep(v,x) ∧ var(∅,x): specific unknown (conjunctive).
      Rare because it imposes two simultaneous restrictions.
      Example: Kannada *-oo*. -/
  | specificUnknown
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §2. Semantic Profiles (derived from type)
-- ============================================================================

/-- Can this type serve the specific-known function?
    Derived from @cite{degano-aloni-2025} / @cite{bubnov-2026} Table 3. -/
def IndefiniteSpecType.profileSK : IndefiniteSpecType → Bool
  | .unmarked        => true
  | .specific        => true
  | .nonSpecific     => false
  | .epistemic       => false
  | .specificKnown   => true
  | .skPlusNS        => true
  | .specificUnknown => false

/-- Can this type serve the specific-unknown function? -/
def IndefiniteSpecType.profileSU : IndefiniteSpecType → Bool
  | .unmarked        => true
  | .specific        => true
  | .nonSpecific     => false
  | .epistemic       => true
  | .specificKnown   => false
  | .skPlusNS        => false
  | .specificUnknown => true

/-- Can this type serve the non-specific/irrealis function? -/
def IndefiniteSpecType.profileNS : IndefiniteSpecType → Bool
  | .unmarked        => true
  | .specific        => false
  | .nonSpecific     => true
  | .epistemic       => true
  | .specificKnown   => false
  | .skPlusNS        => true
  | .specificUnknown => false

-- ============================================================================
-- §3. Entry Structure
-- ============================================================================

/-- A cross-linguistic indefinite pronoun entry.

    `specType` encodes the Degano & Aloni semantic type (which contexts
    the semantics PERMITS — derivable via `profileSK/SU/NS`).
    `allowsSK/SU/NS` encode the actual paradigmatic distribution (which
    contexts the form IS USED for). These may differ when paradigmatic
    competition blocks a form from contexts its semantics would permit.
    For example, Russian *-to* is type (iv) epistemic (permits SU + NS)
    but only appears for SU because *-nibud'* blocks it for NS. -/
structure IndefiniteEntry where
  language : String
  form : String
  gloss : String
  specType : IndefiniteSpecType
  /-- Actual distribution: used in specific-known contexts? -/
  allowsSK : Bool
  /-- Actual distribution: used in specific-unknown contexts? -/
  allowsSU : Bool
  /-- Actual distribution: used in non-specific/irrealis contexts? -/
  allowsNS : Bool
  source : String := ""
  deriving Repr

/-- An entry's distribution is consistent if it only appears in contexts
    its semantics permits: allows implies profile. -/
def IndefiniteEntry.distributionConsistent (e : IndefiniteEntry) : Bool :=
  (!e.allowsSK || e.specType.profileSK) &&
  (!e.allowsSU || e.specType.profileSU) &&
  (!e.allowsNS || e.specType.profileNS)

-- ============================================================================
-- §4. Syncretism Patterns
-- ============================================================================

/-- Syncretism pattern for the NS–SU–SK triple on Haspelmath's map. -/
inductive SyncretismPattern where
  | AAA   -- all three coexpressed (English *some-*)
  | ABB   -- SU+SK coexpressed, NS distinct (Yakut)
  | AAB   -- NS+SU coexpressed, SK distinct (Latin)
  | ABC   -- all distinct (Russian)
  | ABA   -- NS+SK coexpressed but not SU (*unattested*)
  deriving DecidableEq, Repr, BEq

/-- Classify a triple of forms (NS, SU, SK) into a syncretism pattern.
    Derives the pattern from the forms rather than stipulating it. -/
def classifyTriple (nsForm suForm skForm : String) : SyncretismPattern :=
  if nsForm == suForm && suForm == skForm then .AAA
  else if nsForm == suForm then .AAB
  else if suForm == skForm then .ABB
  else if nsForm == skForm then .ABA
  else .ABC

/-- *ABA is predicted unattested by both nanosyntax and the semantic
    account. Under nanosyntax: the Superset Principle prevents it.
    Under the semantic account: it would require dep(∅,x) ∧ var(v,x),
    which is contradictory (type vi). -/
def SyncretismPattern.IsAttested (s : SyncretismPattern) : Prop :=
  s ≠ .ABA

instance : DecidablePred SyncretismPattern.IsAttested :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

theorem aba_unattested : ¬ SyncretismPattern.IsAttested .ABA := by decide

-- ============================================================================
-- §5. Pattern Classification Verification
-- ============================================================================

theorem classify_aaa : classifyTriple "A" "A" "A" = .AAA := rfl
theorem classify_aab : classifyTriple "A" "A" "B" = .AAB := rfl
theorem classify_abb : classifyTriple "A" "B" "B" = .ABB := rfl
theorem classify_abc : classifyTriple "A" "B" "C" = .ABC := rfl
theorem classify_aba : classifyTriple "A" "B" "A" = .ABA := rfl

end Core.IndefiniteType
