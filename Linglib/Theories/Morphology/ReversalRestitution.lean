import Linglib.Theories.Morphology.RootTypology
import Linglib.Theories.Semantics.Lexical.Verb.Affectedness

/-!
# Verb-Root-Outcomes: Reversal and Restitution

@cite{bhadra-2024}

Bhadra, D. (2024). Verb roots encode outcomes: argument structure and
lexical semantics of reversal and restitution. *Linguistics and Philosophy*
47: 557–610.

## Core contribution

Every verb root is lexically equipped with a **set of outcomes** — the possible
states of the direct object after the verb's force is applied. The cardinality
of this set determines compatibility with the reversative prefix *un-* and the
restitutive prefix *re-*:

- **PFC** (potential-for-change): multi-membered outcome sets (fold, wrap, coil)
  → compatible with both *un-* and *re-*
- **IE** (impingement-effecting): singleton outcomes, surface only (hit, scrub)
  → incompatible with both
- **COS** (change-of-state): singleton outcomes, integral change (break, destroy)
  → incompatible with *un-*, partially compatible with *re-*

## Boundary state operators

`res(e)(x)` and `pre(e)(x)` yield the state of object *x* at the right and
left boundaries of event *e*. These are NOT temporal operators — they yield
property bundles (lifespan points). Reversative *un-* requires inverse
equivalence of boundary states across events; restitutive *re-* requires
result-state equivalence.

## Bridges

- `ForceTransmissionClass` refines `AffectednessDegree.potential` into PFC vs IE
- `LevinClass.forceTransmissionClass` bridges @cite{levin-1993} classes to @cite{bhadra-2024}
- `RootType.result` roots have singleton outcomes; `RootType.propertyConcept` is orthogonal
- `Template.hasResultState` is necessary but not sufficient for *un-*/*re-* (must also
  check outcome cardinality)
-/

open Semantics.Lexical.Verb.EventStructure
open Semantics.Lexical.Verb.EntailmentProfile
open Semantics.Lexical.Verb.Affectedness

-- ════════════════════════════════════════════════════
-- § 1. Outcome Set Cardinality (@cite{bhadra-2024} eq. 62)
-- ════════════════════════════════════════════════════

/-- Cardinality of a verb root's outcome set — the possible states of the
    object after force transmission.

    multi-membered sets (PFC) > singleton sets (IE, COS) > empty sets -/
inductive OutcomeCardinality where
  | multi     -- PFC: multiple possible discrete outcomes, none entailed
  | singleton -- COS/IE: one specific outcome entailed
  | empty     -- No outcomes (verb exerts no force on object)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Force Transmission Classification (@cite{bhadra-2024} Table 1)
-- ════════════════════════════════════════════════════

/-- Classification of force-transmitting verbs by impact type.

    @cite{bhadra-2024} Table 1: the three classes are distinguished by whether
    force transmission occurs, whether integral change is entailed, and
    whether surface impingement is effected.

    | Class | Force | Integral change | Impingement |
    |-------|-------|-----------------|-------------|
    | PFC   | ✓     | not entailed    | ✗           |
    | IE    | ✓     | not entailed    | ✓           |
    | COS   | ✓     | entailed        | ✓/✗         |

    This refines `AffectednessDegree.potential` (which lumps PFC and IE). -/
inductive ForceTransmissionClass where
  | potentialForChange    -- PFC: fold, wrap, coil — multi outcomes
  | impingementEffecting  -- IE: hit, scrub, kick — surface only
  | integralChange        -- COS: break, destroy, paint — integral change
  | noForceTransmission   -- No force on object: swim, believe, see
  deriving DecidableEq, BEq, Repr

/-- Outcome set cardinality for each force transmission class.

    PFC verbs have multi-membered sets because their actions produce one of
    many possible discrete outcome states (slightly bent, halfway bent, etc.).
    COS and IE verbs have singleton sets (specific result). No-force verbs
    have empty sets (no object-state change). -/
def ForceTransmissionClass.outcomeCardinality : ForceTransmissionClass → OutcomeCardinality
  | .potentialForChange => .multi
  | .impingementEffecting => .singleton
  | .integralChange => .singleton
  | .noForceTransmission => .empty

-- ════════════════════════════════════════════════════
-- § 3. Boundary State Operators (@cite{bhadra-2024} eqs. 64–65)
-- ════════════════════════════════════════════════════

/-- Boundary states of an event's impact on an object.

    `pre` = state at left boundary (pre-state, eq. 65)
    `res` = state at right boundary (result state, eq. 64)

    These are NOT temporal operators — they yield property bundles
    (lifespan points) at event boundaries, enabling equivalence
    comparisons across events. -/
structure BoundaryStates (S : Type) where
  /-- State of the object at the left boundary of the event -/
  pre : S
  /-- State of the object at the right boundary of the event -/
  res : S

instance {S : Type} [BEq S] : BEq (BoundaryStates S) where
  beq a b := a.pre == b.pre && a.res == b.res

-- ════════════════════════════════════════════════════
-- § 4. Reversal and Restitution Conditions (@cite{bhadra-2024} eqs. 49–50)
-- ════════════════════════════════════════════════════

/-- Reversibility condition (eq. 49): the result state of the base event
    equals the pre-state of the affixed event, and vice versa.

    Captures the "inverseness" at the heart of *un-*. -/
def reversible {S : Type} [BEq S] (base affixed : BoundaryStates S) : Bool :=
  base.res == affixed.pre && affixed.res == base.pre

/-- Restitution condition (eq. 50): the result state of the affixed event
    equals the result state of the base event.

    Captures the "same result achieved again" at the heart of *re-*. -/
def restitutive {S : Type} [BEq S] (base affixed : BoundaryStates S) : Bool :=
  affixed.res == base.res

-- ════════════════════════════════════════════════════
-- § 5. un- and re- Compatibility (@cite{bhadra-2024} eqs. 66–68, Fig. 5)
-- ════════════════════════════════════════════════════

/-- *un-* compatibility (eq. 67): requires multi-membered outcome set
    (reversibility) AND the possibility of inverse equivalence between
    boundary states. Only PFC verbs satisfy both conditions. -/
def ForceTransmissionClass.unCompatible : ForceTransmissionClass → Bool
  | .potentialForChange => true
  | _ => false

/-- *re-* compatibility (eq. 72): requires a result state that can be
    re-achieved without a blocking threshold. PFC verbs always qualify.
    COS verbs qualify when the outcome is not permanently destructive
    (verb-specific; see `LevinClass.reCompatible`). -/
def ForceTransmissionClass.reCompatible : ForceTransmissionClass → Bool
  | .potentialForChange => true
  | .integralChange => true
  | _ => false

-- ════════════════════════════════════════════════════
-- § 6. LevinClass → ForceTransmissionClass Bridge
-- ════════════════════════════════════════════════════

/-- Map @cite{levin-1993} classes to @cite{bhadra-2024}'s force transmission classes.

    NOTE: @cite{bhadra-2024} reclassifies some traditionally COS classes as PFC.
    The bend class (45.2) has `changeOfState = true` per @cite{levin-1993} but
    receives multi-membered outcomes per @cite{bhadra-2024}: fold can yield
    many different states (slightly creased, halfway bent, tightly folded, etc.).
    This is a refinement, not a contradiction — Bhadra's VRO framework captures
    finer-grained distinctions within COS. -/
def LevinClass.forceTransmissionClass : LevinClass → ForceTransmissionClass
  -- PFC: surface contact/configuration, reversible multi-outcome actions
  | .coil => .potentialForChange          -- 9.6: coil, wrap, twist, wind
  | .bend => .potentialForChange          -- 45.2: fold, crease, wrinkle
  -- IE: surface impact/contact, irreversible impingement
  | .hit => .impingementEffecting         -- 18.1: hit, kick, punch
  | .swat => .impingementEffecting        -- 18.2: slap, whack
  | .wipe => .impingementEffecting        -- 10.4: wipe, scrub, sweep, scrape
  | .touch => .impingementEffecting       -- 20: touch, rub, stroke
  -- COS: integral change entailed (singleton outcome sets)
  | .break_ => .integralChange            -- 45.1: break, crack, shatter
  | .destroy => .integralChange           -- 44: destroy, demolish
  | .cooking => .integralChange           -- 45.3: bake, boil, fry
  | .otherCoS => .integralChange          -- 45.4: burn, melt, freeze
  | .entitySpecificCoS => .integralChange -- 45.5: bloom, rust
  | .calibratableCoS => .integralChange   -- 45.6: increase, decrease
  | .color => .integralChange             -- 24: paint, dye
  | .imageCreation => .integralChange     -- 25: draw, etch
  | .build => .integralChange             -- 26.1: build, construct
  | .create => .integralChange            -- 26.4: create, design
  | .grow => .integralChange              -- 26.2: grow, cultivate
  | .knead => .integralChange             -- 26.5: mold, shape
  | .turn => .integralChange              -- 26.6: transform, convert
  | .cut => .integralChange               -- 21.1: cut, slash
  | .carve => .integralChange             -- 21.2: carve, chop
  | .eat => .integralChange               -- 39.1: eat, consume
  | .devour => .integralChange            -- 39.4: devour, gobble
  | .murder => .integralChange            -- 42.1: murder, assassinate
  | .poison => .integralChange            -- 42.2: poison, drown
  | .mix => .integralChange               -- 22.1: mix, blend
  | .amalgamate => .integralChange        -- 22.2: amalgamate
  | .separate => .integralChange          -- 23.1: separate, disconnect
  | .split => .integralChange             -- 23.2: split, divide
  | .conceal => .integralChange           -- 16: conceal, hide
  | .clear => .integralChange             -- 10.3: clear, clean, drain
  | .dress => .integralChange             -- 41.1: dress, clothe
  -- No force transmission: statives, perception, psych, motion, etc.
  | _ => .noForceTransmission

/-- *re-* compatibility at the Levin class level.

    Within COS, *re-* is blocked when the outcome permanently eliminates or
    irreversibly transforms the object. Consumption verbs (*redestroy,
    *reeat) and killing verbs (*remurder) block *re-*. Physical property,
    creation, and degree achievement verbs allow *re-* (repaint, rebuild,
    refill). -/
def LevinClass.reCompatible : LevinClass → Bool
  -- PFC: always re-compatible
  | .coil | .bend => true
  -- COS: re-compatible when result can be re-achieved
  | .break_ | .color | .imageCreation | .build | .create | .grow
  | .knead | .otherCoS | .cooking | .calibratableCoS | .clear
  | .entitySpecificCoS | .conceal | .dress | .separate
  | .mix | .amalgamate => true
  -- COS: blocked (consumption, destruction, killing, transforms)
  | .destroy | .eat | .devour | .murder | .poison | .turn
  | .cut | .carve | .split => false
  -- IE: not re-compatible (irreversible impingement)
  | .hit | .swat | .wipe | .touch => false
  -- No force: not re-compatible
  | _ => false

-- ════════════════════════════════════════════════════
-- § 7. Key Structural Theorems
-- ════════════════════════════════════════════════════

/-- Only PFC has multi-membered outcomes. -/
theorem un_requires_multi (ftc : ForceTransmissionClass) :
    ftc.unCompatible = true → ftc.outcomeCardinality = .multi := by
  cases ftc <;> simp [ForceTransmissionClass.unCompatible,
    ForceTransmissionClass.outcomeCardinality]

/-- PFC is the unique class compatible with both *un-* and *re-*. -/
theorem pfc_unique_overlap :
    ForceTransmissionClass.unCompatible .potentialForChange = true ∧
    ForceTransmissionClass.reCompatible .potentialForChange = true := ⟨rfl, rfl⟩

/-- IE is incompatible with both affixes. -/
theorem ie_disallows_both :
    ForceTransmissionClass.unCompatible .impingementEffecting = false ∧
    ForceTransmissionClass.reCompatible .impingementEffecting = false := ⟨rfl, rfl⟩

/-- COS is un-incompatible but re-compatible (class-level;
    verb-specific blocking handled by `LevinClass.reCompatible`). -/
theorem cos_un_blocked_re_available :
    ForceTransmissionClass.unCompatible .integralChange = false ∧
    ForceTransmissionClass.reCompatible .integralChange = true := ⟨rfl, rfl⟩

/-- No-force verbs are incompatible with both. -/
theorem noforce_disallows_both :
    ForceTransmissionClass.unCompatible .noForceTransmission = false ∧
    ForceTransmissionClass.reCompatible .noForceTransmission = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Bridge to EventStructure
-- ════════════════════════════════════════════════════

/-- @cite{bhadra-2024}'s PFC classification is orthogonal to the template-level
    `hasResultState` property. Bend (45.2) has a result state (accomplishment
    template) but coil (9.6) does not (putting template lacks BECOME). Both are
    PFC — outcome cardinality captures a different dimension than template shape. -/
theorem pfc_orthogonal_to_hasResultState :
    (LevinClass.eventTemplate .bend).hasResultState = true ∧
    (LevinClass.eventTemplate .coil).hasResultState = false ∧
    LevinClass.forceTransmissionClass .bend = .potentialForChange ∧
    LevinClass.forceTransmissionClass .coil = .potentialForChange := ⟨rfl, rfl, rfl, rfl⟩

/-- @cite{bhadra-2024} reclassifies bend (45.2) from COS to PFC despite
    Levin's CoS=true meaning components. This is the central refinement. -/
theorem bend_cos_per_levin_pfc_per_bhadra :
    (LevinClass.meaningComponents .bend).changeOfState = true ∧
    LevinClass.forceTransmissionClass .bend = .potentialForChange := ⟨rfl, rfl⟩

/-- IE verbs map to the motionContact template (for wipe class)
    or activity template (for hit class). -/
theorem ie_templates :
    LevinClass.eventTemplate .wipe = .motionContact ∧
    LevinClass.eventTemplate .hit = .activity := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. Bridge to Affectedness Hierarchy
-- ════════════════════════════════════════════════════

/-- @cite{bhadra-2024}'s PFC/IE distinction refines @cite{beavers-2010}'s
    `potential` degree. Both PFC and IE objects have `causallyAffected`
    without `changeOfState`, mapping to `AffectednessDegree.potential`.
    But they differ in outcome cardinality:
    PFC → multi (reversible), IE → singleton (irreversible impingement).

    The kick object profile (canonical IE) maps to `.nonquantized` because
    it has CoS=true; the prototypical PFC profile (CA+St, no CoS) maps
    to `.potential`. -/
theorem affectedness_bridge_pfc :
    profileToDegree ⟨false, false, false, false, false,
                     false, false, true, true, false⟩ = .potential := rfl

theorem affectedness_bridge_ie_kick :
    profileToDegree kickObjectProfile = .nonquantized := rfl

-- ════════════════════════════════════════════════════
-- § 10. Bridge to RootTypology (@cite{beavers-etal-2021})
-- ════════════════════════════════════════════════════

/-- Result roots (@cite{beavers-etal-2021}) lexically entail change and thus have
    singleton outcome sets — the entailed result IS the single outcome.
    PC roots do not entail change, so their outcome cardinality depends on
    their force transmission class (COS vs PFC). -/
theorem result_roots_singleton_outcomes :
    RootType.entailsChange .result = true ∧
    RootType.allowsRestitutiveAgain .result = false := ⟨rfl, rfl⟩

/-- PC roots allow restitutive 'again' (@cite{beavers-etal-2021}), which aligns
    with @cite{bhadra-2024}'s prediction: verbs with multi-membered outcome sets
    (PFC verbs) can return to a prior state. Result roots cannot, because their
    singleton outcome is deterministically entailed. -/
theorem pc_roots_allow_restitutive_again :
    RootType.allowsRestitutiveAgain .propertyConcept = true ∧
    RootType.entailsChange .propertyConcept = false := ⟨rfl, rfl⟩
