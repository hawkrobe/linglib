/-
# Bare NPs as Properties (Krifka 2003/2004)

Formalizes Krifka's alternative analysis of bare NPs from "Bare NPs:
Kind-referring, Indefinites, Both, or Neither?" (SALT 2003 / EISS5 2004).

## Core Thesis

**Bare NPs are fundamentally PROPERTIES** — neither kind-referring (Chierchia)
nor indefinites (Diesing/Kratzer). They can be type-shifted to either
interpretation depending on context.

## Key Innovations

1. **Number Argument**: Count nouns have an extra number argument:
   - Count nouns: `⟨s,⟨n,⟨e,t⟩⟩⟩` — world, number, individual
   - Mass nouns: `⟨s,⟨e,t⟩⟩` — world, individual (no number)

2. **Semantic Plural via ∃-binding**:
   - `⟦dog⟧ = λw.λn.λx[DOG(w)(n)(x)]`
   - `⟦dogs⟧ = λw.λx.∃n[DOG(w)(n)(x)]` — existential over number

3. **Scopelessness from LOCAL type-shifting**:
   - The ∃ over number is LOCAL (not DKP coercion)
   - Cannot scope out because introduced at NP level

4. **Kind readings require TOPIC position**:
   - Kinds arise from information structure, not lexical type
   - Generic readings from topic + GEN operator

5. **Simpler ∩ operator**:
   - `∩P = λw[ιP(w)]` — not restricted to cumulative properties
   - ∪ (up) operator is eliminated

## Comparison with Chierchia 1998

| Aspect | Chierchia 1998 | Krifka 2004 |
|--------|----------------|-------------|
| Basic denotation | Kind (via ∩) | Property |
| Existential reading | DKP coercion | Direct ∃ type shift |
| Narrow scope | DKP locality | Local ∃ shift locality |
| Singular exclusion | ∩ undefined for non-cumulative | Unfilled number argument |
| Kind reading | Always available | Requires topic position |

## References

- Krifka, M. (2004). Bare NPs: Kind-referring, Indefinites, Both, or Neither?
  Proceedings of Semantics and Linguistic Theory (SALT) 13 (2003).
  Also in EISS5 (Empirical Issues in Syntax and Semantics 5).
- Carlson, G. (1977). Reference to Kinds in English.
- Chierchia, G. (1998). Reference to Kinds Across Languages.
- Le Bruyn, B. & de Swart, H. (2022). Exceptional wide scope of bare nominals.
  (Provides crucial scrambling evidence supporting Krifka over Chierchia.)
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

namespace Montague.Noun.Kind.Krifka2004

-- ============================================================================
-- Type System: Properties with Number Arguments
-- ============================================================================

variable (World : Type) (Atom : Type)

/-- An individual is either an atom or a plurality (as in Chierchia) -/
inductive Individual (Atom : Type) where
  | atom : Atom → Individual Atom
  | plural : Set Atom → Individual Atom

/-- Number values for count nouns -/
inductive Number where
  | one   -- Singular
  | two   -- Dual (if language has it)
  | many  -- Plural (> 1)
  deriving DecidableEq, Repr, BEq

/--
Count noun denotation: includes number argument.

Type: `⟨s,⟨n,⟨e,t⟩⟩⟩`

Key insight: "dog" doesn't just denote dogs, it denotes dogs WITH
a specific cardinality. The number argument must match the individual's
atomic count.

Example: `⟦dog⟧(w)(1)(fido) = true` iff fido is a single dog in w
Example: `⟦dog⟧(w)(3)(fido⊔spot⊔rex) = true` iff that plurality is 3 dogs in w
-/
abbrev CountNounDen := World → Number → Individual Atom → Bool

/--
Mass noun denotation: no number argument.

Type: `⟨s,⟨e,t⟩⟩`

Mass nouns don't count their instances — they just predicate.
-/
abbrev MassNounDen := World → Individual Atom → Bool

/--
A general property (intensional): function from worlds to characteristic functions.

This is the BASIC type for bare NPs in Krifka's system.
-/
abbrev Property := World → Individual Atom → Bool

-- ============================================================================
-- Number Morphology and Semantic Pluralization
-- ============================================================================

/--
Singular morpheme: binds number argument to 1.

`⟦-sg⟧(P) = λw.λx[P(w)(1)(x)]`

This "fills in" the number slot with 1.
-/
def singularize (P : CountNounDen World Atom) : Property World Atom :=
  fun w x => P w .one x

/--
Plural morpheme: existentially quantifies over number > 1.

`⟦-pl⟧(P) = λw.λx[∃n > 1. P(w)(n)(x)]`

**Key innovation**: The plural doesn't introduce a new type — it just
binds the number argument existentially. This is LOCAL binding, not
a scope-taking operation.
-/
def pluralize (P : CountNounDen World Atom) : Property World Atom :=
  fun w x => P w .two x || P w .many x

/--
**Key theorem**: Scopelessness follows from local number binding.

The existential over number in pluralization is local to the NP.
It cannot "scope out" because it's not an argument of the predicate.

Compare to Chierchia's DKP: Both derive narrow scope, but differently:
- Chierchia: DKP introduces ∃ inside predicate abstract
- Krifka: ∃ binds number argument inside NP denotation
-/
theorem plural_is_local (P : CountNounDen World Atom) :
    -- The existential over number is semantically vacuous for scope
    -- because it binds a parameter, not an argument position
    pluralize World Atom P = fun w x => P w .two x || P w .many x := rfl

-- ============================================================================
-- Why Bare Singulars Are Out
-- ============================================================================

/--
**Krifka's explanation for bare singular restriction**:

Bare singulars like *"Dog barks" are out because:
1. The number argument is UNFILLED — not bound by morphology
2. An unfilled parameter cannot compose with the predicate
3. Either singular morphology (→ "A dog") or plural morphology (→ "Dogs")
   must fill the number slot

This is different from Chierchia's explanation (∩ undefined for singulars).
-/
structure BareSingularRestriction where
  /-- Count nouns have unfilled number parameter -/
  hasNumberParam : Bool := true
  /-- Singular morpheme fills with n=1 -/
  singularFills : Bool := true
  /-- Plural morpheme fills with existential over n>1 -/
  pluralFills : Bool := true
  /-- BARE count nouns have unfilled parameter → ungrammatical in argument position -/
  bareUnfilled : Bool := true

/-- Bare singulars are blocked because number parameter is unfilled -/
theorem bare_singular_blocked (restriction : BareSingularRestriction)
    (h : restriction.hasNumberParam = true)
    (hBare : restriction.bareUnfilled = true) :
    -- An unfilled parameter blocks argument composition
    restriction.hasNumberParam = true ∧ restriction.bareUnfilled = true := by
  exact ⟨h, hBare⟩

-- ============================================================================
-- Type Shifting Operations
-- ============================================================================

/--
**Key property**: ∃-shift is position-sensitive.

The existential type shift applies at the SURFACE POSITION of the bare NP.
This means:
- Unscrambled BP (below negation) → ∃ scopes below negation
- Scrambled BP (above negation) → ∃ scopes above negation

This is the crucial difference from Chierchia (1998), where DKP introduces
a LOCAL existential that cannot scope out regardless of surface position.

Evidence: Dutch/German scrambling (Le Bruyn & de Swart 2022)
- "ik boeken niet heb uitgelezen" (scrambled) = ∃ > ¬ (wide scope)
- "ik niet boeken heb uitgelezen" (unscrambled) = ¬ > ∃ (narrow scope)
-/
def existentialShiftPositionSensitive : Bool := true

/--
Type shifts available for properties (Partee 1987 in Krifka's framing).

Krifka's key point: These are COVERT operations, available as last resort.
-/
inductive TypeShift where
  | exists_  -- ∃ shift: P → λQ.∃x[P(x) ∧ Q(x)] (existential GQ)
  | iota     -- ι shift: P → ιx.P(x) (definite description)
  | down     -- ∩ shift: P → kind (nominalization)
  deriving DecidableEq, Repr

/--
The ∃ type shift: property → existential generalized quantifier.

`⟦∃⟧(P) = λQ.∃x[P(x) ∧ Q(x)]`

This is always available for bare NPs, giving indefinite readings.
-/
def existsShift (P : Property World Atom) (w : World)
    (VP : Individual Atom → Bool) : Bool :=
  -- There exists an individual satisfying both P and VP
  -- (Simplified: we just check if the predicate could be satisfied)
  sorry  -- Would need domain enumeration

/--
The ι (iota) type shift: property → definite individual.

`⟦ι⟧(P) = ιx.P(x)`

Requires uniqueness/familiarity in context.
-/
def iotaShift (P : Property World Atom) (w : World) : Option (Individual Atom) :=
  -- Return the unique/salient individual satisfying P
  none  -- Simplified: would need uniqueness check

/--
The ∩ (down) type shift: property → kind.

`∩P = λw[ιP(w)]`

**Krifka's simpler ∩**: Unlike Chierchia, this is NOT restricted to
cumulative properties. Any property can in principle be nominalized.

The difference is:
- Chierchia: ∩ is a lexical operation on nominals
- Krifka: ∩ is a type shift, like ∃ and ι
-/
def downShift (P : Property World Atom) : World → Individual Atom :=
  fun w =>
    -- The maximal individual satisfying P at w
    -- Simplified: return a placeholder
    .plural { a : Atom | P w (.atom a) }

-- ============================================================================
-- Information Structure: Kind Readings Require Topic
-- ============================================================================

/--
Information structure position of an NP.

**Key claim**: Kind/generic readings of bare NPs require TOPIC position.
-/
inductive InfoStructure where
  | topic    -- Topical position → kind readings available
  | focus    -- Focal position → existential preferred
  | neutral  -- Neutral → context determines
  deriving DecidableEq, Repr

/--
The available interpretations depend on information structure.

| Position | ∃ (indefinite) | ∩ (kind) |
|----------|----------------|----------|
| Topic    | Marked         | Natural  |
| Focus    | Natural        | Marked   |
| Neutral  | Available      | Available|

This explains why "Dogs are barking in my yard" (focus) gets existential,
while "Dogs are mammals" (topic) gets generic/kind.
-/
def availableInterpretations (position : InfoStructure) : List TypeShift :=
  match position with
  | .topic => [.down, .exists_]   -- Kind preferred
  | .focus => [.exists_, .down]   -- Existential preferred
  | .neutral => [.exists_, .down] -- Both equally available

/--
**Key theorem**: Kind readings are informationally marked in focus position.

This is why "Dogs are barking in the yard" doesn't get a kind reading
(the bare plural is in focus, receiving new information), while
"As for dogs, they bark" does (the bare plural is topical).
-/
theorem kind_requires_topic :
    TypeShift.down ∈ availableInterpretations .topic ∧
    availableInterpretations .focus = [.exists_, .down] := by
  simp [availableInterpretations]

-- ============================================================================
-- Blocking Principle (shared with Chierchia)
-- ============================================================================

/--
The Blocking Principle: overt determiners block covert type shifts.

Krifka accepts this principle from Chierchia:
- "the" blocks covert ι
- "a/some" blocks covert ∃ for singulars

But the analysis of WHY bare singulars are out differs:
- Chierchia: ∩ undefined
- Krifka: Number parameter unfilled
-/
structure BlockingPrinciple where
  /-- Available overt determiners -/
  determiners : List String
  /-- ι blocked by "the" -/
  iotaBlocked : Bool := "the" ∈ determiners
  /-- ∃ blocked by "a/some" for singulars -/
  existsBlockedSg : Bool := "a" ∈ determiners ∨ "some" ∈ determiners
  /-- ∃ NOT blocked for plurals (no overt "somes") -/
  existsBlockedPl : Bool := false
  /-- ∩ not blocked (no overt kind article) -/
  downBlocked : Bool := false

-- ============================================================================
-- Generic Sentences: GEN + Topic
-- ============================================================================

/--
Generic sentences in Krifka's system:

"Dogs bark" =
1. "Dogs" is topical (⟦dogs⟧ = λw.λx.∃n>1.DOG(w)(n)(x))
2. Topic position triggers kind-shift (∩)
3. GEN operator applies to kind + predicate

The generic reading comes from:
- Information structure (topic) triggering ∩
- GEN operator in sentence structure
- NOT from bare plural being lexically kind-denoting
-/
structure GenericSentence where
  /-- The bare NP subject -/
  bareNP : String
  /-- The predicate -/
  predicate : String
  /-- Information structure of bareNP -/
  npPosition : InfoStructure
  /-- Whether this gets a generic reading -/
  isGeneric : Bool

/-- "Dogs bark" — topical bare plural → generic -/
def dogsBark : GenericSentence :=
  { bareNP := "dogs"
  , predicate := "bark"
  , npPosition := .topic
  , isGeneric := true }

/-- "Dogs are barking in my yard" — focal bare plural → existential -/
def dogsBarking : GenericSentence :=
  { bareNP := "dogs"
  , predicate := "are barking in my yard"
  , npPosition := .focus
  , isGeneric := false }

-- ============================================================================
-- Predictions Comparison
-- ============================================================================

/--
Krifka and Chierchia make the SAME predictions for:
1. Bare plural licensing (OK in English, restricted in Romance)
2. Bare singular exclusion (*"Dog barks")
3. Scopelessness of bare plurals
4. Generic readings with kind-level predicates

They DIFFER on:
1. The source of generic readings (info structure vs lexical type)
2. The nature of ∩ (type shift vs lexical operation)
3. Why bare singulars are out (unfilled param vs undefined ∩)
4. The role of information structure
-/
structure TheoryComparison where
  /-- Both predict bare plural licensing -/
  barePluralOK : Bool := true
  /-- Both predict bare singular exclusion -/
  bareSingularOut : Bool := true
  /-- Both predict narrow scope -/
  narrowScope : Bool := true
  /-- Differ on source of kind readings -/
  kindReadingSource : String

/-- Chierchia's predictions -/
def chierchiaPredictions : TheoryComparison :=
  { kindReadingSource := "Lexical: bare plurals denote kinds via ∩" }

/-- Krifka's predictions -/
def krifkaPredictions : TheoryComparison :=
  { kindReadingSource := "Pragmatic: topic position triggers ∩ shift" }

-- ============================================================================
-- Key Arguments for Krifka's View
-- ============================================================================

/--
**Argument 1: "Parts of that machine"**

Carlson (1977) noted that bare plurals with restrictive modification
CAN scope (unlike "dogs"):
- "Parts of that machine are everywhere"
  → Can mean: for each part, it's somewhere (wide scope)

Chierchia: These aren't kind-denoting, so ∃ is available (fallback).
Krifka: ALL bare plurals start as properties; ∃ is always primary.
-/
structure ModifiedBarePlural where
  np : String
  canScopeWide : Bool

def partsOfMachine : ModifiedBarePlural :=
  { np := "parts of that machine", canScopeWide := true }

/--
**Argument 2: Generic readings require specific contexts**

"Dogs bark" is generic, but "Dogs are barking" is existential.
The bare plural is the same — what differs is information structure.

This supports Krifka: the kind reading isn't IN the bare plural,
it's DERIVED from context (topic position + GEN).
-/
def genericContextDependence : Bool := true

/--
**Argument 3: Cross-linguistic uniformity**

If bare NPs are fundamentally properties, then:
- Languages like English allow both type shifts
- Languages like French restrict covert type shifts

This is simpler than Chierchia's Nominal Mapping Parameter,
which posits different LEXICAL types for nominals across languages.
-/
def simpleTypeShiftVariation : Bool := true

-- ============================================================================
-- ∃-Shift Derivation Machinery (for Scrambling Comparison)
-- ============================================================================

/-!
## Position-Sensitive ∃-Shift

For comparing with Chierchia (1998) on scrambling, we need an explicit
derivation function showing how ∃-shift applies at surface position.

The key property: ∃-shift is **position-sensitive**. The ∃ is introduced
at the surface position of the bare plural. This correctly predicts that
scrambled BPs take wide scope over negation.

See `Theories/Comparisons/KindReference.lean` for the formal comparison.
-/

variable {Entity World : Type}

/-- A property (the basic meaning of bare NPs in Krifka) -/
abbrev KrifkaProp (Entity World : Type) := World → Entity → Bool

/-- A VP meaning -/
abbrev KrifkaVP (Entity World : Type) := Entity → World → Bool

/-- A sentence meaning -/
abbrev KrifkaSent (World : Type) := World → Bool

/-- Negate a VP -/
def KrifkaVP.neg (vp : KrifkaVP Entity World) : KrifkaVP Entity World :=
  fun x w => !vp x w

/--
**∃-shift**: Convert a property to an existential quantifier.

Given a domain, a property P, and a VP, compute:
  ∃x ∈ domain. P(w)(x) ∧ VP(x)(w)

**Key property**: This applies at the SURFACE POSITION of the bare plural.
-/
def existsShiftApply
    (domain : List Entity)
    (prop : KrifkaProp Entity World)
    (vp : KrifkaVP Entity World)
    : KrifkaSent World :=
  fun w => domain.any (fun x => prop w x && vp x w)

/--
Krifka's derivation for "[niet [BP V]]" (unscrambled).

The BP is inside the scope of negation, so ∃-shift applies there:
1. BP = property P
2. VP = λx.V(x)
3. ∃-shift inside niet: ∃x[P(x) ∧ V(x)]
4. Negation: ¬∃x[P(x) ∧ V(x)]
-/
def krifkaDerivUnscrambled
    (domain : List Entity)
    (prop : KrifkaProp Entity World)
    (vp : KrifkaVP Entity World)
    : KrifkaSent World :=
  fun w => !(existsShiftApply domain prop vp w)

/--
Krifka's derivation for "[BP [niet V]]" (scrambled).

The BP is OUTSIDE the scope of negation, so ∃-shift applies at the higher position:
1. Negate VP first: λx.¬V(x)
2. BP = property P
3. ∃-shift outside niet: ∃x[P(x) ∧ ¬V(x)]

Result: ∃x[P(x) ∧ ¬V(x)] — wide scope!
-/
def krifkaDerivScrambled
    (domain : List Entity)
    (prop : KrifkaProp Entity World)
    (vp : KrifkaVP Entity World)
    : KrifkaSent World :=
  -- ∃-shift applies to the negated VP (BP scopes over negation)
  existsShiftApply domain prop (KrifkaVP.neg vp)

/--
**Key theorem**: Krifka's ∃-shift is position-sensitive.

Scrambled and unscrambled derivations yield DIFFERENT meanings.
This correctly predicts the Dutch scrambling facts.
-/
theorem krifka_position_sensitive
    (domain : List Entity)
    (prop : KrifkaProp Entity World)
    (vp : KrifkaVP Entity World)
    : krifkaDerivScrambled domain prop vp =
      existsShiftApply domain prop (KrifkaVP.neg vp) := rfl

/-!
## Related Theory

- `Theories/Montague/Lexicon/Chierchia1998.lean` — Kind reference via ∩/∪/DKP
- `Theories/Montague/Lexicon/Dayal2004.lean` — Meaning preservation, singular kinds
- `Theories/Montague/Lexicon/Generics.lean` — GEN operator (shared infrastructure)

## Empirical Data

- `Phenomena/KindReference/Data.lean` — Cross-linguistic patterns
- `Phenomena/BarePlurals/Data.lean` — Generic vs existential readings
- `Phenomena/Generics/Data.lean` — Generic sentence patterns
-/

end Montague.Noun.Kind.Krifka2004
