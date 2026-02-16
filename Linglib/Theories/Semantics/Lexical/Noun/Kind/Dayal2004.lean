/-
# Kind Reference and Number Marking (Dayal 2004)

Formalizes Dayal's "Number Marking and (In)definiteness in Kind Terms"
which extends Chierchia's NMP analysis with:

1. Meaning Preservation Ranking: {∩, ι} > ∃
2. Number morphology constraints on instantiation sets
3. Taxonomic readings of common nouns
4. Singular kinds ("the dodo", "the lion")

## Core Insight

Type-shifting operations are RANKED by meaning preservation:
- ∩ (kind formation) and ι (definite) preserve all semantic content
- ∃ (indefinite/existential) loses information

When multiple type-shifts are available, choose the one that preserves
the most meaning. This derives cross-linguistic patterns.

## Innovation: Singular Kinds

"The dodo is extinct" - grammatically singular but about a kind.

Analysis: ι can apply to kinds directly when the instantiation set is:
- Singleton: only one salient instance (unique species)
- Inaccessible: no actual instances to distinguish (extinct species)

Number morphology (sg/pl) constrains the instantiation set, not the
denotation type. Singular morphology requires that instances are
"conceptualized as a single entity."

## References

- Dayal, V. (2004). Number Marking and (In)definiteness in Kind Terms.
  Linguistics and Philosophy 27: 393-450.
- Chierchia, G. (1998). Reference to Kinds Across Languages.
- Carlson, G. (1977). Reference to Kinds in English.
-/

import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

namespace TruthConditional.Noun.Kind.Dayal2004

open TruthConditional.Noun.Kind.Chierchia1998 (NominalMapping BlockingPrinciple Individual Kind Property
                              NounType downDefinedFor)

variable (World Atom : Type)

-- Type-Shifting Operations (with Ranking)

/--
Type-shifting operations from Partee (1987) / Dayal (2004).

These convert between semantic types:
- ∩ (down/cap): Property → Kind (nominalization)
- ι (iota): Property → Individual (definite description)
- ∃ (exists): Property → GQ (existential quantification)
-/
inductive TypeShift where
  | down   -- ∩: λP λs ιx[Ps(x)] - kind formation
  | iota   -- ι: λP ιx[Ps(x)] - definite description
  | exists -- ∃: λP λQ ∃x[P(x) ∧ Q(x)] - existential
  deriving DecidableEq, Repr, BEq

/--
Meaning Preservation Ranking (Dayal 2004: 408)

{∩, ι} > ∃

The key insight: ∩ and ι both preserve the full semantic content
of the property, while ∃ introduces existential quantification
that "loses" some information.

∩P preserves P's intension (the full function from worlds to extensions)
ιP preserves P's intension (picks unique satisfier per world)
∃P only preserves existence of some satisfier (loses identity)
-/
def meaningPreservationRank : TypeShift → Nat
  | .down => 1   -- Highest rank (most preserving)
  | .iota => 1   -- Same rank as ∩
  | .exists => 2 -- Lower rank (less preserving)

/-- Type shifts with equal rank are equally preferred -/
def equallyPreferred (t1 t2 : TypeShift) : Bool :=
  meaningPreservationRank t1 == meaningPreservationRank t2

/-- t1 is more preferred than t2 if it has lower rank -/
def morePreferred (t1 t2 : TypeShift) : Bool :=
  meaningPreservationRank t1 < meaningPreservationRank t2

-- Verify the ranking
example : morePreferred .down .exists = true := rfl
example : morePreferred .iota .exists = true := rfl
example : equallyPreferred .down .iota = true := rfl

-- Instantiation Sets and Number

/--
Instantiation set of a kind at a world.

The instantiation set is the collection of actual instances of the kind.
For "dog-kind" at world w, this is the set of all dogs in w.

Key insight: Number morphology constrains the instantiation set:
- Singular: instantiation set is singleton OR inaccessible
- Plural: instantiation set has multiple accessible members

For computational purposes, we represent this abstractly.
-/
structure InstantiationSet where
  /-- Count of instances (0 = empty, 1 = singleton, >1 = multiple) -/
  count : Nat
  /-- Whether instances are "accessible" (epistemically available) -/
  accessible : Bool
  deriving Repr, DecidableEq, BEq

/--
Accessibility of instantiation sets.

An instantiation set is "inaccessible" when:
1. The kind is extinct (no actual instances exist)
2. The instances are not salient/distinguishable in context
3. The kind is treated as atomic (collective reading)

Inaccessible instantiation sets allow singular morphology even for kinds
with "conceptually plural" members.
-/
def InstantiationSet.isSingleton (is : InstantiationSet) : Bool :=
  is.count ≤ 1

def InstantiationSet.allowsSingular (is : InstantiationSet) : Bool :=
  !is.accessible || is.isSingleton

def InstantiationSet.allowsPlural (is : InstantiationSet) : Bool :=
  is.accessible

-- Number Morphology

/--
Number feature on nominals.

Key insight from Dayal: Number is NOT about semantic plurality vs singularity.
It's about whether the instantiation set is conceptualized as:
- Atomic/unitary (singular)
- Non-atomic/multiple (plural)
-/
inductive NumberFeature where
  | sg   -- Singular: atomic instantiation set
  | pl   -- Plural: non-atomic instantiation set
  | mass -- Mass: no number distinction
  deriving DecidableEq, Repr, BEq

/--
License for singular morphology on kinds.
-/
inductive SingularLicense where
  /-- Singleton instantiation set (unique in context) -/
  | singleton
  /-- Inaccessible instantiation set (extinct, collective) -/
  | inaccessible
  /-- Taxonomic reading (sub-kinds, not individuals) -/
  | taxonomic
  deriving DecidableEq, Repr, BEq

/--
Singular Kinds (Dayal 2004: 411-423)

Grammatically singular but denoting kinds:
- "The lion is a predator" (taxonomic)
- "The dodo is extinct" (no living instances)
- "The computer has revolutionized communication" (collective)

These are possible when the instantiation set is:
1. Singleton (unique species/type in context)
2. Inaccessible (extinct, conceptualized as atomic)

The ι operator applies to KIND-LEVEL properties, not individual-level.
-/
structure SingularKind where
  /-- The underlying kind -/
  kind : String  -- Simplified from Kind World Atom
  /-- Why singular is allowed -/
  singularLicense : SingularLicense
  deriving Repr

-- Taxonomic Readings

/--
Taxonomic readings (Dayal 2004: 426-433)

Common nouns can denote:
1. Properties of INDIVIDUALS: dog(x) = "x is a dog individual"
2. Properties of SUB-KINDS: dog(k) = "k is a dog sub-kind"

Example: "The dog evolved from the wolf"
- Individual reading: Some specific dog evolved (anomalous)
- Taxonomic reading: Dog-kind evolved from wolf-kind (natural)

The taxonomic reading treats sub-kinds as the "atoms" of predication.
-/
inductive CNDenotation where
  /-- Property of individuals: λx. P(x) -/
  | individual
  /-- Property of sub-kinds: λk. P(k) where k ranges over sub-kinds -/
  | taxonomic
  deriving DecidableEq, Repr, BEq

/--
When a CN has a taxonomic reading, "the CN" can be singular even when
the kind has multiple sub-kinds.

"The dog" (taxonomic) = ιk[dog-kind(k)] where k ranges over basic-level kinds

The uniqueness is at the TAXONOMIC level (one dog-kind), not the instance level.
-/
def taxonomicIota (kindName : String) : String :=
  s!"ιk[{kindName}-kind(k)]"

/--
Taxonomic hierarchy: kinds can have sub-kinds.

"Dogs" can mean:
- All dog individuals (individual reading)
- All dog breeds (taxonomic reading)

The taxonomic reading explains why some kind-level predicates work with
"the NP" even when there are many instances.
-/
structure TaxonomicHierarchy where
  /-- The super-kind -/
  superKind : String
  /-- Sub-kinds (breeds, species, etc.) -/
  subKinds : List String

-- Example: Dog has sub-kinds
def dogTaxonomy : TaxonomicHierarchy :=
  { superKind := "dog"
  , subKinds := ["poodle", "labrador", "beagle", "collie"] }

-- Extended Type-Shifting with Dayal's Constraints

/--
Type-shift availability given number and blocking.

Dayal's system: type-shifts are constrained by:
1. Meaning preservation ranking: prefer ∩/ι over ∃
2. Number morphology: sg requires singleton/inaccessible instantiation
3. Blocking: overt D blocks covert equivalent
4. ∩ definedness: requires kind-compatible property
-/
structure TypeShiftContext where
  /-- Number feature on the NP -/
  number : NumberFeature
  /-- Is ∩ defined (is this a kind-compatible property)? -/
  downDefined : Bool
  /-- Is ι blocked by an overt definite article? -/
  iotaBlocked : Bool
  /-- Is ∃ blocked by an overt indefinite article? -/
  existsBlocked : Bool
  /-- Is the instantiation set accessible? -/
  instantiationAccessible : Bool
  deriving Repr

/--
Available type-shifts given context.

Returns shifts in preference order (most preferred first).
-/
def availableShifts (ctx : TypeShiftContext) : List TypeShift :=
  let shifts := []
  -- ∩ is available if defined and number is compatible
  let shifts := if ctx.downDefined &&
                   (ctx.number == .pl || ctx.number == .mass ||
                    !ctx.instantiationAccessible)
                then shifts ++ [.down]
                else shifts
  -- ι is available if not blocked and number is sg
  let shifts := if !ctx.iotaBlocked &&
                   (ctx.number == .sg ||
                    !ctx.instantiationAccessible)
                then shifts ++ [.iota]
                else shifts
  -- ∃ is available if not blocked (but lower preference)
  let shifts := if !ctx.existsBlocked
                then shifts ++ [.exists]
                else shifts
  shifts

/--
Select the best available type-shift.

Follows Meaning Preservation: choose highest-ranked available shift.
-/
def selectShift (ctx : TypeShiftContext) : Option TypeShift :=
  (availableShifts ctx).head?

-- Cross-Linguistic Kind Reference Patterns

/--
Language-specific parameters for kind reference (Dayal 2004: 433-445).

Languages differ in:
1. Whether they have definite/indefinite articles
2. Whether bare nominals can denote kinds
3. Whether singular kinds require "the"
-/
structure KindReferenceParams where
  /-- Does this language have a definite article? -/
  hasDefiniteArticle : Bool
  /-- Does this language have an indefinite article? -/
  hasIndefiniteArticle : Bool
  /-- Can bare nominals denote kinds (∩ unblocked)? -/
  bareKindsOK : Bool
  /-- Can singular kinds use "the"? -/
  definiteSingularKinds : Bool
  /-- Can plural kinds use "the"? -/
  definitePluralKinds : Bool
  deriving Repr

/--
English kind reference:
- Bare plurals for kinds: "Dogs are mammals"
- "The" for singular kinds: "The lion is a predator"
- "The" for plural kinds is marked: ?"The dogs are mammals"
-/
def englishKindRef : KindReferenceParams :=
  { hasDefiniteArticle := true
  , hasIndefiniteArticle := true
  , bareKindsOK := true  -- For plurals only
  , definiteSingularKinds := true
  , definitePluralKinds := false }

/--
Romance (French, Italian, Spanish) kind reference:
- Definite article required for kinds: "Les chiens sont des mammifères"
- Both singular and plural kinds use definite article
- Bare nominals restricted to special contexts
-/
def romanceKindRef : KindReferenceParams :=
  { hasDefiniteArticle := true
  , hasIndefiniteArticle := true
  , bareKindsOK := false
  , definiteSingularKinds := true
  , definitePluralKinds := true }

/--
Determiner-less languages (Hindi, Russian, Chinese) kind reference:
- Bare nominals freely denote kinds
- No definite/indefinite distinction in morphology
- All interpretations available in context
-/
def determinerlessKindRef : KindReferenceParams :=
  { hasDefiniteArticle := false
  , hasIndefiniteArticle := false
  , bareKindsOK := true
  , definiteSingularKinds := false  -- N/A
  , definitePluralKinds := false }  -- N/A

/--
German kind reference (intermediate):
- Bare plurals OK for kinds: "Hunde sind Säugetiere"
- Definite optional for plural/mass kinds
- Similar to English but with more flexibility
-/
def germanKindRef : KindReferenceParams :=
  { hasDefiniteArticle := true
  , hasIndefiniteArticle := true
  , bareKindsOK := true
  , definiteSingularKinds := true
  , definitePluralKinds := true }  -- Optional

-- Derived Kind Predication (DKP) - Extended

/--
DKP (Derived Kind Predication) - Dayal's version.

When an object-level predicate applies to a kind, introduce existential
quantification over instances:

  P(k) = ∃x[∪k(x) ∧ P(x)]

Key insight: DKP is only invoked when NECESSARY.
If the predicate is kind-level, no coercion needed.
-/
inductive PredicateType where
  /-- Kind-level predicates: extinct, widespread, evolve -/
  | kindLevel
  /-- Object-level predicates: bark, be in the garden -/
  | objectLevel
  deriving DecidableEq, Repr, BEq

/-- Does this predicate require DKP when applied to a kind? -/
def requiresDKP : PredicateType → Bool
  | .kindLevel => false
  | .objectLevel => true

/--
Kind-level predicates (Dayal 2004: 401-403):
- be extinct, be widespread, be rare
- evolve, originate, die out
- be invented, be discovered

These directly predicate of kinds without coercion.
-/
def isKindLevelPredicate : String → Bool
  | "extinct" | "widespread" | "rare" | "common" => true
  | "evolve" | "originate" | "die_out" => true
  | "invented" | "discovered" => true
  | _ => false

-- Well-Established Kinds

/--
Well-established kinds (Dayal 2004: 417-420)

For ι to apply to a kind (giving "the NP"), the kind must be
"well-established" - a recognized natural class.

- "The lion is a predator" - lion is well-established kind ✓
- *"The lion sitting here is a predator" - not a natural kind ✗

This explains why modified NPs resist the singular kind reading.
-/
def isWellEstablishedKind : String → Bool
  | "lion" | "tiger" | "dog" | "cat" => true
  | "dodo" | "mammoth" | "dinosaur" => true  -- Extinct kinds
  | "computer" | "telephone" | "automobile" => true  -- Artifacts
  | "wheel" | "printing_press" => true  -- Inventions
  | _ => false

/--
Why modification blocks singular kind reading:

"The tall lion" cannot mean "the lion-kind" because:
1. "Tall lion" does not denote a well-established kind
2. Modification restricts the extension, breaking kind status
3. ι must apply at object-level → definite description of individual
-/
structure ModificationEffect where
  /-- Base noun (well-established kind) -/
  base : String
  /-- Modifier -/
  modifier : String
  /-- Result is still a well-established kind? -/
  stillKind : Bool := false

def modificationBlocksKind : ModificationEffect :=
  { base := "lion"
  , modifier := "tall"
  , stillKind := false }

-- Grounding Theorems

/-- Meaning preservation ranking is transitive -/
theorem ranking_transitive (t1 t2 t3 : TypeShift)
    (h1 : morePreferred t1 t2 = true)
    (h2 : morePreferred t2 t3 = true) :
    morePreferred t1 t3 = true := by
  simp only [morePreferred] at *
  cases t1 <;> cases t2 <;> cases t3 <;> simp_all [meaningPreservationRank]

/-- ∩ and ι are always preferred over ∃ -/
theorem down_preferred_over_exists : morePreferred .down .exists = true := rfl
theorem iota_preferred_over_exists : morePreferred .iota .exists = true := rfl

/-- English bare plurals use ∩ (most preferred available shift) -/
theorem english_bare_plural_uses_down :
    let ctx : TypeShiftContext := {
      number := .pl
      downDefined := true
      iotaBlocked := true
      existsBlocked := true
      instantiationAccessible := true
    }
    selectShift ctx = some .down := rfl

/-- English singular kinds use ι -/
theorem english_singular_kind_uses_iota :
    let ctx : TypeShiftContext := {
      number := .sg
      downDefined := false  -- ∩ undefined for singular count
      iotaBlocked := false  -- "the" makes ι available
      existsBlocked := true
      instantiationAccessible := false  -- Inaccessible allows singular
    }
    selectShift ctx = some .iota := rfl

-- Dayal/Chierchia Integration

/--
Convert Chierchia's BlockingPrinciple + noun info to Dayal's TypeShiftContext.

This shows how Dayal's framework generalizes Chierchia's:
- Chierchia: BlockingPrinciple + NounType + isPlural → bare argument OK?
- Dayal: TypeShiftContext → which type-shift is selected?
-/
def chierchiaToContext (bp : BlockingPrinciple) (nt : NounType) (isPlural : Bool)
    (instantiationAccessible : Bool := true) : TypeShiftContext :=
  { number := match nt with
              | .mass => .mass
              | .count => if isPlural then .pl else .sg
  , downDefined := downDefinedFor nt isPlural
  , iotaBlocked := bp.iotaBlocked
  , existsBlocked := bp.existsBlocked
  , instantiationAccessible := instantiationAccessible
  }

/--
English-like blocking principle: has "the" and "a", so ι and ∃ blocked.
-/
def englishBlocking : BlockingPrinciple :=
  { determiners := ["the", "a", "some"]
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := false }

/--
Dayal's framework is consistent with Chierchia's for English.

When Chierchia predicts bare plurals are licensed (∩ defined and not blocked),
Dayal's selectShift returns .down (the kind-forming shift).
-/
theorem dayal_consistent_english_bare_plural :
    let ctx := chierchiaToContext englishBlocking .count true
    selectShift ctx = some .down := by native_decide

/--
When ∩ is undefined (singular count) and ι/∃ are blocked (English),
both frameworks predict bare singular is OUT.
-/
theorem dayal_consistent_english_bare_singular_out :
    let ctx := chierchiaToContext englishBlocking .count false
    selectShift ctx = none := by native_decide

/--
Mass nouns: both frameworks predict bare mass nouns are OK (use ∩).
-/
theorem dayal_consistent_english_mass_noun :
    let ctx := chierchiaToContext englishBlocking .mass false
    selectShift ctx = some .down := by native_decide

/--
Dayal subsumes Chierchia: When a type-shift is available, selectShift finds it.

Verified for the key cases via the concrete theorems above.
The general pattern: selectShift returns Some iff at least one of:
- ∩ is defined (bare plural/mass)
- ι is not blocked
- ∃ is not blocked
-/
theorem dayal_subsumes_chierchia_plural_available :
    let ctx := chierchiaToContext englishBlocking .count true
    (selectShift ctx).isSome = true := by native_decide

theorem dayal_subsumes_chierchia_singular_blocked :
    let ctx := chierchiaToContext englishBlocking .count false
    (selectShift ctx).isSome = false := by native_decide

/--
Romance-like blocking: has definite article, so bare kinds need "the".
But for kind reference, the definite is used (not blocked for that purpose).
-/
def romanceBlocking : BlockingPrinciple :=
  { determiners := ["le", "la", "les", "un", "une", "des"]
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := false }

/--
In Romance, bare plurals are also predicted to use ∩ when available.
-/
theorem dayal_consistent_romance_bare_plural :
    let ctx := chierchiaToContext romanceBlocking .count true
    selectShift ctx = some .down := by native_decide

/--
Meaning Preservation explains Chierchia's blocking.

When both ∩ and ∃ are available, Dayal selects ∩ (more meaning-preserving).
This derives Chierchia's observation that bare plurals prefer kind readings.
-/
theorem meaning_preservation_derives_kind_preference :
    let ctx : TypeShiftContext := {
      number := .pl
      downDefined := true
      iotaBlocked := true
      existsBlocked := false  -- ∃ available but not preferred
      instantiationAccessible := true
    }
    selectShift ctx = some .down  -- ∩ selected over ∃
    := rfl

-- Examples

-- "Dogs are mammals" - bare plural kind reference
#check englishKindRef.bareKindsOK  -- true

-- "The dodo is extinct" - singular kind (inaccessible instantiation)
#check SingularKind.mk "dodo" .inaccessible

-- "The lion is a predator" - singular kind (taxonomic)
#check SingularKind.mk "lion" .taxonomic

-- Meaning preservation: ∩ > ∃
#eval morePreferred .down .exists  -- true

-- Available shifts for English bare plural
#eval availableShifts {
  number := .pl
  downDefined := true
  iotaBlocked := true
  existsBlocked := true
  instantiationAccessible := true
}  -- [.down]

-- French requires definite for kinds
#check romanceKindRef.definitePluralKinds  -- true

/-!
## Related Theory

- `Theories/Montague/Lexicon/Kinds.lean` - Chierchia's NMP, ∩/∪ operators, DKP
- `Theories/Montague/Lexicon/Generics.lean` - GEN operator for generic readings

## Empirical Data

- `Phenomena/KindReference/Data.lean` - cross-linguistic patterns, singular kinds, scopelessness
-/

end TruthConditional.Noun.Kind.Dayal2004
