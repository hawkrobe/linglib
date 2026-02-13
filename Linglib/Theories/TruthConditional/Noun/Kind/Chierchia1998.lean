/-
# Kind-Level Semantics (Chierchia 1998)

Formalizes Chierchia's "Reference to Kinds Across Languages" framework for
bare plural composition and the Nominal Mapping Parameter.

## The Core Insight

Languages vary in what they let their NPs denote:
- [+arg, -pred]: NPs denote kinds (Chinese) → bare arguments everywhere
- [+arg, +pred]: NPs can be kinds or predicates (Germanic) → bare plurals/mass
- [-arg, +pred]: NPs denote predicates (Romance) → D required for arguments

## Key Operators

1. ∩ (down): ⟨s,⟨e,t⟩⟩ → e — nominalize property to kind
2. ∪ (up): e → ⟨e,t⟩ — predicativize kind to property
3. DKP: Derived Kind Predication — coerce object predicates to kind predicates

## Ontology

Following Link (1983) and Chierchia (1998):
- Domain U is a complete atomic join semilattice
- Atoms are singular individuals
- Non-atoms are pluralities (modeled as sets)
- Kinds are individual concepts: functions from worlds to pluralities
- Kinds ⊆ U^S (subset of individual concepts)

## References

- Chierchia, G. (1998). Reference to Kinds Across Languages.
- Carlson, G. (1977). Reference to Kinds in English.
- Link, G. (1983). The Logical Analysis of Plural and Mass Nouns.
- Partee, B. (1987). Noun Phrase Interpretation and Type-Shifting Principles.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.UpperLower.Basic

namespace TruthConditional.Noun.Kind.Chierchia1998

-- Domain Structure (Link's Semilattice)

/--
The domain of individuals forms a complete atomic join semilattice.

Following Link (1983):
- Atoms are singular individuals (John, Mary, Fido)
- Non-atoms are pluralities ({John, Mary}, {Fido, Spot, Rex})
- The ≤ relation is "part-of" or "subgroup"
- Join ⊔ forms the smallest plurality containing both

For simplicity, we model pluralities as sets of atoms.
-/
structure Domain (Atom : Type) where
  /-- Pluralities are non-empty sets of atoms -/
  plurality : Set Atom → Prop
  /-- Singletons count as (degenerate) pluralities -/
  singleton_is_plurality : ∀ a, plurality {a}
  /-- Non-empty unions of pluralities are pluralities -/
  union_plurality : ∀ s t, plurality s → plurality t → plurality (s ∪ t)

/-- An individual is either an atom or a plurality -/
inductive Individual (Atom : Type) where
  | atom : Atom → Individual Atom
  | plural : Set Atom → Individual Atom

/-- The part-of relation on individuals -/
def Individual.partOf {Atom : Type} : Individual Atom → Individual Atom → Prop
  | .atom a, .atom b => a = b
  | .atom a, .plural s => a ∈ s
  | .plural _, .atom _ => False
  | .plural s, .plural t => s ⊆ t

instance {Atom : Type} : LE (Individual Atom) where
  le := Individual.partOf

/-- Join of two individuals -/
def Individual.join {Atom : Type} : Individual Atom → Individual Atom → Individual Atom
  | .atom a, .atom b => .plural {a, b}
  | .atom a, .plural s => .plural (s ∪ {a})
  | .plural s, .atom a => .plural (s ∪ {a})
  | .plural s, .plural t => .plural (s ∪ t)

-- Kinds as Individual Concepts

variable (World Atom : Type)

/-- A property (intension): function from worlds to sets of individuals -/
abbrev Property := World → Set (Individual Atom)

/-- An individual concept: function from worlds to individuals -/
abbrev IndividualConcept := World → Individual Atom

/--
Kinds are a special subset of individual concepts.

A kind is an individual concept that:
1. Maps each world to the totality of instances (a plurality)
2. Represents a "natural" class with regular behavior

Not every individual concept is a kind. Only those corresponding to
natural properties qualify.
-/
structure Kind where
  /-- The underlying individual concept -/
  concept : IndividualConcept World Atom
  /-- Kinds map to pluralities (the totality of instances) -/
  isPlurality : ∀ w, ∃ s : Set Atom, concept w = .plural s
  /-- Marker that this is a "natural" kind (placeholder for regularity condition) -/
  isNatural : Prop := True

-- The Down Operator: ∩ (Property → Kind)

/--
The "down" operator ∩ (cap): nominalize a property to a kind.

∩P = λs. ιPₛ

That is, at each world s, take the largest individual in the extension of P.
For plural/mass properties, this is the fusion of all instances.

Constraint: ∩ is only defined when the result is a kind.
This means:
- ∩ is undefined for singular count nouns (no corresponding kind)
- ∩ is defined for plural nouns and mass nouns

This is why bare singular count nouns cannot occur as arguments in English.
-/
noncomputable def down (P : Property World Atom) : Option (Kind World Atom) :=
  -- Simplified: assume all properties can be nominalized
  -- In reality, this should check that the result is a "natural kind"
  some {
    concept := λ w =>
      -- The fusion/join of all instances at world w
      -- Simplified: return a placeholder plurality
      .plural { a : Atom | .atom a ∈ P w }
    isPlurality := λ w => ⟨{ a : Atom | .atom a ∈ P w }, rfl⟩
    isNatural := True
  }

-- The Up Operator: ∪ (Kind → Property)

/--
The "up" operator ∪ (cup): predicativize a kind to a property.

∪k = λx[x ≤ kₛ]

The extension is the ideal generated by the kind's instances:
all individuals that are "part of" the totality of instances.

Property: ∪ applied to a kind yields a MASS denotation.
This is because the extension includes both atoms and pluralities.
-/
def up (k : Kind World Atom) : Property World Atom :=
  λ w => { x | x ≤ k.concept w }

/--
Key theorem: ∪(∩P) = P for mass/plural properties.

Going down and then up returns the original property (for suitable P).
-/
theorem up_down_id (P : Property World Atom) (_hMass : True) :
    ∀ k, down World Atom P = some k → up World Atom k = P := by
  sorry  -- Requires careful setup of the domain

/--
Key theorem: ∩(∪k) = k for any kind k.

Going up and then down returns the original kind.
-/
theorem down_up_id (k : Kind World Atom) :
    down World Atom (up World Atom k) = some k := by
  sorry

-- Derived Kind Predication (DKP)

/--
Derived Kind Predication: coerce object-level predicates to accept kinds.

When an object-level predicate P applies to a kind k, introduce
existential quantification over instances:

  P(k) = ∃x[∪k(x) ∧ P(x)]

This is a type-coercion triggered by sort mismatch.

Example: "Lions are roaring in the zoo"
- "lions" denotes a kind
- "roaring in the zoo" is an object-level predicate
- DKP yields: ∃x[lion(x) ∧ roaring-in-the-zoo(x)]
-/
def DKP (P : Individual Atom → Bool) (k : Kind World Atom) (w : World) : Prop :=
  ∃ x, x ∈ up World Atom k w ∧ P x = true

/--
DKP as a type-shifting operation on predicates.

Takes an object-level predicate and returns a kind-level predicate.
-/
def liftToKind (P : Individual Atom → Bool) : Kind World Atom → World → Prop :=
  λ k w => DKP World Atom P k w

-- The Nominal Mapping Parameter

/--
The Nominal Mapping Parameter (Chierchia 1998).

Languages vary in what they let their NPs denote:
- [+arg]: NPs can be argumental (type e, denoting kinds)
- [+pred]: NPs can be predicative (type ⟨e,t⟩)

The combination determines the language's nominal system.
-/
inductive NominalMapping where
  /-- [+arg, -pred]: All nouns are kinds (Chinese-like)
      - All nouns are mass-like
      - No plural morphology
      - Generalized classifier system
      - Bare arguments everywhere -/
  | argOnly
  /-- [+arg, +pred]: Nouns can be kinds or predicates (Germanic-like)
      - Mass/count distinction
      - Bare plurals and mass nouns as arguments
      - Singular count nouns require D -/
  | argAndPred
  /-- [-arg, +pred]: All nouns are predicates (Romance-like)
      - Mass/count distinction
      - Bare arguments restricted (need licensing)
      - D must be projected for argumenthood -/
  | predOnly
  deriving DecidableEq, Repr

/-- Language family classification -/
def languageFamily : NominalMapping → String
  | .argOnly => "Chinese, Japanese (classifier languages)"
  | .argAndPred => "English, German, Slavic (bare argument languages)"
  | .predOnly => "French, Italian, Spanish (Romance languages)"

-- Mass/Count Distinction

/--
The mass/count distinction in [+pred] languages.

Count nouns have atomic extensions (sets of atoms).
Mass nouns have non-atomic extensions (closed under parts).
-/
inductive NounType where
  | count  -- Extension is a set of atoms
  | mass   -- Extension is closed under the part-of relation
  deriving DecidableEq, Repr

/--
Pluralization: PL(F) = λx[¬At(x) ∧ ∀y(y ≤ x ∧ At(y) → F(y))]

Takes a count noun (set of atoms) and returns the set of pluralities
whose atomic parts are all in the original extension.
-/
def pluralize {Atom : Type} (F : Set Atom) : Set (Set Atom) :=
  { s | s.Nonempty ∧ s ⊆ F }

/--
Key insight: Mass nouns come out of the lexicon "already pluralized."

A mass noun like "furniture" is true of individual pieces AND
pluralities of pieces, without distinction.
-/
def massExtension {Atom : Type} (atoms : Set Atom) : Set (Individual Atom) :=
  { x | ∃ a ∈ atoms, x = .atom a } ∪ { x | ∃ s : Set Atom, s ⊆ atoms ∧ s.Nonempty ∧ x = .plural s }

-- Type Shifting as Last Resort (Blocking Principle)

/--
The Blocking Principle: covert type shifting is blocked when an
overt determiner has the same meaning.

For any type shifting operation τ and any X:
  *τ(X) if there is a determiner D such that D(X) = τ(X)

In English:
- ι (iota) is blocked by "the" → can't use ι covertly
- ∃ is blocked by "a/some" for singulars → can't use ∃ covertly for singulars
- ∩ is NOT blocked → can use ∩ freely for bare plurals/mass

This explains why English allows bare plurals but not bare singulars.
-/
structure BlockingPrinciple where
  /-- Available overt determiners -/
  determiners : List String
  /-- Whether ι (definite) is blocked -/
  iotaBlocked : Bool := "the" ∈ determiners
  /-- Whether ∃ (indefinite singular) is blocked -/
  existsBlocked : Bool := "a" ∈ determiners ∨ "some" ∈ determiners
  /-- Whether ∩ (kind formation) is blocked -/
  downBlocked : Bool := False  -- Never blocked in natural languages

/-- Bare argument is licensed iff the required type shift is not blocked -/
def bareArgumentLicensed (bp : BlockingPrinciple) (nounType : NounType) : Bool :=
  match nounType with
  | .mass => !bp.downBlocked  -- Mass nouns use ∩, which is not blocked
  | .count => !bp.downBlocked  -- But only plurals can use ∩ (see below)

-- Why Bare Singulars Are Out

/--
The key insight: ∩ is undefined for singular count nouns.

∩ applied to a singular property would need to yield a kind.
But kinds necessarily have plurality of instances (across worlds).
A property that is necessarily instantiated by just one individual
does not qualify as a kind.

Therefore:
- ∩(dogs) = the dog-kind ✓
- ∩(dog) = undefined ✗

This, combined with blocking of ι and ∃ by articles, explains why
bare singular count nouns cannot occur as arguments in English.
-/
def downDefinedFor (nounType : NounType) (isPlural : Bool) : Bool :=
  match nounType with
  | .mass => true           -- Mass nouns can always use ∩
  | .count => isPlural      -- Count nouns can use ∩ only if plural

/--
Why bare plurals are OK but bare singulars are not (in languages with articles).

Given a language where:
- ι is blocked (has "the")
- ∃ is blocked for singulars (has "a")
- ∩ is not blocked

Then:
- Bare plurals OK: ∩ is defined and not blocked
- Bare singulars OUT: ∩ is undefined, and ι/∃ are blocked

Language-specific configurations live in Fragments/{Language}/Nouns.lean.
-/
theorem bare_plural_ok_bare_singular_not (bp : BlockingPrinciple)
    (hIota : bp.iotaBlocked = true)
    (hExists : bp.existsBlocked = true) :
    downDefinedFor .count true = true ∧
    downDefinedFor .count false = false ∧
    bp.iotaBlocked = true ∧
    bp.existsBlocked = true := by
  simp [hIota, hExists, downDefinedFor]

-- Scopelessness (Theoretical Basis)

/--
Bare plurals are scopeless because DKP introduces a LOCAL existential.

The existential reading from DKP cannot scope out because the coercion
applies inside the predicate abstract.

See `Phenomena/KindReference/Data.lean` for empirical scope data.
-/
def dkpIsLocal : Bool := true

/--
When ∩ is undefined (NP doesn't denote a kind), we fall back to ∃.

For non-kind-denoting NPs like "parts of that machine":
- ∩ is undefined (no corresponding natural kind)
- ∃ is available (not blocked for plurals)
- Result: these NPs behave like regular existential GQs
-/
def fallbackToExists (isKindDenoting : Bool) (bp : BlockingPrinciple) : Bool :=
  !isKindDenoting ∧ !bp.existsBlocked

-- DKP Derivation Machinery (for Scrambling Comparison)

/-!
## Compositional DKP

For comparing with Krifka (2004) on scrambling, we need an explicit
derivation function showing how DKP introduces existential quantification.

DKP is position-invariant. The ∃ is introduced when
the kind combines with the predicate, regardless of surface position.
This predicts narrow scope always — problematic for scrambled bare plurals.

See `Theories/Comparisons/KindReference.lean` for the formal comparison.
-/

variable {Entity World : Type}

/-- A kind's extension at each world (the instances) -/
abbrev KindExtension (Entity World : Type) := World → List Entity

/-- A VP meaning (intensional) -/
abbrev ChierchiaVP (Entity World : Type) := Entity → World → Bool

/-- A sentence meaning (proposition) -/
abbrev ChierchiaSent (World : Type) := World → Bool

/--
DKP (Derived Kind Predication): Coerce a kind to work with object-level predicates.

Given a kind (represented by its extension at each world) and an object-level VP,
DKP introduces existential quantification:

  DKP(VP)(k) = λw. ∃x ∈ k(w). VP(x)(w)

Property: The ∃ is introduced HERE, at the point of composition,
not at a syntactic position. This makes DKP position-invariant.
-/
def dkpApply
    (kind : KindExtension Entity World)
    (vp : ChierchiaVP Entity World)
    : ChierchiaSent World :=
  λ w => (kind w).any (λ x => vp x w)

/--
Chierchia's derivation for "[niet [BP V]]" (unscrambled).

1. BP = kind k
2. VP = λx.V(x)
3. DKP: ∃x[k(x) ∧ V(x)]
4. Negation: ¬∃x[k(x) ∧ V(x)]
-/
def chierchiaDerivUnscrambled
    (kind : KindExtension Entity World)
    (vp : ChierchiaVP Entity World)
    : ChierchiaSent World :=
  λ w => !(dkpApply kind vp w)

/--
Chierchia's derivation for "[BP [niet V]]" (scrambled).

In Chierchia's system, scrambling doesn't change the derivation.
DKP still applies when the kind meets the predicate, and the ∃
is introduced at that point (the trace position in LF).

Result: Same as unscrambled — ¬∃x[k(x) ∧ V(x)]
-/
def chierchiaDerivScrambled
    (kind : KindExtension Entity World)
    (vp : ChierchiaVP Entity World)
    : ChierchiaSent World :=
  -- Scrambling is invisible to DKP — same derivation
  λ w => !(dkpApply kind vp w)

/--
Chierchia's DKP is position-invariant.

Scrambled and unscrambled derivations yield the same meaning.
This is the source of Chierchia's incorrect prediction for Dutch scrambling.
-/
theorem chierchia_position_invariant
    (kind : KindExtension Entity World)
    (vp : ChierchiaVP Entity World)
    : chierchiaDerivScrambled kind vp = chierchiaDerivUnscrambled kind vp := rfl

-- Theory Verification

/-- ∩ is defined for plural count nouns -/
example : downDefinedFor .count true = true := rfl

/-- ∩ is undefined for singular count nouns -/
example : downDefinedFor .count false = false := rfl

/-- ∩ is always defined for mass nouns -/
example : downDefinedFor .mass true = true := rfl
example : downDefinedFor .mass false = true := rfl

/-!
## Related Theory

- `Theories/Montague/Lexicon/Krifka2004.lean` - Alternative: Bare NPs as properties
- `Theories/Montague/Lexicon/Dayal2004.lean` - Meaning Preservation, singular kinds
- `Theories/Montague/Lexicon/Generics.lean` - GEN operator for generic readings

## Empirical Data

For empirical patterns (cross-linguistic data, scope judgments, predicate
class effects), see:
- `Phenomena/KindReference/Data.lean` - unified kind reference phenomena
- `Phenomena/BarePlurals/Data.lean` - generic vs existential readings
- `Phenomena/Generics/Data.lean` - generic sentence patterns
-/

-- ============================================================================
-- Kind Formation via Equivalence Relations (Mendia 2020, Snyder 2026 §4.1)
-- ============================================================================

section KindFormation

/-- An equivalence relation on atoms partitions them into subkinds. -/
structure KindFormation (Atom : Type) where
  /-- The salient equivalence relation -/
  rel : Atom → Atom → Prop
  /-- Must be an equivalence -/
  isEquiv : Equivalence rel

/-- Subkind relation: k₁ is a subkind of k₂ iff every
    entity instantiating k₁ also instantiates k₂. -/
def isSubkindOf {Atom : Type} (k₁ k₂ : Set Atom) : Prop :=
  k₁ ⊆ k₂

/-- Carlson's (1977) Disjointness Condition: subkinds induced by an
    equivalence relation are pairwise disjoint in any context. -/
theorem disjointness_condition {Atom : Type} [DecidableEq Atom]
    (kf : KindFormation Atom) (a b : Atom) (h : ¬kf.rel a b) :
    Disjoint {x | kf.rel a x} {x | kf.rel b x} := by
  rw [Set.disjoint_iff]
  intro x ⟨ha, hb⟩
  have hxa : kf.rel x a := kf.isEquiv.symm ha
  have hxb : kf.rel x b := kf.isEquiv.symm hb
  have hab : kf.rel a b := kf.isEquiv.trans (kf.isEquiv.symm hxa) hxb
  exact h hab

/-- Number taxonomy: NUMBER has subkinds ℕ, ℤ, ℚ, ℝ, etc.
    TWO has subkinds 2_ℕ, 2_ℤ, 2_ℚ, 2_ℝ (Snyder §4.3). -/
inductive NumberSystem where
  | nat | int | rat | real
  deriving DecidableEq, BEq, Repr

instance : Fintype NumberSystem where
  elems := {.nat, .int, .rat, .real}
  complete := by intro x; cases x <;> simp

/-- Two twos from different systems are distinct subkinds of TWO. -/
def twoSubkinds : NumberSystem → NumberSystem → Prop := (· ≠ ·)

/-- The four number systems. -/
def NumberSystem.all : List NumberSystem := [.nat, .int, .rat, .real]

/-- NUMBER has four subkinds (ℕ, ℤ, ℚ, ℝ).
    This is what makes taxonomic predication ("two comes in several
    varieties") felicitous: the kind TWO has genuinely distinct subkinds. -/
theorem numberSystem_count : NumberSystem.all.length = 4 := rfl

/-- All pairs of distinct number systems yield distinct subkinds. -/
theorem twoSubkinds_of_ne (s₁ s₂ : NumberSystem) (h : s₁ ≠ s₂) :
    twoSubkinds s₁ s₂ := h

end KindFormation

end TruthConditional.Noun.Kind.Chierchia1998
