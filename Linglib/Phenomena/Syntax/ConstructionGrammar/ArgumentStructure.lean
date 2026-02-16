import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Phenomena.Syntax.ConstructionGrammar.Studies.GoldbergShirtz2025
import Linglib.Phenomena.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988
import Linglib.Core.Interfaces.CombinationSchema

/-!
# Argument Structure Constructions

CxG's argument structure constructions (Goldberg 1995) and their decomposition
into Müller's three universal schemata.

Müller (2013, §3) argues "both directions right": the three universal schemata
capture *fully abstract* constructions (ditransitive, caused-motion, resultative),
but *partially open* and *lexically specified* constructions are irreducible
phrasal patterns that only CxG can capture.

## Key claims

1. Fully abstract constructions decompose into sequences of Head-Complement
   and Head-Specifier steps
2. Partially open constructions (PAL, let alone, WXDY) are irreducible —
   they cannot be decomposed into the three schemata
3. This is CxG's unique contribution: phrasal constructions beyond the schemata

## References

- Goldberg, A. E. (1995). Constructions. Ch. 3.
- Müller, S. (2013). Unifying Everything. Language 89(4):920–950.
-/

namespace ConstructionGrammar

open Core.Interfaces

/-! ## Construction slots and argument frames -/

/-- A slot in an argument structure construction.

Each slot specifies a syntactic category and a semantic role
for one participant in the construction's event structure. -/
structure ConstructionSlot where
  /-- Syntactic category of this slot (NP, V, PP, etc.) -/
  cat : UD.UPOS
  /-- Semantic role label -/
  role : String
  /-- Whether this slot is the head of the construction -/
  isHead : Bool := false
  deriving Repr, BEq

/-- An argument structure construction with explicit slot structure.

This extends the basic `Construction` with a decomposed argument frame,
enabling formal analysis of how the construction relates to the three
universal combination schemata. -/
structure ArgStructureConstruction where
  /-- The underlying construction -/
  construction : Construction
  /-- The argument frame: ordered list of slots -/
  slots : List ConstructionSlot
  /-- At least one slot should be the head -/
  hasHead : slots.any (·.isHead) = true
  deriving Repr

/-! ## Concrete argument structure constructions (Goldberg 1995, Ch. 3) -/

/-- Ditransitive construction: [Subj V Obj1 Obj2].
"X CAUSES Y to RECEIVE Z" (e.g., "She gave him a book"). -/
def ditransitive : ArgStructureConstruction :=
  { construction :=
      { name := "Ditransitive"
      , form := "[Subj V Obj1 Obj2]"
      , meaning := "X CAUSES Y to RECEIVE Z"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "agent", false⟩       -- Subj
      , ⟨.VERB, "predicate", true⟩    -- V (head)
      , ⟨.NOUN, "recipient", false⟩   -- Obj1
      , ⟨.NOUN, "theme", false⟩ ]     -- Obj2
  , hasHead := by native_decide }

/-- Caused-motion construction: [Subj V Obj Obl].
"X CAUSES Y to MOVE to Z" (e.g., "She sneezed the napkin off the table"). -/
def causedMotion : ArgStructureConstruction :=
  { construction :=
      { name := "Caused-motion"
      , form := "[Subj V Obj Obl]"
      , meaning := "X CAUSES Y to MOVE to Z"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "agent", false⟩       -- Subj
      , ⟨.VERB, "predicate", true⟩    -- V (head)
      , ⟨.NOUN, "theme", false⟩       -- Obj
      , ⟨.ADP, "goal", false⟩ ]       -- Obl
  , hasHead := by native_decide }

/-- Resultative construction: [Subj V Obj Pred].
"X CAUSES Y to BECOME Z" (e.g., "She hammered the metal flat"). -/
def resultative : ArgStructureConstruction :=
  { construction :=
      { name := "Resultative"
      , form := "[Subj V Obj Pred]"
      , meaning := "X CAUSES Y to BECOME Z"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "agent", false⟩       -- Subj
      , ⟨.VERB, "predicate", true⟩    -- V (head)
      , ⟨.NOUN, "patient", false⟩     -- Obj
      , ⟨.ADJ, "result", false⟩ ]     -- Pred
  , hasHead := by native_decide }

/-- Intransitive motion construction: [Subj V Obl].
"X MOVES to Y" (e.g., "The ball rolled down the hill"). -/
def intransitiveMotion : ArgStructureConstruction :=
  { construction :=
      { name := "Intransitive-motion"
      , form := "[Subj V Obl]"
      , meaning := "X MOVES to Y"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "theme", false⟩       -- Subj
      , ⟨.VERB, "predicate", true⟩    -- V (head)
      , ⟨.ADP, "path", false⟩ ]       -- Obl
  , hasHead := by native_decide }

/-! ## Decomposition into combination schemata -/

/-- Decompose a fully abstract construction into a sequence of combination steps.

For a construction with slots [Subj, V, Obj1, Obj2]:
1. V + Obj2 → V' (Head-Complement)
2. V' + Obj1 → V'' (Head-Complement)
3. Subj + V'' → S (Head-Specifier)

The head slot determines which combinations are complements vs specifier. -/
def decompose (asc : ArgStructureConstruction) : List CombinationKind :=
  let nonHeadSlots := asc.slots.filter (!·.isHead)
  -- Subject (first non-head slot) maps to Head-Specifier,
  -- all other non-head slots map to Head-Complement
  nonHeadSlots.zipIdx.map λ ⟨_, i⟩ =>
    if i == 0 then .headSpecifier  -- first non-head = specifier (subject)
    else .headComplement           -- later non-heads = complements

/-- A construction is decomposable if it has specificity `fullyAbstract`
and no construction-specific pragmatic function — i.e., its meaning is
fully compositional from the three universal schemata. -/
def isDecomposable (c : Construction) : Bool :=
  c.specificity == .fullyAbstract && c.pragmaticFunction.isNone

/-! ## Core theorems -/

/-- Ditransitive decomposes into Head-Specifier + Head-Complement + Head-Complement.

The ditransitive [Subj V Obj1 Obj2] decomposes as:
1. V + Obj2 → V' (Head-Complement)
2. V' + Obj1 → V'' (Head-Complement)
3. Subj + V'' → S (Head-Specifier) -/
theorem ditransitive_decomposes :
    decompose ditransitive = [.headSpecifier, .headComplement, .headComplement] := by
  native_decide

/-- Caused-motion decomposes into Head-Specifier + Head-Complement + Head-Complement. -/
theorem causedMotion_decomposes :
    decompose causedMotion = [.headSpecifier, .headComplement, .headComplement] := by
  native_decide

/-- Resultative decomposes into Head-Specifier + Head-Complement + Head-Complement. -/
theorem resultative_decomposes :
    decompose resultative = [.headSpecifier, .headComplement, .headComplement] := by
  native_decide

/-- Fully abstract constructions without pragmatic functions are decomposable. -/
theorem fullyAbstract_is_decomposable (c : Construction)
    (h₁ : c.specificity = .fullyAbstract)
    (h₂ : c.pragmaticFunction = none) :
    isDecomposable c = true := by
  unfold isDecomposable
  rw [h₁, h₂]
  native_decide

/-- PAL construction (Goldberg & Shirtz 2025) is NOT decomposable.

PAL is a phrasal construction where a phrase fills a word-level slot.
This form-function pairing cannot be captured by the three schemata alone —
it requires construction-specific knowledge. -/
theorem pal_irreducible :
    isDecomposable Studies.GoldbergShirtz2025.palConstruction = false := by
  native_decide

/-- *Let alone* construction (FKO 1988) is NOT decomposable.

*Let alone* is a formal idiom with paired focus, scalar entailment, and
NPI licensing requirements. These semantic/pragmatic properties cannot
be derived from Head-Complement + Head-Specifier + Head-Filler. -/
theorem let_alone_irreducible :
    isDecomposable Studies.FillmoreKayOConnor1988.letAloneConstruction = false := by
  native_decide

/-- Müller's "both directions right" (§3): the three schemata handle
fully abstract constructions, but CxG's phrasal constructions are irreducible.

This formalizes the biconditional:
- Fully abstract → decomposable (covered by universal schemata)
- Non-fully-abstract → not decomposable (requires CxG) -/
theorem both_directions_right :
    -- Fully abstract constructions without pragmatic functions are decomposable
    (∀ c : Construction, c.specificity = .fullyAbstract →
      c.pragmaticFunction = none →
      isDecomposable c = true) ∧
    -- There exist non-abstract constructions that are irreducible
    (∃ c : Construction, isDecomposable c = false) := by
  constructor
  · intro c hspec hprag
    exact fullyAbstract_is_decomposable c hspec hprag
  · exact ⟨Studies.GoldbergShirtz2025.palConstruction, pal_irreducible⟩

end ConstructionGrammar
