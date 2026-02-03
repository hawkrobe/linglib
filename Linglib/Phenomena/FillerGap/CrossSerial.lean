/-
# Cross-Serial Dependencies

Empirical data on cross-serial dependencies in Dutch verb clusters.

## The Phenomenon

In Dutch subordinate clauses, multiple NPs can precede multiple verbs,
with each NP interpreted as the argument of a corresponding verb:

  "... dat Jan Piet Marie zag helpen zwemmen"
  "... that Jan Piet Marie saw help   swim"
  = "that Jan saw Piet help Marie swim"

The dependencies are CROSS-SERIAL (not nested):
  NP₁ NP₂ NP₃ V₁ V₂ V₃
  └────────────┘
      └────────────┘
          └────────────┘

This pattern is beyond the power of context-free grammars.
CCG handles it via generalized composition.

## Key Contrast with German

German has NESTED dependencies (can be handled by CFG):
  NP₁ NP₂ NP₃ V₃ V₂ V₁
  └────────────────────┘
      └────────────┘
          └────┘

## References

- Bresnan et al. (1982) "Cross-serial dependencies in Dutch"
- Steedman (2000) "The Syntactic Process" Chapter 6
- Shieber (1985) "Evidence against the context-freeness of natural language"
-/

namespace Phenomena.FillerGap.CrossSerial

-- ============================================================================
-- NP-Verb Pairing Types
-- ============================================================================

/--
A dependency pairing: which NP goes with which verb.

Position 1 is leftmost in the string.
-/
structure Dependency where
  /-- Position of the NP (1-indexed from left) -/
  npPosition : Nat
  /-- Position of the verb (1-indexed from left among verbs) -/
  verbPosition : Nat
  deriving DecidableEq, BEq, Repr

/--
Dependency pattern: how NPs and verbs are paired.
-/
inductive DependencyPattern where
  | crossSerial  -- NP₁→V₁, NP₂→V₂, ... (Dutch)
  | nested       -- NP₁→Vₙ, NP₂→Vₙ₋₁, ... (German)
  deriving DecidableEq, BEq, Repr

/-- Generate cross-serial dependencies for n NP-V pairs -/
def crossSerialDeps (n : Nat) : List Dependency :=
  List.range n |>.map (fun i => ⟨i + 1, i + 1⟩)

/-- Generate nested dependencies for n NP-V pairs -/
def nestedDeps (n : Nat) : List Dependency :=
  List.range n |>.map (fun i => ⟨i + 1, n - i⟩)

-- ============================================================================
-- Dutch Examples (Steedman 2000)
-- ============================================================================

/--
Dutch cross-serial dependency example.

Surface: ... dat Jan Piet Marie zag helpen zwemmen
Gloss:   ... that Jan Piet Marie saw help   swim
Meaning: ... that Jan saw Piet help Marie swim

Dependencies:
- Jan (NP₁) → zag (V₁) "saw"
- Piet (NP₂) → helpen (V₂) "help"
- Marie (NP₃) → zwemmen (V₃) "swim"
-/
structure DutchExample where
  /-- Surface string (Dutch) -/
  surface : String
  /-- English gloss -/
  gloss : String
  /-- English translation -/
  translation : String
  /-- NPs in order -/
  nps : List String
  /-- Verbs in order -/
  verbs : List String
  /-- The observed dependency pattern -/
  pattern : DependencyPattern
  /-- The actual pairings -/
  dependencies : List Dependency
  deriving Repr

def dutch_3np_3v : DutchExample :=
  { surface := "... dat Jan Piet Marie zag helpen zwemmen"
  , gloss := "... that Jan Piet Marie saw help swim"
  , translation := "that Jan saw Piet help Marie swim"
  , nps := ["Jan", "Piet", "Marie"]
  , verbs := ["zag", "helpen", "zwemmen"]
  , pattern := .crossSerial
  , dependencies := crossSerialDeps 3
  }

def dutch_2np_2v : DutchExample :=
  { surface := "... dat Jan Piet zag zwemmen"
  , gloss := "... that Jan Piet saw swim"
  , translation := "that Jan saw Piet swim"
  , nps := ["Jan", "Piet"]
  , verbs := ["zag", "zwemmen"]
  , pattern := .crossSerial
  , dependencies := crossSerialDeps 2
  }

def dutch_4np_4v : DutchExample :=
  { surface := "... dat Jan Piet Marie Karel zag helpen laten zwemmen"
  , gloss := "... that Jan Piet Marie Karel saw help let swim"
  , translation := "that Jan saw Piet help Marie let Karel swim"
  , nps := ["Jan", "Piet", "Marie", "Karel"]
  , verbs := ["zag", "helpen", "laten", "zwemmen"]
  , pattern := .crossSerial
  , dependencies := crossSerialDeps 4
  }

-- ============================================================================
-- German Contrast (Nested)
-- ============================================================================

/--
German nested dependency example.

German has the OPPOSITE verb order from Dutch, giving nested dependencies
that ARE context-free.
-/
structure GermanExample where
  surface : String
  gloss : String
  translation : String
  nps : List String
  verbs : List String
  pattern : DependencyPattern
  dependencies : List Dependency
  deriving Repr

def german_3np_3v : GermanExample :=
  { surface := "... dass Jan Piet Marie schwimmen helfen sah"
  , gloss := "... that Jan Piet Marie swim help saw"
  , translation := "that Jan saw Piet help Marie swim"
  , nps := ["Jan", "Piet", "Marie"]
  , verbs := ["schwimmen", "helfen", "sah"]
  , pattern := .nested
  , dependencies := nestedDeps 3
  }

-- ============================================================================
-- The Formal Language Connection
-- ============================================================================

/--
Cross-serial dependencies correspond to the copy language {ww | w ∈ Σ*},
or more precisely to {aⁿbⁿcⁿdⁿ | n ≥ 1}.

This is NOT context-free (proven by pumping lemma).
CCG can generate it via generalized composition.
-/
inductive FormalLanguageType where
  | contextFree      -- Can be generated by CFG
  | mildlyContextSensitive  -- CCG, TAG, etc.
  | contextSensitive -- Full CSG power
  deriving DecidableEq, BEq, Repr

/-- Cross-serial dependencies require mild context-sensitivity -/
def crossSerialRequires : FormalLanguageType := .mildlyContextSensitive

/-- Nested dependencies are context-free -/
def nestedRequires : FormalLanguageType := .contextFree

-- ============================================================================
-- Collected Data
-- ============================================================================

def allDutchExamples : List DutchExample :=
  [dutch_2np_2v, dutch_3np_3v, dutch_4np_4v]

def allGermanExamples : List GermanExample :=
  [german_3np_3v]

-- ============================================================================
-- Verification
-- ============================================================================

/-- Cross-serial has same number of dependencies as NPs -/
theorem crossSerial_length (n : Nat) :
    (crossSerialDeps n).length = n := by
  simp [crossSerialDeps]

/-- Nested has same number of dependencies as NPs -/
theorem nested_length (n : Nat) :
    (nestedDeps n).length = n := by
  simp [nestedDeps]

/-- Dutch 3-NP example has cross-serial pattern -/
theorem dutch_3_is_crossSerial :
    dutch_3np_3v.pattern = .crossSerial := rfl

/-- German 3-NP example has nested pattern -/
theorem german_3_is_nested :
    german_3np_3v.pattern = .nested := rfl

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Empirical Data
- Dutch cross-serial examples (2, 3, 4 NP-V clusters)
- German nested examples (for contrast)
- Dependency pairings (which NP goes with which V)

### Key Distinction
- **Cross-serial (Dutch)**: NP₁→V₁, NP₂→V₂, NP₃→V₃
- **Nested (German)**: NP₁→V₃, NP₂→V₂, NP₃→V₁

### Formal Language Connection
- Cross-serial requires MILD CONTEXT-SENSITIVITY (CCG, TAG)
- Nested is CONTEXT-FREE (standard CFG can handle)

### What's NOT Here (belongs in Theories/CCG/)
- CCG derivations for these sentences
- Generalized composition rules (B, B², S)
- Proof that CCG generates cross-serial pattern
-/

end Phenomena.FillerGap.CrossSerial
