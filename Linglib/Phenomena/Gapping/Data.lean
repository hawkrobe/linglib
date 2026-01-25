/-
# Gapping and Constituent Order

Empirical data on gapping patterns across SOV, VSO, and SVO languages.

## The Phenomenon

Gapping involves the apparent "ellipsis" of a verb in coordinated structures:

  "Dexter ate bread, and Warren, potatoes."
       ↑                    ↑
    overt verb           "gapped" verb

## Ross's Generalization (1970)

The directionality of gapping correlates with basic word order:

  SOV languages: backward gapping (SO and SOV)
    "Ken-ga Naomi-o, Erika-ga Sara-o tazuneta"
    (Ken Naomi-ACC, Erika Sara-ACC visited)

  VSO languages: forward gapping (VSO and SO)
    "Chonaic Eoghan Siobhán agus Eoghnai Ciaran"
    (Saw Eoghan Siobhán and Eoghnai Ciaran)

  SVO languages: forward gapping (SVO and SO)
    "Dexter ate bread, and Warren, potatoes"

## Key Insight (Steedman 2000)

Gapping direction depends on the AVAILABILITY of verb categories:
- Forward gapping requires rightward-combining verbs
- Backward gapping requires leftward-combining verbs

Languages with BOTH verb orders (Dutch, Zapotec) allow BOTH gapping patterns.

## References

- Ross (1970) "Gapping and the order of constituents"
- Steedman (2000) "The Syntactic Process" Chapter 7
- Maling (1972) "On 'Gapping and the order of constituents'"
-/

namespace Phenomena.Gapping

-- ============================================================================
-- Word Order Typology
-- ============================================================================

/--
Basic word order types for transitive clauses.

S = Subject, V = Verb, O = Object
-/
inductive WordOrder where
  | SOV   -- Subject-Object-Verb (Japanese, Korean, Turkish)
  | SVO   -- Subject-Verb-Object (English, French, Chinese)
  | VSO   -- Verb-Subject-Object (Irish, Welsh, Arabic)
  | VOS   -- Verb-Object-Subject (Malagasy)
  | OVS   -- Object-Verb-Subject (Hixkaryana)
  | OSV   -- Object-Subject-Verb (rare)
  deriving DecidableEq, BEq, Repr

/-- Languages can have different orders in main vs subordinate clauses -/
structure WordOrderProfile where
  mainClause : WordOrder
  subClause : WordOrder
  deriving Repr

-- ============================================================================
-- Gapping Direction
-- ============================================================================

/--
Direction of gapping in coordinate structures.

Forward: Verb in FIRST conjunct, gap in SECOND
  "Dexter ate bread, and Warren, potatoes"
        ↑                        ↑gap

Backward: Gap in FIRST conjunct, verb in SECOND
  "Ken Naomi-o, Erika Sara-o tazuneta"
       ↑gap                    ↑verb
-/
inductive GappingDirection where
  | forward   -- Gap follows the overt verb (VSO, SVO pattern)
  | backward  -- Gap precedes the overt verb (SOV pattern)
  deriving DecidableEq, BEq, Repr

/--
A gapping pattern describes what a language allows.
-/
structure GappingPattern where
  allowsForward : Bool
  allowsBackward : Bool
  deriving Repr

def GappingPattern.forwardOnly : GappingPattern := ⟨true, false⟩
def GappingPattern.backwardOnly : GappingPattern := ⟨false, true⟩
def GappingPattern.both : GappingPattern := ⟨true, true⟩
def GappingPattern.neither : GappingPattern := ⟨false, false⟩

-- ============================================================================
-- Ross's Generalization
-- ============================================================================

/--
Ross's original generalization about gapping and word order.
-/
def rossOriginal (order : WordOrder) : GappingPattern :=
  match order with
  | .SOV => GappingPattern.backwardOnly  -- *SOV and SO, SO and SOV
  | .VSO => GappingPattern.forwardOnly   -- VSO and SO, *SO and VSO
  | .SVO => GappingPattern.forwardOnly   -- SVO and SO, *SO and SVO
  | .VOS => GappingPattern.forwardOnly   -- Patterns with VSO
  | .OVS => GappingPattern.backwardOnly  -- Patterns with SOV
  | .OSV => GappingPattern.backwardOnly  -- Rare, patterns with SOV

/--
Steedman's revised generalization: gapping depends on LEXICAL availability
of verb categories, not "underlying" word order.

A language allows forward gapping iff it has rightward-combining verbs.
A language allows backward gapping iff it has leftward-combining verbs.
-/
def hasRightwardVerbs : WordOrder → Bool
  | .VSO => true
  | .SVO => true
  | .VOS => true
  | _ => false

def hasLeftwardVerbs : WordOrder → Bool
  | .SOV => true
  | .OVS => true
  | .OSV => true
  | _ => false

def rossRevised (profile : WordOrderProfile) : GappingPattern :=
  let hasRightward := hasRightwardVerbs profile.mainClause
  let hasLeftward := hasLeftwardVerbs profile.mainClause ||
                     hasLeftwardVerbs profile.subClause
  ⟨hasRightward, hasLeftward⟩

-- ============================================================================
-- Language Examples
-- ============================================================================

/-- Japanese: pure SOV, backward gapping only -/
def japanese : WordOrderProfile := ⟨.SOV, .SOV⟩

/-- Irish: pure VSO, forward gapping only -/
def irish : WordOrderProfile := ⟨.VSO, .VSO⟩

/-- English: pure SVO, forward gapping only -/
def english : WordOrderProfile := ⟨.SVO, .SVO⟩

/-- Dutch: VSO main clause, SOV subordinate clause - BOTH directions -/
def dutch : WordOrderProfile := ⟨.SVO, .SOV⟩  -- Main is V2 ≈ VSO

/-- German: similar to Dutch -/
def german : WordOrderProfile := ⟨.SVO, .SOV⟩

/-- Zapotec: VSO subordinate, but allows SOV main clause - BOTH directions -/
def zapotec : WordOrderProfile := ⟨.VSO, .VSO⟩  -- But allows SOV main

-- ============================================================================
-- Gapping Examples
-- ============================================================================

/--
A gapping example in a specific language.
-/
structure GappingExample where
  language : String
  surface : String
  gloss : String
  translation : String
  direction : GappingDirection
  isGrammatical : Bool
  deriving Repr

-- Japanese (SOV) examples
def japanese_backward : GappingExample :=
  { language := "Japanese"
  , surface := "[Ken-ga Naomi-o], [Erika-ga Sara-o] tazuneta"
  , gloss := "[Ken-NOM Naomi-ACC], [Erika-NOM Sara-ACC] visited"
  , translation := "Ken visited Naomi, and Erika, Sara"
  , direction := .backward
  , isGrammatical := true
  }

def japanese_forward_bad : GappingExample :=
  { language := "Japanese"
  , surface := "*Ken-ga Naomi-o tazunete, Erika-ga Sara-o"
  , gloss := "*Ken-NOM Naomi-ACC visited, Erika-NOM Sara-ACC"
  , translation := "Ken visited Naomi, and Erika, Sara"
  , direction := .forward
  , isGrammatical := false
  }

-- Irish (VSO) examples
def irish_forward : GappingExample :=
  { language := "Irish"
  , surface := "Chonaic [Eoghan Siobhán] agus [Eoghnai Ciaran]"
  , gloss := "saw [Eoghan Siobhán] and [Eoghnai Ciaran]"
  , translation := "Eoghan saw Siobhán, and Eoghnai, Ciaran"
  , direction := .forward
  , isGrammatical := true
  }

def irish_backward_bad : GappingExample :=
  { language := "Irish"
  , surface := "*[Eoghan Siobhán] agus chonaic [Eoghnai Ciaran]"
  , gloss := "*[Eoghan Siobhán] and saw [Eoghnai Ciaran]"
  , translation := "Eoghan saw Siobhán, and Eoghnai, Ciaran"
  , direction := .backward
  , isGrammatical := false
  }

-- English (SVO) examples
def english_forward : GappingExample :=
  { language := "English"
  , surface := "Dexter ate bread, and Warren, potatoes"
  , gloss := "Dexter ate bread, and Warren, potatoes"
  , translation := "Dexter ate bread, and Warren ate potatoes"
  , direction := .forward
  , isGrammatical := true
  }

def english_backward_bad : GappingExample :=
  { language := "English"
  , surface := "*Warren, potatoes, and Dexter ate bread"
  , gloss := "*Warren, potatoes, and Dexter ate bread"
  , translation := "Warren ate potatoes, and Dexter ate bread"
  , direction := .backward
  , isGrammatical := false
  }

-- Dutch examples (both directions)
def dutch_main_forward : GappingExample :=
  { language := "Dutch"
  , surface := "Wil jij een ijsje en Marietje limonade?"
  , gloss := "want you an ice-cream and Marietje lemonade?"
  , translation := "Do you want an ice-cream, and Marietje lemonade?"
  , direction := .forward
  , isGrammatical := true
  }

def dutch_sub_backward : GappingExample :=
  { language := "Dutch"
  , surface := "...dat [Jan Syntactic Structures en Piet Aspects] gelezen heeft"
  , gloss := "...that [Jan Syntactic Structures and Piet Aspects] read has"
  , translation := "that Jan read Syntactic Structures and Piet Aspects"
  , direction := .backward
  , isGrammatical := true
  }

-- ============================================================================
-- Collected Data
-- ============================================================================

def allGappingExamples : List GappingExample :=
  [ japanese_backward, japanese_forward_bad
  , irish_forward, irish_backward_bad
  , english_forward, english_backward_bad
  , dutch_main_forward, dutch_sub_backward
  ]

def grammaticalExamples : List GappingExample :=
  allGappingExamples.filter (·.isGrammatical)

def ungrammaticalExamples : List GappingExample :=
  allGappingExamples.filter (!·.isGrammatical)

-- ============================================================================
-- Gapping vs Other Ellipsis
-- ============================================================================

/--
Types of elliptical constructions (Steedman's taxonomy).

Gapping and Stripping are syntactically mediated via CCG.
VP Ellipsis and Sluicing are purely anaphoric.
-/
inductive EllipsisType where
  | gapping      -- "Dexter ate bread, and Warren, potatoes"
  | stripping    -- "Dexter ran away, and Warren (too)"
  | vpEllipsis   -- "Dexter ate bread, and Warren did too"
  | sluicing     -- "Dexter did something, but I don't know what"
  deriving DecidableEq, BEq, Repr

/-- Is the ellipsis type syntactically mediated (vs purely anaphoric)? -/
def isSyntacticallyMediated : EllipsisType → Bool
  | .gapping => true
  | .stripping => true
  | .vpEllipsis => false
  | .sluicing => false

/-- Does the ellipsis type exhibit word-order constraints? -/
def hasWordOrderConstraints : EllipsisType → Bool
  | .gapping => true
  | .stripping => true
  | .vpEllipsis => false  -- Same pattern in all languages
  | .sluicing => false    -- Same pattern in all languages

-- ============================================================================
-- Verification: Ross's Predictions
-- ============================================================================

/-- Pure SOV language has backward gapping only -/
theorem sov_backward_only :
    (rossRevised japanese).allowsForward = false ∧
    (rossRevised japanese).allowsBackward = true := by
  constructor <;> rfl

/-- Pure VSO language has forward gapping only -/
theorem vso_forward_only :
    (rossRevised irish).allowsForward = true ∧
    (rossRevised irish).allowsBackward = false := by
  constructor <;> rfl

/-- Pure SVO language has forward gapping only -/
theorem svo_forward_only :
    (rossRevised english).allowsForward = true ∧
    (rossRevised english).allowsBackward = false := by
  constructor <;> rfl

/-- Mixed order language (Dutch) allows both -/
theorem mixed_allows_both :
    (rossRevised dutch).allowsForward = true ∧
    (rossRevised dutch).allowsBackward = true := by
  constructor <;> rfl

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Word Order Typology
- `WordOrder`: SOV, SVO, VSO, VOS, OVS, OSV
- `WordOrderProfile`: main vs subordinate clause orders
- `GappingDirection`: forward vs backward

### Ross's Generalization
- `rossOriginal`: original correlation
- `rossRevised`: Steedman's lexically-based revision

### Key Examples
- Japanese (pure SOV): backward only
- Irish (pure VSO): forward only
- English (pure SVO): forward only
- Dutch (mixed): both directions

### Key Theorems
- `sov_backward_only`: SOV → backward gapping
- `vso_forward_only`: VSO → forward gapping
- `svo_forward_only`: SVO → forward gapping
- `mixed_allows_both`: Mixed order → both directions

### What's NOT Here (belongs in Theories/CCG/)
- CCG derivations of gapped sentences
- Category decomposition rules
- Type-raised argument coordination
-/

end Phenomena.Gapping
