/-
# Dependency Grammar Examples

Demonstrates dependency tree construction and well-formedness checking.
-/

import LingLean.Syntax.DependencyGrammar.Basic

open Lexicon DepGrammar

-- ============================================================================
-- Basic Tree Examples
-- ============================================================================

/-- "John sleeps" - intransitive
    John ←subj─ sleeps
-/
def johnSleepsTree : DepTree :=
  { words := [john, sleeps]
    deps := [⟨1, 0, .subj⟩]
    rootIdx := 1 }

/-- "He sleeps" - with agreement -/
def heSleepsTree : DepTree :=
  { words := [he, sleeps]
    deps := [⟨1, 0, .subj⟩]
    rootIdx := 1 }

/-- "*He sleep" - agreement violation -/
def heSleepTree : DepTree :=
  { words := [he, sleep]
    deps := [⟨1, 0, .subj⟩]
    rootIdx := 1 }

/-- "John sees Mary" - transitive SVO
    John ←subj─ sees ─obj→ Mary
-/
def johnSeesMaryTree : DepTree :=
  { words := [john, sees, mary]
    deps := [⟨1, 0, .subj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1 }

/-- "The girl sleeps" - with determiner
    the ─det→ girl ←subj─ sleeps
-/
def theGirlSleepsTree : DepTree :=
  { words := [the, girl, sleeps]
    deps := [⟨1, 0, .det⟩, ⟨2, 1, .subj⟩]
    rootIdx := 2 }

/-- "*a girls" - determiner-noun agreement violation -/
def aGirlsTree : DepTree :=
  { words := [a, girls]
    deps := [⟨1, 0, .det⟩]
    rootIdx := 1 }

/-- "these books" - correct det-noun agreement -/
def theseBooksTree : DepTree :=
  { words := [these, books]
    deps := [⟨1, 0, .det⟩]
    rootIdx := 1 }

/-- "John gives Mary book" - ditransitive
    John ←subj─ gives ─iobj→ Mary
                  │
                  └─obj→ book
-/
def johnGivesMaryBookTree : DepTree :=
  { words := [john, gives, mary, book]
    deps := [⟨1, 0, .subj⟩, ⟨1, 2, .iobj⟩, ⟨1, 3, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- Well-formedness Tests
-- ============================================================================

-- Structure tests
#eval hasUniqueHeads johnSleepsTree      -- true
#eval isAcyclic johnSleepsTree           -- true
#eval isProjective johnSleepsTree        -- true

-- Agreement tests
#eval checkSubjVerbAgr heSleepsTree      -- true (3sg-3sg)
#eval checkSubjVerbAgr heSleepTree       -- false (3sg-pl)
#eval checkDetNounAgr theseBooksTree     -- true (pl-pl)
#eval checkDetNounAgr aGirlsTree         -- false (sg-pl)

-- Subcategorization tests
#eval checkVerbSubcat johnSleepsTree     -- true (intrans, 0 obj)
#eval checkVerbSubcat johnSeesMaryTree   -- true (trans, 1 obj)
#eval checkVerbSubcat johnGivesMaryBookTree  -- true (ditrans, 1 obj, 1 iobj)

-- Overall well-formedness
#eval isWellFormed heSleepsTree          -- true
#eval isWellFormed heSleepTree           -- false (agreement)
#eval isWellFormed johnSeesMaryTree      -- true
#eval isWellFormed theGirlSleepsTree     -- true
#eval isWellFormed aGirlsTree            -- false (det-noun agr)
#eval isWellFormed theseBooksTree        -- true

-- ============================================================================
-- Projectivity Examples
-- ============================================================================

/-- A projective tree (no crossing dependencies)
    The   girl   saw   the   cat
     └─det─┘      │     └─det─┘
           └─subj─┘─obj─────┘
-/
def projectiveTree : DepTree :=
  { words := [the, girl, sees, the, cat_]
    deps := [
      ⟨1, 0, .det⟩,   -- the → girl
      ⟨2, 1, .subj⟩,  -- girl → sees
      ⟨4, 3, .det⟩,   -- the → cat
      ⟨2, 4, .obj⟩    -- cat → sees
    ]
    rootIdx := 2 }

#eval isProjective projectiveTree  -- true

-- ============================================================================
-- Visualizing Dependencies (as strings)
-- ============================================================================

/-- Convert a dependency tree to a simple string representation -/
def depTreeToString (t : DepTree) : String :=
  let wordStrs := t.words.map (·.form)
  let depStrs := t.deps.map fun d =>
    let headWord := t.words.get? d.headIdx |>.map (·.form) |>.getD "?"
    let depWord := t.words.get? d.depIdx |>.map (·.form) |>.getD "?"
    s!"{depWord} ←{d.depType}─ {headWord}"
  s!"Words: {wordStrs}\nDeps:\n" ++ "\n".intercalate depStrs

#eval depTreeToString johnSeesMaryTree
#eval depTreeToString theGirlSleepsTree

-- ============================================================================
-- Debug: Check individual constraints
-- ============================================================================

#eval hasUniqueHeads johnSeesMaryTree    -- should be true
#eval isAcyclic johnSeesMaryTree         -- should be true
#eval isProjective johnSeesMaryTree      -- checking...
#eval checkSubjVerbAgr johnSeesMaryTree  -- should be true
#eval checkDetNounAgr johnSeesMaryTree   -- should be true (no det)
#eval checkVerbSubcat johnSeesMaryTree   -- should be true
