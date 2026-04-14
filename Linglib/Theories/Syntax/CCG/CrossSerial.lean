/-
# CCG Cross-Serial Dependencies

CCG derivations for Dutch cross-serial dependencies using generalized composition.

## Insight

CCG handles cross-serial dependencies via generalized composition:

  Forward Composition (B): X/Y Y/Z → X/Z
  Forward Composition² (B²): X/Y Y/Z/W → X/Z/W
  Forward Composition³ (B³): X/Y Y/Z/W/V → X/Z/W/V

These allow a transitive verb to "inherit" arguments from an
embedded verb, creating the cross-serial pattern.

## The Derivation Pattern

For "Jan Piet zag zwemmen" (Jan saw Piet swim):

  Jan Piet zag zwemmen
  NP NP (S\NP)/VP VP/NP
  ↓T ↓
  S/(S\NP) (S\NP)/VP VP/NP
             ↓T
             VP/(VP\NP)
                        └────>B──────┘
                        (S\NP)/NP
             └──────────>B───────────┘
             S/NP
  └────────────────────>─────────────┘
  S

-/

import Linglib.Theories.Syntax.CCG.Core.Basic

namespace CCG.CrossSerial

open CCG

-- Additional Categories for Dutch

/-- Verb phrase (infinitival) -/
def VP : Cat := S \ NP

/-- Control verb: takes VP, gives VP (e.g., "helpen" = help) -/
def ControlV : Cat := VP / VP

/-- Perception verb: takes VP, gives TV-like (e.g., "zag" = saw) -/
def PercV : Cat := (S \ NP) / VP

/-- Infinitival transitive: VP/NP (e.g., "zwemmen" when taking object) -/
def InfTV : Cat := VP / NP

/-- Infinitival verb needing subject (for cross-serial): (S\NP)/NP

    In Dutch verb-raising constructions, the infinitive's subject appears
    in what looks like an object position. This category allows the embedded
    subject to be picked up via composition.

      zwemmen : (S\NP)/NP — "swim" needing its subject as argument

    This differs from the simple intransitive VP = S\NP. -/
def InfSubj : Cat := (S \ NP) / NP

/-- Verb-raising control verb: ((S\NP)/NP)/(S\NP)

    In verb-raising constructions with 3+ verbs, each intermediate
    restructuring verb (helpen, laten) must provide an extra /NP slot
    for its own raised subject. Standard `ControlV = (S\NP)/(S\NP)`
    only passes through the complement's arguments; `ControlVR` adds
    an /NP so the verb's subject can be picked up via composition.

    This is what enables the full cross-serial derivation:
    - zwemmen  : (S\NP)/NP           — base: needs subject
    - helpen   : ((S\NP)/NP)/(S\NP)  — VR: needs complement + passes NP
    - zag      : (S\NP)/(S\NP)       — matrix: standard perception verb -/
def ControlVR : Cat := ((S \ NP) / NP) / (S \ NP)

-- Generalized Composition Rules

-- Forward Composition (B): X/Y  Y/Z  →  X/Z
-- This is already in CCG.Basic as `forwardComp`.

/--
Forward Composition² (B²): X/Y (Y/Z)/W → (X/Z)/W

Allows "reaching through" one extra argument.
-/
def forwardComp2 : Cat → Cat → Option Cat
  | .rslash x y, .rslash (.rslash y' z) w =>
    if y == y' then some (.rslash (.rslash x z) w) else none
  | _, _ => none

/--
Forward Composition³ (B³): X/Y ((Y/Z)/W)/V → ((X/Z)/W)/V

Allows "reaching through" two extra arguments.
-/
def forwardComp3 : Cat → Cat → Option Cat
  | .rslash x y, .rslash (.rslash (.rslash y' z) w) v =>
    if y == y' then some (.rslash (.rslash (.rslash x z) w) v) else none
  | _, _ => none

-- Extended Derivation Steps

/--
Extended derivation with generalized composition.
-/
inductive ExtDerivStep where
  | lex : LexEntry → ExtDerivStep
  | fapp : ExtDerivStep → ExtDerivStep → ExtDerivStep
  | bapp : ExtDerivStep → ExtDerivStep → ExtDerivStep
  | fcomp : ExtDerivStep → ExtDerivStep → ExtDerivStep   -- B
  | fcomp2 : ExtDerivStep → ExtDerivStep → ExtDerivStep  -- B²
  | fcomp3 : ExtDerivStep → ExtDerivStep → ExtDerivStep  -- B³
  | ftr : ExtDerivStep → Cat → ExtDerivStep              -- Forward type-raise
  deriving Repr

/-- Get category from extended derivation -/
def ExtDerivStep.cat : ExtDerivStep → Option Cat
  | .lex e => some e.cat
  | .fapp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardApp c1 c2
  | .bapp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    backwardApp c1 c2
  | .fcomp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardComp c1 c2
  | .fcomp2 d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardComp2 c1 c2
  | .fcomp3 d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardComp3 c1 c2
  | .ftr d t => do
    let x ← d.cat
    some (forwardTypeRaise x t)

-- Dutch Lexicon

def dutchLexicon : List LexEntry := [
  -- NPs (proper names)
  ⟨"Jan", NP⟩,
  ⟨"Piet", NP⟩,
  ⟨"Marie", NP⟩,
  ⟨"Karel", NP⟩,

  -- Perception verb: "zag" (saw) - takes VP complement
  ⟨"zag", PercV⟩,  -- (S\NP)/(S\NP)

  -- Control verbs: "helpen" (help), "laten" (let)
  ⟨"helpen", ControlV⟩,   -- (S\NP)/(S\NP) — simple (2-verb clusters)
  ⟨"laten", ControlV⟩,    -- (S\NP)/(S\NP) — simple
  ⟨"helpen", ControlVR⟩,  -- ((S\NP)/NP)/(S\NP) — verb-raising (3+ verb clusters)
  ⟨"laten", ControlVR⟩,   -- ((S\NP)/NP)/(S\NP) — verb-raising

  -- Intransitive infinitive: "zwemmen" (swim)
  ⟨"zwemmen", VP⟩,        -- S\NP — simple intransitive
  ⟨"zwemmen", InfSubj⟩    -- (S\NP)/NP — verb-raising (needs raised subject)
]

-- Lexical Entries for Derivations

def jan_lex : ExtDerivStep := .lex ⟨"Jan", NP⟩
def piet_lex : ExtDerivStep := .lex ⟨"Piet", NP⟩
def marie_lex : ExtDerivStep := .lex ⟨"Marie", NP⟩
def karel_lex : ExtDerivStep := .lex ⟨"Karel", NP⟩

def zag_lex : ExtDerivStep := .lex ⟨"zag", PercV⟩         -- (S\NP)/VP
def helpen_lex : ExtDerivStep := .lex ⟨"helpen", ControlV⟩ -- VP/VP
def laten_lex : ExtDerivStep := .lex ⟨"laten", ControlV⟩   -- VP/VP

/-- zwemmen with InfSubj category for verb-raising -/
def zwemmen_vr : ExtDerivStep := .lex ⟨"zwemmen", InfSubj⟩ -- (S\NP)/NP

/-- helpen with ControlVR category for verb-raising (3+ verb clusters) -/
def helpen_vr : ExtDerivStep := .lex ⟨"helpen", ControlVR⟩ -- ((S\NP)/NP)/(S\NP)

/-- laten with ControlVR category for verb-raising -/
def laten_vr : ExtDerivStep := .lex ⟨"laten", ControlVR⟩ -- ((S\NP)/NP)/(S\NP)

-- Derivation: "Jan Piet zag zwemmen" (2 NPs, 2 Vs)

/-
## Cross-Serial Derivation Strategy

For "Jan Piet zag zwemmen" (Jan saw Piet swim):

The key insight is that zwemmen in verb-raising has category (S\NP)/NP,
allowing it to pick up its subject (Piet) as an argument via composition.

  Jan Piet zag zwemmen
  NP NP (S\NP)/(S\NP) (S\NP)/NP
                        └─────────>B─────────────┘
                               (S\NP)/NP
                        └────────────>────────────┘
                                  S\NP
  └───────────────────<───────────────────────────┘
                        S

Step-by-step:
1. zag >B zwemmen: (S\NP)/(S\NP) >B (S\NP)/NP = (S\NP)/NP
   (Forward composition: perception verb + infinitive needing subject)

2. (zag >B zwemmen) + Piet: (S\NP)/NP + NP = S\NP
   (Forward application: give zwemmen its subject)

3. Jan + (zag zwemmen Piet): NP + S\NP = S
   (Backward application: give zag its subject)

The semantic bindings are cross-serial:
- Jan is subject of "zag" (Jan saw...)
- Piet is subject of "zwemmen" (...Piet swim)

The syntactic derivation encodes this: Jan combines with the matrix,
Piet combines with the embedded (via the argument passed through composition).
-/

-- Step 1: zag >B zwemmen via forward composition
-- (S\NP)/(S\NP) >B (S\NP)/NP = (S\NP)/NP
def zag_comp_zwemmen : ExtDerivStep := .fcomp zag_lex zwemmen_vr

-- Step 2: (zag zwemmen) + Piet via forward application
-- (S\NP)/NP + NP = S\NP
def zag_zwemmen_piet : ExtDerivStep := .fapp zag_comp_zwemmen piet_lex

-- Step 3: Jan + (zag zwemmen Piet) via backward application
-- NP + S\NP = S
def jan_zag_zwemmen_piet : ExtDerivStep := .bapp jan_lex zag_zwemmen_piet

-- Derivation: "Jan Piet Marie zag helpen zwemmen" (3 NPs, 3 Vs)

/-!
### Full cross-serial derivation for 3 verbs

For "Jan Piet Marie zag helpen zwemmen" (Jan saw Piet help Marie swim),
the cross-serial bindings are: Jan→zag, Piet→helpen, Marie→zwemmen.

The key is the verb-raising category `ControlVR = ((S\NP)/NP)/(S\NP)`:
helpen in verb-raising passes through an /NP slot for its raised subject (Piet),
in addition to taking its VP complement. This lets B² thread both Piet's and
Marie's argument slots through the verb cluster:

    helpen_vr >B zwemmen_vr : ((S\NP)/NP)/(S\NP) >B (S\NP)/NP = ((S\NP)/NP)/NP
    zag >B² result          : (S\NP)/(S\NP) >B² ((S\NP)/NP)/NP = ((S\NP)/NP)/NP
    result + Marie          : ((S\NP)/NP)/NP + NP = (S\NP)/NP       — Marie→zwemmen
    result + Piet           : (S\NP)/NP + NP = S\NP                 — Piet→helpen
    Jan + result            : NP + S\NP = S                          — Jan→zag

The outermost /NP originates from zwemmen_vr, so Marie binds with zwemmen.
The inner /NP originates from helpen_vr, so Piet binds with helpen.
The \NP is zag's subject slot, so Jan binds with zag.
-/

-- Step 1: helpen_vr >B zwemmen_vr
-- ((S\NP)/NP)/(S\NP) >B (S\NP)/NP = ((S\NP)/NP)/NP
def helpen_comp_zwemmen : ExtDerivStep := .fcomp helpen_vr zwemmen_vr

-- Step 2: zag >B² (helpen_vr >B zwemmen_vr)
-- (S\NP)/(S\NP) >B² ((S\NP)/NP)/NP = ((S\NP)/NP)/NP
def zag_comp2_helpen_zwemmen : ExtDerivStep := .fcomp2 zag_lex helpen_comp_zwemmen

-- Step 3: verb cluster + Marie
-- ((S\NP)/NP)/NP + NP = (S\NP)/NP
def verbs_marie : ExtDerivStep := .fapp zag_comp2_helpen_zwemmen marie_lex

-- Step 4: result + Piet
-- (S\NP)/NP + NP = S\NP
def verbs_marie_piet : ExtDerivStep := .fapp verbs_marie piet_lex

-- Step 5: Jan + result
-- NP + S\NP = S
def jan_piet_marie_zag_helpen_zwemmen_deriv : ExtDerivStep :=
  .bapp jan_lex verbs_marie_piet

-- Verification

/-- The 2-NP cross-serial derivation yields category S. -/
theorem two_np_derives_S : jan_zag_zwemmen_piet.cat = some S := by decide

/-- The 3-NP cross-serial derivation yields category S.
    This uses B (forward composition) and B² (generalized composition)
    to thread all three NP argument slots through the verb cluster. -/
theorem three_np_derives_S :
    jan_piet_marie_zag_helpen_zwemmen_deriv.cat = some S := by decide

/-- Intermediate: the verb cluster composes into ((S\NP)/NP)/NP,
    a 3-place predicate needing Jan (\NP), Piet (/NP), Marie (/NP). -/
theorem verb_cluster_cat :
    zag_comp2_helpen_zwemmen.cat = some (((S \ NP) / NP) / NP) := by decide

-- Generative Capacity: Beyond CFG

/--
The cross-serial language {aⁿbⁿcⁿ | n ≥ 1} is NOT context-free.

CCG can generate this via generalized composition, proving
CCG is mildly context-sensitive.
-/
def crossSerialLanguage (n : Nat) : List String :=
  List.replicate n "a" ++ List.replicate n "b" ++ List.replicate n "c"

end CCG.CrossSerial
