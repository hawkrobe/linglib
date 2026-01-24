/-
# Surface Grammar

A simple constraint-checking grammar that works directly on word sequences.
No feature structures or derivations - just pattern matching and constraint checking.
Useful as a reference implementation before encoding in HPSG or Minimalism.
-/

import Linglib.Core.Basic
import Linglib.Core.Grammar

namespace Surface

-- ============================================================================
-- Surface Grammar Type
-- ============================================================================

/-- A surface grammar is just a set of constraint checkers -/
structure SurfaceGrammar where
  /-- Check agreement between subject and verb -/
  checkAgreement : Bool := true
  /-- Check subcategorization (argument structure) -/
  checkSubcat : Bool := true
  /-- Check word order -/
  checkWordOrder : Bool := true
  /-- Check case marking -/
  checkCase : Bool := true
  /-- Check determiner-noun agreement -/
  checkDetNounAgr : Bool := true
  /-- Check passive construction -/
  checkPassive : Bool := true

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Find the word in subject position (first DP before verb) -/
def findSubjectPosition (ws : List Word) : Option Word :=
  let verbIdx := ws.findIdx? (·.cat == Cat.V)
  match verbIdx with
  | some vIdx =>
    let beforeVerb := ws.take vIdx
    beforeVerb.find? (·.cat == Cat.D)
  | none => ws.find? (·.cat == Cat.D)  -- no verb, just find first DP

/-- Find the main verb -/
def findMainVerb (ws : List Word) : Option Word :=
  ws.find? (·.cat == Cat.V)

/-- Find the object (accusative DP or noun after verb) -/
def findObject (ws : List Word) : Option Word :=
  let verbIdx := ws.findIdx? (·.cat == Cat.V)
  match verbIdx with
  | some idx =>
    let afterVerb := ws.drop (idx + 1)
    afterVerb.find? fun w => w.cat == Cat.D || w.cat == Cat.N
  | none => none

/-- Count direct objects after the verb (excluding those in by-phrases) -/
def countObjects (ws : List Word) : Nat :=
  let verbIdx := ws.findIdx? (·.cat == Cat.V)
  match verbIdx with
  | some idx =>
    let afterVerb := ws.drop (idx + 1)
    -- Exclude elements in by-phrases (for passive)
    let byIdx := afterVerb.findIdx? fun w => w.cat == Cat.P && w.form == "by"
    let relevantPart := match byIdx with
      | some bIdx => afterVerb.take bIdx
      | none => afterVerb
    relevantPart.filter (fun w => w.cat == Cat.D || w.cat == Cat.N) |>.length
  | none => 0

/-- Check if there's a preposition after the verb -/
def hasPostVerbalPrep (ws : List Word) : Bool :=
  let verbIdx := ws.findIdx? (·.cat == Cat.V)
  match verbIdx with
  | some idx =>
    let afterVerb := ws.drop (idx + 1)
    afterVerb.any (·.cat == Cat.P)
  | none => false

/-- Find Det-N pairs (determiner immediately followed by noun) -/
def findDetNounPairs (ws : List Word) : List (Word × Word) :=
  let rec go : List Word → List (Word × Word)
    | [] => []
    | [_] => []
    | w1 :: w2 :: rest =>
      if w1.cat == Cat.D && w2.cat == Cat.N then
        (w1, w2) :: go (w2 :: rest)
      else
        go (w2 :: rest)
  go ws

/-- Check if a passive auxiliary (was/were) is present -/
def hasPassiveAux (ws : List Word) : Bool :=
  ws.any fun w => w.cat == Cat.Aux && (w.form == "was" || w.form == "were")

/-- Check if verb is a passive participle -/
def hasPassiveParticiple (ws : List Word) : Bool :=
  ws.any fun w => w.cat == Cat.V && w.features.vform == some VForm.pastParticiple

/-- Find the by-phrase agent (if any) -/
def findByAgent (ws : List Word) : Option Word :=
  let byIdx := ws.findIdx? fun w => w.cat == Cat.P && w.form == "by"
  match byIdx with
  | some idx =>
    let afterBy := ws.drop (idx + 1)
    afterBy.find? fun w => w.cat == Cat.D || w.cat == Cat.N
  | none => none

-- ============================================================================
-- Agreement Checking
-- ============================================================================

/-- Check if subject and verb agree in number -/
def agreementOk (ws : List Word) : Bool :=
  match findSubjectPosition ws, findMainVerb ws with
  | some subj, some verb =>
    match subj.features.number, verb.features.number with
    | some sn, some vn => sn == vn
    | _, _ => true  -- if either is underspecified, allow
  | _, _ => true  -- no subject or verb, vacuously true

-- ============================================================================
-- Subcategorization Checking
-- ============================================================================

/-- Count objects before any preposition (for dative/locative frames) -/
def countObjectsBeforePrep (ws : List Word) : Nat :=
  let verbIdx := ws.findIdx? (·.cat == Cat.V)
  match verbIdx with
  | some vIdx =>
    let afterVerb := ws.drop (vIdx + 1)
    let prepIdx := afterVerb.findIdx? (·.cat == Cat.P)
    let beforePrep := match prepIdx with
      | some pIdx => afterVerb.take pIdx
      | none => afterVerb
    beforePrep.filter (fun w => w.cat == Cat.D || w.cat == Cat.N) |>.length
  | none => 0

/-- Check if verb has the right number of arguments -/
def subcatOk (ws : List Word) : Bool :=
  match findMainVerb ws with
  | some verb =>
    let objCount := countObjects ws
    let objBeforePrep := countObjectsBeforePrep ws
    let hasPrep := hasPostVerbalPrep ws
    let isPassive := verb.features.voice == some Voice.passive
    match verb.features.valence with
    | some .intransitive => objCount == 0
    | some .transitive =>
      if isPassive then objCount == 0  -- passive: object promoted to subject
      else objCount == 1               -- active: needs object
    | some .ditransitive =>
      if isPassive then objCount <= 1  -- passive ditransitive can have 0 or 1 remaining obj
      else objCount == 2               -- active: needs two objects
    | some .dative => objBeforePrep == 1 && hasPrep  -- give the book to Mary
    | some .locative => objBeforePrep == 1 && hasPrep  -- put the book on the table
    | some .copular => true  -- copular is complex, allow for now
    | none => true  -- unspecified valence, allow
  | none => true

-- ============================================================================
-- Word Order Checking
-- ============================================================================

/-- Check basic SVO word order for declaratives -/
def wordOrderOk (ws : List Word) (ct : ClauseType) : Bool :=
  match ct with
  | .declarative =>
    let verbIdx := ws.findIdx? (·.cat == Cat.V)
    match verbIdx with
    | some vIdx =>
      -- Find first DP before verb (should be subject)
      let beforeVerb := ws.take vIdx
      let subjIdx := beforeVerb.findIdx? (·.cat == Cat.D)
      -- Check: subject exists before verb, and no DP between subject and verb
      -- that isn't the subject (i.e., object shouldn't be before verb)
      let dpsBetweenSubjAndVerb := match subjIdx with
        | some sIdx => (beforeVerb.drop (sIdx + 1)).filter (·.cat == Cat.D) |>.length
        | none => 0
      subjIdx.isSome && dpsBetweenSubjAndVerb == 0
    | none => true  -- no verb, vacuously ok
  | _ => true  -- other clause types handled elsewhere

-- ============================================================================
-- Case Checking
-- ============================================================================

/-- Check that subject is nominative and object is accusative -/
def caseOk (ws : List Word) : Bool :=
  -- Check subject position has nominative (not accusative)
  let subjOk := match findSubjectPosition ws with
    | some subj =>
      match subj.features.case_ with
      | some Case.acc => false  -- accusative in subject position = bad
      | _ => true  -- nominative or unspecified = ok
    | none => true

  -- Check object position has accusative (not nominative)
  let objOk := match findObject ws with
    | some obj =>
      match obj.features.case_ with
      | some Case.nom => false  -- nominative in object position = bad
      | _ => true  -- accusative or unspecified = ok
    | none => true

  subjOk && objOk

-- ============================================================================
-- Determiner-Noun Agreement
-- ============================================================================

/-- Check if determiner and noun agree in number -/
def detNounAgrOk (ws : List Word) : Bool :=
  let pairs := findDetNounPairs ws
  pairs.all fun (det, noun) =>
    match det.features.number, noun.features.number with
    | some dn, some nn => dn == nn
    | _, _ => true  -- if either is underspecified, allow

-- ============================================================================
-- Passive Construction Checking
-- ============================================================================

/-- Check passive construction: aux + participle, no direct object -/
def passiveOk (ws : List Word) : Bool :=
  let hasAux := hasPassiveAux ws
  let hasPart := hasPassiveParticiple ws
  -- If we have passive aux + participle, should have 0 direct objects
  -- (the by-phrase agent doesn't count as a direct object)
  if hasAux && hasPart then
    -- In passive, the original object is now the subject
    -- There should be no direct object after the verb
    -- But we need to exclude the by-phrase from counting
    let verbIdx := ws.findIdx? (·.cat == Cat.V)
    match verbIdx with
    | some vIdx =>
      let afterVerb := ws.drop (vIdx + 1)
      -- Count DPs/Ns that are NOT in a by-phrase
      let byIdx := afterVerb.findIdx? fun w => w.cat == Cat.P && w.form == "by"
      match byIdx with
      | some bIdx =>
        -- Only count objects before "by"
        let beforeBy := afterVerb.take bIdx
        (beforeBy.filter (fun w => w.cat == Cat.D || w.cat == Cat.N)).length == 0
      | none =>
        -- No by-phrase, just check no objects
        (afterVerb.filter (fun w => w.cat == Cat.D || w.cat == Cat.N)).length == 0
    | none => true
  else
    true  -- not a passive, vacuously ok

-- ============================================================================
-- Main Derivation Check
-- ============================================================================

/-- A "derivation" in surface grammar is just the word list itself -/
abbrev SurfaceDerivation := List Word

/-- Check if a word sequence is well-formed according to surface constraints -/
def checkSentence (g : SurfaceGrammar) (ws : List Word) (ct : ClauseType) : Bool :=
  (if g.checkAgreement then agreementOk ws else true) &&
  (if g.checkSubcat then subcatOk ws else true) &&
  (if g.checkWordOrder then wordOrderOk ws ct else true) &&
  (if g.checkCase then caseOk ws else true) &&
  (if g.checkDetNounAgr then detNounAgrOk ws else true) &&
  (if g.checkPassive then passiveOk ws else true)

-- ============================================================================
-- Grammar Instance
-- ============================================================================

instance : Grammar SurfaceGrammar where
  Derivation := SurfaceDerivation
  realizes d ws _ := d = ws
  derives g ws ct := checkSentence g ws ct = true

/-- Default surface grammar with all checks enabled -/
def defaultGrammar : SurfaceGrammar := {}

end Surface
