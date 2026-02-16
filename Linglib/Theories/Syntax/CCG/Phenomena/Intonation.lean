/-
# CCG Intonation and Information Structure

Steedman's (2000) theory of how prosodic structure aligns with CCG derivations.

## Insight

CCG's "spurious ambiguity" is not spurious: different derivations correspond to
different Information Structures, disambiguated by intonation in speech.

The sentence "Anna married Manny" has multiple CCG derivations:
1. [Anna] [married Manny]  — traditional subject-predicate
2. [Anna married] [Manny]  — via composition: theme "Anna married _", rheme "Manny"

Intonation selects among these:
- "ANNA married" (L+H* LH%) "MANNY" (H* LL%) → theme/rheme split at "married"

## Prosodic Marking

- Pitch accents (H*, L+H*): Mark focus/contrast at word level
- Boundary tones (L, LH%, LL%): Mark prosodic phrase edges
- Information feature (theta/rho): Projects theme/rheme through derivation

## Reference

Steedman (2000). The Syntactic Process, Chapter 5: Structure and Intonation.
-/

import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Core.InformationStructure
import Linglib.Core.Prosody
import Linglib.Phenomena.Focus.Basic

namespace CCG.Intonation

open CCG
open Core.InformationStructure
open Core.Prosody

-- Information Feature

/--
The INFORMATION feature on CCG categories.

Categories are marked as:
- θ (theta): Part of the theme
- ρ (rho): Part of the rheme
- unmarked: Unspecified (can unify with either)
- φ (phi): Phrasal (after boundary tone applies)
-/
inductive InfoFeature where
  | θ         -- Theme
  | ρ         -- Rheme
  | unmarked  -- Unspecified
  | φ         -- Phrasal (boundary applied)
  deriving Repr, DecidableEq, Inhabited

/-- Can two info features unify? -/
def InfoFeature.unifies : InfoFeature → InfoFeature → Bool
  | .unmarked, _ => true
  | _, .unmarked => true
  | .θ, .θ => true
  | .ρ, .ρ => true
  | .φ, .φ => true
  | _, _ => false

/-- Unify two info features -/
def InfoFeature.unify : InfoFeature → InfoFeature → Option InfoFeature
  | .unmarked, f => some f
  | f, .unmarked => some f
  | .θ, .θ => some .θ
  | .ρ, .ρ => some .ρ
  | .φ, .φ => some .φ
  | _, _ => none

-- Prosodic CCG Categories

/--
A CCG category with prosodic annotation.

The INFORMATION feature projects through the category:
- (Sθ\NPθ)/NPθ: All arguments and result share the same info value
-/
structure ProsodicCat where
  cat : Cat
  info : InfoFeature
  deriving Repr, DecidableEq

/-- Notation helpers -/
def ProsodicCat.theme (c : Cat) : ProsodicCat := ⟨c, .θ⟩
def ProsodicCat.rheme (c : Cat) : ProsodicCat := ⟨c, .ρ⟩
def ProsodicCat.plain (c : Cat) : ProsodicCat := ⟨c, .unmarked⟩
def ProsodicCat.phrasal (c : Cat) : ProsodicCat := ⟨c, .φ⟩

-- Prosodic Lexical Entries

/--
A prosodic lexical entry: word + pitch accent → prosodic category.

The pitch accent determines the INFORMATION feature:
- H*    → ρ (rheme)
- L+H*  → θ (theme)
- null  → unmarked
-/
structure ProsodicLexEntry where
  form : String
  cat : Cat
  accent : PitchAccent
  deriving Repr

/-- Get the prosodic category from a lexical entry -/
def ProsodicLexEntry.prosodicCat (e : ProsodicLexEntry) : ProsodicCat :=
  let info := match e.accent with
    | .H_star => .ρ
    | .L_plus_H_star => .θ
    | .null => .unmarked
  ⟨e.cat, info⟩

-- Intonational Tunes

/--
An intonational tune: pitch accent + boundary.

The two main tunes in English:
- L+H* LH%: Theme tune (fall-rise)
- H* LL%: Rheme tune (fall)
-/
structure Tune where
  accent : PitchAccent
  boundary : BoundaryTone
  deriving Repr, DecidableEq

/-- The canonical theme tune -/
def themeTune : Tune := ⟨.L_plus_H_star, .LH_pct⟩

/-- The canonical rheme tune -/
def rhemeTune : Tune := ⟨.H_star, .LL_pct⟩

/-- Is this a theme tune? -/
def Tune.isTheme (t : Tune) : Bool :=
  t.accent == .L_plus_H_star && t.boundary == .LH_pct

/-- Is this a rheme tune? -/
def Tune.isRheme (t : Tune) : Bool :=
  t.accent == .H_star && t.boundary == .LL_pct

-- Prosodic Combination Rules

/--
Prosodic forward application: X/Y + Y → X
Only succeeds if INFORMATION features unify.
-/
def prosodicForwardApp : ProsodicCat → ProsodicCat → Option ProsodicCat
  | ⟨.rslash x y, i1⟩, ⟨c2, i2⟩ =>
    if y == c2 then
      match i1.unify i2 with
      | some i => some ⟨x, i⟩
      | none => none
    else none
  | _, _ => none

/--
Prosodic backward application: Y + X\Y → X
Only succeeds if INFORMATION features unify.
-/
def prosodicBackwardApp : ProsodicCat → ProsodicCat → Option ProsodicCat
  | ⟨c1, i1⟩, ⟨.lslash x y, i2⟩ =>
    if y == c1 then
      match i1.unify i2 with
      | some i => some ⟨x, i⟩
      | none => none
    else none
  | _, _ => none

/--
Prosodic forward composition: X/Y + Y/Z → X/Z
INFORMATION features must unify and project to result.
-/
def prosodicForwardComp : ProsodicCat → ProsodicCat → Option ProsodicCat
  | ⟨.rslash x y, i1⟩, ⟨.rslash y' z, i2⟩ =>
    if y == y' then
      match i1.unify i2 with
      | some i => some ⟨.rslash x z, i⟩
      | none => none
    else none
  | _, _ => none

/--
Apply a boundary tone to a prosodic category.
Converts θ/ρ marking to φ (phrasal).
-/
def applyBoundary : ProsodicCat → BoundaryTone → ProsodicCat
  | ⟨cat, info⟩, _ =>
    match info with
    | .θ | .ρ | .unmarked => ⟨cat, .φ⟩
    | .φ => ⟨cat, .φ⟩  -- already phrasal

-- Prosodic Derivations

/--
A prosodic derivation step.
Extends CCG derivations with prosodic information.
-/
inductive ProsodicDeriv where
  | lex : ProsodicLexEntry → ProsodicDeriv
  | fapp : ProsodicDeriv → ProsodicDeriv → ProsodicDeriv
  | bapp : ProsodicDeriv → ProsodicDeriv → ProsodicDeriv
  | fcomp : ProsodicDeriv → ProsodicDeriv → ProsodicDeriv
  | bcomp : ProsodicDeriv → ProsodicDeriv → ProsodicDeriv
  | ftr : ProsodicDeriv → Cat → ProsodicDeriv  -- forward type-raise
  | boundary : ProsodicDeriv → BoundaryTone → ProsodicDeriv
  deriving Repr

/-- Get the prosodic category of a derivation -/
def ProsodicDeriv.prosodicCat : ProsodicDeriv → Option ProsodicCat
  | .lex e => some e.prosodicCat
  | .fapp d1 d2 => do
    let c1 ← d1.prosodicCat
    let c2 ← d2.prosodicCat
    prosodicForwardApp c1 c2
  | .bapp d1 d2 => do
    let c1 ← d1.prosodicCat
    let c2 ← d2.prosodicCat
    prosodicBackwardApp c1 c2
  | .fcomp d1 d2 => do
    let c1 ← d1.prosodicCat
    let c2 ← d2.prosodicCat
    prosodicForwardComp c1 c2
  | .bcomp _ _ => none  -- TODO
  | .ftr d t => do
    let ⟨x, i⟩ ← d.prosodicCat
    some ⟨forwardTypeRaise x t, i⟩
  | .boundary d b => do
    let c ← d.prosodicCat
    some (applyBoundary c b)

-- Information Structure Extraction

/--
A prosodic phrase: a derivation with a boundary tone applied.
-/
structure ProsodicPhrase where
  deriv : ProsodicDeriv
  tune : Tune
  deriving Repr

/--
Extract Information Structure from a sequence of prosodic phrases.

The phrase with theme tune (L+H* LH%) becomes the theme.
The phrase with rheme tune (H* LL%) becomes the rheme.
-/
def extractInfoStructure (phrases : List ProsodicPhrase)
    : Option (InfoStructure (ProsodicDeriv)) :=
  let themes := phrases.filter (·.tune.isTheme)
  let rhemes := phrases.filter (·.tune.isRheme)
  match themes, rhemes with
  | [t], [r] => some {
      theme := ⟨t.deriv, true⟩
      rheme := ⟨r.deriv, true⟩
    }
  | [], [r] => some {
      theme := ⟨r.deriv, false⟩  -- unmarked theme
      rheme := ⟨r.deriv, true⟩
    }
  | _, _ => none  -- ambiguous or ill-formed

-- Instance: CCG Intonation provides Information Structure

/--
Prosodic CCG derivations have Information Structure.
-/
instance : HasInfoStructure (List ProsodicPhrase) ProsodicDeriv where
  infoStructure phrases :=
    match extractInfoStructure phrases with
    | some info => info
    | none => {  -- default: everything is rheme
        theme := ⟨.lex ⟨"", S, .null⟩, false⟩
        rheme := ⟨.lex ⟨"", S, .null⟩, false⟩
      }

-- Example: "FRED ate the BEANS"

/-
Context: "What did Fred eat?"
Answer: "(FRED ate) (the BEANS)"
         L+H* LH%   H*  LL%
         Theme      Rheme

Derivation:
1. FRED: NP with L+H* → NPθ
2. Type-raise: NPθ → Sθ/(Sθ\NPθ)
3. ate: (S\NP)/NP with null → unifies to θ
4. Compose: Sθ/(Sθ\NPθ) + (Sθ\NPθ)/NPθ → Sθ/NPθ
5. Boundary LH%: Sθ/NPθ → Sφ/NPφ (theme phrase)

6. the BEANS: NP with H* → NPρ
7. Boundary LL%: NPρ → NPφ (rheme phrase)

8. Apply: Sφ/NPφ + NPφ → Sφ
-/

-- Lexical entries
def fred_L : ProsodicLexEntry := ⟨"Fred", NP, .L_plus_H_star⟩
def ate_null : ProsodicLexEntry := ⟨"ate", TV, .null⟩
def the_null : ProsodicLexEntry := ⟨"the", Det, .null⟩
def beans_H : ProsodicLexEntry := ⟨"beans", N, .H_star⟩

-- Derivation of theme "FRED ate"
def fred_tr : ProsodicDeriv := .ftr (.lex fred_L) S
def fred_ate : ProsodicDeriv := .fcomp fred_tr (.lex ate_null)
def fred_ate_phrase : ProsodicDeriv := .boundary fred_ate .LH_pct

-- Derivation of rheme "the BEANS"
def the_beans : ProsodicDeriv := .fapp (.lex the_null) (.lex beans_H)
def the_beans_phrase : ProsodicDeriv := .boundary the_beans .LL_pct

-- Check categories
#eval fred_tr.prosodicCat        -- Sθ/(Sθ\NPθ)
#eval fred_ate.prosodicCat       -- Sθ/NPθ (theme: "Fred ate _")
#eval fred_ate_phrase.prosodicCat -- Sφ/NPφ

-- Example: "(ANNA married) (MANNY)" from Steedman Ch. 5

def anna_L : ProsodicLexEntry := ⟨"Anna", NP, .L_plus_H_star⟩
def married_null : ProsodicLexEntry := ⟨"married", TV, .null⟩
def manny_H : ProsodicLexEntry := ⟨"Manny", NP, .H_star⟩

-- Theme: "ANNA married" (L+H* LH%)
def anna_tr : ProsodicDeriv := .ftr (.lex anna_L) S
def anna_married : ProsodicDeriv := .fcomp anna_tr (.lex married_null)
def anna_married_theme : ProsodicPhrase := ⟨.boundary anna_married .LH_pct, themeTune⟩

-- Rheme: "MANNY" (H* LL%)
def manny_rheme : ProsodicPhrase := ⟨.boundary (.lex manny_H) .LL_pct, rhemeTune⟩

-- Full utterance
def anna_married_manny : List ProsodicPhrase := [anna_married_theme, manny_rheme]

-- Extract Information Structure
-- #eval extractInfoStructure anna_married_manny
-- (uncomment after adding Repr instance to InfoStructure)
-- Theme: "Anna married _" (λx. married x anna)
-- Rheme: "Manny"

-- Constraint: Prosody must align with CCG constituency

/-
Prosodic boundaries can only occur at CCG constituent boundaries
(Steedman 2000). This explains Selkirk's "Sense Unit Condition" as a theorem.

Allowed:
  (FRED ate) (the BEANS)   -- "Fred ate" is a CCG constituent (S/NP)

Disallowed:
  *(FRED ate the) (BEANS)  -- "Fred ate the" is not a constituent
  *(The beans that FRED) (ate were DELICIOUS)  -- violates island
-/

/-- Check if a prosodic derivation is well-formed (simplified) -/
def ProsodicDeriv.wellFormed : ProsodicDeriv → Bool
  | .lex _ => true
  | .fapp d1 d2 => d1.wellFormed && d2.wellFormed && d1.prosodicCat.isSome
  | .bapp d1 d2 => d1.wellFormed && d2.wellFormed
  | .fcomp d1 d2 => d1.wellFormed && d2.wellFormed && d1.prosodicCat.isSome
  | .bcomp d1 d2 => d1.wellFormed && d2.wellFormed
  | .ftr d _ => d.wellFormed
  | .boundary d _ => d.wellFormed && d.prosodicCat.isSome

end CCG.Intonation
