import Linglib.Theories.Syntax.Minimalist.Features

/-!
# Taos Verbal Agreement Fragment
@cite{kontak-kunkel-1987} @cite{watkins-1984} @cite{harrington-1916}
@cite{harbour-2014} @cite{harbour-2016} @cite{middleton-2026}

Taos (Kiowa-Tanoan, Northern Tiwa) verbal agreement prefixes index up
to three arguments — agent (A), goal (G), object (O) — linearized in
that order @cite{watkins-1984}. The prefix decomposes into person and
number morphemes whose exponence and ordering are described by
@cite{middleton-2026} (building on @cite{harbour-2003},
@cite{harbour-2008}, @cite{harbour-2011}, @cite{harbour-2014}).

This fragment provides only the *morpheme inventory* and a
representation of agreement prefixes as `FeatureBundle` lists. The
postsyntactic rules of impoverishment and metathesis that derive the
surface forms — and the theorems about ordering — live in
`Phenomena/Allomorphy/Studies/Middleton2026.lean`.

## Person and Number Features (Harbour)

Number features are `[±atomic]` and `[±minimal]`
(@cite{harbour-2014}); person features are `[±participant]` and
`[±author]` (@cite{harbour-2016}). Their denotations on Taos:

* singular `s` = `[+atomic +minimal]`
* dual    `d` = `[−atomic +minimal]`
* plural  `p` = `[−atomic −minimal]`
* 1       = `[+participant +author]`
* 2       = `[+participant −author]`
* 3       = `[−participant −author]`

(Following @cite{middleton-2026} fn. 4, `[−atomic]` is used in place of
A&N's `[−singular]` for direct compatibility with @cite{harbour-2014}.)
-/

namespace Fragments.Taos.Agreement

open Minimalist

-- ============================================================================
-- § 1: Argument Position
-- ============================================================================

/-- Argument position in a Taos verbal prefix. The linearization is
    `A G O` (agent, goal, object) per @cite{watkins-1984}. -/
inductive ArgRole where
  | agent
  | goal
  | object
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Feature Constructors (Harbour)
-- ============================================================================

/-- A `[±atomic]` feature (@cite{harbour-2014}). -/
abbrev fAtomic (b : Bool) : FeatureVal := .atomic b

/-- A `[±minimal]` feature (@cite{harbour-2014}). -/
abbrev fMinimal (b : Bool) : FeatureVal := .minimal b

/-- A `[±participant]` feature (@cite{harbour-2016}). -/
abbrev fParticipant (b : Bool) : FeatureVal := .participant b

/-- A `[±author]` feature (@cite{harbour-2016}). -/
abbrev fAuthor (b : Bool) : FeatureVal := .author b

-- ============================================================================
-- § 3: Person and Number Bundles
-- ============================================================================

/-- 1st person bundle: `[+participant +author]`. -/
def person1 : List FeatureVal := [fParticipant true, fAuthor true]

/-- 2nd person bundle: `[+participant −author]`. -/
def person2 : List FeatureVal := [fParticipant true, fAuthor false]

/-- 3rd person bundle: `[−participant −author]`. -/
def person3 : List FeatureVal := [fParticipant false, fAuthor false]

/-- Singular: `[+atomic +minimal]`. -/
def numSg : List FeatureVal := [fAtomic true, fMinimal true]

/-- Dual: `[−atomic +minimal]`. -/
def numDu : List FeatureVal := [fAtomic false, fMinimal true]

/-- Plural: `[−atomic −minimal]`. -/
def numPl : List FeatureVal := [fAtomic false, fMinimal false]

/-- An argument bundle = its person features then its number features,
    aligned per the Taos ordering convention `[±part]:[±auth]:[±atom]:[±min]`
    (@cite{middleton-2026} ex. 4 and 5). -/
def argBundle (person number : List FeatureVal) : FeatureBundle :=
  (person ++ number).map .valued

-- ============================================================================
-- § 4: Diagnostic Prefixes (Middleton 2026, Tables 1, 22, 25)
-- ============================================================================

/-- The 1s:3i possessive prefix `tó` — the case in §4.2.5 where a
    paradigmatic rule must precede a syntagmatic one. Goal is 1s,
    object is 3i (3rd inverse). The agent slot is empty in possessive
    prefixes. -/
def prefix_1s3i_possessive_goal : FeatureBundle :=
  argBundle person1 numSg

/-- The 1d:3p prefix `opénôw` — fully-articulated, no impoverishment. -/
def prefix_1d3p_agent : FeatureBundle :=
  argBundle person1 numDu

/-- The 3s agent (transitive) bundle, the target of paradigmatic rule
    (35) `3s → ∅ / [[A _] (O)]`. -/
def prefix_3s_agent : FeatureBundle :=
  argBundle person3 numSg

-- ============================================================================
-- § 5: Surface Exponents (vocabulary items)
-- ============================================================================

/-- The Taos morphemes named in @cite{middleton-2026}. We carry them as
    strings; vocabulary insertion is not modeled in this fragment
    (it would require a full DM exponent-competition model). The
    relevant facts are exponence rules (20–22), (31), (33), (34),
    (38), (42). -/
inductive Morpheme where
  | pé   -- [−author] on goal in dual / inverse contexts (rule 20)
  | n    -- [+minimal] in left-most number bundle (rule 21)
  | o    -- [−atomic] elsewhere; epenthetic for vocalic-nasal repair (rule 22)
  | m    -- [+participant] / 2 (rules 31, 38b)
  | k    -- 2 in singular possessives (rule 38a)
  | mo   -- reflexive object (rule 34)
  | w    -- 3p object (rule 33)
  | i    -- 3i (3rd inverse) reference
  | u    -- 3p subject reference
  | ô    -- epenthetic vowel after `n`
  deriving DecidableEq, Repr

/-- Render a morpheme as its surface form. -/
def Morpheme.surface : Morpheme → String
  | .pé => "pé"
  | .n  => "n"
  | .o  => "o"
  | .m  => "m"
  | .k  => "k"
  | .mo => "mo"
  | .w  => "w"
  | .i  => "i"
  | .u  => "u"
  | .ô  => "ô"

end Fragments.Taos.Agreement
