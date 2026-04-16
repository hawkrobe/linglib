import Linglib.Theories.Phonology.Autosegmental.RegisterTier

/-!
# Drubea Prosodic Fragment
@cite{lionnet-2025}

Lexical register specifications for Drubea [ŋaa ⁺ⁿɖuᵐbea] (Glottocode: dumb1241),
an Oceanic language of New Caledonia spoken by approximately 1,000 people in Unya
on the east coast and Paita on the west coast of Grande Terre.

The word-prosodic system consists of an underlying binary contrast between
registerless and downstepped register-bearing units (RBUs), with the mora as the
RBU. There are no tone features.

Data from @cite{lionnet-2025}, building on @cite{rivierre-1973} and
@cite{shintani-paita-1990b}.
-/

namespace Fragments.Drubea.Prosody

open Phonology.Autosegmental.RegisterTier

-- ============================================================================
-- § 1: Stem Prosodic Patterns
-- ============================================================================

/-- The three native stem-level register patterns in Drubea
    (@cite{lionnet-2025}: Table 2, §4.2).

    The contrast is between downstepped and registerless RBUs. Each stem
    contains at most one `l` feature (culminativity). The `l` feature
    associates with the leftmost mora of a syllable (Table 3). -/
inductive StemPattern where
  | registerless    -- ∅: no register feature (e.g., /kuɾe/ 'forest')
  | σ1_downstepped  -- l on first mora (e.g., /⁺kuɾe/ 'end')
  | σ2_downstepped  -- l on second mora (e.g., /ku⁺ɾe/ 'crayfish', /be⁺e/ NEG)
  deriving DecidableEq, Repr

/-- Expand a stem pattern to mora-level register specifications.

    `nMorae` is the total mora count of the stem. The three patterns map to:
    - ∅: `[∅, ∅, …]`
    - l: `[l, ∅, …]`
    - ∅l: `[∅, l, ∅, …]` -/
def StemPattern.toSpecs (p : StemPattern) (nMorae : Nat) : List RegisterSpec :=
  match p with
  | .registerless => List.replicate nMorae none
  | .σ1_downstepped => some .l :: List.replicate (nMorae - 1) none
  | .σ2_downstepped =>
      if nMorae > 1 then none :: some .l :: List.replicate (nMorae - 2) none
      else List.replicate nMorae none

-- ============================================================================
-- § 2: Lexical Data
-- ============================================================================

/-- A Drubea stem with its prosodic specification. -/
structure StemEntry where
  form     : String       -- segmental content (IPA, no register marks)
  gloss    : String
  pattern  : StemPattern
  nMorae   : Nat          -- total mora count
  deriving Repr

/-- Register specification derived from a stem entry. -/
def StemEntry.specs (e : StemEntry) : List RegisterSpec :=
  e.pattern.toSpecs e.nMorae

/-- Monosyllabic CV minimal pairs: segmentally identical stems
    contrasting only in register (@cite{lionnet-2025}: ex. 4).

    Each pair shares the same segmental form; the prosodic contrast is
    purely a matter of the presence vs. absence of a downstep feature. -/
def monoMinimalPairs : List (StemEntry × StemEntry) :=
  [ (⟨"ɨ",   "extremity, tip",  .registerless,   1⟩,
     ⟨"ɨ",   "piece, bit",      .σ1_downstepped, 1⟩)
  , (⟨"ɪ",   "indigenous bamboo", .registerless, 1⟩,
     ⟨"ɪ",   "tree sp.",        .σ1_downstepped, 1⟩)
  , (⟨"be",  "death; to die",   .registerless,   1⟩,
     ⟨"be",  "niaouli tree",    .σ1_downstepped, 1⟩)
  , (⟨"ɖoo", "bag, envelope",   .registerless,   2⟩,  -- CVV = 2 morae
     ⟨"ɖoo", "Cordyline spp.",  .σ1_downstepped, 2⟩)
  , (⟨"cu",  "to wipe",         .registerless,   1⟩,
     ⟨"cu",  "to knock down",   .σ1_downstepped, 1⟩)
  , (⟨"ɲi",  "coconut tree",    .registerless,   1⟩,
     ⟨"ɲi",  "breast",          .σ1_downstepped, 1⟩)
  , (⟨"kee", "husband",         .registerless,   2⟩,  -- CVV = 2 morae
     ⟨"kee", "mulberry tree",   .σ1_downstepped, 2⟩)
  ]

/-- CV⁺V minimal triplets: three-way contrast on bimoraic monosyllables
    (@cite{lionnet-2025}: ex. 45).

    These triplets demonstrate that the RBU is the **mora**, not the
    syllable: within a single bimoraic syllable CVV, the downstep can
    target either the first mora (⁺CVV) or the second (CV⁺V). -/
def cvPlusVTriplets : List (StemEntry × StemEntry × StemEntry) :=
  [ -- /bee/ 'fish' vs /⁺bee/ 'descendance' vs /be⁺e/ NEGATION
    (⟨"bee", "fish",          .registerless,   2⟩,
     ⟨"bee", "descendance",   .σ1_downstepped, 2⟩,
     ⟨"bee", "NEGATION",      .σ2_downstepped, 2⟩)
  , -- /koo/ 'fish sp.' vs /⁺koo/ 'egg' vs /ko⁺o/ 'place, field'
    (⟨"koo", "fish sp.",      .registerless,   2⟩,
     ⟨"koo", "egg",           .σ1_downstepped, 2⟩,
     ⟨"koo", "place, field",  .σ2_downstepped, 2⟩)
  , -- /kãã/ 'parent, friend' vs /⁺kãã/ 'big' vs /kã⁺ã/ PROSPEC
    (⟨"kãã", "parent, friend", .registerless,   2⟩,
     ⟨"kãã", "big",            .σ1_downstepped, 2⟩,
     ⟨"kãã", "PROSPEC",        .σ2_downstepped, 2⟩)
  ]

/-- Disyllabic CV.CV stems illustrating all three register types
    (@cite{lionnet-2025}: ex. 34). -/
def disyllableExamples : List StemEntry :=
  [ ⟨"kuɾe", "forest",   .registerless,   2⟩  -- Type 1: σ σ
  , ⟨"kuɾe", "end",      .σ1_downstepped, 2⟩  -- Type 2: ⁺σ σ
  , ⟨"kuɾe", "crayfish", .σ2_downstepped, 2⟩  -- Type 3: σ ⁺σ
  ]

/-- All stems in the fragment. -/
def allStems : List StemEntry :=
  monoMinimalPairs.flatMap (fun (a, b) => [a, b]) ++
  cvPlusVTriplets.flatMap (fun (a, b, c) => [a, b, c]) ++
  disyllableExamples

-- ============================================================================
-- § 3: Language Properties
-- ============================================================================

/-- Every minimal pair shares the same segmental form — the contrast
    is purely prosodic (register), not segmental. -/
theorem mono_pairs_same_form :
    monoMinimalPairs.all (fun (a, b) => a.form == b.form) = true := by
  native_decide

-- ============================================================================
-- § 4: Utterance-Final Prosody
-- ============================================================================

/-- Boundary register features for utterance-final prosody
    (@cite{lionnet-2025} §4.8).

    - `h%`: utterance-final raising (Drubea)
    - `l%`: utterance-final lowering (Numèè) -/
inductive BoundaryFeature where
  | h_pct  -- h%: final raising (Drubea, Paita dialect)
  | l_pct  -- l%: final lowering (Numèè)
  deriving DecidableEq, Repr

/-- Apply a boundary feature to the final registerless syllable.

    Simplified model: replaces the last registerless RBU with the
    boundary feature. Does not model spreading of h%, the mora-weight
    restriction on l%, or the preceding-context condition (Numèè l%
    only applies after registerless syllables; @cite{lionnet-2025}
    §§3.3–3.4, §4.8). -/
def applyBoundary (specs : List RegisterSpec)
    (boundary : BoundaryFeature) : List RegisterSpec :=
  let feature : RegisterSpec := match boundary with
    | .h_pct => some RegisterFeature.h
    | .l_pct => some RegisterFeature.l
  let rec go : List RegisterSpec → List RegisterSpec
    | [] => []
    | [none] => [feature]
    | x :: rest => x :: go rest
  go specs

-- ============================================================================
-- § 5: Language Properties
-- ============================================================================

/-- Drubea is a register-based tone system (@cite{lionnet-2025} §6.2). -/
def wordProsodicType : WordProsodicType := .registerBased

/-- The register-bearing unit in Drubea is the mora (@cite{lionnet-2025} §4.2). -/
def tbuKind : TBUKind := .mora

/-- Drubea uses utterance-final raising (h%). -/
def drubeaBoundary : BoundaryFeature := .h_pct

/-- Numèè uses utterance-final lowering (l%). -/
def numeeBoundary : BoundaryFeature := .l_pct

end Fragments.Drubea.Prosody
