import Linglib.Theories.Syntax.Minimalism.Agree

/-!
# Spellout: Feature-to-Morphology Mapping
@cite{elkins-torrence-brown-2026} @cite{halle-marantz-1993} @cite{kiparsky-1973}

Bridges the gap between Agree (which values features in narrow syntax) and
PF (which realizes valued feature bundles as phonological exponents). In
Distributed Morphology terms, this is Vocabulary
Insertion: a Vocabulary Item is inserted into a terminal node if its
features are a subset of the node's features.

The key mechanism is the **Elsewhere Condition**: when
multiple Vocabulary Items match, the most specific one (most features)
wins. This captures e.g. Mam =(y)a' appearing specifically when Voice⁰
bears [+oblique], while a less specific entry would yield the default
(zero) exponent.

-/

namespace Minimalism

-- ============================================================================
-- § 1: Vocabulary Entries
-- ============================================================================

/-- A Vocabulary Item: a pairing of a feature set with a phonological
    exponent, optionally restricted to a particular syntactic context
    (the category of the terminal node being spelled out).

    Vocabulary Insertion inserts the most specific matching entry. -/
structure VocabEntry where
  /-- Features this entry matches (must be a subset of the target) -/
  features : FeatureBundle
  /-- The phonological exponent (morpheme string) -/
  exponent : String
  /-- Optional context restriction: the category of the host head.
      `none` = unrestricted (can insert anywhere features match). -/
  context : Option Cat := none
  deriving Repr

/-- Does this entry's feature bundle match a target bundle?
    Matching means every feature in the entry is present (with matching
    type) in the target bundle. This is subset matching — the entry
    need not specify all features of the target. -/
def VocabEntry.matchesFeatures (entry : VocabEntry) (target : FeatureBundle) : Bool :=
  entry.features.all λ ef =>
    target.any λ tf => ef == tf

/-- Does this entry match a target bundle in a given syntactic context? -/
def VocabEntry.matches (entry : VocabEntry) (target : FeatureBundle) (ctx : Option Cat) : Bool :=
  entry.matchesFeatures target &&
  match entry.context with
  | none => true
  | some c => ctx == some c

/-- Specificity of a vocabulary entry: the number of features it specifies.
    Used for Elsewhere ordering — more specific entries take priority. -/
def VocabEntry.specificity (entry : VocabEntry) : Nat :=
  entry.features.length

-- ============================================================================
-- § 2: Vocabulary and Spellout
-- ============================================================================

/-- A vocabulary: an ordered list of vocabulary entries.
    Entries are tried in order; the most specific matching entry wins. -/
abbrev Vocabulary := List VocabEntry

/-- Find the best (most specific) matching vocabulary entry for a target
    feature bundle in a given syntactic context.

    Implements the Elsewhere Condition: among all matching entries,
    the one with the most features wins. Ties are broken by list order. -/
def bestMatch (vocab : Vocabulary) (target : FeatureBundle) (ctx : Option Cat) : Option VocabEntry :=
  let candidates := vocab.filter (·.matches target ctx)
  -- Pick the most specific (most features) among matching entries
  match candidates with
  | [] => none
  | _ => candidates.foldl (λ best entry =>
      match best with
      | none => some entry
      | some b => if entry.specificity > b.specificity then some entry else some b
    ) none

/-- Spell out a feature bundle: find the best matching entry's exponent.
    Returns `none` if no vocabulary entry matches (zero/null exponent). -/
def spellout (vocab : Vocabulary) (target : FeatureBundle) (ctx : Option Cat) : Option String :=
  (bestMatch vocab target ctx).map (·.exponent)

-- ============================================================================
-- § 3: Properties
-- ============================================================================

/-- A vocabulary entry with no features matches any target (Elsewhere entry). -/
theorem empty_features_matches_any (entry : VocabEntry)
    (h : entry.features = []) (target : FeatureBundle) :
    entry.matchesFeatures target = true := by
  simp only [VocabEntry.matchesFeatures, h, List.all_nil]

end Minimalism
