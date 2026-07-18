import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Morphology.Exponence.Rule
import Linglib.Morphology.DM.VocabularyInsertion
import Mathlib.Data.List.MinMax

/-!
# VocabSimple: Minimalist-specific Vocabulary Insertion
[halle-marantz-1993] [kiparsky-1973] [elkins-torrence-brown-2026]

A concrete Minimalist specialization of Vocabulary Insertion.
`VocabEntry` carries `features : FeatureBundle` (the Minimalist
global) + `exponent : String` + optional context restriction
`Option Cat`. Sits alongside the more general parametric type
`Morphology.DM.VI.VocabItem (Ctx Root : Type)` in
`VocabularyInsertion.lean`: same Distributed Morphology mechanism
(Halle-Marantz late insertion + Elsewhere Condition), specialized to
Minimalist's feature-bundle ergonomics so downstream consumers don't
have to instantiate the parametric Ctx/Root each call.

Bridges Agree (which values features in narrow syntax) and PF (which
realizes the valued bundles as phonological exponents). When multiple
Vocabulary Items match, the most specific one (most features) wins —
the **Elsewhere Condition**. Captures e.g. Mam =(y)a' surfacing only
when Voice⁰ bears [+oblique], while a less specific entry yields the
default (zero) exponent.

The `makePersonVocab` builder at the end of this file constructs
Vocabularies from per-cell paradigm functions; used by Mayan, Romance,
and Bantu agreement studies (Scott2023, Preminger2014,
ElkinsTorrenceBrown2026).
-/

namespace Minimalist

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
def VocabEntry.MatchesFeatures (entry : VocabEntry) (target : FeatureBundle) : Prop :=
  (FeatureBundle.toGramFeatures entry.features).all
    (λ ef => (FeatureBundle.toGramFeatures target).any (λ tf => ef == tf)) = true

instance (entry : VocabEntry) (target : FeatureBundle) :
    Decidable (entry.MatchesFeatures target) :=
  inferInstanceAs (Decidable (_ = true))

/-- Does this entry match a target bundle in a given syntactic context?
    Combines feature-bundle subset matching with the optional context
    restriction. -/
def VocabEntry.Matches (entry : VocabEntry) (target : FeatureBundle)
    (ctx : Option Cat) : Prop :=
  entry.MatchesFeatures target ∧
  (entry.context = none ∨ entry.context = ctx)

instance (entry : VocabEntry) (target : FeatureBundle) (ctx : Option Cat) :
    Decidable (entry.Matches target ctx) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Specificity of a vocabulary entry: the number of features it specifies.
    Used for Elsewhere ordering — more specific entries take priority. -/
def VocabEntry.specificity (entry : VocabEntry) : Nat :=
  (FeatureBundle.toGramFeatures entry.features).length

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
def bestMatch (vocab : Vocabulary) (target : FeatureBundle) (ctx : Option Cat) :
    Option VocabEntry :=
  (vocab.filter (λ e => decide (e.Matches target ctx))).argmax VocabEntry.specificity

/-- Spell out a feature bundle: find the best matching entry's exponent.
    Returns `none` if no vocabulary entry matches (zero/null exponent). -/
def spellout (vocab : Vocabulary) (target : FeatureBundle) (ctx : Option Cat) : Option String :=
  (bestMatch vocab target ctx).map (·.exponent)

-- ============================================================================
-- § 3: Vocabulary Builders
-- ============================================================================

/-- The φ-feature list of a person-number cell, in the shape `makePersonVocab`
    consumes. Shared by the Mayan agreement studies (Scott2023, Preminger2014). -/
def _root_.Agreement.Cell.toPhiFeatures (c : Agreement.Cell) : List PhiFeature :=
  [.person c.toPerson, .number (if c.isPlural then .plural else .singular)]

/-- Build a Vocabulary from a paradigm cell type. For each cell `pn`, emits
    one VocabEntry whose features are `toPhi pn` lifted into valued
    `FeatureValue`s, whose exponent is `exponentOf pn`, and whose context
    is `ctx`. Used to deduplicate the per-cell paradigm-to-vocabulary
    construction shared across study files (e.g., Kaqchikel Set A on
    Voice/v, Kaqchikel Set B on Infl/T). Elsewhere entries (no features)
    are appended separately by the caller — this helper covers only the
    regular cells. The `ctx` argument matches `VocabEntry.context`'s
    `Option Cat` shape; default `none` admits unrestricted contexts. -/
def makePersonVocab {PN : Type*} (cells : List PN) (toPhi : PN → List PhiFeature)
    (exponentOf : PN → String) (ctx : Option Cat := none) : Vocabulary :=
  cells.map λ pn =>
    { features := .ofGramFeatures ((toPhi pn).map (λ p => .valued (.phi p)))
    , exponent := exponentOf pn
    , context := ctx }

-- ============================================================================
-- § 4: The shared exponence core
-- ============================================================================

section ExponenceCore

open Morphology.Exponence

/-- View a vocabulary entry as a rule of the shared exponence core
(`Morphology.Exponence.Rule`): contexts are (target bundle, syntactic
context) pairs, applicability is `Matches`. -/
def VocabEntry.toRule (e : VocabEntry) : Rule (FeatureBundle × Option Cat) String :=
  ⟨e.exponent, λ tc => e.Matches tc.1 tc.2⟩

/-- Syntactic refinement: a feature-superset entry (with compatible
context restriction) is at least as specific in the derived order of
the shared core. -/
theorem VocabEntry.toRule_moreSpecific_of_superset {e e' : VocabEntry}
    (hf : ∀ f ∈ FeatureBundle.toGramFeatures e'.features,
      f ∈ FeatureBundle.toGramFeatures e.features)
    (hc : e'.context = none ∨ e'.context = e.context) :
    e.toRule.MoreSpecific e'.toRule := by
  rintro ⟨t, c⟩ ⟨hm, hctx⟩
  refine ⟨?_, ?_⟩
  · rw [VocabEntry.MatchesFeatures, List.all_eq_true] at hm ⊢
    exact λ ef hef => hm _ (hf ef hef)
  · rcases hc with h | h
    · exact Or.inl h
    · rcases hctx with h2 | h2
      · exact Or.inl (h.trans h2)
      · exact Or.inr (h.trans h2)

/-- Every entry matches its own feature bundle. -/
theorem VocabEntry.matchesFeatures_self (e : VocabEntry) :
    e.MatchesFeatures e.features := by
  rw [VocabEntry.MatchesFeatures, List.all_eq_true]
  intro ef hef
  exact List.any_eq_true.mpr ⟨ef, hef, beq_self_eq_true ef⟩

/-- Derived specificity, characterized: `e` is at least as specific as
`e'` in the shared core iff `e'`'s features are a subset of `e`'s and
`e'`'s context restriction is compatible. Upgrades
`toRule_moreSpecific_of_superset` to an iff — over feature bundles the
intensional superset order IS the derived order, with no faithfulness
assumption (contrast `Morphology.DM.VI.SpecificityFaithful`, which the
opaque-predicate engine must stipulate). -/
theorem VocabEntry.toRule_moreSpecific_iff {e e' : VocabEntry} :
    e.toRule.MoreSpecific e'.toRule ↔
      (∀ f ∈ FeatureBundle.toGramFeatures e'.features,
        f ∈ FeatureBundle.toGramFeatures e.features) ∧
      (e'.context = none ∨ e'.context = e.context) := by
  constructor
  · intro h
    obtain ⟨hm', hctx'⟩ :=
      h (c := (e.features, e.context)) ⟨e.matchesFeatures_self, Or.inr rfl⟩
    refine ⟨?_, hctx'⟩
    rw [VocabEntry.MatchesFeatures, List.all_eq_true] at hm'
    intro f hf
    obtain ⟨tf, htf, hbeq⟩ := List.any_eq_true.mp (hm' f hf)
    exact (beq_iff_eq.mp hbeq) ▸ htf
  · exact λ ⟨hf, hc⟩ => toRule_moreSpecific_of_superset hf hc

/-! #### Bridge to the opaque-predicate engine -/

/-- Embed a vocabulary entry into the opaque-predicate engine
(`Morphology.DM.VI.VocabItem`): the context check is feature matching,
the root check is the category restriction, and the stipulated rank is
the feature count. -/
def VocabEntry.toVocabItem (e : VocabEntry) :
    Morphology.DM.VI.VocabItem FeatureBundle (Option Cat) where
  exponent := e.exponent
  contextMatch := λ t => decide (e.MatchesFeatures t)
  rootMatch := some (λ c => decide (e.context = none ∨ e.context = c))
  specificity := (FeatureBundle.toGramFeatures e.features).length

/-- The embedding tracks applicability: the opaque engine's `matches`
agrees with `Matches`. -/
theorem VocabEntry.toVocabItem_matches (e : VocabEntry)
    (t : FeatureBundle) (c : Option Cat) :
    e.toVocabItem.matches t c = true ↔ e.Matches t c := by
  simp [Morphology.DM.VI.VocabItem.matches, VocabEntry.toVocabItem,
    VocabEntry.Matches]

/-- The two engines' shared-core views agree: the embedded item's rule
applies exactly where the entry's rule does. -/
theorem VocabEntry.toVocabItem_toRule_applies (e : VocabEntry)
    (tc : FeatureBundle × Option Cat) :
    e.toVocabItem.toRule.Applies tc ↔ e.toRule.Applies tc :=
  e.toVocabItem_matches tc.1 tc.2

/-- Derived specificity transfers along the embedding — the cross-engine
translation is faithful to the shared core's order. -/
theorem VocabEntry.toVocabItem_toRule_moreSpecific {e f : VocabEntry} :
    e.toVocabItem.toRule.MoreSpecific f.toVocabItem.toRule ↔
      e.toRule.MoreSpecific f.toRule := by
  constructor <;> intro h c hc
  · exact (f.toVocabItem_toRule_applies c).mp
      (h ((e.toVocabItem_toRule_applies c).mpr hc))
  · exact (f.toVocabItem_toRule_applies c).mpr
      (h ((e.toVocabItem_toRule_applies c).mp hc))

/-- Under a specificity stipulation faithful to the derived order on
the matching entries, `bestMatch` returns an Elsewhere winner of the
shared core. The feature-count `specificity` is one such stipulation
whenever distinct matching entries are feature-comparable. -/
theorem bestMatch_isElsewhereWinner {vocab : Vocabulary} {target : FeatureBundle}
    {ctx : Option Cat} {e : VocabEntry}
    (h : bestMatch vocab target ctx = some e)
    (hfaith : ∀ a ∈ vocab, ∀ b ∈ vocab, a.Matches target ctx →
      b.Matches target ctx → a.toRule.MoreSpecific b.toRule →
      ¬ b.toRule.MoreSpecific a.toRule → b.specificity < a.specificity) :
    IsElsewhereWinner (vocab.map VocabEntry.toRule) (target, ctx) e.toRule := by
  have hmem := List.argmax_mem h
  rw [List.mem_filter] at hmem
  obtain ⟨hev, hem⟩ := hmem
  have hematch : e.Matches target ctx := of_decide_eq_true hem
  refine ⟨List.mem_map_of_mem hev, hematch, ?_⟩
  rintro s hs happ hspec
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
  by_contra hns
  have hlt : e.specificity < b.specificity :=
    hfaith b hb e hev happ hematch hspec hns
  have hble : ¬ e.specificity < b.specificity :=
    List.not_lt_of_mem_argmax
      (List.mem_filter.mpr
        ⟨hb, decide_eq_true (show b.Matches target ctx from happ)⟩) h
  exact hble hlt

end ExponenceCore

end Minimalist
