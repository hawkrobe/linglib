import Linglib.Syntax.Minimalist.Defs
import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Mathlib.Data.List.MinMax

/-!
# Vocabulary insertion over Minimalist bundles

The Minimalist specialization of Vocabulary Insertion: a `VocabEntry`
pairs a `FeatureBundle` with an exponent and an optional category
restriction, matching by feature-list inclusion, and `spellout` realizes
a valued bundle as the most specific matching exponent. This is the
bridge from Agree, which values features in narrow syntax, to PF —
Mam *=(y)a'* surfaces only when Voice bears [+oblique], while a less
specific entry yields the default exponent.

Selection and realization are the shared exponence engine
(`Exponence.selectBy`, `Exponence.realize`), so the Elsewhere Condition
is inherited, not reproved. Over concrete feature bundles the intensional
subset order is provably the engine's specificity order
(`VocabEntry.le_iff`), with no faithfulness stipulation — contrast the
opaque-predicate engine (`VocabularyInsertion/Basic.lean`), which must
assume it.

## Main definitions

* `VocabEntry`, `Vocabulary` — Vocabulary Items over `FeatureBundle`
  with optional category restriction
* `bestMatch`, `spellout` — Elsewhere selection and realization, as
  instances of the shared engine
* `Agreement.Cell.toPhiFeatures`, `makePersonVocab` — building
  vocabularies from paradigm cells

## Main statements

* `VocabEntry.le_iff` — the engine's specificity order is feature-list
  inclusion plus context compatibility
* `bestMatch_isElsewhereWinner` — inherited from the engine
* `VocabEntry.toVocabItem_le_iff` — the embedding into the
  opaque-predicate engine preserves specificity

## Implementation notes

This is the ergonomic specialization of the parametric
`VI.VocabItem (Ctx Root)` in `VocabularyInsertion/Basic.lean` — same
late insertion and Elsewhere Condition ([halle-marantz-1993]),
concretized to Minimalist bundles so consumers need not instantiate the
parameters; `VocabEntry.toVocabItem` is the faithfulness-preserving
embedding. The namespace is `Minimalist`, since the entry's vocabulary
is the Minimalist feature system's PF interface.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
-/

/-- The φ-feature list of a person-number cell, in the shape
`makePersonVocab` consumes. -/
def Agreement.Cell.toPhiFeatures (c : Agreement.Cell) : List Minimalist.PhiFeature :=
  [.person c.toPerson, .number (if c.isPlural then .plural else .singular)]

namespace Minimalist

/-! ### Vocabulary entries -/

/-- A Vocabulary Item: a feature set paired with a phonological
exponent, optionally restricted to the category of the terminal being
spelled out. Vocabulary Insertion inserts the most specific matching
entry. -/
structure VocabEntry where
  /-- Features this entry matches (must be included in the target). -/
  features : FeatureBundle
  /-- The phonological exponent. -/
  exponent : String
  /-- Optional context restriction: the category of the host head;
  `none` is unrestricted. -/
  context : Option Cat := none
  deriving Repr

/-- The entry's features are included in the target bundle's: subset
matching, so an entry need not specify all features of the target. -/
def VocabEntry.MatchesFeatures (entry : VocabEntry) (target : FeatureBundle) : Prop :=
  FeatureBundle.toGramFeatures entry.features ⊆
    FeatureBundle.toGramFeatures target

instance (entry : VocabEntry) (target : FeatureBundle) :
    Decidable (entry.MatchesFeatures target) :=
  decidable_of_iff
    (∀ f ∈ FeatureBundle.toGramFeatures entry.features,
      f ∈ FeatureBundle.toGramFeatures target)
    Iff.rfl

/-- The entry matches the target bundle in the given syntactic context:
feature inclusion plus the optional context restriction. -/
def VocabEntry.Matches (entry : VocabEntry) (target : FeatureBundle)
    (ctx : Option Cat) : Prop :=
  entry.MatchesFeatures target ∧
  (entry.context = none ∨ entry.context = ctx)

instance (entry : VocabEntry) (target : FeatureBundle) (ctx : Option Cat) :
    Decidable (entry.Matches target ctx) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The number of features an entry specifies — the score for Elsewhere
ordering. -/
def VocabEntry.specificity (entry : VocabEntry) : Nat :=
  (FeatureBundle.toGramFeatures entry.features).length

/-- A vocabulary: the list of entries competing for insertion. -/
abbrev Vocabulary := List VocabEntry

/-! ### The shared exponence core -/

section ExponenceCore

open Morphology Morphology.Exponence

/-- A vocabulary entry exposes the shared exponence interface: contexts
are (target bundle, syntactic context) pairs, applicability is
`Matches`. -/
instance : Morphology.Exponence.Rule VocabEntry (FeatureBundle × Option Cat) String :=
  ⟨VocabEntry.exponent, fun e tc => e.Matches tc.1 tc.2⟩

instance : Preorder VocabEntry := Morphology.Exponence.toPreorder

instance : DecidableRel (Applies : VocabEntry → FeatureBundle × Option Cat → Prop) :=
  fun e tc => inferInstanceAs (Decidable (e.Matches tc.1 tc.2))

/-- The engine's specificity order, unfolded: `e ≤ e'` iff `e'` matches
wherever `e` does. -/
theorem VocabEntry.le_iff_matches {e e' : VocabEntry} :
    e ≤ e' ↔ ∀ ⦃tc : FeatureBundle × Option Cat⦄,
      e.Matches tc.1 tc.2 → e'.Matches tc.1 tc.2 :=
  Iff.rfl

/-- Every entry matches its own feature bundle. -/
theorem VocabEntry.matchesFeatures_self (e : VocabEntry) :
    e.MatchesFeatures e.features :=
  List.Subset.refl _

/-- The engine's specificity order, characterized: `e ≤ e'` iff `e'`'s
features are included in `e`'s and `e'`'s context restriction is
compatible. Over feature bundles the intensional inclusion order IS the
specificity order, with no faithfulness assumption — contrast
`DistributedMorphology.VI.SpecificityFaithful`, which the
opaque-predicate engine must stipulate. -/
theorem VocabEntry.le_iff {e e' : VocabEntry} :
    e ≤ e' ↔
      FeatureBundle.toGramFeatures e'.features ⊆
          FeatureBundle.toGramFeatures e.features
        ∧ (e'.context = none ∨ e'.context = e.context) := by
  constructor
  · intro h
    obtain ⟨hm', hctx'⟩ :=
      VocabEntry.le_iff_matches.mp h (tc := (e.features, e.context))
        ⟨e.matchesFeatures_self, Or.inr rfl⟩
    exact ⟨hm', hctx'⟩
  · rintro ⟨hf, hc⟩
    rw [VocabEntry.le_iff_matches]
    rintro ⟨t, c⟩ ⟨hm, hctx⟩
    refine ⟨List.Subset.trans hf hm, ?_⟩
    rcases hc with h | h
    · exact Or.inl h
    · rcases hctx with h2 | h2
      · exact Or.inl (h.trans h2)
      · exact Or.inr (h.trans h2)

/-! ### Selection and realization -/

/-- The most specific matching entry: the shared engine's `selectBy` on
the feature-count score. -/
def bestMatch (vocab : Vocabulary) (target : FeatureBundle) (ctx : Option Cat) :
    Option VocabEntry :=
  selectBy VocabEntry.specificity vocab (target, ctx)

/-- Spell out a feature bundle as the best matching entry's exponent —
the shared engine's `realize`. `none` is the zero/null exponent. -/
def spellout (vocab : Vocabulary) (target : FeatureBundle) (ctx : Option Cat) :
    Option String :=
  Morphology.Exponence.realize VocabEntry.specificity vocab (target, ctx)

/-- With the feature-count score strictly antitone on the applicable
entries, `bestMatch` returns an Elsewhere winner — inherited from the
engine (`selectBy_isElsewhereWinner`). -/
theorem bestMatch_isElsewhereWinner {vocab : Vocabulary}
    {target : FeatureBundle} {ctx : Option Cat} {e : VocabEntry}
    (hf : StrictAntiOn VocabEntry.specificity
      {r | r ∈ applicable vocab (target, ctx)})
    (h : bestMatch vocab target ctx = some e) :
    IsElsewhereWinner vocab (target, ctx) e :=
  selectBy_isElsewhereWinner hf h

/-! ### Bridge to the opaque-predicate engine -/

/-- Embed a vocabulary entry into the opaque-predicate engine
(`DistributedMorphology.VI.VocabItem`): the context check is feature
matching, the root check is the category restriction, and the
stipulated rank is the feature count. -/
def VocabEntry.toVocabItem (e : VocabEntry) :
    DistributedMorphology.VI.VocabItem FeatureBundle (Option Cat) where
  exponent := e.exponent
  contextMatch := λ t => decide (e.MatchesFeatures t)
  rootMatch := some (λ c => decide (e.context = none ∨ e.context = c))
  specificity := (FeatureBundle.toGramFeatures e.features).length

/-- The embedding tracks applicability: the opaque engine's `matches`
agrees with `Matches`. -/
theorem VocabEntry.toVocabItem_matches (e : VocabEntry)
    (t : FeatureBundle) (c : Option Cat) :
    e.toVocabItem.matches t c = true ↔ e.Matches t c := by
  simp [DistributedMorphology.VI.VocabItem.matches, VocabEntry.toVocabItem,
    VocabEntry.Matches]

/-- The two engines' interfaces agree: the embedded item applies exactly
where the entry does. -/
theorem VocabEntry.toVocabItem_applies (e : VocabEntry)
    (tc : FeatureBundle × Option Cat) :
    Morphology.Exponence.Applies e.toVocabItem tc ↔
      Morphology.Exponence.Applies e tc :=
  e.toVocabItem_matches tc.1 tc.2

/-- Specificity transfers along the embedding — the cross-engine
translation is faithful to the shared core's order. -/
theorem VocabEntry.toVocabItem_le_iff {e f : VocabEntry} :
    e.toVocabItem ≤ f.toVocabItem ↔ e ≤ f := by
  constructor <;> intro h c hc
  · exact (f.toVocabItem_applies c).mp (h ((e.toVocabItem_applies c).mpr hc))
  · exact (f.toVocabItem_applies c).mpr (h ((e.toVocabItem_applies c).mp hc))

end ExponenceCore

/-! ### Vocabulary builders -/

/-- Build a Vocabulary from a paradigm cell type: for each cell, one
entry with the cell's φ-features as valued features, its exponent, and
the given context. Elsewhere entries (no features) are appended by the
caller — this covers only the regular cells. -/
def makePersonVocab {PN : Type*} (cells : List PN) (toPhi : PN → List PhiFeature)
    (exponentOf : PN → String) (ctx : Option Cat := none) : Vocabulary :=
  cells.map λ pn =>
    { features := .ofGramFeatures ((toPhi pn).map (λ p => .valued (.phi p)))
    , exponent := exponentOf pn
    , context := ctx }

end Minimalist
