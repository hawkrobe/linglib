import Linglib.Syntax.Agreement.Controller

/-!
# Bybee's relevance hierarchy
[bybee-1985]

Morpheme functional categories ordered by semantic relevance to the
verb stem, and the stem-outward order this ranking induces.

## Main definitions

- `MorphCategory`: the functional categories.
- `MorphCategory.peripherality`: a numeric rank realizing the order.
- `MorphCategory.RelevanceLE`/`RelevanceLT`: the induced order.
- `RespectsRelevanceHierarchy`: a slot list sorted stem-outward.
-/

namespace Morphology

/-- Morpheme functional category.

Categories are ordered by semantic relevance to the verb stem:
more relevant categories appear closer to the stem in suffixal
morphology. -/
inductive MorphCategory where
  | stem
  | derivation    -- derives verbs from other categories (e.g., *suru*)
  | valence       -- causative, applicative, reciprocal
  | voice         -- passive, potential
  | aspect        -- perfective, imperfective
  | tense         -- past, future, present
  | mood          -- desiderative, subjunctive, imperative
  | negation      -- negation markers
  /-- Agreement morphology, parameterized by the grammatical role of
      the controlling NP (`Agreement.Controller`). The role
      distinction (subj vs obj vs poss vs ...) is what allows
      [anderson-2006]'s split/doubled AVC typology to be Lean-checkable;
      [bybee-1985]'s `personAgr / personAgrObj / genderAgr` source
      distinctions also round-trip cleanly. -/
  | agreement (controller : Agreement.Controller)
  | nonfinite     -- nonfinite markers, interrogative/relative
  | number        -- number marking on nouns (not verb agreement)
  | degree        -- comparative/superlative on adjectives
  deriving Repr, DecidableEq

/-- Peripherality: numerical embedding of Bybee's relevance hierarchy
where **higher = farther from stem = less semantically relevant**.

In Bybee's text, "high relevance" means *more* semantically
integrated with the stem ([bybee-1985] Ch 2 §2.1 p. 13). The
substrate uses the *opposite* numerical direction: stem = 0 (most
relevant), agreement = 8 (least relevant), so that Nat ordering
mirrors stem-outward linear position in suffixing morphology
(Ch 2 §6 iconicity, p. 33). The field name `peripherality` makes
this directionality explicit and avoids the wrong-on-its-face
gloss "high relevance rank means low relevance."

**Categories from Bybee 1985 Ch 2 §3** (verified against the book):
valence, voice, aspect, tense, mood, agreement.

**Linglib extensions** (NOT in Bybee 1985 — flag in any consumer
that reads these ranks):
- `derivation` (rank 1): Bybee Ch 4 argues lex/deriv/infl is a
  *continuum*, not a discrete level on the relevance scale.
- `number` (rank 3): Bybee discusses verbal-number agreement at
  the low end (with person agreement). Noun number is treated
  separately (Ch 2 §6 cites [greenberg-1963] only, "stem < number
  < case" for nouns). Cross-comparison of noun-number rank with
  verb-aspect rank is an artifact of unifying both onto one scale.
- `degree` (rank 5): Bybee never discusses adjectival degree
  morphology. Comparative morphology is often *derivational*
  cross-linguistically ([stassen-2013]).
- `negation` (rank 7): Bybee discusses negation as a kind of mood
  (Part II Ch 8 §5), not a separate level. Rank 7 is plausible
  per [miestamo-2005] cross-linguistic ordering data, but is a
  linglib extension.
- `nonfinite` (rank 9): not on Bybee's hierarchy at all (nonfinite
  morphology often changes syntactic category, outside the scope
  of inflectional categories proper). -/
def MorphCategory.peripherality : MorphCategory → Nat
  | .stem        => 0
  | .derivation  => 1
  | .valence     => 2
  | .number      => 3
  | .voice       => 3
  | .aspect      => 4
  | .degree      => 5
  | .tense       => 5
  | .mood        => 6
  | .negation    => 7
  | .agreement _ => 8  -- any controller role lands at Bybee rank 8
  | .nonfinite   => 9

/-! ### The relevance order

`peripherality` is a *rank function* — a numeric embedding. The object the
hierarchy is really about is the **order** it induces: which categories are
more stem-relevant than which. All relevance-hierarchy code — this file's
`RespectsRelevanceHierarchy` and the consumers in `Studies/` — speaks in that
order via `RelevanceLE` / `RelevanceLT`; the specific ℕ values of
`peripherality` are an implementation detail (only their comparisons carry
meaning, as `relevanceLE_iff_peripherality` records). -/

/-- `a` is at least as stem-relevant as `b`: the rank order induced by
`peripherality`. This is the unified relation relevance-hierarchy code uses. -/
def MorphCategory.RelevanceLE (a b : MorphCategory) : Prop :=
  a.peripherality ≤ b.peripherality

/-- `a` is strictly more stem-relevant than `b`. -/
def MorphCategory.RelevanceLT (a b : MorphCategory) : Prop :=
  a.peripherality < b.peripherality

instance : DecidableRel MorphCategory.RelevanceLE :=
  fun a b => inferInstanceAs (Decidable (a.peripherality ≤ b.peripherality))

instance : DecidableRel MorphCategory.RelevanceLT :=
  fun a b => inferInstanceAs (Decidable (a.peripherality < b.peripherality))

/-- The relevance order is reflexive. -/
@[refl] theorem MorphCategory.RelevanceLE.refl (a : MorphCategory) : a.RelevanceLE a :=
  Nat.le_refl _

/-- The relevance order is transitive. -/
theorem MorphCategory.RelevanceLE.trans {a b c : MorphCategory}
    (h₁ : a.RelevanceLE b) (h₂ : b.RelevanceLE c) : a.RelevanceLE c :=
  Nat.le_trans h₁ h₂

/-- The relevance order is total: any two categories are comparable. -/
theorem MorphCategory.RelevanceLE.total (a b : MorphCategory) :
    a.RelevanceLE b ∨ b.RelevanceLE a :=
  Nat.le_total _ _

/-- Strict relevance order is the strict part of the order, as expected. -/
theorem MorphCategory.RelevanceLT_iff {a b : MorphCategory} :
    a.RelevanceLT b ↔ a.RelevanceLE b ∧ ¬ b.RelevanceLE a := by
  unfold MorphCategory.RelevanceLT MorphCategory.RelevanceLE; omega

/-- `peripherality` reflects the relevance order exactly: it is the canonical
rank realizing the order, so the order carries precisely the information the
rank does. -/
theorem MorphCategory.relevanceLE_iff_peripherality {a b : MorphCategory} :
    a.RelevanceLE b ↔ a.peripherality ≤ b.peripherality := Iff.rfl

/-- A morpheme ordering respects the relevance hierarchy when its categories
are sorted stem-outward by the relevance order. -/
def RespectsRelevanceHierarchy (slots : List MorphCategory) : Prop :=
  slots.Pairwise MorphCategory.RelevanceLE

instance : DecidablePred RespectsRelevanceHierarchy := fun _ => by
  unfold RespectsRelevanceHierarchy; exact inferInstance

end Morphology
