/-!
# Wordhood Typology: ms-words vs p-words
@cite{kalin-bjorkman-etal-2026}

@cite{kalin-bjorkman-etal-2026} (§3.2) argue that solving the wordhood problem
requires distinguishing at minimum two notions of "word":

- **ms-word** (morphosyntactic/grammatical word): a constituent containing
  one or more morphemes, contained in a morphosyntactic phrase. Identified
  by cohesiveness, fixed internal order, selectivity, and domainhood
  for morphological operations (§3.2.1).

- **p-word** (phonological/prosodic word): a constituent containing one or
  more syllables grouped into feet, contained in a phonological phrase.
  Identified by phonotactic bounding and edge phenomena (§3.2.2).

Crossing ms-boundedness (bound vs free) with p-boundedness yields a
four-way typology of morpheme attachment (Table 3):

| | ms-free | ms-bound |
|---------|-----------------|----------------------|
| p-free  | canonical word  | non-cohering affix   |
| p-bound | simple clitic   | canonical affix      |

This classification connects `Theories.Morphology.Diagnostics`
(Zwicky & Pullum's clitic-vs-affix criteria, which diagnose
ms-boundedness) with `Phonology.ProsodicWord` (PrWd
structure, which diagnoses p-boundedness).
-/

namespace Core.Morphology.Wordhood

-- ============================================================================
-- §1: Boundedness dimensions
-- ============================================================================

/-- Morphosyntactic boundedness: whether an element must be internal
    to a (complex) ms-word.

    **ms-bound** elements are diagnosed by cohesiveness (the ms-word
    they belong to cannot be interrupted), fixed order (their position
    within the ms-word is rigid), and selectivity (they are picky about
    what they attach to). @cite{kalin-bjorkman-etal-2026} §3.2.1.

    **ms-free** elements are independent ms-words: they can be reordered
    with respect to other ms-words, separated from them, etc. -/
inductive MSBoundedness where
  | free   -- independent ms-word (can stand alone, be reordered, etc.)
  | bound  -- must be internal to a host ms-word
  deriving DecidableEq, Repr

/-- Phonological/prosodic boundedness: whether an element must be
    internal to a (complex) p-word.

    **p-bound** elements are diagnosed by participating in p-word-bounded
    phonological processes (vowel harmony, stress assignment, nasal
    assimilation) and not exhibiting independent p-word edge phenomena.
    @cite{kalin-bjorkman-etal-2026} §3.2.2.

    **p-free** elements form their own p-word: they satisfy minimal word
    constraints independently, trigger p-word edge phenomena, and
    block cross-boundary processes. -/
inductive PBoundedness where
  | free   -- forms its own p-word
  | bound  -- must be internal to a host p-word
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Wordhood profile and classification
-- ============================================================================

/-- A morpheme's wordhood profile: its boundedness on both the
    morphosyntactic and phonological/prosodic dimensions.
    @cite{kalin-bjorkman-etal-2026} Table 3. -/
structure WordhoodProfile where
  /-- Morphosyntactic boundedness. -/
  ms : MSBoundedness
  /-- Phonological/prosodic boundedness. -/
  p  : PBoundedness
  deriving DecidableEq, Repr

/-- The four-way classification of morpheme attachment from Table 3.
    @cite{kalin-bjorkman-etal-2026} §3.2.3. -/
inductive WordhoodClass where
  /-- ms-free, p-free: an independent word by both criteria.
      Example: English *cat*. -/
  | canonicalWord
  /-- ms-free, p-bound: syntactically independent but phonologically
      dependent. Requires prosodic incorporation (e.g., Clitic Group).
      Example: English possessive *-'s*, Romance clitics.
      @cite{zwicky-1977} -/
  | simpleClitic
  /-- ms-bound, p-free: morphosyntactically part of a word but
      phonologically independent (forms own p-word).
      Example: Dutch non-cohering prefixes. -/
  | nonCoheringAffix
  /-- ms-bound, p-bound: part of a word by both criteria.
      Example: English plural *-s*, past tense *-ed*. -/
  | canonicalAffix
  deriving DecidableEq, Repr

/-- Classify a wordhood profile into the four-way typology. -/
def WordhoodProfile.classify : WordhoodProfile → WordhoodClass
  | ⟨.free,  .free⟩  => .canonicalWord
  | ⟨.free,  .bound⟩ => .simpleClitic
  | ⟨.bound, .free⟩  => .nonCoheringAffix
  | ⟨.bound, .bound⟩ => .canonicalAffix

-- ============================================================================
-- §3: Verification theorems
-- ============================================================================

theorem canonicalWord_is_doubly_free :
    (WordhoodProfile.mk .free .free).classify = .canonicalWord := rfl

theorem simpleClitic_is_ms_free_p_bound :
    (WordhoodProfile.mk .free .bound).classify = .simpleClitic := rfl

theorem nonCoheringAffix_is_ms_bound_p_free :
    (WordhoodProfile.mk .bound .free).classify = .nonCoheringAffix := rfl

theorem canonicalAffix_is_doubly_bound :
    (WordhoodProfile.mk .bound .bound).classify = .canonicalAffix := rfl

/-- The four classes are exhaustive: every profile maps to some class. -/
theorem classify_total (w : WordhoodProfile) :
    w.classify = .canonicalWord ∨
    w.classify = .simpleClitic ∨
    w.classify = .nonCoheringAffix ∨
    w.classify = .canonicalAffix := by
  cases w with | mk ms p => cases ms <;> cases p <;> simp [WordhoodProfile.classify]

/-- The four classes are mutually exclusive (each profile maps to
    exactly one class). -/
theorem classify_injective (w₁ w₂ : WordhoodProfile)
    (h : w₁.classify = w₂.classify) :
    w₁ = w₂ := by
  cases w₁ with | mk ms₁ p₁ =>
  cases w₂ with | mk ms₂ p₂ =>
  cases ms₁ <;> cases p₁ <;> cases ms₂ <;> cases p₂ <;>
    simp [WordhoodProfile.classify] at h <;> rfl

end Core.Morphology.Wordhood
