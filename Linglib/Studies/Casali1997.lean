import Linglib.Phonology.Hiatus
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Casali (1997): Vowel Elision in Hiatus Contexts: Which Vowel Goes?

This file formalizes Casali's account of which of two vowels in hiatus elides. Casali observes
that elision of the first vowel is possible everywhere, while elision of the second is found
only where a lexical word or root precedes a function word or suffix. He derives this from
faithfulness constraints that protect segments in prominent positions: the beginning of a
word, a lexical word or root, the beginning of a morpheme, and a morpheme of one segment.

A context is a juncture together with the status of its two morphemes and the kind of boundary
between them, and the prominent positions of each vowel are read off that description. Eliding
a vowel violates the constraint of each prominent position it occupies. Where the first vowel
begins no morpheme, the second vowel can elide under some ranking exactly when the first
morpheme is lexical and the second is not (`exists_mem_optimal_v2_iff`), by harmonic bounding
in one direction and by ranking the constraint on lexical material on top in the other, while
the first vowel can always elide (`exists_optimal_eq_v1`). One ranking therefore elides the
first vowel after a prefix and the second before a suffix (`lexical_on_top`). The constraint on
morphemes of one segment is violated exactly when elision leaves the bare stem
(`prominent_v2_soleSegment_iff`), and ranked over the constraint on lexical material it makes
the first vowel elide before a suffix of one segment and the second before a longer one
(`soleSegment_over_lexical`). The general statement behind all of these is
`optimal_eq_singleton_iff`: a vowel elides alone exactly when some position protecting only
the other vowel outranks every position protecting only it.

## Implementation notes

The general constraint against deletion, which the position-sensitive constraints universally
dominate, is violated once by either elision and so never decides between them; it is kept as
the last constraint of the set. A word-initial vowel is also morpheme-initial, so the second
vowel violates the morpheme-initial constraint at a word boundary too, which the paper's table
of violations leaves out and which changes no prediction. The paper's survey of languages is
not recorded.

## References

* [casali-1997]
-/

namespace Casali1997

open Phonology Constraints OptimalityTheory

/-- A prominent position, whose segments a faithfulness constraint protects from deletion. -/
inductive Prominence where
  /-- The beginning of a word. -/
  | wordInitial
  /-- A lexical word or a root. -/
  | lexical
  /-- The beginning of a morpheme. -/
  | morphemeInitial
  /-- A morpheme of one segment. -/
  | soleSegment
  deriving DecidableEq, Fintype, Repr

/-- A word or morpheme is lexical, as nouns, verbs, adjectives and roots are, or functional, as
other words and affixes are. -/
inductive Status where
  | lexical
  | functional
  deriving DecidableEq, Repr

/-- The boundary at a juncture lies between two words or between two morphemes of one word. -/
inductive Boundary where
  | word
  | morpheme
  deriving DecidableEq, Repr

/-- A context is a juncture, whose stem and suffix stand for the first and second word or
morpheme, together with the status of each, the boundary between them, and whether the first
begins its word. -/
structure Context extends Hiatus.Juncture where
  /-- The status of the first word or morpheme. -/
  left : Status
  /-- The status of the second word or morpheme. -/
  right : Status
  /-- The boundary between them. -/
  boundary : Boundary
  /-- The first morpheme begins its word. -/
  LeftBeginsWord : Prop
  [decLeftBeginsWord : Decidable LeftBeginsWord]

attribute [instance] Context.decLeftBeginsWord

/-- The vowel that elides. -/
inductive Elision where
  | v1
  | v2
  deriving DecidableEq, Repr

variable (c : Context)

/-- `c.Prominent e p` holds when the vowel that `e` elides occupies the prominent position `p`
in the context `c`. -/
def Context.Prominent : Elision → Prominence → Prop
  | .v1, .wordInitial => c.stemBody = [] ∧ c.LeftBeginsWord
  | .v1, .lexical => c.left = .lexical
  | .v1, .morphemeInitial => c.stemBody = []
  | .v1, .soleSegment => c.stemBody = []
  | .v2, .wordInitial => c.boundary = .word
  | .v2, .lexical => c.right = .lexical
  | .v2, .morphemeInitial => True
  | .v2, .soleSegment => c.suffixBody = []

instance (e : Elision) (p : Prominence) : Decidable (c.Prominent e p) := by
  cases e <;> cases p <;> unfold Context.Prominent <;> infer_instance

/-- `c.resolve e` is the form that the elision `e` gives. -/
def Context.resolve : Elision → List Segment
  | .v1 => c.elideV1
  | .v2 => c.elideV2

/-- The constraint of a prominent position is violated by eliding a vowel in that position. -/
def maxP (p : Prominence) : Constraint Elision := Constraint.binary (c.Prominent · p)

/-- The index of the constraint of a prominent position. -/
def index : Prominence → Fin 5
  | .wordInitial => 0
  | .lexical => 1
  | .morphemeInitial => 2
  | .soleSegment => 3

/-- The prominent position whose constraint has a given index, the last index being that of the
general constraint against deletion. -/
def position? : Fin 5 → Option Prominence
  | 0 => some .wordInitial
  | 1 => some .lexical
  | 2 => some .morphemeInitial
  | 3 => some .soleSegment
  | 4 => none

theorem index_injective : Function.Injective index := by decide

theorem position?_eq_some_iff {i : Fin 5} {p : Prominence} :
    position? i = some p ↔ i = index p := by
  revert i p; decide

/-- The constraint set consists of the constraints of word-initial position, of lexical
material, of morpheme-initial position and of morphemes of one segment, followed by the
general constraint against deletion, which every elision violates once. -/
def con : CON Elision 5 := fun i ↦ (position? i).elim (fun _ ↦ 1) (maxP c)

@[simp] theorem con_index (p : Prominence) (e : Elision) :
    con c (index p) e = if c.Prominent e p then 1 else 0 := by
  cases p <;> rfl

/-- The tableau of the two elisions under the ranking `r`. -/
abbrev tableau (r : Ranking 5) : Tableau Elision 5 := Tableau.ofPerm (con c) r [.v1, .v2]

theorem candidates_tableau (r : Ranking 5) : (tableau c r).candidates = {.v1, .v2} := rfl

variable {c}

/-- If every prominent position of the vowel that `e` elides is one of the vowel that `e'`
elides, then `e` violates no constraint more than `e'` does. -/
theorem con_le {e e' : Elision} (hle : ∀ p, c.Prominent e p → c.Prominent e' p) (i : Fin 5) :
    con c i e ≤ con c i e' := by
  cases hi : position? i with
  | none => simp [con, hi]
  | some p =>
    obtain rfl := position?_eq_some_iff.1 hi
    by_cases hp : c.Prominent e p <;> simp [hp, hle]

theorem con_lt_iff {e e' : Elision} {i : Fin 5} :
    con c i e < con c i e' ↔ ∃ p, i = index p ∧ ¬ c.Prominent e p ∧ c.Prominent e' p := by
  cases hi : position? i with
  | none => simp [con, hi, ← position?_eq_some_iff]
  | some p =>
    obtain rfl := position?_eq_some_iff.1 hi
    by_cases he : c.Prominent e p <;> by_cases he' : c.Prominent e' p <;>
      simp [he, he', index_injective.eq_iff]

/-- One vowel is the sole one to elide exactly when some position protecting only the other
outranks every position protecting only it, which is the elementary ranking condition stated
over positions. -/
theorem optimal_eq_singleton_iff {e e' : Elision} (hne : e ≠ e') (r : Ranking 5) :
    (tableau c r).optimal = {e} ↔ ∃ p, ¬ c.Prominent e p ∧ c.Prominent e' p ∧
      ∀ q, c.Prominent e q → ¬ c.Prominent e' q → r.Dominates (index p) (index q) := by
  have hcand : (tableau c r).candidates = {e, e'} := by
    rw [candidates_tableau]
    cases e <;> cases e' <;> first | exact absurd rfl hne | decide
  rw [Tableau.optimal_eq_singleton_iff_pair hcand hne,
    Tableau.ofPerm_profile_lt_iff_exists_dominates]
  constructor
  · rintro ⟨i, hi, hr⟩
    obtain ⟨p, rfl, he, he'⟩ := con_lt_iff.1 hi
    exact ⟨p, he, he', fun q hq hq' ↦ hr _ (con_lt_iff.2 ⟨q, rfl, hq', hq⟩)⟩
  · rintro ⟨p, he, he', hr⟩
    refine ⟨index p, con_lt_iff.2 ⟨p, rfl, he, he'⟩, fun j hj ↦ ?_⟩
    obtain ⟨q, rfl, hq', hq⟩ := con_lt_iff.1 hj
    exact hr q hq hq'

/-- A position in which only one of the two vowels is prominent can be ranked so that the other
vowel is the one that elides. -/
theorem exists_optimal_eq {e e' : Elision} (hne : e ≠ e') {p : Prominence}
    (he : ¬ c.Prominent e p) (he' : c.Prominent e' p) : ∃ r, (tableau c r).optimal = {e} := by
  obtain ⟨r, hr⟩ := Ranking.exists_forall_dominates (index p)
  exact ⟨r, (optimal_eq_singleton_iff hne r).2 ⟨p, he, he', fun q hq _ ↦
    hr _ fun hqp ↦ he (index_injective hqp ▸ hq)⟩⟩

/-- A vowel whose prominent positions are all positions of the other vowel too, and which
lacks one of them, harmonically bounds the other, which elides under no ranking. -/
theorem notMem_optimal {e e' : Elision} (hle : ∀ p, c.Prominent e p → c.Prominent e' p)
    {p : Prominence} (he : ¬ c.Prominent e p) (he' : c.Prominent e' p) (r : Ranking 5) :
    e' ∉ (tableau c r).optimal :=
  Tableau.ofPerm_notMem_optimal_of_lt (c := e) (by cases e <;> simp) <|
    Pi.lt_def.2 ⟨con_le hle, index p, by simp [he, he']⟩

/-- The first vowel can elide in every context where it begins no morpheme. -/
theorem exists_optimal_eq_v1 (h : c.stemBody ≠ []) : ∃ r, (tableau c r).optimal = {.v1} :=
  exists_optimal_eq (e := .v1) (e' := .v2) (by decide) (p := .morphemeInitial) h trivial

/-- Where the first vowel begins no morpheme, the second vowel elides under some ranking
exactly when the first morpheme is lexical and the second is not. This covers the boundary
between two lexical words, between a lexical and a function word in either order, between a
prefix of more than one segment and a root, and between a root and a suffix. -/
theorem exists_mem_optimal_v2_iff (h : c.stemBody ≠ []) :
    (∃ r, .v2 ∈ (tableau c r).optimal) ↔ c.left = .lexical ∧ c.right = .functional := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · by_contra hc
    refine notMem_optimal (e := .v1) (e' := .v2) (p := .morphemeInitial) ?_ h trivial r hr
    rintro (_ | _ | _ | _) hp
    · exact absurd hp.1 h
    · cases hr' : c.right
      · exact hr'
      · exact absurd ⟨hp, hr'⟩ hc
    · trivial
    · exact absurd hp h
  · obtain ⟨r, hr'⟩ := exists_optimal_eq (e := .v2) (e' := .v1) (by decide) (p := .lexical)
      (by simp [Context.Prominent, hr]) hl
    exact ⟨r, hr' ▸ Finset.mem_singleton_self _⟩

/-- The second vowel occupies a morpheme of one segment exactly when eliding it leaves the bare
stem, so that no segment of the second morpheme remains. -/
theorem prominent_v2_soleSegment_iff : c.Prominent .v2 .soleSegment ↔ c.resolve .v2 = c.stem :=
  c.elideV2_eq_stem_iff.symm

/-- A root followed by a suffix, where the first vowel begins no morpheme. -/
structure Context.IsRootSuffix (c : Context) : Prop where
  stemBody_ne_nil : c.stemBody ≠ []
  left : c.left = .lexical
  right : c.right = .functional
  boundary : c.boundary = .morpheme

/-- A prefix of more than one segment followed by a root. -/
structure Context.IsPrefixRoot (c : Context) : Prop where
  stemBody_ne_nil : c.stemBody ≠ []
  left : c.left = .functional
  right : c.right = .lexical

/-- With the constraint on lexical material on top, the first vowel elides after a prefix and
the second before a suffix of any length, the asymmetry within one language that the paper
reports for Chichewa. -/
theorem lexical_on_top {r : Ranking 5}
    (hr : ∀ j, j ≠ index .lexical → r.Dominates (index .lexical) j) {c c' : Context}
    (hc : c.IsPrefixRoot) (hc' : c'.IsRootSuffix) :
    (tableau c r).optimal = {.v1} ∧ (tableau c' r).optimal = {.v2} := by
  have h₁ : ¬ c.Prominent .v1 .lexical := by simp [Context.Prominent, hc.left]
  have h₂ : ¬ c'.Prominent .v2 .lexical := by simp [Context.Prominent, hc'.right]
  exact ⟨(optimal_eq_singleton_iff (e' := .v2) (by decide) r).2 ⟨.lexical, h₁, hc.right,
      fun q hq _ ↦ hr _ fun hqp ↦ h₁ (index_injective hqp ▸ hq)⟩,
    (optimal_eq_singleton_iff (e' := .v1) (by decide) r).2 ⟨.lexical, h₂, hc'.left,
      fun q hq _ ↦ hr _ fun hqp ↦ h₂ (index_injective hqp ▸ hq)⟩⟩

/-- With the constraint on morphemes of one segment over the constraint on lexical material,
and that over the morpheme-initial constraint, the first vowel elides before a suffix of one
segment and the second before a longer one, as in the paper's tableaux (19) and (20). -/
theorem soleSegment_over_lexical {r : Ranking 5}
    (h₁ : r.Dominates (index .soleSegment) (index .lexical))
    (h₂ : r.Dominates (index .lexical) (index .morphemeInitial)) (hc : c.IsRootSuffix) :
    (tableau c r).optimal = {if c.suffixBody = [] then .v1 else .v2} := by
  split_ifs with hs
  · refine (optimal_eq_singleton_iff (e' := .v2) (by decide) r).2 ⟨.soleSegment,
      hc.stemBody_ne_nil, hs, ?_⟩
    rintro (_ | _ | _ | _) hq hq'
    · exact absurd hq.1 hc.stemBody_ne_nil
    · exact h₁
    · exact absurd hq hc.stemBody_ne_nil
    · exact absurd hq hc.stemBody_ne_nil
  · refine (optimal_eq_singleton_iff (e' := .v1) (by decide) r).2 ⟨.lexical,
      by simp [Context.Prominent, hc.right], hc.left, ?_⟩
    rintro (_ | _ | _ | _) hq hq'
    · simp [Context.Prominent, hc.boundary] at hq
    · simp [Context.Prominent, hc.right] at hq
    · exact h₂
    · exact absurd hq hs

end Casali1997
