import Linglib.Phonology.Hiatus
import Linglib.Phonology.OptimalityTheory.Correspondence.Erase
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Casali (1997): Vowel Elision in Hiatus Contexts: Which Vowel Goes?

This file formalizes Casali's account of which of two vowels in hiatus elides. Casali observes
that elision of the first vowel is possible everywhere, while elision of the second is found
only where a lexical word or root precedes a function word or suffix. He derives this from
faithfulness constraints that protect segments in prominent positions: the beginning of a
word, a lexical word or root, the beginning of a morpheme, and a morpheme of one segment.

A context is a juncture together with the status of its two morphemes and the kind of boundary
between them, and the prominent positions are predicates on the positions of the unrepaired
concatenation read off that description. An elision is the deletion of one vowel in the sense of
Correspondence Theory, and the constraint of a position is MAX restricted to it, so that an
elision violates the constraint exactly when the elided vowel stands in the position
(`maxP_apply`). Where the first vowel begins no morpheme, the second vowel can elide under some
ranking exactly when the first morpheme is lexical and the second is not
(`exists_mem_optimal_v2_iff`), by harmonic bounding in one direction and by ranking the
constraint on lexical material on top in the other, while the first vowel can always elide
(`exists_optimal_eq_v1`). One ranking therefore elides the first vowel after a prefix and the
second before a suffix (`lexical_on_top`). The constraint on morphemes of one segment is
violated exactly when elision leaves the bare stem (`prominent_v2_soleSegment_iff`), and ranked
over the constraint on lexical material it makes the first vowel elide before a suffix of one
segment and the second before a longer one (`soleSegment_over_lexical`). The general statement
behind all of these is `optimal_eq_singleton_iff`: a vowel elides alone exactly when some
position protecting only the other vowel outranks every position protecting only it.

## Implementation notes

The general constraint against deletion, which the position-sensitive constraints universally
dominate, is violated once by either elision (`max_apply`) and so never decides between them; it
is kept as the last constraint of the set. A word-initial vowel is also morpheme-initial, so the
second vowel violates the morpheme-initial constraint at a word boundary too, which the paper's
table of violations leaves out and which changes no prediction. The paper's survey of languages
is not recorded.

## References

* [casali-1997]
* [mccarthy-prince-1995]
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

/-- `c.Protects p i` holds when position `i` of the unrepaired concatenation is the prominent
position `p`. The first position begins a morpheme, and begins a word when the first morpheme
does. The position of the second vowel begins a morpheme, and begins a word at a word
boundary. A position is lexical when its morpheme is, and is a sole segment when its morpheme
has no other. -/
def Context.Protects : Prominence → ℕ → Prop
  | .wordInitial, i => i = 0 ∧ c.LeftBeginsWord ∨ i = c.v2Idx ∧ c.boundary = .word
  | .lexical, i => i ≤ c.v1Idx ∧ c.left = .lexical ∨ c.v2Idx ≤ i ∧ c.right = .lexical
  | .morphemeInitial, i => i = 0 ∨ i = c.v2Idx
  | .soleSegment, i => i = 0 ∧ c.stemBody = [] ∨ i = c.v2Idx ∧ c.suffixBody = []

instance (p : Prominence) : DecidablePred (c.Protects p) := fun _ ↦ by
  cases p <;> unfold Context.Protects <;> infer_instance

/-- `c.idx e` is the position of the vowel that `e` elides. -/
def Context.idx : Elision → ℕ
  | .v1 => c.v1Idx
  | .v2 => c.v2Idx

theorem Context.idx_lt_length_input (e : Elision) : c.idx e < c.input.length := by
  cases e
  · exact c.v1Idx_lt_length_input
  · exact c.v2Idx_lt_length_input

/-- `c.Prominent e p` holds when the vowel that `e` elides stands in the prominent position
`p`. -/
def Context.Prominent (e : Elision) (p : Prominence) : Prop := c.Protects p (c.idx e)

instance (e : Elision) (p : Prominence) : Decidable (c.Prominent e p) :=
  inferInstanceAs (Decidable (c.Protects p (c.idx e)))

/-- `c.corr e` is the correspondence between the unrepaired concatenation and the form that
the elision `e` gives, the deletion of one vowel. -/
def Context.corr (e : Elision) : Correspondence Correspondence.Side Segment :=
  Correspondence.eraseIdx c.input (c.idx e)

/-- `c.resolve e` is the form that the elision `e` gives. -/
def Context.resolve (e : Elision) : List Segment := (c.corr e).form .rhs

theorem Context.resolve_v1 : c.resolve .v1 = c.elideV1 := c.elideV1_eq_eraseIdx.symm

theorem Context.resolve_v2 : c.resolve .v2 = c.elideV2 := c.elideV2_eq_eraseIdx.symm

/-- The constraint of a prominent position counts the input segments in that position that
have no correspondent in the output. -/
def maxP (p : Prominence) : Constraint Elision :=
  fun e ↦ (c.corr e).maxViolAt (c.Protects p) .lhs .rhs

/-- The general constraint against deletion counts the input segments that have no
correspondent in the output. -/
def max : Constraint Elision := fun e ↦ (c.corr e).maxViol .lhs .rhs

/-- An elision violates the constraint of a position exactly when the elided vowel stands in
it. -/
theorem maxP_apply (p : Prominence) (e : Elision) :
    maxP c p e = if c.Prominent e p then 1 else 0 :=
  Correspondence.maxViolAt_eraseIdx (c.idx_lt_length_input e) _

/-- Every elision violates the general constraint against deletion once. -/
theorem max_apply (e : Elision) : max c e = 1 :=
  Correspondence.maxViol_eraseIdx (c.idx_lt_length_input e)

section Prominent

variable {c}

local macro "prominent_simp" : tactic =>
  `(tactic| simp [Context.Prominent, Context.Protects, Context.idx, Hiatus.Juncture.v1Idx,
    Hiatus.Juncture.v2Idx])

@[simp] theorem prominent_v1_wordInitial :
    c.Prominent .v1 .wordInitial ↔ c.stemBody = [] ∧ c.LeftBeginsWord := by prominent_simp

@[simp] theorem prominent_v1_lexical : c.Prominent .v1 .lexical ↔ c.left = .lexical := by
  prominent_simp

@[simp] theorem prominent_v1_morphemeInitial :
    c.Prominent .v1 .morphemeInitial ↔ c.stemBody = [] := by prominent_simp

@[simp] theorem prominent_v1_soleSegment : c.Prominent .v1 .soleSegment ↔ c.stemBody = [] := by
  prominent_simp

@[simp] theorem prominent_v2_wordInitial :
    c.Prominent .v2 .wordInitial ↔ c.boundary = .word := by prominent_simp

@[simp] theorem prominent_v2_lexical : c.Prominent .v2 .lexical ↔ c.right = .lexical := by
  prominent_simp

@[simp] theorem prominent_v2_morphemeInitial : c.Prominent .v2 .morphemeInitial := by
  prominent_simp

@[simp] theorem prominent_v2_soleSegment :
    c.Prominent .v2 .soleSegment ↔ c.suffixBody = [] := by prominent_simp

end Prominent

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
general constraint against deletion. -/
def con : CON Elision 5 := fun i ↦ (position? i).elim (max c) (maxP c)

@[simp] theorem con_index (p : Prominence) (e : Elision) :
    con c (index p) e = if c.Prominent e p then 1 else 0 := by
  rw [← maxP_apply]; cases p <;> rfl

theorem con_of_position?_eq_none {i : Fin 5} (hi : position? i = none) (e : Elision) :
    con c i e = 1 := by
  rw [con, hi]; exact max_apply c e

/-- The tableau of the two elisions under the ranking `r`. -/
abbrev tableau (r : Ranking 5) : Tableau Elision 5 := Tableau.ofPerm (con c) r [.v1, .v2]

theorem candidates_tableau (r : Ranking 5) : (tableau c r).candidates = {.v1, .v2} := rfl

variable {c}

/-- If every prominent position of the vowel that `e` elides is one of the vowel that `e'`
elides, then `e` violates no constraint more than `e'` does. -/
theorem con_le {e e' : Elision} (hle : ∀ p, c.Prominent e p → c.Prominent e' p) (i : Fin 5) :
    con c i e ≤ con c i e' := by
  cases hi : position? i with
  | none => simp [con_of_position?_eq_none c hi]
  | some p =>
    obtain rfl := position?_eq_some_iff.1 hi
    by_cases hp : c.Prominent e p <;> simp [hp, hle]

theorem con_lt_iff {e e' : Elision} {i : Fin 5} :
    con c i e < con c i e' ↔ ∃ p, i = index p ∧ ¬ c.Prominent e p ∧ c.Prominent e' p := by
  cases hi : position? i with
  | none => simp [con_of_position?_eq_none c hi, ← position?_eq_some_iff, hi]
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
  exists_optimal_eq (e := .v1) (e' := .v2) (by decide) (p := .morphemeInitial) (by simpa using h)
    prominent_v2_morphemeInitial

/-- Where the first vowel begins no morpheme, the second vowel elides under some ranking
exactly when the first morpheme is lexical and the second is not. This covers the boundary
between two lexical words, between a lexical and a function word in either order, between a
prefix of more than one segment and a root, and between a root and a suffix. -/
theorem exists_mem_optimal_v2_iff (h : c.stemBody ≠ []) :
    (∃ r, .v2 ∈ (tableau c r).optimal) ↔ c.left = .lexical ∧ c.right = .functional := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · by_contra hc
    refine notMem_optimal (e := .v1) (e' := .v2) (p := .morphemeInitial) ?_ (by simpa using h)
      prominent_v2_morphemeInitial r hr
    rintro (_ | _ | _ | _) hp
    · exact absurd (prominent_v1_wordInitial.1 hp).1 h
    · cases hr' : c.right
      · exact prominent_v2_lexical.2 hr'
      · exact absurd ⟨prominent_v1_lexical.1 hp, hr'⟩ hc
    · exact prominent_v2_morphemeInitial
    · exact absurd (prominent_v1_soleSegment.1 hp) h
  · obtain ⟨r, hr'⟩ := exists_optimal_eq (e := .v2) (e' := .v1) (by decide) (p := .lexical)
      (by simp [hr]) (prominent_v1_lexical.2 hl)
    exact ⟨r, hr' ▸ Finset.mem_singleton_self _⟩

/-- The second vowel occupies a morpheme of one segment exactly when eliding it leaves the bare
stem, so that no segment of the second morpheme remains. -/
theorem prominent_v2_soleSegment_iff : c.Prominent .v2 .soleSegment ↔ c.resolve .v2 = c.stem := by
  rw [prominent_v2_soleSegment, c.resolve_v2, c.elideV2_eq_stem_iff]

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
  have h₁ : ¬ c.Prominent .v1 .lexical := by simp [hc.left]
  have h₂ : ¬ c'.Prominent .v2 .lexical := by simp [hc'.right]
  exact ⟨(optimal_eq_singleton_iff (e' := .v2) (by decide) r).2 ⟨.lexical, h₁,
      prominent_v2_lexical.2 hc.right, fun q hq _ ↦ hr _ fun hqp ↦ h₁ (index_injective hqp ▸ hq)⟩,
    (optimal_eq_singleton_iff (e' := .v1) (by decide) r).2 ⟨.lexical, h₂,
      prominent_v1_lexical.2 hc'.left, fun q hq _ ↦ hr _ fun hqp ↦ h₂ (index_injective hqp ▸ hq)⟩⟩

/-- With the constraint on morphemes of one segment over the constraint on lexical material,
and that over the morpheme-initial constraint, the first vowel elides before a suffix of one
segment and the second before a longer one, as in the paper's tableaux (19) and (20). -/
theorem soleSegment_over_lexical {r : Ranking 5}
    (h₁ : r.Dominates (index .soleSegment) (index .lexical))
    (h₂ : r.Dominates (index .lexical) (index .morphemeInitial)) (hc : c.IsRootSuffix) :
    (tableau c r).optimal = {if c.suffixBody = [] then .v1 else .v2} := by
  split_ifs with hs
  · refine (optimal_eq_singleton_iff (e' := .v2) (by decide) r).2 ⟨.soleSegment,
      by simpa using hc.stemBody_ne_nil, prominent_v2_soleSegment.2 hs, ?_⟩
    rintro (_ | _ | _ | _) hq hq'
    · exact absurd (prominent_v1_wordInitial.1 hq).1 hc.stemBody_ne_nil
    · exact h₁
    · exact absurd (prominent_v1_morphemeInitial.1 hq) hc.stemBody_ne_nil
    · exact absurd (prominent_v1_soleSegment.1 hq) hc.stemBody_ne_nil
  · refine (optimal_eq_singleton_iff (e' := .v1) (by decide) r).2 ⟨.lexical,
      by simp [hc.right], prominent_v1_lexical.2 hc.left, ?_⟩
    rintro (_ | _ | _ | _) hq hq'
    · simp [hc.boundary] at hq
    · simp [hc.right] at hq
    · exact h₂
    · exact absurd (prominent_v2_soleSegment.1 hq) hs

end Casali1997
