module

public import Linglib.Phonology.Hiatus
public import Linglib.Data.Hiatus.Casali1997
public import Linglib.Phonology.OptimalityTheory.Correspondence.Erase
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Casali (1997): Vowel Elision in Hiatus Contexts: Which Vowel Goes?

Casali observes that elision of the first of two vowels in hiatus is possible everywhere, while
elision of the second is found only where a lexical word or root precedes a function word or
suffix. He derives this from MAX constraints that protect segments in prominent positions: the
beginning of a word, a lexical word or root, the beginning of a morpheme, and a morpheme of one
segment. An elision deletes one vowel in the sense of Correspondence Theory, so it violates the
constraints that protect the position of that vowel, and an elision can be optimal exactly when
the constraints it violates are not a proper superset of those the other elision violates.

## Main definitions

* `Context`: a juncture with the status of its two morphemes and the boundaries before and
  between them.
* `Context.violations`: the constraints an elision violates, a row of the paper's table of
  violations.
* `tableau`: the tableau of the two elisions under a ranking.

## Main results

* `exists_mem_optimal_iff`: an elision is optimal under some ranking iff the constraints it
  violates are not a proper superset of those the other elision violates.
* `exists_mem_optimal_second_iff`: where the first vowel begins no morpheme, the second can
  elide iff the first morpheme is lexical and the second is not.
* `survey_allowed`, `survey_second_iff`: every elision the survey of Section 2 reports is
  allowed, and the survey reports an elision of the second vowel at exactly the kinds of juncture
  where one is allowed.

## Implementation notes

* The constraints are indexed by `Option Prominence`: `some p` is MAX restricted to the position
  `p`, and `none` is general MAX (`con_none`). Every elision violates general MAX once, so it
  never decides between them, and the universal ranking of the positional constraints above it
  is not imposed.
* The candidates are the survey's `ElidedVowel`, the vowel that elides.
* A word-initial vowel is also morpheme-initial, so the second vowel violates the
  morpheme-initial constraint at a word boundary too, which the paper's table of violations
  leaves out and which changes no prediction.
* `schematic k` is the paper's schematic juncture `/CV₁ + V₂C/` at the survey's kind `k`, with
  `C` and `V` the natural classes [+consonantal] and [+syllabic]; it witnesses that every kind of
  juncture has a context.

## References

* [casali-1997]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace Casali1997

open Phonology OptimalityTheory
open Data.Hiatus (ElidedVowel)

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

/-- A boundary between two words or between two morphemes of one word. -/
inductive Boundary where
  | word
  | morpheme
  deriving DecidableEq, Repr

/-- A context is a juncture, whose stem and suffix stand for the first and second word or
morpheme, together with the status of each and the boundaries before and between them. -/
structure Context extends Hiatus.Juncture where
  /-- The status of the first word or morpheme. -/
  left : Status
  /-- The status of the second word or morpheme. -/
  right : Status
  /-- The boundary before the first word or morpheme. -/
  leftEdge : Boundary
  /-- The boundary between them. -/
  boundary : Boundary

variable (c : Context)

/-- `c.Protects i k` holds when the constraint `i` protects position `k` of the unrepaired
concatenation. General MAX (`none`) protects every position. The first position and the position
of the second vowel each begin a morpheme, and begin a word after a word boundary. A position is
lexical when its morpheme is, and is a sole segment when its morpheme has no other. -/
def Context.Protects : Option Prominence → ℕ → Prop
  | none, _ => True
  | some .wordInitial, k => k = 0 ∧ c.leftEdge = .word ∨ k = c.v2Idx ∧ c.boundary = .word
  | some .lexical, k => k ≤ c.v1Idx ∧ c.left = .lexical ∨ c.v2Idx ≤ k ∧ c.right = .lexical
  | some .morphemeInitial, k => k = 0 ∨ k = c.v2Idx
  | some .soleSegment, k => k = 0 ∧ c.stemBody = [] ∨ k = c.v2Idx ∧ c.suffixBody = []

instance (i : Option Prominence) : DecidablePred (c.Protects i) := fun _ ↦ by
  rcases i with _ | _ | _ | _ | _ <;> unfold Context.Protects <;> infer_instance

/-- `c.idx e` is the position of the vowel that `e` elides. -/
def Context.idx : ElidedVowel → ℕ
  | .first => c.v1Idx
  | .second => c.v2Idx

theorem Context.idx_lt_length_input (e : ElidedVowel) : c.idx e < c.input.length := by
  cases e
  exacts [c.v1Idx_lt_length_input, c.v2Idx_lt_length_input]

/-- `c.violations e` is the set of constraints that the elision `e` violates, those protecting
the position of the elided vowel. It is a row of the paper's table of violations. -/
def Context.violations (e : ElidedVowel) : Set (Option Prominence) :=
  {i | c.Protects i (c.idx e)}

instance (e : ElidedVowel) : DecidablePred (· ∈ c.violations e) := fun i ↦
  inferInstanceAs (Decidable (c.Protects i (c.idx e)))

/-- `c.corr e` is the correspondence between the unrepaired concatenation and the form that
the elision `e` gives, the deletion of one vowel. -/
def Context.corr (e : ElidedVowel) : Correspondence BinaryRole Segment :=
  Correspondence.eraseIdx c.input (c.idx e)

/-- `c.resolve e` is the form that the elision `e` gives. -/
def Context.resolve (e : ElidedVowel) : List Segment := (c.corr e).form .rhs

theorem Context.resolve_first : c.resolve .first = c.elideV1 := c.elideV1_eq_eraseIdx.symm

theorem Context.resolve_second : c.resolve .second = c.elideV2 := c.elideV2_eq_eraseIdx.symm

/-- The constraint `i` counts the input segments it protects that have no correspondent in the
output. -/
def con : ConstraintSet ElidedVowel (Option Prominence) :=
  fun i e ↦ (c.corr e).maxViolAt (c.Protects i) .lhs .rhs

/-- General MAX counts the input segments that have no correspondent in the output. -/
theorem con_none (e : ElidedVowel) : con c none e = (c.corr e).maxViol .lhs .rhs :=
  Correspondence.maxViolAt_true _ _ _

/-- An elision violates a constraint once when the elided vowel stands in a position the
constraint protects, and otherwise not at all. -/
theorem con_apply (i : Option Prominence) (e : ElidedVowel) :
    con c i e = if i ∈ c.violations e then 1 else 0 :=
  Correspondence.maxViolAt_eraseIdx (c.idx_lt_length_input e) _

/-! ### The table of violations -/

section Violations

variable {c}

local macro "violations_simp" : tactic =>
  `(tactic| simp [Context.violations, Context.Protects, Context.idx, Hiatus.Juncture.v1Idx,
    Hiatus.Juncture.v2Idx])

@[simp] theorem none_mem_violations (e : ElidedVowel) : none ∈ c.violations e := trivial

@[simp] theorem wordInitial_mem_violations_first :
    some .wordInitial ∈ c.violations .first ↔ c.stemBody = [] ∧ c.leftEdge = .word := by
  violations_simp

@[simp] theorem lexical_mem_violations_first :
    some .lexical ∈ c.violations .first ↔ c.left = .lexical := by violations_simp

@[simp] theorem morphemeInitial_mem_violations_first :
    some .morphemeInitial ∈ c.violations .first ↔ c.stemBody = [] := by violations_simp

@[simp] theorem soleSegment_mem_violations_first :
    some .soleSegment ∈ c.violations .first ↔ c.stemBody = [] := by violations_simp

@[simp] theorem wordInitial_mem_violations_second :
    some .wordInitial ∈ c.violations .second ↔ c.boundary = .word := by violations_simp

@[simp] theorem lexical_mem_violations_second :
    some .lexical ∈ c.violations .second ↔ c.right = .lexical := by violations_simp

@[simp] theorem morphemeInitial_mem_violations_second :
    some .morphemeInitial ∈ c.violations .second := by violations_simp

@[simp] theorem soleSegment_mem_violations_second :
    some .soleSegment ∈ c.violations .second ↔ c.suffixBody = [] := by violations_simp

/-- The second vowel occupies a morpheme of one segment exactly when eliding it leaves the bare
stem, so that no segment of the second morpheme remains. -/
theorem soleSegment_mem_violations_second_iff_resolve :
    some .soleSegment ∈ c.violations .second ↔ c.resolve .second = c.stem := by
  rw [soleSegment_mem_violations_second, c.resolve_second, c.elideV2_eq_stem_iff]

end Violations

/-! ### Which vowel elides -/

/-- The tableau of the two elisions under the ranking `r`. -/
abbrev tableau (r : Ranking (Option Prominence) 5) : Tableau ElidedVowel 5 :=
  Tableau.ofPerm (con c) r [.first, .second]

private theorem card_option_prominence : Fintype.card (Option Prominence) = 5 := rfl

private theorem toFinset_eq_pair {e e' : ElidedVowel} (hne : e ≠ e') :
    [ElidedVowel.first, .second].toFinset = {e, e'} := by
  cases e <;> cases e' <;> first | exact absurd rfl hne | decide

variable {c}

theorem con_lt_con_iff {i : Option Prominence} {e e' : ElidedVowel} :
    con c i e < con c i e' ↔ i ∉ c.violations e ∧ i ∈ c.violations e' := by
  rw [con_apply, con_apply]
  split_ifs <;> simp_all

/-- One elision is pointwise below the other on the constraint set exactly when the constraints it
violates are a proper subset of those the other violates. -/
theorem con_lt_iff_ssubset {e e' : ElidedVowel} :
    (con c · e) < (con c · e') ↔ c.violations e ⊂ c.violations e' := by
  rw [Pi.lt_def, Set.ssubset_def, Set.not_subset]
  simp only [con_lt_con_iff]
  simp only [Pi.le_def, con_apply, Set.subset_def]
  refine and_congr (forall_congr' fun i ↦ ?_) (exists_congr fun _ ↦ and_comm)
  split_ifs <;> simp_all

/-- An elision is optimal under some ranking exactly when the constraints it violates are not a
proper superset of those the other elision violates. -/
theorem exists_mem_optimal_iff {e e' : ElidedVowel} (hne : e ≠ e') :
    (∃ r, e ∈ (tableau c r).optimal) ↔ ¬ c.violations e' ⊂ c.violations e := by
  rw [Tableau.exists_mem_ofPerm_optimal_iff_pair card_option_prominence (toFinset_eq_pair hne),
    con_lt_iff_ssubset]

/-- An elision is the sole optimum under some ranking exactly when the other elision violates a
constraint it does not. -/
theorem exists_optimal_eq_singleton_iff {e e' : ElidedVowel} (hne : e ≠ e') :
    (∃ r, (tableau c r).optimal = {e}) ↔ ¬ c.violations e' ⊆ c.violations e := by
  rw [Tableau.exists_ofPerm_optimal_eq_singleton_iff_pair card_option_prominence
    (toFinset_eq_pair hne) hne, Set.not_subset]
  simp only [con_lt_con_iff]
  exact exists_congr fun _ ↦ and_comm

/-- One elision is the sole optimum under a ranking exactly when some constraint violated only by
the other outranks every constraint violated only by it. -/
theorem optimal_eq_singleton_iff {e e' : ElidedVowel} (hne : e ≠ e') (r) :
    (tableau c r).optimal = {e} ↔ ∃ i ∈ c.violations e', i ∉ c.violations e ∧
      ∀ j ∈ c.violations e, j ∉ c.violations e' → r.Dominates i j := by
  rw [Tableau.optimal_eq_singleton_iff_pair (toFinset_eq_pair hne) hne,
    Tableau.ofPerm_profile_lt_iff_exists_dominates]
  simp only [con_lt_con_iff]
  exact exists_congr fun _ ↦ ⟨fun ⟨⟨h, h'⟩, hr⟩ ↦ ⟨h', h, fun j hj hj' ↦ hr j ⟨hj', hj⟩⟩,
    fun ⟨h', h, hr⟩ ↦ ⟨⟨h, h'⟩, fun j ⟨hj', hj⟩ ↦ hr j hj hj'⟩⟩

/-- A constraint violated only by the other elision and ranked on top makes an elision the sole
optimum. -/
theorem optimal_eq_singleton_of_forall_dominates {e e' : ElidedVowel} (hne : e ≠ e')
    {r : Ranking (Option Prominence) 5} {i : Option Prominence} (hi : i ∉ c.violations e)
    (hi' : i ∈ c.violations e') (hr : ∀ j, j ≠ i → r.Dominates i j) :
    (tableau c r).optimal = {e} :=
  (optimal_eq_singleton_iff hne r).2 ⟨i, hi', hi, fun j hj _ ↦ hr j fun h ↦ hi (h ▸ hj)⟩

/-- The first vowel can elide alone in every context where it begins no morpheme. -/
theorem exists_optimal_eq_first (h : c.stemBody ≠ []) : ∃ r, (tableau c r).optimal = {.first} :=
  (exists_optimal_eq_singleton_iff (e' := .second) (by decide)).2 fun hs ↦
    h (morphemeInitial_mem_violations_first.1 (hs morphemeInitial_mem_violations_second))

private theorem forall_option_prominence {P : Option Prominence → Prop} :
    (∀ i, P i) ↔ P none ∧ P (some .wordInitial) ∧ P (some .lexical) ∧
      P (some .morphemeInitial) ∧ P (some .soleSegment) :=
  ⟨fun h ↦ ⟨h _, h _, h _, h _, h _⟩,
    by rintro ⟨h₀, h₁, h₂, h₃, h₄⟩ (_ | _ | _ | _ | _) <;> assumption⟩

/-- Where the first vowel begins no morpheme, the second vowel elides under some ranking
exactly when the first morpheme is lexical and the second is not. This covers the boundary
between two lexical words, between a lexical and a function word in either order, between a
prefix of more than one segment and a root, and between a root and a suffix. -/
theorem exists_mem_optimal_second_iff (h : c.stemBody ≠ []) :
    (∃ r, .second ∈ (tableau c r).optimal) ↔ c.left = .lexical ∧ c.right = .functional := by
  rw [exists_mem_optimal_iff (e' := .first) (by decide), Set.ssubset_def, Set.subset_def,
    Set.subset_def, forall_option_prominence, forall_option_prominence]
  cases hl : c.left <;> cases hr : c.right <;> simp [h, hl, hr]

/-- After a prefix of one vowel, either vowel can elide alone, since only eliding the first
violates the constraint on morphemes of one segment and only eliding the second violates the
constraint on lexical material, as in the paper's tableaux (15) and (16). -/
theorem exists_optimal_eq_of_vowelPrefix (h : c.stemBody = []) (hs : c.suffixBody ≠ [])
    (hl : c.left = .functional) (hr : c.right = .lexical) (e : ElidedVowel) :
    ∃ r, (tableau c r).optimal = {e} := by
  cases e
  · refine (exists_optimal_eq_singleton_iff (e' := .second) (by decide)).2 fun hsub ↦ ?_
    simpa [hl] using hsub (lexical_mem_violations_second.2 hr)
  · refine (exists_optimal_eq_singleton_iff (e' := .first) (by decide)).2 fun hsub ↦ ?_
    simpa [hs] using hsub (soleSegment_mem_violations_first.2 h)

/-! ### The kinds of juncture of the survey -/

/-- The status of the first word or morpheme at a kind of juncture of the survey. -/
def leftStatus : Data.Hiatus.Juncture → Status
  | .lexicalLexical | .lexicalFunction | .rootSuffix => .lexical
  | .prefixRoot => .functional

/-- The status of the second word or morpheme at a kind of juncture of the survey. -/
def rightStatus : Data.Hiatus.Juncture → Status
  | .lexicalLexical | .prefixRoot => .lexical
  | .lexicalFunction | .rootSuffix => .functional

/-- The boundary at a kind of juncture of the survey. -/
def junctureBoundary : Data.Hiatus.Juncture → Boundary
  | .lexicalLexical | .lexicalFunction => .word
  | .prefixRoot | .rootSuffix => .morpheme

/-- `c.IsOfKind k` holds when the context `c` is a juncture of the survey's kind `k` at which the
first vowel begins no morpheme. -/
structure Context.IsOfKind (c : Context) (k : Data.Hiatus.Juncture) : Prop where
  stemBody_ne_nil : c.stemBody ≠ []
  left : c.left = leftStatus k
  right : c.right = rightStatus k
  boundary : c.boundary = junctureBoundary k

/-- The paper's schematic consonant, the natural class [+consonantal]. -/
def C : Segment := .ofSpecs [(.consonantal, true)]

/-- The paper's schematic vowel, the natural class [+syllabic]. -/
def V : Segment := .ofSpecs [(.syllabic, true)]

/-- The paper's schematic juncture `/CV₁ + V₂C/` at the survey's kind `k`. -/
def schematic (k : Data.Hiatus.Juncture) : Context where
  stemBody := [C]
  v1 := V
  v2 := V
  suffixBody := [C]
  v1_isVowel := by decide
  v2_isVowel := by decide
  left := leftStatus k
  right := rightStatus k
  leftEdge := .word
  boundary := junctureBoundary k

theorem schematic_isOfKind (k : Data.Hiatus.Juncture) : (schematic k).IsOfKind k :=
  ⟨List.cons_ne_nil _ _, rfl, rfl, rfl⟩

/-- At a juncture of the survey's kind `k`, the first vowel can always elide, and the second
exactly when the first word or morpheme is lexical and the second is not. -/
theorem exists_mem_optimal_iff_of_isOfKind {k : Data.Hiatus.Juncture} (hc : c.IsOfKind k)
    {e : ElidedVowel} : (∃ r, e ∈ (tableau c r).optimal) ↔
      e = .first ∨ leftStatus k = .lexical ∧ rightStatus k = .functional := by
  cases e
  · obtain ⟨r, hr⟩ := exists_optimal_eq_first hc.stemBody_ne_nil
    exact iff_of_true ⟨r, hr ▸ Finset.mem_singleton_self _⟩ (.inl rfl)
  · rw [exists_mem_optimal_second_iff hc.stemBody_ne_nil, hc.left, hc.right]
    simp

/-- At the paper's schematic juncture of two lexical words no ranking elides the second vowel, as
in its tableau (10), while before a function word some ranking does, as in its tableau (12). -/
theorem schematic_second :
    (¬ ∃ r, .second ∈ (tableau (schematic .lexicalLexical) r).optimal) ∧
      ∃ r, .second ∈ (tableau (schematic .lexicalFunction) r).optimal := by
  simp only [exists_mem_optimal_iff_of_isOfKind (schematic_isOfKind _)]
  decide

/-- With the constraint on lexical material on top, the first vowel elides after a prefix and
the second before a suffix of any length, the asymmetry within one language that the paper
reports for Chichewa. -/
theorem lexical_on_top {r : Ranking (Option Prominence) 5}
    (hr : ∀ j, j ≠ some .lexical → r.Dominates (some .lexical) j) {c c' : Context}
    (hc : c.IsOfKind .prefixRoot) (hc' : c'.IsOfKind .rootSuffix) :
    (tableau c r).optimal = {.first} ∧ (tableau c' r).optimal = {.second} :=
  ⟨optimal_eq_singleton_of_forall_dominates (e' := .second) (by decide)
      (by simp [hc.left, leftStatus]) (by simp [hc.right, rightStatus]) hr,
    optimal_eq_singleton_of_forall_dominates (e' := .first) (by decide)
      (by simp [hc'.right, rightStatus]) (by simp [hc'.left, leftStatus]) hr⟩

/-- With the constraint on morphemes of one segment over the constraint on lexical material,
and that over the morpheme-initial constraint, the first vowel elides before a suffix of one
segment and the second before a longer one, as in the paper's tableaux (19) and (20). -/
theorem soleSegment_over_lexical {r : Ranking (Option Prominence) 5}
    (h₁ : r.Dominates (some .soleSegment) (some .lexical))
    (h₂ : r.Dominates (some .lexical) (some .morphemeInitial)) (hc : c.IsOfKind .rootSuffix) :
    (tableau c r).optimal = {if c.suffixBody = [] then .first else .second} := by
  obtain ⟨hs, hl, hr, hb⟩ := hc
  simp only [leftStatus, rightStatus, junctureBoundary] at hl hr hb
  split_ifs with hsuf
  · refine (optimal_eq_singleton_iff (e' := .second) (by decide) r).2
      ⟨some .soleSegment, by simpa using hsuf, by simpa using hs, ?_⟩
    rintro (_ | _ | _ | _ | _) hj hj' <;> simp_all
  · refine (optimal_eq_singleton_iff (e' := .first) (by decide) r).2
      ⟨some .lexical, by simp [hl], by simp [hr], ?_⟩
    rintro (_ | _ | _ | _ | _) hj hj' <;> simp_all

/-! ### The survey -/

/-- Every elision the survey reports is one the analysis allows, in that some ranking elides the
reported vowel at a juncture of the reported kind. -/
theorem survey_allowed :
    ∀ row ∈ Data.Hiatus.Casali1997.rows, ∀ c : Context, c.IsOfKind row.juncture →
      ∃ r, row.elided ∈ (tableau c r).optimal := by
  have key : ∀ row ∈ Data.Hiatus.Casali1997.rows, row.elided = .first ∨
      leftStatus row.juncture = .lexical ∧ rightStatus row.juncture = .functional := by
    decide
  exact fun row hrow _ hc ↦ (exists_mem_optimal_iff_of_isOfKind hc).2 (key row hrow)

/-- The survey reports an elision of the second vowel at exactly the kinds of juncture where the
analysis allows one, before a function word and before a suffix. -/
theorem survey_second_iff {k : Data.Hiatus.Juncture} (hc : c.IsOfKind k) :
    (∃ row ∈ Data.Hiatus.Casali1997.rows, row.juncture = k ∧ row.elided = .second) ↔
      ∃ r, .second ∈ (tableau c r).optimal := by
  rw [exists_mem_optimal_iff_of_isOfKind hc]
  cases k <;> decide

end Casali1997
