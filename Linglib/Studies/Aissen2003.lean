module

public import Linglib.Semantics.Reference.Prominence
public import Linglib.Fragments.Turkish.ObjectMarking
public import Linglib.Phonology.Constraints.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Aissen 2003: Differential Object Marking
[aissen-2003]

Differential Object Marking: Iconicity vs. Economy. Natural Language &
Linguistic Theory 21(3), 435–483.

The higher in prominence a direct object, the more likely it is to be overtly
case-marked. [aissen-2003] derives this in OT: harmonic alignment of the
animacy and definiteness scales with the relational scale, locally conjoined
with \*Ø_C, yields a fixed subhierarchy of iconicity constraints \*Oj/X & \*Ø_C
("penalize a zero-marked object at prominence X"), and a single economy
constraint \*STRUC_C ("penalize overt case morphology") interpolates into it.
The interpolation point is the grammar: an object is obligatorily marked iff
its iconicity constraint outranks \*STRUC_C, so each of the n + 1 points on an
n-level scale is a language type, and every type marks an upward-closed
segment of the scale. The subhierarchies' derivation by harmonic alignment
(the paper's §§2–3) is taken as given; the constraint lists below are written
directly in their derived ranking.

Language grids (`Reference.Prominence.MarkingPattern`) record *obligatory*
marking — the zone whose constraints strictly dominate \*STRUC_C. The paper's
optional zones (constraints that rerank with \*STRUC_C, stochastically in
Boersma's sense) are noted in docstrings but not represented.

## Main results

- `dom_monotonicity_universal`, `dom_obligatory_zone_upperSet` — the paper's
  (33b): every attested obligatory-marking zone is an upper set in Figure 4's
  product prominence order.
- `tableaux_1_2` — the Hebrew/Turkish minimal pair on specific indefinites.
- `figure2_typology` / `figure2_languages` — the six interpolation points on
  the definiteness subhierarchy generate exactly the six cutoff systems,
  matched type-for-type to Kalkatungu, Catalan, Pitjantjatjara, Hebrew,
  Turkish, and Written Japanese.
- `figure3_typology` / `figure3_languages` — likewise for the animacy scale.
- `two_dimensional_systems` — Hindi and both stages of Spanish need both
  scales.
-/

@[expose] public section

namespace Aissen2003

open Reference.Prominence
open Constraints OptimalityTheory

/-! ### The DOM systems of the paper

The one-dimensional definiteness systems are the six interpolation types of
Figure 2, one cited language each; Ritharngu and Dhargari instantiate the
clean animacy types of Figure 3 (Yiddish and Sinhalese sit at its
optional-zone points). Hindi, Persian, and the two stages of Spanish are the
two-dimensional systems of §5. -/

section DOMLanguages

/-- Catalan marks only strong personal-pronoun objects, with *a* (Figure 2, §4.1). -/
def catalanDOM : MarkingPattern := .definitenessAtLeast .personalPronoun

/-- Pitjantjatjara case-marks only pronoun and proper-name objects (Figure 2). -/
def pitjantjatjaraDOM : MarkingPattern := .definitenessAtLeast .properName

/-- Hebrew has *ʔet* obligatorily on pronoun, proper-name and definite objects (Figure 2,
§4.1). -/
def hebrewDOM : MarkingPattern := .definitenessAtLeast .definite

/-- Turkish marks every object but the non-specific ones, so unlike Hebrew it marks specific
indefinites obligatorily (Figure 2, Tableaux 1–2); the pattern is the fragment's. -/
def turkishDOM : MarkingPattern := Turkish.ObjectMarking.accusative

/-- Persian has *-rā* obligatorily on all definites regardless of animacy and, exactly as in
Turkish, on specific indefinites (§5.3). Animacy enters only in the optional zone, the
non-specific indefinites, so the obligatory grid is one-dimensional. -/
def persianDOM : MarkingPattern := .definitenessAtLeast .indefiniteSpecific

/-- Written Japanese case-marks all objects, DOM extended to the whole scale, "thereby
ceasing to be differential" (Figures 2–3, fn. 33). -/
def writtenJapaneseDOM : MarkingPattern := .definitenessAtLeast .nonSpecific

/-- Ritharngu case-marks all human objects obligatorily; the "some animates" spillover the
paper reports is in the optional zone (Figure 3). -/
def ritharnguDOM : MarkingPattern := .animacyAtLeast .human

/-- Dhargari case-marks all animate objects (Figure 3). -/
def dhargariDOM : MarkingPattern := .animacyAtLeast .animate

/-- The pattern with no DOM marks no object, Kalkatungu in Figures 2–3, where \*STRUC_C
dominates the whole subhierarchy. It is the neutral no-marking baseline other studies
consume. -/
def noDOM : MarkingPattern := fun _ _ ↦ false

/-- Hindi marks with *-ko* (§5.2, Figure 7). It is obligatory on human objects down to specific
indefinites and on animate pronouns and proper names, which "assimilate to the human class";
optional on human non-specifics, animate definites and below, and inanimate definites; and
excluded on other inanimates. -/
def hindiDOM : MarkingPattern := fun a d ↦
  match a with
  | .human     => decide (DefinitenessLevel.indefiniteSpecific ≤ d)
  | .animate   => decide (DefinitenessLevel.properName ≤ d)
  | .inanimate => false

/-- The Spanish of the Cantar de Mio Cid has *a* obligatorily on exactly the personal pronouns
and proper names of humans and animals (§5.1, Figure 5), and optionally on human common
NPs and geographic proper names. -/
def cmcSpanishDOM : MarkingPattern := fun a d ↦
  decide (AnimacyLevel.animate ≤ a) && decide (DefinitenessLevel.properName ≤ d)

/-- Modern Spanish is the CMC system with \*STRUC_C demoted below the human-definite and
human-specific constraints, so *a* is now also obligatory with definite and specific human
objects (§5.4, Figure 9). The obligatory grid coincides with Hindi's; the two differ in their
optional zones (Figure 7 against Figure 9). -/
def spanishDOM : MarkingPattern := fun a d ↦
  match a with
  | .human     => decide (DefinitenessLevel.indefiniteSpecific ≤ d)
  | .animate   => decide (DefinitenessLevel.properName ≤ d)
  | .inanimate => false

end DOMLanguages

/-- The DOM systems cited in the paper. -/
def allDOMPatterns : List MarkingPattern :=
  [catalanDOM, pitjantjatjaraDOM, hebrewDOM, turkishDOM, persianDOM,
   writtenJapaneseDOM, ritharnguDOM, dhargariDOM, hindiDOM, cmcSpanishDOM,
   spanishDOM, noDOM]

/-! ### Monotonicity: the (33b) universal -/

/-- Every attested DOM system is monotone, since no language obligatorily marks a less
prominent object while leaving a more prominent one unmarked. -/
theorem dom_monotonicity_universal :
    ∀ p ∈ allDOMPatterns, p.MonotoneP := by decide

/-- In every attested system the obligatorily marked cells form an upper set in the product
prominence order of Figure 4, which is (33b) order-theoretically. -/
theorem dom_obligatory_zone_upperSet :
    ∀ p ∈ allDOMPatterns,
      IsUpperSet {c : AnimacyLevel × DefinitenessLevel | p c.1 c.2 = true} :=
  fun p hp ↦ p.monotoneP_iff_isUpperSet.mp (dom_monotonicity_universal p hp)

/-- The Figure 2 and §5.3 systems are animacy-blind. -/
theorem definiteness_systems_one_dimensional :
    ∀ p ∈ [catalanDOM, pitjantjatjaraDOM, hebrewDOM, turkishDOM, persianDOM,
      writtenJapaneseDOM], p.DefinitenessOnly := by decide

/-- The Figure 3 systems are definiteness-blind. -/
theorem animacy_systems_one_dimensional :
    ∀ p ∈ [ritharnguDOM, dhargariDOM], p.AnimacyOnly := by decide

/-- Hindi and both stages of Spanish are genuinely two-dimensional (§5), since neither scale
alone determines the obligatory zone. -/
theorem two_dimensional_systems :
    ∀ p ∈ [hindiDOM, cmcSpanishDOM, spanishDOM],
      ¬ p.AnimacyOnly ∧ ¬ p.DefinitenessOnly := by decide

/-! ### The interpolation engine

The paper evaluates candidates per input: for an object at prominence level
`ℓ`, GEN offers a case-marked and a zero-marked parse. \*Oj/ℓ & \*Ø_C
penalizes the zero-marked parse; \*STRUC_C penalizes the case-marked one. A
grammar linearizes the fixed subhierarchy with \*STRUC_C interpolated, and
the winner at `ℓ` is the marked parse iff `ℓ`'s iconicity constraint
outranks \*STRUC_C. -/

variable {L : Type} [DecidableEq L]

/-- \*STRUC_C penalizes overt case morphology, so the case-marked parse violates it.
Candidates are level–marking pairs, and `true` is the marked parse. -/
def starStruc : Constraint (L × Bool) := Constraint.binary (·.2 = true)

/-- \*Oj/ℓ & \*Ø_C is violated by a zero-marked object at level `ℓ`. -/
def starZero (ℓ : L) : Constraint (L × Bool) :=
  Constraint.binary (fun c ↦ c.1 = ℓ ∧ c.2 = false)

/-- The iconicity subhierarchy of a scale (most prominent level first) with
    \*STRUC_C interpolated at position `k`. -/
def interpolation (levels : List L) (k : Nat) : List (Constraint (L × Bool)) :=
  (levels.map starZero).insertIdx k starStruc

/-- Whether the case-marked parse wins for an object at level `ℓ`. -/
def markedWins (ranking : List (Constraint (L × Bool))) (ℓ : L) : Bool :=
  decide ((Tableau.ofRanking [(ℓ, true), (ℓ, false)] ranking (by simp)).optimal
    = {(ℓ, true)})

/-- Tableaux 1–2 evaluate a specific indefinite object. In Hebrew \*STRUC_C outranks
\*Oj/Spec & \*Ø_C and the zero parse wins; in Turkish the ranking is reversed and the marked
parse wins. -/
theorem tableaux_1_2 :
    markedWins (interpolation DefinitenessLevel.all 3) .indefiniteSpecific = false ∧
    markedWins (interpolation DefinitenessLevel.all 4) .indefiniteSpecific = true := by
  constructor <;> decide

/-- The six interpolation points on the definiteness subhierarchy of Figure 2 generate exactly
the six cutoff systems, and no non-monotone pattern arises. -/
theorem figure2_typology :
    (List.range 6).map
        (fun k ↦ DefinitenessLevel.all.map (markedWins (interpolation DefinitenessLevel.all k)))
      = [[false, false, false, false, false],
         [true,  false, false, false, false],
         [true,  true,  false, false, false],
         [true,  true,  true,  false, false],
         [true,  true,  true,  true,  false],
         [true,  true,  true,  true,  true]] := by decide

/-- Figure 2 cites "one language for each of the possible DOM types", and each cited
language's obligatory grid is its interpolation type's predicted pattern. -/
theorem figure2_languages :
    (∀ a d, noDOM a d = markedWins (interpolation DefinitenessLevel.all 0) d) ∧
    (∀ a d, catalanDOM a d = markedWins (interpolation DefinitenessLevel.all 1) d) ∧
    (∀ a d, pitjantjatjaraDOM a d = markedWins (interpolation DefinitenessLevel.all 2) d) ∧
    (∀ a d, hebrewDOM a d = markedWins (interpolation DefinitenessLevel.all 3) d) ∧
    (∀ a d, turkishDOM a d = markedWins (interpolation DefinitenessLevel.all 4) d) ∧
    (∀ a d, writtenJapaneseDOM a d = markedWins (interpolation DefinitenessLevel.all 5) d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Persian's obligatory grid realizes the same interpolation type as Turkish's, since specific
indefinites "require the suffix -rā, exactly as ... the accusative suffix in Turkish"
(§5.3). -/
theorem persian_same_type_as_turkish :
    ∀ a d, persianDOM a d = turkishDOM a d := by decide

/-- The four interpolation points on the animacy subhierarchy of Figure 3 generate exactly the
four cutoff systems. -/
theorem figure3_typology :
    (List.range 4).map
        (fun k ↦ AnimacyLevel.all.map (markedWins (interpolation AnimacyLevel.all k)))
      = [[false, false, false],
         [true,  false, false],
         [true,  true,  false],
         [true,  true,  true]] := by decide

/-- Figure 3's cleanly cutoff languages match their types, Kalkatungu with none, Ritharngu
with the humans, Dhargari with the animates, and Written Japanese and Dhalandji with all. -/
theorem figure3_languages :
    (∀ a d, noDOM a d = markedWins (interpolation AnimacyLevel.all 0) a) ∧
    (∀ a d, ritharnguDOM a d = markedWins (interpolation AnimacyLevel.all 1) a) ∧
    (∀ a d, dhargariDOM a d = markedWins (interpolation AnimacyLevel.all 2) a) ∧
    (∀ a d, writtenJapaneseDOM a d = markedWins (interpolation AnimacyLevel.all 3) a) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- "This account predicts that the reverse is not found, e.g., languages in which only
inanimates are case-marked", since every interpolation grammar marks an upward-closed
segment of the scale. -/
theorem no_reversed_system :
    ∀ k < 4, ∀ a a' : AnimacyLevel, a ≤ a' →
      markedWins (interpolation AnimacyLevel.all k) a = true →
      markedWins (interpolation AnimacyLevel.all k) a' = true := by decide

end Aissen2003
