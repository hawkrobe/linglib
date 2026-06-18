import Linglib.Semantics.Modality.Exclusion
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.Mandarin.Conditionals
import Linglib.Studies.Iatridou2000
import Linglib.Data.Examples.Mizuno2024

/-!
# [mizuno-2024] — Strategies for Anderson Conditionals

Teruyuki Mizuno (2024), "Strategies for Anderson Conditionals: Their Implications for
the Typology of O-Marking and X-Marking", *Semantics and Pragmatics* 17(8): 1–14.
[anderson-1951] [schlenker-2004] [von-fintel-iatridou-2023] [iatridou-2000]

Anderson conditionals ([anderson-1951]) argue *for* the truth of their antecedent
("If Jones had taken arsenic, he would show exactly the symptoms he is showing — so he
took arsenic"). Mizuno shows that English must X-mark them (O-marking is trivial),
whereas Japanese and Mandarin must O-mark them (X-marking — Past -ta, perfective le —
forces a counterfactual reading). Both strategies avoid triviality by **expanding** the
modal domain `D ⊆ D⁺`; Mizuno adopts the *expansion* analysis of X-marking (fn 6, citing
[mackay-2015] against the [iatridou-2000] / [schulz-2014] exclusion analysis), and
analyzes Japanese O-marking as a Historical-Present perspectival shift ([schlenker-2004],
[ogihara-2014], [mizuno-kaufmann-2019]) that expands `D` by shifting the evaluation time
backward under branching time.

## Main results

* `english_japanese_discrepancy` — English X-marks, Japanese O-marks: the typological twist.
* `complementary_strategy` — in each language exactly one of the two markings is felicitous.
* `attested_felicity_matches_strategy` — the attested judgments fit the per-language strategy.
* `flv_anderson_correlation` — Anderson X-marking ⇔ Future-Less-Vivid X-marking (§4.2).
* `oMarking_anderson_trivial` / `expansion_resolves_anderson` / `expanded_anderson_informative`
  — the triviality puzzle and its resolution by domain expansion, on the Jones-arsenic scenario.
* `hp_expands_jones_domain` — Japanese HP: the backward time shift enlarges the live-possibility domain.

The glossed stimuli live in `Data/Examples/Mizuno2024.json` (generated module
`Mizuno2024.Examples`); the substrate (`Semantics.Modality.Exclusion`,
`Semantics.Tense.ConditionalShift`, both of which cite [mizuno-2024]) supplies the
domain-expansion machinery instantiated here.
-/

namespace Mizuno2024

open Semantics.Modality.Exclusion
  (MarkingStrategy oMarking_trivial domain_expansion_avoids_triviality
   expanded_conditional_informative)
open Tense.ConditionalShift
  (trivialConsequent nonTrivialConsequent domainRestrictedConditional history_monotone_set)
open Data.Examples (LinguisticExample)

/-! ### Languages and Anderson-conditional strategies

The X-marking / O-marking labels are [von-fintel-iatridou-2023]'s typological vocabulary
(the theory-neutral `MarkingStrategy` substrate enum). Mizuno's claim is *which* of the two
each language uses for a felicitous Anderson conditional. -/

/-- The three languages in [mizuno-2024]. -/
inductive Language where
  | english | japanese | mandarin
  deriving DecidableEq, Repr

/-- The marking strategy each language uses for *felicitous* Anderson conditionals
    ([mizuno-2024], §2–3): English X-marks (ex. 1a); Japanese and Mandarin O-mark
    (ex. 4a -ru, ex. 13a without final le). -/
def andersonStrategy : Language → MarkingStrategy
  | .english => .xMarking
  | .japanese => .oMarking
  | .mandarin => .oMarking

/-- Whether X-marking is available for Future-Less-Vivid conditionals ([mizuno-2024], §4.2).
    English allows it (ex. 8); Japanese Past -ta (ex. 10) and Mandarin perfective le
    (ex. 12) instead induce strong counterfactuality, blocking the FLV reading. -/
def flvXMarkingAvailable : Language → Bool
  | .english => true
  | .japanese => false
  | .mandarin => false

/-- A marking is felicitous for an Anderson conditional in a language iff it is that
    language's Anderson strategy. Derived from `andersonStrategy`, not stipulated:
    English requires X-marking (O-marking is trivial, ex. 2); Japanese/Mandarin require
    O-marking (X-marking is counterfactual, ex. 4a #ta / ex. 13a #le). -/
def felicitousForAnderson (lang : Language) (m : MarkingStrategy) : Prop :=
  m = andersonStrategy lang

theorem english_xMarks : andersonStrategy .english = .xMarking := rfl
theorem japanese_oMarks : andersonStrategy .japanese = .oMarking := rfl
theorem mandarin_oMarks : andersonStrategy .mandarin = .oMarking := rfl

/-- The core typological twist ([mizuno-2024], §3): English and Japanese pick *opposite*
    strategies for Anderson conditionals. -/
theorem english_japanese_discrepancy :
    andersonStrategy .english ≠ andersonStrategy .japanese := by decide

/-- The two strategies are in complementary distribution: in every language exactly one
    of X-marking / O-marking is felicitous for an Anderson conditional ([mizuno-2024], §3). -/
theorem complementary_strategy (lang : Language) :
    felicitousForAnderson lang .xMarking ↔ ¬ felicitousForAnderson lang .oMarking := by
  unfold felicitousForAnderson; cases lang <;> decide

/-! ### Attested minimal pairs (the empirical anchor)

The glossed stimuli live in `Data/Examples/Mizuno2024.json` → generated module
`Mizuno2024.Examples` (ex. 1a, 2, 4a, 7a, 13a for Anderson; 8, 9, 11 for FLV). The X/O
minimal pairs within one numbered example (4a's -ru / -ta, 13a's ∅ / le) are recorded as
the felicitous `primaryText` plus the infelicitous `alternatives` entry; the realized
strategy is tagged in `paperFeatures`. The adapters below are interpretation-light: they
read the `strategy` / `construction` tags and the recorded judgments, never parsing the
surface forms. -/

/-- Felicity as a Bool: an Anderson conditional counts as felicitous iff fully acceptable. -/
def isFelicitous : Features.Judgment → Bool
  | .acceptable => true
  | _ => false

/-- Map a Glottocode to the [mizuno-2024] `Language` (English, Japanese, Mandarin). -/
def ofGlottocode : String → Option Language
  | "stan1293" => some .english
  | "nucl1643" => some .japanese
  | "mand1415" => some .mandarin
  | _ => none

/-- Value of a `paperFeatures` key, if present. -/
def featureOf (e : LinguisticExample) (k : String) : Option String :=
  (e.paperFeatures.find? (·.1 == k)).map (·.2)

/-- Parse the `strategy` tag into a `MarkingStrategy`. -/
def ofStrategyTag : String → Option MarkingStrategy
  | "x-marking" => some .xMarking
  | "o-marking" => some .oMarking
  | _ => none

/-- The complementary marking strategy ([mizuno-2024], §2: "O-marking [is] generally
    defined as the absence of X-marking"). The infelicitous alternative in a minimal pair
    realizes the complement of the felicitous `primaryText`'s strategy. -/
def otherMarking : MarkingStrategy → MarkingStrategy
  | .xMarking => .oMarking
  | .oMarking => .xMarking

/-- Project the Anderson rows from an example: the `primaryText`'s (strategy, felicity),
    plus — for a minimal-pair example — the complementary strategy paired with the
    alternative's judgment. Non-Anderson examples and unrecognized language/strategy tags
    yield no rows. -/
def andersonRows (e : LinguisticExample) : List (Language × MarkingStrategy × Bool) :=
  match ofGlottocode e.language, featureOf e "construction",
        (featureOf e "strategy").bind ofStrategyTag with
  | some lang, some "anderson", some m =>
      (lang, m, isFelicitous e.judgment) ::
        e.alternatives.map (fun a => (lang, otherMarking m, isFelicitous a.2))
  | _, _, _ => []

/-- All attested Anderson rows, projected from the generated example data. -/
def attestedAndersonRows : List (Language × MarkingStrategy × Bool) :=
  Examples.all.flatMap andersonRows

/-- The attested judgments fit the per-language strategy: every projected row is
    felicitous iff its marking is the language's `andersonStrategy` (i.e.
    `felicitousForAnderson`). Derived from the JSON data, not stipulated — flipping any
    judgment in `Data/Examples/Mizuno2024.json` breaks this. -/
theorem attested_felicity_matches_strategy :
    ∀ r ∈ attestedAndersonRows, (r.2.2 = true ↔ r.2.1 = andersonStrategy r.1) := by decide

/-- The projection is non-vacuous and covers all six cells: both markings are attested in
    every language (English via ex. 1a / 2, Japanese and Mandarin via the 4a / 13a minimal
    pairs and 7a). -/
theorem attestedAndersonRows_complete :
    (.english, .xMarking, true) ∈ attestedAndersonRows ∧
    (.english, .oMarking, false) ∈ attestedAndersonRows ∧
    (.japanese, .oMarking, true) ∈ attestedAndersonRows ∧
    (.japanese, .xMarking, false) ∈ attestedAndersonRows ∧
    (.mandarin, .oMarking, true) ∈ attestedAndersonRows ∧
    (.mandarin, .xMarking, false) ∈ attestedAndersonRows := by decide

/-! ### The Future-Less-Vivid correlation (§4.2) -/

/-- [mizuno-2024], §4.2: X-marking for Anderson conditionals and X-marking for FLV
    conditionals stand or fall together. Across English / Japanese / Mandarin, a language
    X-marks Anderson conditionals iff X-marking is available for its FLV conditionals.
    An empirical generalization (Mizuno speculates a [chierchia-1998] Blocking Principle:
    covert HP is blocked where overt X-marking is available), not a definitional identity —
    the two functions are recorded independently. -/
theorem flv_anderson_correlation (lang : Language) :
    (andersonStrategy lang).hasXMarking = flvXMarkingAvailable lang := by
  cases lang <;> rfl

/-- Cross-reference to [iatridou-2000]: English has X-marking available for FLV
    ([mizuno-2024], §4.2), and Iatridou independently classifies the FLV as carrying a
    single ExclF (past) layer. The morphological count is Iatridou's; Mizuno cites
    [iatridou-2000] for the FLV connection without adopting her exclusion analysis. -/
theorem english_flv_matches_iatridou :
    flvXMarkingAvailable .english = true ∧ Iatridou2000.CounterfactualType.flv.exclFCount = 1 :=
  ⟨rfl, rfl⟩

/-- FLV X-marking availability read from the example data (`flv_xmarking` tag). -/
def flvAvailableTag (e : LinguisticExample) : Option Bool :=
  match featureOf e "flv_xmarking" with
  | some "available"   => some true
  | some "unavailable" => some false
  | _                  => none

/-- The recorded FLV availability (ex. 8 English, ex. 9–10 Japanese, ex. 11–12 Mandarin)
    matches the `flvXMarkingAvailable` generalization the §4.2 correlation runs on. -/
theorem flv_examples_match_generalization :
    flvAvailableTag Examples.en8 = some (flvXMarkingAvailable .english) ∧
    flvAvailableTag Examples.ja9 = some (flvXMarkingAvailable .japanese) ∧
    flvAvailableTag Examples.ma11 = some (flvXMarkingAvailable .mandarin) := by decide

/-! ### The triviality puzzle and its resolution by domain expansion

[mizuno-2024]'s core semantic argument (§2): an Anderson consequent is an observed *fact*,
true at every world in the non-expanded domain `D` of live possibilities, so over `D` the
conditional is trivially true and uninformative. Both strategies fix this by expanding `D`
to `D⁺ ⊋ D` containing a world where the consequent fails. Mizuno adopts the *expansion*
analysis of X-marking (fn 6, citing [mackay-2015] against [iatridou-2000] exclusion).

We instantiate the substrate's expansion machinery (`Semantics.Modality.Exclusion`,
`Semantics.Tense.ConditionalShift`) on the Jones-arsenic scenario: `World = Bool`, where
`true` is a world in which Jones shows the arsenic symptoms (the observed fact) and `false`
one in which he does not. -/

/-- The Anderson consequent: Jones shows the (arsenic) symptoms. -/
def showsSymptoms : Bool → Prop := fun w => w = true

/-- The non-expanded domain `D` of live possibilities: Jones is assumed to show the
    symptoms, so the only live world is the symptom-showing one. -/
def liveDomain : Set Bool := {true}

/-- The expanded domain `D⁺`, including the non-live world where the symptoms are absent. -/
def expandedDomain : Set Bool := Set.univ

/-- Over `D`, the consequent is trivial — it is an observed fact holding at every live
    world ([mizuno-2024], §2). -/
theorem consequent_trivial_over_live : trivialConsequent liveDomain showsSymptoms := by
  intro w hw
  simp only [liveDomain, Set.mem_singleton_iff] at hw
  simpa [showsSymptoms] using hw

/-- O-marking without expansion: the Anderson conditional is vacuously true over `D` for
    *any* antecedent — Mizuno's triviality puzzle, the infelicity of ex. (2). -/
theorem oMarking_anderson_trivial (antecedent : Bool → Prop) :
    domainRestrictedConditional liveDomain antecedent showsSymptoms :=
  oMarking_trivial liveDomain antecedent showsSymptoms consequent_trivial_over_live

/-- Expansion resolves triviality: `D⁺` contains the symptom-absent `false`-world, so the
    consequent is non-trivial over `D⁺` ([mizuno-2024], §2). -/
theorem expansion_resolves_anderson :
    nonTrivialConsequent expandedDomain showsSymptoms :=
  domain_expansion_avoids_triviality liveDomain expandedDomain showsSymptoms
    (by simp only [expandedDomain]; exact Set.subset_univ _)
    consequent_trivial_over_live
    false (by simp only [expandedDomain]; exact Set.mem_univ _)
    (by simp only [showsSymptoms]; decide)

/-- The payoff ([mizuno-2024], §2: "one can make a meaningful, contingent claim"): an
    Anderson conditional that holds over the expanded `D⁺` is informative — its antecedent
    genuinely excludes the symptom-absent world. -/
theorem expanded_anderson_informative (antecedent : Bool → Prop)
    (h : domainRestrictedConditional expandedDomain antecedent showsSymptoms) :
    ∃ w ∈ expandedDomain, ¬ antecedent w :=
  expanded_conditional_informative expandedDomain antecedent showsSymptoms
    expansion_resolves_anderson h

/-! ### Japanese O-marking: HP expansion under branching time

[mizuno-2024]'s analysis of why Japanese O-marking (Non-Past) escapes triviality without
X-marking (§3.3–3.4): the Historical-Present shift moves the evaluation time backward, and
since live possibilities monotonically shrink as time develops ([condoravdi-2002]'s
backward-closed history), the earlier-time domain is *larger* — domain expansion without
counterfactual morphology. -/

/-- A backward-closed history witnessing HP expansion: a world is a live alternative to
    `s` iff it is `s`'s own world, or `s`'s time is at or before `0`. Earlier times have
    strictly more alternatives. -/
def historyJones : HistoricalAlternatives Bool ℤ :=
  fun s => { w | w = s.world ∨ s.time ≤ 0 }

theorem historyJones_backwardsClosed : historyJones.backwardsClosed := by
  intro w w' t t' hle hmem
  simp only [historyJones, Set.mem_setOf_eq] at hmem ⊢
  rcases hmem with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hle h)

/-- The HP backward shift enlarges the domain of live possibilities: the symptom-absent
    world `false` is *not* a live alternative at the utterance time (`t = 1`) but *is* one
    at the HP-shifted earlier time (`t = 0`), so the expanded domain contains a
    consequent-failing world — exactly [mizuno-2024]'s argument for Japanese (§3.3–3.4).
    The subset direction is the substrate's `history_monotone_set`. -/
theorem hp_expands_jones_domain :
    historyJones ⟨true, 1⟩ ⊆ historyJones ⟨true, 0⟩ ∧
      false ∈ historyJones ⟨true, 0⟩ ∧ false ∉ historyJones ⟨true, 1⟩ := by
  refine ⟨history_monotone_set historyJones historyJones_backwardsClosed ⟨true, 1⟩ 0 (by decide),
    ?_, ?_⟩
  · simp only [historyJones, Set.mem_setOf_eq]; decide
  · simp only [historyJones, Set.mem_setOf_eq]; decide

/-! ### Fragment marker connection -/

-- Japanese Anderson conditionals use -(r)eba, which marks both HC and PC (unlike HC-only
-- -ra): with Non-Past consequent → Anderson, with Past consequent → counterfactual.
#guard Japanese.Conditionals.eba.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

-- Mandarin Anderson conditionals use the general-purpose marker ruguo; the X/O-marking
-- distinction is carried by consequent-final le, not by the conditional marker.
#guard Mandarin.Conditionals.ruguo.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

end Mizuno2024
