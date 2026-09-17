import Linglib.Data.Examples.Storment2026
import Linglib.Syntax.Minimalist.Features

/-!
# Storment (2026): Quotative Inversion as Smuggling

This file formalizes [storment-2026]'s analysis of quotative inversion in English and Setswana,
the order in which a quote precedes the verb and the agent follows it, as smuggling: the VP
moves to Spec,VoiceP over the agent, which stays in Spec,vP, and the quotative theme A-moves on
to Spec,TP (`qiSmuggling`, (122)). The paper's four arguments are theorems over its examples
(`Data/Examples/Storment2026.json`): VP complements precede the agent and vP adjuncts follow
it, in both languages (§2, `order_predicted`); the agent is in situ, since Setswana agreement
is the default class 17, English agreement tracks the agent by defective circumvention, the
theme licenses no parasitic gap, raises, and the disjoint form is excluded (§3); the
transitivity constraint follows from T⁰ licensing at most one smuggled DP, so a goal DP blocks
inversion and a PP or adjunct goal does not (§5, `transitivity_predicted`); and locative
inversion shares the mechanism and the constraint (§6). The paper places quotative inversion
in a family of inverse voice constructions (§4.3, `InverseVoiceKind`).

## Implementation notes

* The Voice head of the paper is the smuggling projection and not the introducer of the
  external argument (§4.3); nothing here classifies the verbs of quotative inversion as
  unaccusative, which the paper does not do.
* Heavy NP shift (14) lets an adjunct precede the agent; the row is data and outside the
  ordering theorem.

## References

* [storment-2026]
* [roberts-2010]
* [storment-2025]
-/

namespace Storment2026

open Data.Examples

/-! ### The derivation (§4) -/

/-- The structural positions of the smuggling derivation (122). -/
inductive QIPosition
  /-- The A-movement landing site of the quotative theme. -/
  | specTP
  /-- The landing site of the smuggled VP. -/
  | specVoiceP
  /-- The in-situ position of the agent. -/
  | specvP
  /-- The discourse head bearing the quotation feature that binds the theme. -/
  | discourseQUOT
  deriving DecidableEq, Repr

/-- The positions of the theme, the agent, the VP and the quote's binder (§3.5, §4). -/
structure QIDerivation where
  themePosition : QIPosition
  agentPosition : QIPosition
  vpPosition : QIPosition
  quoteBinder : QIPosition
  deriving DecidableEq, Repr

/-- The paper's derivation of quotative inversion (122). -/
def qiSmuggling : QIDerivation :=
  ⟨.specTP, .specvP, .specVoiceP, .discourseQUOT⟩

/-! ### VP movement over the agent (§2)

Material inside the VP moves with it above the agent; material adjoined to vP stays below. -/

/-- Where a constituent sits relative to the VP. -/
inductive Material
  | vpComplement | vpAdjunct
  deriving DecidableEq, Repr

/-- Where a constituent surfaces relative to the agent. -/
inductive Position
  | beforeAgent | afterAgent
  deriving DecidableEq, Repr

/-- The order the derivation predicts: a VP complement is smuggled to Spec,VoiceP above the
agent, a vP adjunct is not. -/
def predictedPosition (d : QIDerivation) : Material → Position
  | .vpComplement => if d.vpPosition = .specVoiceP ∧ d.agentPosition = .specvP then .beforeAgent
      else .afterAgent
  | .vpAdjunct => .afterAgent

/-- The material and position a row records. -/
def orderOf (ex : LinguisticExample) : Option (Material × Position) := do
  let m ← ex.parse? "material" [("vpComplement", Material.vpComplement), ("vpAdjunct", .vpAdjunct)]
  let p ← ex.parse? "position" [("beforeAgent", Position.beforeAgent), ("afterAgent", .afterAgent)]
  pure (m, p)

/-- (10)–(31): a quotative inversion is acceptable exactly when its constituent surfaces where
the smuggling derivation puts it, complements before the agent and adjuncts after. -/
theorem order_predicted :
    ∀ ex ∈ Examples.all, ex.feature? "heavyNPShift" = none → ∀ o ∈ orderOf ex,
      (ex.judgment = .acceptable ↔ o.2 = predictedPosition qiSmuggling o.1) := by
  decide

/-! ### The agent in situ (§3)

Each position of the derivation predicts a diagnostic. -/

/-- The theme A-moves to Spec,TP, so Setswana agreement is the default class 17 and never the
agent's class (36), (38), whereas a preposed quote without inversion leaves the agent in
Spec,TP and its agreement (65). -/
theorem theme_specTP_setswana_agreement :
    qiSmuggling.themePosition = .specTP ∧
      Examples.ex36.judgment = .acceptable ∧ Examples.ex36_sm10.judgment = .ungrammatical ∧
      Examples.ex38.judgment = .acceptable ∧ Examples.ex38_ke.judgment = .ungrammatical ∧
      Examples.ex65.judgment = .acceptable ∧ Examples.ex65_ga.judgment = .ungrammatical := by
  decide

/-- English agreement tracks the postverbal agent (40), by re-probing past the defective
theme (`defectiveCircumvention`), as it must without inversion (64). -/
theorem theme_specTP_english_agreement :
    qiSmuggling.themePosition = .specTP ∧
      Examples.ex40.judgment = .acceptable ∧ Examples.ex40_sg.judgment = .ungrammatical ∧
      Examples.ex64.judgment = .acceptable ∧ Examples.ex64_sg.judgment = .ungrammatical := by
  decide

/-- The A-moved theme licenses no parasitic gap (62a); the Ā-moved preposed quote does
(62b). -/
theorem theme_specTP_no_parasitic_gap :
    qiSmuggling.themePosition = .specTP ∧
      Examples.ex62a.judgment = .ungrammatical ∧ Examples.ex62b.judgment = .acceptable := by
  decide

/-- The theme raises (67a), (77), as the Ā-moved preposed quote cannot (69a). -/
theorem theme_specTP_raising :
    qiSmuggling.themePosition = .specTP ∧
      Examples.ex67a.judgment = .acceptable ∧ Examples.ex69a.judgment = .ungrammatical ∧
      Examples.ex77.judgment = .acceptable := by
  decide

/-- The agent stays in the vP, so the disjoint form, which needs an empty vP, is excluded
(87). -/
theorem agent_specvP_conjoint :
    qiSmuggling.agentPosition = .specvP ∧
      Examples.ex87.judgment = .acceptable ∧ Examples.ex87_disj.judgment = .ungrammatical := by
  decide

/-- The quote is bound by the discourse head rather than moved: it may stay postverbal (88),
(89), split around the verb and the agent (90), (92), and need not be a constituent or
grammatical (96a), (97a), unlike the fronted phrase of locative inversion (93a). -/
theorem quote_discourseQUOT :
    qiSmuggling.quoteBinder = .discourseQUOT ∧
      Examples.ex88.judgment = .acceptable ∧ Examples.ex89.judgment = .acceptable ∧
      Examples.ex90.judgment = .acceptable ∧ Examples.ex92.judgment = .acceptable ∧
      Examples.ex96a.judgment = .acceptable ∧ Examples.ex97a.judgment = .acceptable ∧
      Examples.ex93a.judgment = .ungrammatical := by
  decide

/-! ### The transitivity constraint (§5)

A smuggled DP is licensed by T⁰, which licenses one argument; Voice⁰ licenses the agent
(133). -/

/-- The smuggled constituent is licensed when it carries at most one DP for T⁰. -/
def Licensed (smuggledDPs : ℕ) : Prop := smuggledDPs ≤ 1

instance (n : ℕ) : Decidable (Licensed n) := inferInstanceAs (Decidable (_ ≤ _))

/-- (125)–(135): an inversion is acceptable exactly when the smuggled constituent carries at
most one DP, a goal DP blocking it and a PP or adjunct goal not, in quotative and locative
inversion alike. -/
theorem transitivity_predicted :
    ∀ ex ∈ Examples.all, ∀ n ∈ ex.parse? "smuggledDPs" [("1", 1), ("2", 2)],
      (ex.judgment = .acceptable ↔ Licensed n) := by
  decide

/-! ### Inverse voice (§4.3, §6)

Quotative inversion joins the constructions the paper analyses as smuggling through VoiceP, and
locative inversion shows the same in-situ agent, raising and transitivity constraint. -/

/-- The constructions the paper groups as inverse voice, analysed as smuggling (§4.3). -/
inductive InverseVoiceKind
  | passive | dativeShift | causative | middle | inverseVoice | quotativeInversion
  | locativeInversion
  deriving DecidableEq, Repr

/-- Locative inversion parallels quotative inversion: it is acceptable with an unergative verb
of motion (136a) and with *arrive* in Setswana (55), raises the same way (138), and obeys the
transitivity constraint (134a), (135). -/
theorem locative_inversion_parallel :
    Examples.ex136a.judgment = .acceptable ∧ Examples.ex55.judgment = .acceptable ∧
      Examples.ex138.judgment = .acceptable ∧ Examples.ex134a.judgment = .ungrammatical ∧
      Examples.ex135.judgment = .ungrammatical := by
  decide

/-! ## §14. Defective circumvention derives the agreement contrast

Storment §3.1.4 (eq. 59): the difference between Setswana QI agreement
(always SM17 default) and English QI agreement (optionally tracks the
postverbal agent) reduces to a single parameter — whether the probe T⁰
is allowed to re-probe past the defective quotative-theme operator.
Roberts's *defective goal* and the *defective-circumvention* operation
are defined inline below (folded in from the former single-consumer
`Minimalist/Probing/`); the theorems then wire them to the QI data.

The theorems abstract over the precise feature bundles and feature-
compatibility predicate — Storment's substantive claim is that the
*operation* is the same and only the `allowReprobe` parameter varies. -/

open Minimalist (FeatureBundle)

/-- A goal `G` is **defective** w.r.t. a probe `P` iff `G`'s formal
    features are a proper subset of `P`'s, so checking is incomplete
    ([roberts-2010], ch. 2; eq. (49) in [storment-2026]). The feature
    comparison is over the bundles' grammatical-feature lists
    (`FeatureBundle.toGramFeatures`). -/
def DefectiveGoal (probe goal : FeatureBundle) : Prop :=
  goal.toGramFeatures ⊆ probe.toGramFeatures ∧
    ∃ f ∈ probe.toGramFeatures, f ∉ goal.toGramFeatures

instance (probe goal : FeatureBundle) : Decidable (DefectiveGoal probe goal) := by
  unfold DefectiveGoal; infer_instance

/-- The empty goal is defective w.r.t. any nonempty probe. -/
theorem DefectiveGoal.empty_of_nonempty (probe : FeatureBundle)
    (h : probe ≠ ⊥) : DefectiveGoal probe ⊥ := by
  refine ⟨List.nil_subset _, ?_⟩
  have hne : probe.toGramFeatures ≠ [] := by
    intro he
    refine h (funext λ t => ?_)
    have hnone := (List.filterMap_eq_nil_iff.mp he) t (by cases t <;> decide)
    cases hp : probe t with
    | absent => rfl
    | unvalued => rw [hp] at hnone; exact absurd hnone (by simp)
    | valued v => rw [hp] at hnone; exact absurd hnone (by simp)
  match hp : probe.toGramFeatures, hne with
  | f :: _, _ => exact ⟨f, List.mem_cons_self, List.not_mem_nil⟩

/-- A defective goal is missing some feature the probe has. -/
theorem DefectiveGoal.exists_missing {probe goal : FeatureBundle}
    (h : DefectiveGoal probe goal) :
    ∃ f ∈ probe.toGramFeatures, f ∉ goal.toGramFeatures := h.2

/-- A defective goal's features are all in the probe. -/
theorem DefectiveGoal.subset {probe goal : FeatureBundle}
    (h : DefectiveGoal probe goal) :
    goal.toGramFeatures ⊆ probe.toGramFeatures := h.1

/-- No goal is defective w.r.t. itself. -/
theorem DefectiveGoal.irrefl (fb : FeatureBundle) : ¬ DefectiveGoal fb fb := by
  intro ⟨_, f, hf, hnf⟩; exact hnf hf

/-- The four outcomes of a probe that may invoke defective circumvention
    ([storment-2025] ch. 2; eq. 59 in [storment-2026]): the probe Agrees
    with a higher defective goal α, then conditionally re-probes past α
    to a lower, more specified goal β. -/
inductive ProbingOutcome where
  /-- α was not defective; α suffices, no re-probe. -/
  | trackHigher
  /-- α defective; re-probe disallowed; default features spell out. -/
  | defaultAgreement
  /-- α defective; re-probe to β succeeded (features compatible). -/
  | trackLower
  /-- α defective; re-probe to β attempted but features conflict; crash. -/
  | featureClash
  deriving DecidableEq, Repr

/-- Defective-circumvention probing, parameterized by `allowReprobe`
    (may the probe search past a defective goal) and `compatible`
    (can circumvention complete without feature conflict). -/
def defectiveCircumvention
    (probe alpha beta : FeatureBundle) (allowReprobe : Bool)
    (compatible : FeatureBundle → FeatureBundle → Bool) : ProbingOutcome :=
  if DefectiveGoal probe alpha then
    if allowReprobe then
      (if compatible alpha beta then .trackLower else .featureClash)
    else .defaultAgreement
  else .trackHigher

/-- A non-defective higher goal never invokes circumvention. -/
theorem defectiveCircumvention_trackHigher_of_nondefective
    (probe alpha beta : FeatureBundle) (allowReprobe : Bool)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (h : ¬ DefectiveGoal probe alpha) :
    defectiveCircumvention probe alpha beta allowReprobe compatible = .trackHigher := by
  unfold defectiveCircumvention; simp [h]

/-- Defective higher goal, re-probe disallowed → default agreement
    (Setswana case). -/
theorem defectiveCircumvention_default_when_no_reprobe
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) :
    defectiveCircumvention probe alpha beta false compatible = .defaultAgreement := by
  unfold defectiveCircumvention; simp [hd]

/-- Defective higher goal, re-probe allowed, β compatible → tracks β
    (English `advise the dieticians`). -/
theorem defectiveCircumvention_tracks_lower
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compatible alpha beta = true) :
    defectiveCircumvention probe alpha beta true compatible = .trackLower := by
  unfold defectiveCircumvention; simp [hd, hc]

/-- Defective higher goal, re-probe allowed, β incompatible → crash
    (English `*ask we`). -/
theorem defectiveCircumvention_clash_on_incompatible
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compatible alpha beta = false) :
    defectiveCircumvention probe alpha beta true compatible = .featureClash := by
  unfold defectiveCircumvention; simp [hd, hc]

/-- The same defective-probing situation produces Setswana's
    obligatory default agreement (no re-probe) and English's optional
    agent-tracking agreement (re-probe with compatible features) — a
    single Bool parameter accounts for the cross-linguistic split. -/
theorem setswana_vs_english_reduces_to_reprobe
    (probe alpha beta : FeatureBundle)
    (compat : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compat alpha beta = true) :
    defectiveCircumvention probe alpha beta false compat = .defaultAgreement ∧
    defectiveCircumvention probe alpha beta true  compat = .trackLower :=
  ⟨defectiveCircumvention_default_when_no_reprobe _ _ _ _ hd,
   defectiveCircumvention_tracks_lower _ _ _ _ hd hc⟩

/-- Storment's English-specific prediction: a 1st/2nd person agent
    (whose phi-features clash with the defective theme's [3]) cannot
    license re-probe — `*"What do we do now?" ask we`. The derivation
    crashes on feature incompatibility (eq. 46, page 14). -/
theorem english_qi_clash_on_incompatible_agent
    (probe alpha beta : FeatureBundle)
    (compat : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compat alpha beta = false) :
    defectiveCircumvention probe alpha beta true compat = .featureClash :=
  defectiveCircumvention_clash_on_incompatible _ _ _ _ hd hc

end Storment2026
