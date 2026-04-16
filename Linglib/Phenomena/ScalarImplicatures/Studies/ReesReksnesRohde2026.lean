import Linglib.Theories.Pragmatics.RelevanceTheory.Comprehension
import Linglib.Theories.Pragmatics.RelevanceTheory.CognitiveEffects
import Linglib.Theories.Pragmatics.RelevanceTheory.Ostension

/-!
# Rees, Reksnes & Rohde (2026) @cite{rees-reksnes-rohde-2026}

Why are you telling me this? The availability and timing of relevance
inferences. *Journal of Memory and Language* 148, 104741.

@cite{sperber-wilson-1986} @cite{bergen-grodner-2012}
@cite{kravtchenko-demberg-2022} @cite{bott-noveck-2004}

## Key contribution

Identifies **relevance inferences**: pragmatic inferences from *trivial*
utterances where listeners reason about WHY the speaker chose to speak.
Unlike scalar implicatures, these are not triggered by a weaker scalar
term — there is no scale to search, and no stronger alternative the
speaker chose not to use. Instead, the speaker's decision to produce a
trivial utterance like "the library walls are blue" violates expectations
of relevance, prompting the listener to infer enriched content (e.g.,
*the walls used to be a different colour*).

This distinction from scalar implicatures is the paper's central
theoretical contribution: the phenomenon is about *why did the speaker
choose to speak at all?*, not *why did the speaker use a weaker term?*.

## Formalization strategy

We model relevance inferences using RT's comprehension procedure
(@cite{sperber-wilson-1986}). A trivial utterance's literal interpretation
fails the relevance threshold when the speaker is knowledgeable (its
content is already expected), forcing the comprehension procedure to
search further. The enriched interpretation ("something has changed")
passes threshold when warranted by speaker knowledge.

### Speaker factors as effect modulation

Both manipulated factors — Speaker Knowledge and Speaker Style — modulate
the EFFECTS of the enriched interpretation, not the threshold:

- **Speaker Knowledge** (Exps 1–4): A knowledgeable speaker's trivial
  utterance produces stronger contextual implications for the "changed"
  interpretation, because the inference is warranted (the speaker would
  notice changes to a familiar location). Cf. @cite{bergen-grodner-2012}:
  speaker knowledge modulates SI computation in the same direction.

- **Speaker Style** (Exp 2): A quiet speaker's decision to speak amplifies
  the effects of the enriched interpretation — if they bothered to
  mention it, there must be a strong reason. This connects to
  @cite{burnett-2019}'s persona framework.

Both are instances of **effect strengthening**, the monotonicity property
of RT's comprehension procedure (`RTScenario.selects_of_strengthened_effects`).

### Emphasis Cue null effect (Exp 1)

"Hey, guess what" does not significantly increase inference rates. This
follows from RT's communicative principle: every act of ostensive
communication already presumes its own optimal relevance
(@cite{sperber-wilson-1986}, 2nd ed). An explicit emphasis cue is
redundant with the ostensive act of speaking itself.

### Processing cost (Exps 3–4)

Relevance inferences are costly to compute: cross-experiment analysis of
Exps 3–4 shows inference-endorsing "Yes" responses (Exp 4, where "Yes" =
inference) are slower than non-inference "Yes" responses (Exp 3, where
"Yes" = no inference). Cf. @cite{bott-noveck-2004}: scalar implicature
computation shows the same response-time cost pattern.

### Graded predictions

RT's comprehension procedure is qualitative (binary selection), but the
monotonicity theorem is independent of threshold shape: it holds for
both a step function (qualitative RT) and any sigmoid extension (graded
RT). The ordinal predictions — Speaker Knowledge and Speaker Style each
strengthen the enriched interpretation — produce graded proportion
predictions under any noisy-threshold model.

### Relation to atypicality inferences

@cite{kravtchenko-demberg-2022} found that informationally redundant
utterances (explicitly mentioning a script-typical action like "eating
at a restaurant") trigger atypicality inferences — listeners infer the
action was atypical for the character. Rees et al.'s relevance inferences
extend this: even non-redundant but TRIVIAL utterances trigger enriched
inferences about why the speaker chose to speak.

## Data summary (4 experiments, N = 777)

- Exp 1 (N=197): Speaker Knowledge significant (p<.001); Emphasis Cue n.s.
- Exp 2 (N=192): Speaker Knowledge significant (p<.001); Speaker Style
  significant (p=.001); Knowledge × Style interaction (p=.026) driven
  by increased inferencing in unfamiliar+quiet condition
- Exp 3 (N=194): Speaker Knowledge replicates; response time pattern
  numerically consistent with processing cost but not statistically robust
- Exp 4 (N=194): Speaker Knowledge replicates; cross-experiment analysis
  with Exp 3 confirms inference computation is costly
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.Studies.ReesReksnesRohde2026

open Pragmatics.RelevanceTheory

-- ============================================================================
-- §1. Interpretation Space
-- ============================================================================

/-- Candidate interpretations for a trivial utterance like
    "The library walls are blue."

    A listener can:
    (a) accept the literal content transparently — "the walls are blue"
    (b) infer that the situation has changed — relevance inference
    (c) treat the utterance as a social gesture with no enrichment

    The paper's experimental task is binary ("same" vs "different"), but
    the three-candidate decomposition captures the RT comprehension
    procedure's search space: the procedure considers candidates in
    accessibility order and stops at the first that passes threshold.
    The phatic interpretation is maximally costly to access and never
    selected, but its presence in the candidate set reflects that
    phatic communication is always available as a last resort
    (@cite{crystal-1991}, @cite{zegarac-clark-1999}). -/
inductive TrivialInterp where
  /-- Transparent acceptance: "The walls are blue" (no enrichment) -/
  | literal
  /-- Relevance inference: "The walls USED TO BE different" -/
  | changed
  /-- Phatic: social gesture, no contentful enrichment -/
  | phatic
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. Experimental Data
-- ============================================================================

/-- Sample size per experiment (after exclusions). -/
def expN : Fin 4 → Nat
  | 0 => 197  -- Exp 1
  | 1 => 192  -- Exp 2
  | 2 => 194  -- Exp 3
  | 3 => 194  -- Exp 4

/-- Total participants across all four experiments. -/
theorem totalN : (List.map expN [0, 1, 2, 3]).sum = 777 := by native_decide

/-- Speaker Knowledge was significant (p < .001) in all four experiments. -/
def knowledgeSignificant : Fin 4 → Bool := λ _ => true

/-- The direction of the Knowledge effect is consistent across all
    experiments: familiar School > unfamiliar PM. -/
inductive KnowledgeDirection where
  | schoolGreaterThanPM
  deriving DecidableEq, Repr

-- ============================================================================
-- §3. Scenarios
-- ============================================================================

/-- Familiar location, normal speaker (School condition).

    The literal reading has low effects: a knowledgeable speaker saying
    something mundane about a familiar location is unsurprising (effects 1).
    The enriched "something has changed" reading is warranted and produces
    strong cognitive effects (effects 3): contextual implication that the
    speaker noticed a change to the familiar environment.

    The enriched effect decomposes as `EffectType.contextualImplication`:
    a new conclusion ("the walls changed") derivable only from the input
    *plus* the contextual assumption that the speaker is knowledgeable. -/
def familiarScenario : RTScenario TrivialInterp :=
  { candidates    := [.literal, .changed, .phatic]
  , accessibility := λ | .literal => 1 | .changed => 2 | .phatic => 3
  , effects       := λ | .literal => 1 | .changed => 3 | .phatic => 1
  , effort        := λ | .literal => 0 | .changed => 1 | .phatic => 0
  , threshold     := 2
  , effortWeight  := 0
  }

/-- Unfamiliar location, normal speaker (Prime Minister's office condition).

    The literal reading is genuinely informative: neither speaker nor
    listener knew what the PM's office looked like, so "the walls are blue"
    is novel information (effects 2, passes threshold).
    The enriched reading is not warranted: the speaker has no baseline
    knowledge of the location, so inferring change is unjustified
    (effects 1, fails threshold). -/
def unfamiliarScenario : RTScenario TrivialInterp :=
  { candidates    := [.literal, .changed, .phatic]
  , accessibility := λ | .literal => 1 | .changed => 2 | .phatic => 3
  , effects       := λ | .literal => 2 | .changed => 1 | .phatic => 1
  , effort        := λ | .literal => 0 | .changed => 1 | .phatic => 0
  , threshold     := 2
  , effortWeight  := 0
  }

/-- Quiet speaker, familiar location.

    A quiet speaker's decision to speak carries extra weight: the rarity
    of their speech makes each utterance more noteworthy, amplifying the
    cognitive effects of the enriched interpretation (effects 4 vs 3).
    The literal reading remains subthreshold (effects 1).

    This connects to @cite{burnett-2019}'s persona framework: "quiet"
    is a stable speaker quality (an attributed characteristic accreted
    from habitual stances) that modulates the listener's expectations
    of the speaker's communicative threshold. -/
def quietFamiliarScenario : RTScenario TrivialInterp :=
  { candidates    := [.literal, .changed, .phatic]
  , accessibility := λ | .literal => 1 | .changed => 2 | .phatic => 3
  , effects       := λ | .literal => 1 | .changed => 4 | .phatic => 1
  , effort        := λ | .literal => 0 | .changed => 1 | .phatic => 0
  , threshold     := 2
  , effortWeight  := 0
  }

/-- Quiet speaker, unfamiliar location.

    The quiet speaker's reticence provides a small boost to the enriched
    interpretation's effects even in the unfamiliar case (effects 2 vs 1
    for normal+unfamiliar), but the literal reading still passes threshold
    (effects 2) and is more accessible, so the qualitative comprehension
    procedure selects literal.

    This scenario captures the Experiment 2 interaction: the Knowledge ×
    Style interaction (p = .026) was driven by increased inferencing in the
    unfamiliar+quiet condition compared to unfamiliar+normal. The authors
    speculate that the quiet speaker mentioning something about an
    unfamiliar location leads participants to infer the speaker is trying
    to convey *some* additional meaning, but the only available response
    was "different" — even if the actual inference was something other
    than "the situation has changed."

    The qualitative RT model predicts literal selection here (both literal
    and changed have effects 2, but literal is more accessible). The
    elevated inference rate (~30% vs ~15% for normal+unfamiliar) reflects
    graded/noisy-threshold effects: the closer `.changed` gets to
    threshold, the more often a noisy threshold lets it through. -/
def quietUnfamiliarScenario : RTScenario TrivialInterp :=
  { candidates    := [.literal, .changed, .phatic]
  , accessibility := λ | .literal => 1 | .changed => 2 | .phatic => 3
  , effects       := λ | .literal => 2 | .changed => 2 | .phatic => 1
  , effort        := λ | .literal => 0 | .changed => 1 | .phatic => 0
  , threshold     := 2
  , effortWeight  := 0
  }

-- ============================================================================
-- §4. Selection Theorems
-- ============================================================================

/-- Familiar + normal speaker: the comprehension procedure selects the
    "changed" interpretation.

    The literal reading fails threshold (1 < 2), so the procedure searches
    further. The enriched reading passes (3 ≥ 2) and is accepted.

    This formalizes the core finding across all four experiments:
    trivial utterances from knowledgeable speakers trigger relevance
    inferences at higher rates than from non-knowledgeable speakers. -/
theorem familiar_selects_changed :
    familiarScenario.comprehensionSelects .changed := by
  refine ⟨List.Mem.tail _ (List.Mem.head _), ?_, ?_⟩
  · show familiarScenario.adjustedThreshold .changed ≤ 3
    simp [familiarScenario, RTScenario.adjustedThreshold]
  · intro j hj hacc
    simp only [familiarScenario, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · show 1 < familiarScenario.adjustedThreshold .literal
      simp [familiarScenario, RTScenario.adjustedThreshold]
    · simp [familiarScenario] at hacc
    · simp [familiarScenario] at hacc

/-- Unfamiliar + normal speaker: the literal reading is selected.

    The literal reading passes threshold (2 ≥ 2) and is the most accessible
    candidate, so the procedure stops there. The enriched reading is never
    reached — there is no need to search further. -/
theorem unfamiliar_selects_literal :
    unfamiliarScenario.comprehensionSelects .literal := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · simp [unfamiliarScenario, RTScenario.adjustedThreshold]
  · intro j hj hacc
    simp only [unfamiliarScenario, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [unfamiliarScenario] at hacc

/-- Quiet + unfamiliar: literal is still selected.

    Despite the reticence-driven boost to the enriched interpretation
    (effects 2, at threshold), the literal reading is more accessible
    and also passes threshold, so the satisficing procedure stops there. -/
theorem quietUnfamiliar_selects_literal :
    quietUnfamiliarScenario.comprehensionSelects .literal := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · simp [quietUnfamiliarScenario, RTScenario.adjustedThreshold]
  · intro j hj hacc
    simp only [quietUnfamiliarScenario, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [quietUnfamiliarScenario] at hacc

-- ============================================================================
-- §5. Structural Variants and Monotonicity
-- ============================================================================

/-- The familiar and quiet-familiar scenarios are structural variants:
    same candidates, same accessibility ordering, same search path. -/
theorem variant_familiar_quiet :
    familiarScenario.StructuralVariant quietFamiliarScenario :=
  ⟨rfl, λ x => by cases x <;> rfl⟩

/-- Speaker Style preserves selection via effect strengthening.

    The quiet-familiar scenario is a structural variant of the familiar
    scenario with strictly higher effects for `.changed` (4 > 3) and
    equal effects for all other candidates. By the monotonicity theorem
    (`selects_of_strengthened_effects`), the `.changed` interpretation
    is selected — the quiet speaker's reticence REINFORCES the inference.

    This formalizes Experiment 2's Speaker Style finding (p = .001):
    quiet speakers produce more relevance inferences. -/
theorem quiet_familiar_selects_changed :
    quietFamiliarScenario.comprehensionSelects .changed :=
  RTScenario.selects_of_strengthened_effects
    familiarScenario quietFamiliarScenario .changed
    variant_familiar_quiet
    familiar_selects_changed
    rfl rfl
    (λ x => by cases x <;> rfl)
    (by show 3 ≤ 4; omega)
    (by intro j hj hacc
        simp only [familiarScenario, List.mem_cons,
                    List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · show quietFamiliarScenario.effects .literal ≤ familiarScenario.effects .literal
          simp [familiarScenario, quietFamiliarScenario]
        · simp [familiarScenario] at hacc
        · simp [familiarScenario] at hacc)

-- ============================================================================
-- §6. Effect Ordering: The Algebraic Core
-- ============================================================================

/-- Speaker Knowledge increases the enriched interpretation's effects.

    This is the ordinal prediction that holds independently of whether
    the comprehension procedure is a step function (qualitative RT) or
    a sigmoid (graded extension). Under any noisy-threshold model, this
    ordering produces higher inference rates in the familiar condition. -/
theorem knowledge_strengthens_changed :
    unfamiliarScenario.effects .changed < familiarScenario.effects .changed := by
  show 1 < 3; omega

/-- Speaker Knowledge decreases the literal interpretation's effects.

    Complementary to the enriched strengthening: a knowledgeable speaker
    saying something mundane is LESS informative literally (they could
    say more interesting things about a familiar location). -/
theorem knowledge_weakens_literal :
    familiarScenario.effects .literal < unfamiliarScenario.effects .literal := by
  show 1 < 2; omega

/-- Speaker Style (quiet) strengthens the enriched interpretation beyond
    the Speaker Knowledge baseline. -/
theorem reticence_strengthens_changed :
    familiarScenario.effects .changed < quietFamiliarScenario.effects .changed := by
  show 3 < 4; omega

/-- Reticence also boosts the enriched interpretation in the unfamiliar
    condition, formalizing the source of the Knowledge × Style interaction
    in Experiment 2 (p = .026).

    In the data, inferencing in the unfamiliar+quiet condition was elevated
    relative to unfamiliar+normal, narrowing the Knowledge effect gap.
    In the model, this is a strict increase in `.changed` effects (2 > 1)
    that does not cross the selection boundary (literal still wins) but
    would produce higher inference rates under a noisy threshold. -/
theorem reticence_strengthens_unfamiliar_changed :
    unfamiliarScenario.effects .changed < quietUnfamiliarScenario.effects .changed := by
  show 1 < 2; omega

/-- The Knowledge effect gap is smaller under quiet speaker style than
    under normal style: reticence narrows the difference between familiar
    and unfamiliar conditions for the enriched interpretation.

    familiar − unfamiliar gap:
      Normal: 3 − 1 = 2
      Quiet:  4 − 2 = 2

    In this qualitative encoding the gaps are equal. The observed
    interaction (p = .026) reflects that the quiet speaker's boost to the
    unfamiliar condition proportionally closes more of the gap than the
    boost to the familiar condition, an effect visible only under a graded
    (noisy-threshold) extension where the enriched interpretation's
    distance from threshold matters. -/
theorem knowledge_gap_normal :
    familiarScenario.effects .changed - unfamiliarScenario.effects .changed = 2 := by
  show 3 - 1 = 2; omega

theorem knowledge_gap_quiet :
    quietFamiliarScenario.effects .changed - quietUnfamiliarScenario.effects .changed = 2 := by
  show 4 - 2 = 2; omega

-- ============================================================================
-- §7. Emphasis Cue: Ostensive Redundancy
-- ============================================================================

/-! ### Why no `emphasisScenario`

Every act of ostensive communication already creates a presumption
of optimal relevance (@cite{sperber-wilson-1986}, 2nd ed). The emphasis
cue "Hey, guess what" is an ostensive stimulus, but so is the act of
speaking itself. Since the presumption of relevance is already triggered
by the base utterance, the emphasis cue is redundant — it maps to no
parameter change in the `RTScenario`.

This accounts for Experiment 1's null finding for Emphasis Cue (n.s.):
"Hey, guess what" does not significantly increase inference rates. The
decision to speak is itself a sufficient ostensive stimulus; explicit
cueing adds nothing to the relevance presumption.

There is no formal theorem here because the claim is that the emphasis
cue changes NO model parameter — `familiarScenario` already models
both the cued and uncued conditions. A theorem `familiarScenario =
familiarScenario` would be vacuously true (`rfl`), encoding no content.
-/

-- ============================================================================
-- §8. Processing Effort
-- ============================================================================

/-- The enriched interpretation has nonzero processing effort.

    Computing the "something has changed" inference requires reasoning
    about the speaker's goals and knowledge — effort beyond decoding the
    literal content. This nonzero effort maps onto the response time
    cost observed in the cross-experiment analysis of Exps 3–4:
    inference-endorsing "Yes" responses (Exp 4) are slower than
    non-inference "Yes" responses (Exp 3).

    Cf. @cite{bott-noveck-2004}: scalar implicature computation shows
    the same response-time cost pattern in sentence verification tasks. -/
theorem changed_has_effort :
    familiarScenario.effort .changed = 1 := rfl

/-- The literal interpretation is effort-free: it requires only
    decoding the semantic content, no pragmatic reasoning. -/
theorem literal_is_effortless :
    familiarScenario.effort .literal = 0 := rfl

/-- In the current scenarios, effort does not block the enriched
    interpretation (effortWeight = 0). The effort manifests as
    processing cost (response time), not as relevance reduction.

    A future extension could set effortWeight > 0 to model time-pressure
    contexts where pragmatic enrichment IS blocked by effort — predicting
    lower inference rates under cognitive load (cf. @cite{bale-etal-2025}
    for load effects on competence assumption cancellation). -/
theorem enriched_not_effort_blocked :
    ¬familiarScenario.blockedByEffort .changed := by
  intro ⟨_, h⟩
  simp [familiarScenario, RTScenario.adjustedThreshold] at h

-- ============================================================================
-- §9. Speaking vs Silence
-- ============================================================================

/-! ### Clause (b): the speaker's choice to speak

The deep mechanism behind relevance inferences is clause (b) of optimal
relevance (@cite{sperber-wilson-1986}): the ostensive stimulus is the
most relevant one compatible with the communicator's abilities and
preferences. The speaker chose to SPEAK rather than remain silent. Since
silence would have been easier (zero effort, zero risk of irrelevance),
the hearer infers the speaker had a communicative goal that required
speaking. The hearer then searches for an interpretation that makes
the utterance relevant.

Unlike the scalar implicature case ("some" vs "all"), the alternative
here is SILENCE, not a stronger utterance. The existing `ClauseBArgument`
type models stimulus-level alternatives (alternative utterances the
speaker could have produced), not the speaking-vs-silence choice. A
future extension could add a `SpeakingDecision` type to model this.
-/

-- ============================================================================
-- §10. Cognitive Effects Taxonomy
-- ============================================================================

/-- The "something has changed" inference is a contextual implication:
    a new conclusion derivable only from the utterance content PLUS the
    contextual assumption that the speaker is knowledgeable about the
    location.

    This classifies relevance inferences within S&W's effect taxonomy.
    The inference is not strengthening (no prior assumption about the
    walls being different) and not contradiction (the literal content
    isn't contradicted). It is a genuinely new conclusion that requires
    both the input and the context. -/
def changedEffectType : EffectType := .contextualImplication

-- ============================================================================
-- §11. RT Predictions vs Empirical Findings
-- ============================================================================

/-- RT correctly predicts the Knowledge effect direction:
    the familiar scenario selects `.changed` while the unfamiliar
    selects `.literal`, matching the School > PM pattern replicated
    across all four experiments (p < .001 in each).

    Compare @cite{bergen-grodner-2012}: speaker knowledge modulates
    scalar implicature computation in the same direction — listeners are
    less likely to compute SIs when the speaker has "skimmed" rather than
    "read meticulously." Rees et al. extend this to relevance inferences
    from trivial utterances, showing that speaker knowledge effects
    generalize beyond scale-based inferencing. -/
theorem rt_predicts_knowledge_effect :
    familiarScenario.comprehensionSelects .changed ∧
    unfamiliarScenario.comprehensionSelects .literal :=
  ⟨familiar_selects_changed, unfamiliar_selects_literal⟩

/-- RT correctly predicts the Style effect direction:
    quiet+familiar selects `.changed` (via monotonicity), matching
    the Quiet > Normal pattern in Experiment 2 (p = .001). -/
theorem rt_predicts_style_effect :
    quietFamiliarScenario.comprehensionSelects .changed ∧
    familiarScenario.comprehensionSelects .changed :=
  ⟨quiet_familiar_selects_changed, familiar_selects_changed⟩

/-- The Style effect is captured by effect strengthening, not threshold
    lowering. Increasing effects for the target while holding blocking
    candidates constant preserves (and strengthens) selection. -/
theorem style_is_effect_strengthening :
    familiarScenario.effects .changed < quietFamiliarScenario.effects .changed ∧
    familiarScenario.effects .literal = quietFamiliarScenario.effects .literal :=
  ⟨by show 3 < 4; omega, rfl⟩

end Phenomena.ScalarImplicatures.Studies.ReesReksnesRohde2026
