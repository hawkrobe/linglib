---
title: "Psych Verbs Need a Mind: Compositional Denotations via Cognitive Situation Models"
date: 2026-02-27
summary: "Psych verbs like frighten and concern differ in opacity, temporal structure, and causation — but nobody has derived these differences from a single compositional denotation grounded in cognitive architecture. We do, and opacity falls out by computation."
tags: ["psych-verbs", "opacity", "BToM", "situation-semantics", "causation", "formalization"]
---

## Introduction

Psych verbs have been studied from every angle. Belletti and Rizzi (1988) identified the syntactic split between experiencer-subject (*fear*) and experiencer-object (*frighten*) classes. Pesetsky (1995) proposed causal heads to explain why only *frighten*-type verbs encode causation. Landau (2010) argued that experiencers are mental locatives, explaining their special binding properties. More recently, Hartshorne, O'Donnell, and Tenenbaum (2016) demonstrated empirically that the two verb classes correspond to distinct semantic types — habitual attitudes versus caused emotional episodes — and that this mapping holds across English, Mandarin, Korean, and Japanese.

These are genuine insights, and they converge. Pesetsky's causal heads predict exactly the duration and causation differences that Hartshorne et al. measured. Kim's (2024) internal/external causal source distinction captures the same split from a different theoretical angle. Baker, Saxe, and Tenenbaum's (2017) Bayesian Theory of Mind provides a cognitive architecture with the right layers — perception, belief, mental state — to ground the distinction in a model of the experiencer's mind.

The ingredients exist. What is missing is a compositional denotation — a single semantic function that takes a stimulus, an experiencer, and a verb-specific parameter and returns a truth value, from which opacity, temporal structure, and the Uniform Projection Hypothesis all *follow* rather than being stipulated separately. We provide one here.

## The opacity puzzle

The classic opacity contrast with psych verbs runs as follows:

> (1a) Cicero frightens Mary. \
> (1b) Tully frightens Mary. \
> (1a) ↔ (1b) &nbsp; *(co-referential stimuli are interchangeable)*

> (2a) Cicero concerns Mary. \
> (2b) Tully concerns Mary. \
> (2a) ↛ (2b) &nbsp; *(co-referential stimuli are NOT interchangeable)*

*Frighten* is extensional: if Cicero and Tully are the same person, then "Cicero frightens Mary" and "Tully frightens Mary" have the same truth value. *Concern* is potentially intensional: Mary can be concerned about Cicero without being concerned about Tully, even though they are the same individual, because she may not know that the two names corefer.

This is puzzling because both verbs are psych verbs — both relate a stimulus to an experiencer's mental state. Why should the substitution behavior differ? The standard move in formal semantics is to invoke possible worlds: intensional verbs quantify over worlds, extensional verbs do not. But this does not explain *why* some psych verbs are intensional and others are not. The opacity pattern correlates with the experiencer-subject/experiencer-object split, but the mechanism connecting argument structure to substitution behavior has been left unexplained.

## Cognitive situation models

We propose that a psych verb denotes a relation evaluated over a *cognitive situation* — a model of the experiencer's mind, decomposed into the layers of a Bayesian Theory of Mind architecture. The critical parameter is the **causal pathway** through which the stimulus connects to the experiencer's mental state:

- **Perceptual** (*frighten*, *scare*, *amuse*): the stimulus affects the experiencer through perception. The world determines what is perceived, so the perceptual layer is extensional — co-referential stimuli produce the same percept.
- **Representational** (*concern*, *worry*, *bother*): the stimulus affects the experiencer through belief. Beliefs are representations, not world-states, so the belief layer is potentially intensional — the experiencer can have a Cicero-concept without having a Tully-concept.

The causal pathway is the verb's lexical parameter. Everything else — opacity, temporal structure, the linking pattern — is derived.

![Cognitive architecture diagram showing the perceptual and representational pathways through BToM layers](/images/psych-verbs/cognitive-architecture.svg)

## The denotation

The cognitive situation model is an `ExperiencerState` — a record of what the experiencer perceives, believes, and feels, together with the causal connections between these layers:

```lean
structure ExperiencerState (Stimulus MState : Type*) where
  perceives : Stimulus → Bool          -- perceptual layer (extensional)
  represents : Stimulus → Bool         -- belief layer (intensional)
  inMentalState : MState → Bool        -- mental state layer
  perceptCauses : Stimulus → MState → Bool     -- perception triggers state
  beliefMaintains : Stimulus → MState → Bool   -- belief maintains state
```

Each field corresponds to a layer in Baker, Saxe, and Tenenbaum's (2017) BToM architecture. `perceives` is the perception model (World → Percept → F); `represents` is the belief model (Percept → Belief → F). The causal connections `perceptCauses` and `beliefMaintains` correspond to the causal links between BToM layers — the world-driven percept-to-state chain for eventive causation (Kim 2024), and the belief-to-state maintenance relation for stative causation.

The denotation itself is a single function parameterized by the causal pathway:

```lean
def psychVerbSem (pathway : CausalPathway) (root : MState)
    (stimulus : Stimulus) (es : ExperiencerState Stimulus MState) : Bool :=
  es.inMentalState root &&
  match pathway with
  | .perceptual => es.perceives stimulus && es.perceptCauses stimulus root
  | .representational => es.represents stimulus && es.beliefMaintains stimulus root
```

Both pathways take `(stimulus, experiencer-state)` in the same argument positions. The Uniform Projection Hypothesis — that experiencer-subject and experiencer-object verbs share the same thematic structure — is a **type-level guarantee**, not a theorem. It is structurally impossible to write a well-typed psych verb denotation in this framework that violates it.

## Deriving opacity

To demonstrate the opacity derivation, we define a concrete scenario: Cicero and Tully are the same person in the world. The experiencer perceives both (they are the same percept), but represents only Cicero (the agent has a Cicero-concept but not a Tully-concept):

```lean
def ciceroTullyState : ExperiencerState CiceroStimulus ConcernState :=
  { perceives := fun _ => true
    represents := fun | .cicero => true | .tully => false
    inMentalState := fun _ => true
    perceptCauses := fun _ _ => true
    beliefMaintains := fun | .cicero, _ => true | .tully, _ => false }
```

Four theorems follow:

```lean
theorem cicero_frightens :
    psychVerbSem .perceptual .concerned .cicero ciceroTullyState = true := rfl
theorem tully_frightens :
    psychVerbSem .perceptual .concerned .tully ciceroTullyState = true := rfl
theorem cicero_concerns :
    psychVerbSem .representational .concerned .cicero ciceroTullyState = true := rfl
theorem tully_not_concerns :
    psychVerbSem .representational .concerned .tully ciceroTullyState = false := rfl
```

All four proofs are `rfl` — definitional equality. The type checker evaluates the function, unfolds the match, and confirms the result. The opacity contrast between *frighten* and *concern* is a computational consequence of the denotation.

![Diagram showing how Cicero and Tully flow through the perceptual and representational pathways with different results](/images/psych-verbs/opacity.svg)

The general theorem makes the mechanism explicit:

```lean
theorem perceptual_extensional
    (hExt : es.perceptuallyExtensional coref)
    (hCoref : coref a b = true) :
    psychVerbSem .perceptual root a es = psychVerbSem .perceptual root b es
```

If perception is extensional — co-referential stimuli have the same perceptual status and causal effects — then the perceptual pathway is invariant under coreference. The proof unfolds the definition and rewrites with the extensionality hypothesis. An existential theorem confirms that the representational pathway *can* be intensional: the Cicero/Tully state serves as a constructive witness.

## Convergence across three theoretical traditions

The binary distinction between perceptual and representational pathways is not original to this work — it appears independently in three theoretical traditions under different names. What *is* new is demonstrating that they are provably the same distinction:

| Theoretical tradition | Binary distinction | Source |
|---|---|---|
| Empirical semantics | habitualAttitude / causedEpisode | Hartshorne et al. 2016 |
| Causal source theory | internal / external | Kim 2024 |
| Cognitive denotation | representational / perceptual | this post |

We formalize each as a two-element inductive type, define bidirectional mappings between all three pairs, and prove roundtrip theorems establishing that each pair of mappings is an isomorphism. The three-way commutativity theorem confirms that all paths through the diagram agree:

```lean
theorem three_way_agreement (t : SemanticType) :
    causalSourceToPathway (semanticTypeToCausalSource t) =
      semanticTypeToPathway t := by cases t <;> rfl
```

![Diagram showing the three-way isomorphism between SemanticType, CausalSource, and CausalPathway](/images/psych-verbs/three-way-agreement.svg)

This is not a trivial result. The three distinctions were formulated independently — Hartshorne et al. on the basis of behavioral experiments measuring duration and causation ratings, Kim from event-structural analysis of temporal precedence and overlap, and our CausalPathway from BToM cognitive architecture. That they converge is an empirical claim about the structure of psych verb semantics, and the formalization makes it machine-checkable.

## Temporal structure

The causal pathway determines temporal structure through Kim's (2024) `PsychCausalLink`:

```lean
def CausalPathway.toLink (Time : Type*) [LinearOrder Time] :
    CausalPathway → PsychCausalLink Time
  | .perceptual => eventiveLink Time
  | .representational => maintenanceLink Time
```

Perceptual verbs receive eventive links — the stimulus temporally precedes the mental state change, and the event involves a transition (BECOME). Representational verbs receive maintenance links — the stimulus temporally overlaps the mental state, and there is no transition. These predictions are derived, not stipulated:

```lean
theorem perceptual_has_transition (Time : Type*) [LinearOrder Time] :
    (CausalPathway.toLink Time .perceptual).involvesTransition = true := rfl

theorem representational_no_transition (Time : Type*) [LinearOrder Time] :
    (CausalPathway.toLink Time .representational).involvesTransition = false := rfl
```

The transition prediction aligns with the empirical profile from Hartshorne et al.: caused episodes involve BECOME (a transition), habitual attitudes involve BE (no transition). This alignment is itself a theorem — `transition_prediction_consistent` proves that `PsychCausalLink`'s transition prediction matches the empirical profile derived independently from `SemanticType`.

## Causal dynamics

The structural equation model formalization (Nadathur and Lauer 2020) provides a complementary perspective on the same distinction. We encode each pathway as a causal graph:

- **Perceptual**: stimPresent → perceivesStim → inMentalState (a causal chain)
- **Representational**: representsStim → inMentalState (a single causal law)

The formalization verifies causal sufficiency and necessity computationally:

```lean
theorem perceptual_stimulus_sufficient :
    causallySufficient perceptualDynamics Situation.empty
      stimPresent inMentalStateVar = true := by native_decide

theorem perception_intervention_blocks :
    let ⟨dynAfter, bgAfter⟩ :=
      intervene perceptualDynamics
        (Situation.empty.extend stimPresent true) perceivesStim false
    normalDevelopment dynAfter bgAfter 10 |>.get inMentalStateVar = none
```

Intervening on perception — blocking the perceptual pathway while the stimulus is present — prevents the mental state from arising. This formalizes the counterfactual that if Mary does not see the spider, it cannot frighten her. The prediction follows from the causal graph structure, not from stipulation.

## Situation-semantic structure

The `ExperiencerState` has the structure of a situation in the sense of Elbourne (2005, 2013). We define a cognitive refinement relation `cognitiveLE` — one cognitive state is a "part" of another if every positive fact in the first is also in the second — and prove that `psychVerbSem` is persistent under this relation:

```lean
theorem psychVerbSem_monotone
    (hLE : cognitiveLE stimuli states es₁ es₂)
    (hStim : stimulus ∈ stimuli) (hRoot : root ∈ states)
    (hTrue : psychVerbSem pathway root stimulus es₁ = true) :
    psychVerbSem pathway root stimulus es₂ = true
```

If a psych verb is true at a partial cognitive situation, it remains true at any refinement. This connects to Kratzer's (2019) situation-semantic treatment of experiencer predicates and to the de re/de dicto distinction in attitude semantics: the perceptual pathway evaluates stimuli de re (via `SitVarStatus.free` — the stimulus's identity is determined by the world), while the representational pathway evaluates stimuli de dicto (via `SitVarStatus.bound` — the stimulus's identity is determined by the agent's representation).

## Emotion appraisals and the attitude/episode boundary

The distinction between Class I and Class II psych verbs maps naturally onto a deeper question in cognitive science: what kind of mental state does each verb class denote? Houlihan, Kleiman-Weiner, Hewitt, Tenenbaum, and Saxe (2023) provide a computational answer. In their framework, emotions are not primitive mental states — they are *computed* from more basic cognitive variables via a three-layer architecture:

1. **Inverse planning**: observe an action and infer the agent's beliefs, desires, and percepts (i.e., standard BToM inference).
2. **Appraisal computation**: from the inferred mental states, compute four core appraisal dimensions — achieved utility (how much value was realized), prediction error (how surprising the outcome was), counterfactual utility for the agent (what would have happened under an alternative action), and counterfactual utility for an opponent.
3. **Emotion identification**: each emotion is a qualitative pattern of appraisal activations across these dimensions.

The critical architectural claim is that emotions are *post-inference readouts*. They do not introduce new latent variables into the BToM model; they are functions of the posteriors that BToM inference already computes. Achieved utility is a weighted sum over the desire marginal. Prediction error is the difference between outcome and the belief expectation. Counterfactual appraisals compare actual and alternative outcomes.

We formalize the appraisal architecture in `Core.Agent.Emotion`, encoding each of the 20 emotion concepts from Houlihan et al. as a qualitative profile over eight dimensions (four appraisal types × two perspectives: base and reputational). All 20 profiles are pairwise distinguishable — a property verified by `native_decide` over the full set.

The novel synthesis in this work is the bridge between the appraisal architecture and the CausalPathway classification. The key observation is that the **dominant appraisal type** of an emotion predicts which causal pathway the corresponding psych verb uses:

- **Prediction-error-dominant** emotions (surprise, confusion) map to the perceptual pathway: an external stimulus violates expectations.
- **Achieved-utility-dominant** emotions (joy, pride, disgust, respect) map to the representational pathway: the experiencer internally evaluates outcomes against desires.
- **Counterfactual-dominant** emotions (regret, relief) map to the perceptual pathway: an external event enables counterfactual comparison.

This mapping extends the three-way isomorphism from the previous sections to a four-way agreement:

```lean
theorem appraisal_causalSource_agreement :
    appraisalToPathway .predictionError = causalSourceToPathway .external ∧
    appraisalToPathway .achievedUtility = causalSourceToPathway .internal :=
  ⟨rfl, rfl⟩
```

For pure-profile emotions — those where a single appraisal type dominates — the mapping works cleanly. *Surprise* maps to the perceptual pathway via prediction error; *admire* maps to the representational pathway via achieved utility. But mixed-profile emotions like *disappointment* (which activates AU, PE, and counterfactual dimensions equally) expose a genuine limitation: the dominance-based bridge must break ties, and the result may not match the verb's independently classified CausalPathway. We document rather than conceal this.

The most theoretically informative result concerns the verbs that the appraisal architecture *cannot* ground. Class I psych verbs — *fear*, *worry*, *dread*, *hope* — return `none` from the verb-to-emotion mapping, because all 20 Houlihan emotions are retrospective: they are computed after an outcome is observed. Class I verbs denote prospective or dispositional states that persist independent of any particular episode. The attitude/episode distinction from Hartshorne et al. (2016) is thus reflected in which verbs the appraisal architecture can reach — and the formal gap is as informative as the formal connection.

## Computational guarantees

Several properties of this formalization would be difficult to establish informally.

The opacity derivation is not a hand-waved argument about extensionality — it is a computation that the type checker performs. The proof that "Cicero frightens Mary" and "Tully frightens Mary" have the same truth value is `rfl`: the machine unfolds the definition, evaluates both sides, and confirms they are identical. There is no step where a reasoning error could be introduced.

The three-way agreement between Hartshorne et al.'s semantic types, Kim's causal sources, and our causal pathways is verified exhaustively. If a future revision to the empirical data required habitual attitudes to map to *external* rather than internal causal sources, the roundtrip theorem would fail to compile. The isomorphism is a falsifiable claim with an automated check.

The UPH is enforced by the type system rather than stated as a constraint. Both pathways share the same type signature not because we proved they do, but because there is no way to define a well-typed `psychVerbSem` where they differ. This is the strongest kind of guarantee a proof assistant can provide: not that we checked and the property holds, but that it is structurally impossible for it to fail.

Finally, the separation between Linglib proper (published theoretical content) and the blog-side formalization (novel synthesis) reflects a methodological choice. Hartshorne et al.'s semantic types, Kim's causal sources, the BToM model, and the emotion appraisal architecture all live in the library, because they formalize published work. The `ExperiencerState`, `CausalPathway`, and `psychVerbSem` — the novel contributions — live alongside this blog post. If the ideas prove useful, they can be promoted to library status. If they turn out to be wrong, a single file deletion suffices.

## File map

```
Core/Agent/
  BToM.lean                  — Bayesian Theory of Mind (6 marginals)
  Emotion.lean               — Houlihan et al. 2023: appraisal types, 20 emotion profiles

Theories/Semantics/Causation/
  PsychCausation.lean        — CausalSource (internal/external)
  PsychCausalLink.lean       — Temporal/event-structural predictions

Phenomena/PsychVerbs/
  Data.lean                  — B&R classes, diagnostics
  Studies/HartshorneEtAl2016/
    Data.lean                — SemanticType, prominence-based linking, cross-linguistic data
    Bridge.lean              — SemanticType ↔ CausalSource isomorphism

blog/lean/PsychVerbs/
  PsychVerbSem.lean          — ExperiencerState, CausalPathway, psychVerbSem,
                               opacity derivation, BToM/CausalFrame/situation bridges,
                               emotion appraisal grounding (§12)
```

## References

- Baker, C. L., Saxe, R., & Tenenbaum, J. B. (2017). Rational quantitative attribution of beliefs, desires and percepts in human mentalizing. *Nature Human Behaviour* 1, 0064.
- Belletti, A. & Rizzi, L. (1988). Psych-verbs and θ-theory. *Natural Language and Linguistic Theory* 6(3), 291--352.
- Elbourne, P. (2005). *Situations and Individuals*. MIT Press.
- Hartshorne, J. K., O'Donnell, T. J., & Tenenbaum, J. B. (2016). Psych verbs, the linking problem, and the acquisition of language. *Cognition* 157, 268--288.
- Houlihan, S. D., Kleiman-Weiner, M., Hewitt, L. B., Tenenbaum, J. B., & Saxe, R. (2023). Emotion prediction as computation over a generative theory of mind. *Philosophical Transactions of the Royal Society A* 381(2251), 20220047.
- Kim, K. (2024). Causal structures of psych predicates. *Proceedings of SALT 34*.
- Kratzer, A. (2019). Situations in natural language semantics. In E. N. Zalta (Ed.), *Stanford Encyclopedia of Philosophy*.
- Landau, I. (2010). *The Locative Syntax of Experiencers*. MIT Press.
- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency, and the implications of causative verbs. *Glossa* 5(1), 49.
- Pesetsky, D. (1995). *Zero Syntax: Experiencers and Cascades*. MIT Press.
