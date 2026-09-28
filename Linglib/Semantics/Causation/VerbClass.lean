module

/-!
# Causative and implicative verb features

This file defines `Causative`, the force-dynamic mechanism a causative verb lexicalizes. The
other classification a verb entry carries, the polarity of an implicative verb's complement
entailment, is a `Polarity`: positive implicatives (*manage*, *remember*) entail their
complement, negative ones (*fail*, *forget*) its negation.

## References

* [Lauri Karttunen, *Implicative Verbs*][karttunen-1971]
* [Prerna Nadathur and Sven Lauer, *Causal Necessity, Causal Sufficiency, and
  the Implications of Causative Verbs*][nadathur-lauer-2020]
* [Leonard Talmy, *Force dynamics in language and cognition*][talmy-1988]
* [Phillip Wolff, *Direct causation in the linguistic coding and individuation
  of causal events*][wolff-2003]
-/

@[expose] public section

/-! ### Force-dynamic causatives -/

/-- Force-dynamic classification of causative verbs by the causal mechanism
the verb lexicalizes. Studies interpret the classes: [nadathur-lauer-2020] analyse *cause* as
causal necessity and *make* as causal sufficiency, and count *let* and *force* as sufficiency
causatives too. -/
inductive Causative where
  /-- Counterfactual dependence: removing the cause blocks the effect (*cause*). -/
  | cause
  /-- Direct sufficient guarantee: adding the cause ensures the effect (*make*). -/
  | make
  /-- Coercive sufficiency: the causer overcomes the causee's resistance (*force*). -/
  | force
  /-- Permissive: the causer removes a barrier so the effect can occur (*let*). -/
  | enable
  /-- Blocking: the causer adds a barrier so the effect cannot occur (*prevent*). -/
  | prevent
  deriving DecidableEq, Repr
