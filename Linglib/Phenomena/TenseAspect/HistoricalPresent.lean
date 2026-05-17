/-!
# Historical / Narrative Present
@cite{wolfson-1979} @cite{schiffrin-1981} @cite{schlenker-2004-sot}

Sub-phenomenon file (recognized empirical pattern with multiple
traditions): present-tense morphology used to narrate past events.

> "Napoleon enters the room. He sees the generals."
> "Just as the Americans are about to invade Europe, the Germans
>  attack Vercors." (Schlenker 2004's running example)

The present-tense form does not locate the event at the utterance
time. It refers to a past event but uses present morphology, often
for narrative vividness or to recreate a witnessing perspective.

## Two literatures

**Sociolinguistic / discourse-analytic** — variationist accounts of
when speakers switch into Conversational Historical Present (CHP) in
oral narrative, what discourse functions the switch serves, and how
it interacts with evaluative structure of narratives.

- @cite{wolfson-1979}: The Conversational Historical Present
  Alternation (Language). Identifies CHP as a discourse strategy
  whose function is to mark internal evaluation in narrative.
- @cite{schiffrin-1981}: Tense variation in narrative (Language).
  Quantitative analysis of when speakers shift between past and
  present tense forms within a single narrative.

**Semantic / formal** — accounts in which the present-tense form is
re-evaluated against a shifted context. Schlenker's two-context
account separates the Context of Utterance (CU) from a Context of
Thought (CT); the present tense is evaluated at the CT (the narrative
"now"), while temporal adverbials anchored to CU produce the
characteristic "I was there" effect.

- @cite{schlenker-2004-sot}: A plea for monsters (Linguistics and
  Philosophy). Studies/Schlenker2004 formalizes the analysis;
  Schlenker's HP example ("Germans attack Vercors") is in
  `Data/Examples/Schlenker2004.json`.

## Why no Reichenbach frame here

Historical Present is one of the constructions where a Reichenbach
4-tuple `(S, P, R, E)` cannot simultaneously encode both the
morphological tense (the present form `enters` would normally yield
`R = S`) and the interpretation (the event is at a past `E`).
Stipulating a frame with `R = -200` "for narrative perspective"
silently conflates the morphological category with the
interpretation, hiding the very puzzle the phenomenon poses for
tense theories. The semantic content lives in the per-paper Studies
files (currently Schlenker2004, which separates CU from CT); this
sub-phenomenon file is documentation, not substrate.

## Provenance

This file replaces the inline §13 frame `historicalPresent` formerly
in `Phenomena/TenseAspect/Studies/HeimKratzer1998Data.lean`. The
"Napoleon enters the room" example was not attributed in HK1998Data
to any specific Wolfson or Schiffrin example (those papers analyze
naturally-occurring oral narratives, not the Napoleon textbook
example). The example is a generic pedagogical illustration; treat
it as such.

-/

namespace Phenomena.TenseAspect.HistoricalPresent

end Phenomena.TenseAspect.HistoricalPresent
