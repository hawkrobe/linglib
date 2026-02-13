/-!
# Epistemic Evidentiality — Empirical Data

Theory-neutral empirical observations about the interaction between epistemic
necessity modals (English *must*, *have to*) and evidential source.

## Key Generalizations

1. Epistemic *must* is infelicitous when the speaker has direct evidence for
   the prejacent (seeing rain → "#It must be raining")
2. Epistemic *must* is felicitous when the speaker has indirect evidence
   (seeing wet rain gear → "It must be raining")
3. Despite (1), *must φ* entails the bare prejacent φ — *must* is not
   semantically weak, just evidentially restricted
4. *Can't* patterns with *must*, not with weak modals (*might*, *perhaps*)

## The Strength Ordering (p. 352)

must > almost certainly > presumably > might > bare prejacent (?)

The placement of the bare prejacent is Karttunen's Problem:
- Standard modal logic: must φ ⊨ φ (must is ABOVE bare)
- Naive intuition: φ conveys more confidence than must φ (bare is ABOVE must)

## References

- Karttunen, L. (1972). Possible and must. In Kimball (ed.), Syntax and Semantics 1.
- Groenendijk, J. & Stokhof, M. (1975). Modality and conversational information.
- Kratzer, A. (1991). Modality. In von Stechow & Wunderlich (eds.), Semantics.
- von Fintel, K. & Gillies, A. (2010). Must...stay...strong! NLS 18:351–383.
- von Fintel, K. & Gillies, A. (2021). Still going strong. NLS 29:91–113.
-/

namespace Phenomena.Modality.EpistemicEvidentiality

-- ════════════════════════════════════════════════════════════════════════════
-- Datum Structures
-- ════════════════════════════════════════════════════════════════════════════

/-- The type of evidence the speaker has for the prejacent. -/
inductive EvidenceType where
  /-- Direct sensory observation (seeing, hearing). -/
  | direct
  /-- Indirect inference from observable effects. -/
  | indirect
  /-- Elimination reasoning (ruling out alternatives). -/
  | elimination
  /-- Reported / hearsay evidence. -/
  | reported
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A minimal pair comparing a bare prejacent with its modalized counterpart. -/
structure MustMinimalPair where
  /-- The bare prejacent sentence -/
  bare : String
  /-- The must-sentence -/
  must : String
  /-- Evidential context (what the speaker perceives) -/
  context : String
  /-- Type of evidence available -/
  evidenceType : EvidenceType
  /-- Is the bare sentence felicitous in this context? -/
  bareFelicitous : Bool
  /-- Is the must-sentence felicitous in this context? -/
  mustFelicitous : Bool
  /-- Does must φ entail φ (speaker judgment on inference validity)? -/
  mustEntailsPrejacent : Bool
  /-- Source example number from VF&G 2010 -/
  exampleNum : String := ""
  /-- Additional notes -/
  notes : String := ""
  deriving Repr

-- ════════════════════════════════════════════════════════════════════════════
-- §1 — Karttunen's Problem: Bare vs. Must Minimal Pairs
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G ex. 3 (Karttunen 1972): "John left" vs. "John must have left."
    The must-sentence "expresses more conviction" yet is felt to be weaker. -/
def johnLeft : MustMinimalPair where
  bare := "John left."
  must := "John must have left."
  context := "General epistemic context"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "3"
  notes := "Karttunen (1972): 'intuitively, (3b) makes a weaker claim than (3a)'"

/-- VF&G ex. 4 (Groenendijk & Stokhof 1975): "John must be at home" vs.
    "John is at home." -/
def johnHome : MustMinimalPair where
  bare := "John is at home."
  must := "John must be at home."
  context := "General epistemic context"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "4"
  notes := "G&S: 'A statement like (4a) is weaker than (4b). (4b) expresses more conviction'"

/-- VF&G ex. 5 (Kratzer 1991): "She climbed Mount Toby" vs.
    "She must have climbed Mount Toby." -/
def mountToby : MustMinimalPair where
  bare := "She climbed Mount Toby."
  must := "She must have climbed Mount Toby."
  context := "General epistemic context"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "5"
  notes := "Kratzer (1991 p.645): 'I make a stronger claim in uttering (5a) than in (5b)'"

/-- VF&G ex. 2 (Karttunen's Problem stated as question-answer):
    "They must be in the kitchen drawer" conveys less confidence as an
    answer to "Where are the keys?" than the bare "They are in the kitchen
    drawer." -/
def keysInDrawer : MustMinimalPair where
  bare := "They are in the kitchen drawer."
  must := "They must be in the kitchen drawer."
  context := "Answer to: Where are the keys?"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "2"
  notes := "Karttunen's Problem: (2b) is a stronger answer than (2a) by modal logic, but naive intuition reverses this"

-- ════════════════════════════════════════════════════════════════════════════
-- §4.1 — Direct vs. Indirect Evidence (Billy's Weather Reports)
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G ex. 6: DIRECT evidence (seeing rain) blocks must. -/
def billySeesRain : MustMinimalPair where
  bare := "It's raining."
  must := "It must be raining."
  context := "Billy sees the pouring rain through the window"
  evidenceType := .direct
  bareFelicitous := true
  mustFelicitous := false
  mustEntailsPrejacent := true
  exampleNum := "6"
  notes := "Core observation: direct perceptual evidence makes must infelicitous"

/-- VF&G ex. 7: INDIRECT evidence (wet gear, rain is only cause) enables must. -/
def billySeesWetGear : MustMinimalPair where
  bare := "It's raining."
  must := "It must be raining."
  context := "Billy sees people with wet umbrellas/slickers/galoshes and knows rain is the only possible cause"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "7"
  notes := "Indirect causal inference enables must even when prejacent is entailed"

-- ════════════════════════════════════════════════════════════════════════════
-- §4.2 — Must is Not Always Weak
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G ex. 12 (Argument 4.2.1): Elimination reasoning — Chris's ball.
    Must is perfectly felicitous and feels strong, not weak. -/
def chrisBall : MustMinimalPair where
  bare := "It is in C."
  must := "So, it must be in C."
  context := "Chris knows ball is in Box A, B, or C. It is not in A. It is not in B."
  evidenceType := .elimination
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "12"
  notes := "No weakness: elimination with full certainty. Had Chris opened Box C, 'It must be in C' would be weird (direct evidence)."

/-- VF&G Argument 4.2.2: Billy sees wet gear, knows rain is only cause.
    The prejacent is entailed *ex hypothesi*, yet must is felicitous.
    Pattern: B_K entails the prejacent but the kernel doesn't directly
    settle it — the gap that licenses must. -/
def billyWetGearStrong : MustMinimalPair where
  bare := "It's raining."
  must := "It must be raining."
  context := "Billy sees wet rain gear and knows for sure rain is the only possible cause"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "7 (revisited as 4.2.2)"
  notes := "Must is strong here: the indirect inference is conclusive. No weakness."

-- ════════════════════════════════════════════════════════════════════════════
-- §4.3 — Must is Never Weak
-- ════════════════════════════════════════════════════════════════════════════

/-- A datum capturing an inference pattern (modus ponens, contradiction, etc.). -/
structure InferenceDatum where
  /-- The inference pattern or sentences involved -/
  sentences : List String
  /-- Is the inference valid / the pattern contradictory? -/
  judgment : String
  /-- Source example number from VF&G 2010 -/
  exampleNum : String := ""
  /-- What this shows about must's strength -/
  notes : String := ""
  deriving Repr

/-- VF&G ex. 14–15 (Argument 4.3.1): Modus ponens with must is valid.
    If must were weak, the premises would be too weak for the conclusion. -/
def modusPonens : InferenceDatum where
  sentences := [
    "If Carl is at the party, then Lenny must be at the party.",
    "Carl is at the party.",
    "So: Lenny is at the party."
  ]
  judgment := "valid"
  exampleNum := "14–15"
  notes := "The argument form 'If φ, must ψ / φ / ∴ ψ' is valid. The Mantra (must is weak) cannot deliver this."

/-- VF&G ex. 16 (Argument 4.3.2): Must-perhaps contradiction.
    If must φ were compatible with ¬φ, this should be fine. It isn't. -/
def mustPerhapsContradiction : InferenceDatum where
  sentences := [
    "#It must be raining but perhaps it isn't raining.",
    "#Perhaps it isn't raining but it must be."
  ]
  judgment := "contradictory"
  exampleNum := "16"
  notes := "Both orders are contradictory. If must were weak (didn't entail φ), must φ ∧ perhaps ¬φ should be consistent."

/-- VF&G ex. 17–19 (Argument 4.3.3): Must doesn't allow retraction.
    Weak modals (might, ought) do. -/
def noRetraction : InferenceDatum where
  sentences := [
    "Alex: It must be raining.",
    "Billy: [Opens curtains] No it isn't. You were wrong.",
    "Alex: #I was not! Look, I didn't say it WAS raining. I only said it must be raining. Stop picking on me!"
  ]
  judgment := "retraction fails"
  exampleNum := "19"
  notes := "Compare: 'I only said it MIGHT be raining' (17c) is fine. Must doesn't allow this escape — it's not weak."

/-- VF&G ex. 17 (contrast): Might DOES allow retraction. -/
def mightRetraction : InferenceDatum where
  sentences := [
    "Alex: It might be raining.",
    "Billy: [Opens curtains] No it isn't. You were wrong.",
    "Alex: I was not! Look, I didn't say it WAS raining. I only said it might be raining. Stop picking on me!"
  ]
  judgment := "retraction succeeds"
  exampleNum := "17"
  notes := "Might allows distancing from the prejacent. Must does not (see noRetraction)."

/-- VF&G ex. 20 (Argument 4.3.4): When hedging is desired, speakers choose
    *probably*, not *must*. If must were weak, it should be the natural hedge. -/
def hedgingPreference : InferenceDatum where
  sentences := [
    "a. It is raining.",
    "b. It must be raining.",
    "c. It is probably raining."
  ]
  judgment := "(c) preferred for hedging, not (b)"
  exampleNum := "20"
  notes := "Context: pretty sure rain is the explanation but there's a twinge of doubt. Must is clearly preferred over probably — not the pattern if must were weak."

-- ════════════════════════════════════════════════════════════════════════════
-- §5–6 — Can't / Evidential Signal Under Negation
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G ex. 21: "Can't" carries the evidential signal; bare negation doesn't. -/
def cantEvidentialSignal : MustMinimalPair where
  bare := "There aren't two reds."
  must := "There can't be two reds."
  context := "Mastermind game — inferred from clues, not directly observed"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "21"
  notes := "(21b) carries the indirect-evidence signal. (21a) does not. Can't patterns with must."

/-- VF&G ex. 23: Direct evidence blocks can't, paralleling must. -/
def cantDirectEvidence : MustMinimalPair where
  bare := "It's not raining."
  must := "It can't be raining."
  context := "Billy sees brilliant sunshine"
  evidenceType := .direct
  bareFelicitous := true
  mustFelicitous := false
  mustEntailsPrejacent := true
  exampleNum := "23"
  notes := "Direct evidence of ¬rain makes 'can't be raining' infelicitous, just like 'must be raining' with direct evidence of rain."

/-- VF&G ex. 24: Indirect evidence enables can't, paralleling must. -/
def cantIndirectEvidence : MustMinimalPair where
  bare := "It's not raining."
  must := "It can't be raining."
  context := "Billy sees people with sun gear, knows sunshine is the only explanation"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "24"
  notes := "Indirect evidence enables can't — exact parallel with must."

-- ════════════════════════════════════════════════════════════════════════════
-- §5 — Hey Wait a Minute Test (Presupposition Diagnostic)
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G ex. 22: The "Hey! Wait a minute" test diagnoses a presupposition.
    Billy challenges Alex's use of must, targeting the evidential component. -/
def heyWaitAMinute : InferenceDatum where
  sentences := [
    "Alex: It must be raining.",
    "Billy: Hey! Wait a minute. Whaddya mean, must? Aren't you looking outside?"
  ]
  judgment := "presupposition challenge felicitous"
  exampleNum := "22"
  notes := "The 'Hey! Wait a minute' test (von Fintel 2004) diagnoses presuppositions. Billy targets the evidential signal: the presupposition that the prejacent isn't directly settled."

-- ════════════════════════════════════════════════════════════════════════════
-- §8 — Internal States
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G ex. 26: "I must be hungry" — odd because hunger is typically
    known by direct introspection, not indirect inference. -/
def mustBeHungry : MustMinimalPair where
  bare := "I am hungry."
  must := "I must be hungry."
  context := "Speaker reflecting on their own internal state"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "26"
  notes := "Unusual: signals that the speaker is inferring hunger indirectly (e.g., from irritability, time since last meal) rather than from the usual direct introspective access."

-- ════════════════════════════════════════════════════════════════════════════
-- VF&G 2021: Can't–Possible Incompatibility (Observation 5)
-- ════════════════════════════════════════════════════════════════════════════

/-- VF&G 2021 ex. 5a/22: Can't φ is incompatible with "it's possible that φ."
    The flat-footed conjunction is incoherent. -/
def cantPossibleContradiction : InferenceDatum where
  sentences := [
    "#Suppose it's possible the keys are in the drawer but they can't be.",
    "#If it's possible the keys are in the drawer but they can't be, then ..."
  ]
  judgment := "contradictory"
  exampleNum := "VF&G 2021 (5), (22)"
  notes := "Observation 5: can't φ excludes 'it's possible that φ'. If can't were weak necessity (¬perhaps), this should be coherent. The Mantra's dilemma."

/-- VF&G 2021 ex. 6/10: Must doesn't combine with *only* — evidence for
    top-of-scale status, not weakness. -/
def mustOnlyIncompatibility : InferenceDatum where
  sentences := [
    "Alex: It must be raining.",
    "Billy: (opens curtains) No it isn't. You were wrong.",
    "Alex: #I was not! Look, I didn't say it WAS raining. I only said it must be raining. Stop picking on me!"
  ]
  judgment := "retraction with 'only must' fails"
  exampleNum := "VF&G 2021 (6)/(10)"
  notes := "Observation 3: *only* doesn't rescue must, unlike weaker expressions ('I only said it might be raining' is fine). If must were below the top of the epistemic scale, *only must* should work."

/-- VF&G 2021 ex. 24: Anti-knowledge — Phil cooking dinner.
    Direct knowledge makes must infelicitous even without perceptual evidence. -/
def philCooksDinner : MustMinimalPair where
  bare := "Dinner is ready."
  must := "Dinner must be ready."
  context := "Phil has checked all the food himself and knows dinner is ready"
  evidenceType := .direct
  bareFelicitous := true
  mustFelicitous := false
  mustEntailsPrejacent := true
  exampleNum := "VF&G 2021 (24)"
  notes := "Anti-knowledge: Phil's complete checking counts as 'direct enough' information, blocking must."

/-- VF&G 2021 ex. 25: Anti-knowledge — Meryl's indirect knowledge.
    Meryl hasn't checked everything herself, so must is fine. -/
def merylCooksDinner : MustMinimalPair where
  bare := "Dinner is ready."
  must := "Dinner must be ready."
  context := "Meryl followed instructions but wonders if anything else was planned"
  evidenceType := .indirect
  bareFelicitous := true
  mustFelicitous := true
  mustEntailsPrejacent := true
  exampleNum := "VF&G 2021 (25)"
  notes := "Meryl's information is indirect: she followed steps but doesn't have full direct knowledge of what counts as 'ready'."

-- ════════════════════════════════════════════════════════════════════════════
-- Summary Tables
-- ════════════════════════════════════════════════════════════════════════════

/-- All minimal pairs. -/
def allMinimalPairs : List MustMinimalPair :=
  [ johnLeft, johnHome, mountToby, keysInDrawer,
    billySeesRain, billySeesWetGear,
    chrisBall, billyWetGearStrong,
    cantEvidentialSignal, cantDirectEvidence, cantIndirectEvidence,
    mustBeHungry,
    philCooksDinner, merylCooksDinner ]

/-- All inference data. -/
def allInferenceData : List InferenceDatum :=
  [ modusPonens, mustPerhapsContradiction,
    noRetraction, mightRetraction, hedgingPreference,
    heyWaitAMinute,
    cantPossibleContradiction, mustOnlyIncompatibility ]

/-- **Key generalization 1**: Direct evidence → must infelicitous. -/
theorem direct_evidence_blocks_must :
    (allMinimalPairs.filter (λ d => d.evidenceType == .direct)).all
      (λ d => !d.mustFelicitous) = true := by native_decide

/-- **Key generalization 2**: Indirect evidence → must felicitous. -/
theorem indirect_evidence_enables_must :
    (allMinimalPairs.filter (λ d => d.evidenceType == .indirect)).all
      (λ d => d.mustFelicitous) = true := by native_decide

/-- **Key generalization 3**: Must always entails the prejacent
    (in every minimal pair, regardless of evidence type). -/
theorem must_always_entails_prejacent :
    allMinimalPairs.all (λ d => d.mustEntailsPrejacent) = true := by native_decide

/-- **Key generalization 4**: Bare prejacent is always felicitous
    (the felicity restriction is specific to must, not to the content). -/
theorem bare_always_felicitous :
    allMinimalPairs.all (λ d => d.bareFelicitous) = true := by native_decide

end Phenomena.Modality.EpistemicEvidentiality
