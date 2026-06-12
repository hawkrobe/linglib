import Linglib.Data.Examples.Schema

/-!
# `VonFintelGillies2010` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintelGillies2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintelGillies2010.Examples`.
-/

namespace VonFintelGillies2010.Examples

open Data.Examples

def keys_drawer : LinguisticExample :=
  { id := "vonfintelgillies2010_keys_drawer"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They must be in the kitchen drawer."
    discourseSegments := []
    glossedTokens := []
    translation := "They must be in the kitchen drawer."
    context := "Answer to: Where are the keys? The speaker infers the location rather than seeing it."
    judgment := .acceptable
    alternatives := [("They are in the kitchen drawer.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Karttunen's Problem: by standard modal logic the must-answer is at least as strong as the bare answer, but naive intuition takes the bare answer to convey more confidence. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean keysInDrawer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def john_left : LinguisticExample :=
  { id := "vonfintelgillies2010_john_left"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John must have left."
    discourseSegments := []
    glossedTokens := []
    translation := "John must have left."
    context := "General epistemic context; the speaker infers John's departure."
    judgment := .acceptable
    alternatives := [("John left.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Datum due to Karttunen (1972): 'intuitively, (3b) makes a weaker claim than (3a)'. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean johnLeft."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def john_home : LinguisticExample :=
  { id := "vonfintelgillies2010_john_home"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John must be at home."
    discourseSegments := []
    glossedTokens := []
    translation := "John must be at home."
    context := "General epistemic context; the speaker infers John's whereabouts."
    judgment := .acceptable
    alternatives := [("John is at home.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Attributed by VF&G to Groenendijk & Stokhof: 'A statement like (4a) is weaker than (4b). (4b) expresses more conviction'. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean johnHome."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mount_toby : LinguisticExample :=
  { id := "vonfintelgillies2010_mount_toby"
    source := ⟨"kratzer-1991", "UNVERIFIED p. 645"⟩
    reportedIn := some ⟨"von-fintel-gillies-2010", "UNVERIFIED (5)"⟩
    language := "stan1293"
    primaryText := "She must have climbed Mount Toby."
    discourseSegments := []
    glossedTokens := []
    translation := "She must have climbed Mount Toby."
    context := "General epistemic context; the speaker infers the climb."
    judgment := .acceptable
    alternatives := [("She climbed Mount Toby.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Kratzer (1991): 'I make a stronger claim in uttering (5a) than in (5b)' — the canonical statement of the Mantra that must is weak. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean mountToby."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def billy_sees_rain : LinguisticExample :=
  { id := "vonfintelgillies2010_billy_sees_rain"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    discourseSegments := []
    glossedTokens := []
    translation := "It must be raining."
    context := "Billy sees the pouring rain through the window."
    judgment := .unacceptable
    alternatives := [("It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "direct"), ("must_entails_prejacent", "true")]
    comment := "Core observation: direct perceptual evidence for the prejacent makes must infelicitous. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean billySeesRain."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def billy_wet_gear : LinguisticExample :=
  { id := "vonfintelgillies2010_billy_wet_gear"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    discourseSegments := []
    glossedTokens := []
    translation := "It must be raining."
    context := "Billy sees people coming in with wet umbrellas, slickers, and galoshes, and knows for sure that rain is the only possible cause."
    judgment := .acceptable
    alternatives := [("It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Indirect causal inference licenses must even though the prejacent is entailed ex hypothesi. Revisited as Argument 4.2.2: the inference is conclusive, so must is strong here — the licensing gap is that the kernel does not directly settle the prejacent. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean billySeesWetGear (the near-duplicate billyWetGearStrong row was merged into this one)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def chris_ball : LinguisticExample :=
  { id := "vonfintelgillies2010_chris_ball"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "So, it must be in C."
    discourseSegments := []
    glossedTokens := []
    translation := "So, it must be in C."
    context := "Chris knows the ball is in Box A, B, or C; it is not in A; it is not in B."
    judgment := .acceptable
    alternatives := [("It is in C.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "elimination"), ("must_entails_prejacent", "true")]
    comment := "Argument 4.2.1: elimination reasoning with full certainty — must is perfectly felicitous and feels strong, not weak. Had Chris opened Box C, 'It must be in C' would be odd (direct evidence). Migrated from Phenomena/Modality/EpistemicEvidentiality.lean chrisBall."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cant_mastermind : LinguisticExample :=
  { id := "vonfintelgillies2010_cant_mastermind"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There can't be two reds."
    discourseSegments := []
    glossedTokens := []
    translation := "There can't be two reds."
    context := "Mastermind game: the conclusion is inferred from the clues, not directly observed."
    judgment := .acceptable
    alternatives := [("There aren't two reds.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "cant"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "The can't-variant carries the indirect-evidence signal; the bare negation does not. Can't patterns with must, not with weak modals. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean cantEvidentialSignal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cant_sunshine : LinguisticExample :=
  { id := "vonfintelgillies2010_cant_sunshine"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It can't be raining."
    discourseSegments := []
    glossedTokens := []
    translation := "It can't be raining."
    context := "Billy sees brilliant sunshine."
    judgment := .unacceptable
    alternatives := [("It's not raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "cant"), ("evidence", "direct"), ("must_entails_prejacent", "true")]
    comment := "Direct evidence of not-rain makes 'It can't be raining' infelicitous, exactly parallel to must with direct evidence of rain. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean cantDirectEvidence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cant_sun_gear : LinguisticExample :=
  { id := "vonfintelgillies2010_cant_sun_gear"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It can't be raining."
    discourseSegments := []
    glossedTokens := []
    translation := "It can't be raining."
    context := "Billy sees people coming in with sun gear and knows sunshine is the only possible explanation."
    judgment := .acceptable
    alternatives := [("It's not raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "cant"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Indirect evidence licenses can't — exact parallel with must. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean cantIndirectEvidence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def must_be_hungry : LinguisticExample :=
  { id := "vonfintelgillies2010_must_be_hungry"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must be hungry."
    discourseSegments := []
    glossedTokens := []
    translation := "I must be hungry."
    context := "Speaker reflecting on their own internal state."
    judgment := .acceptable
    alternatives := [("I am hungry.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Internal states (§8): must signals that the speaker is inferring hunger indirectly (irritability, time since the last meal) rather than via the usual direct introspective access — hence the marked flavor. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean mustBeHungry."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def modus_ponens : LinguisticExample :=
  { id := "vonfintelgillies2010_modus_ponens"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (14)-(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Carl is at the party, then Lenny must be at the party. Carl is at the party. So: Lenny is at the party."
    discourseSegments := ["If Carl is at the party, then Lenny must be at the party.", "Carl is at the party.", "So: Lenny is at the party."]
    glossedTokens := []
    translation := "If Carl is at the party, then Lenny must be at the party. Carl is at the party. So: Lenny is at the party."
    context := "Assessing the validity of the argument form: if phi, must psi; phi; therefore psi."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "modus_ponens")]
    comment := "Argument 4.3.1: the argument is valid. If must were weak, the premises would be too weak to support the unmodalized conclusion. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean modusPonens."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def must_perhaps : LinguisticExample :=
  { id := "vonfintelgillies2010_must_perhaps"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining but perhaps it isn't raining."
    discourseSegments := []
    glossedTokens := []
    translation := "It must be raining but perhaps it isn't raining."
    context := "Flat-footed conjunction of must phi with perhaps not-phi."
    judgment := .unacceptable
    alternatives := [("Perhaps it isn't raining but it must be.", .unacceptable)]
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "epistemic_contradiction")]
    comment := "Argument 4.3.2: both orders are contradictory. If must phi did not entail phi, must phi together with perhaps not-phi should be consistent. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean mustPerhapsContradiction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def might_retraction : LinguisticExample :=
  { id := "vonfintelgillies2010_might_retraction"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex: It might be raining. Billy: (opens curtains) No it isn't. You were wrong. Alex: I was not! Look, I didn't say it WAS raining. I only said it might be raining. Stop picking on me!"
    discourseSegments := ["Alex: It might be raining.", "Billy: (opens curtains) No it isn't. You were wrong.", "Alex: I was not! Look, I didn't say it WAS raining. I only said it might be raining. Stop picking on me!"]
    glossedTokens := []
    translation := ""
    context := "Alex asserted a might-claim; the prejacent turns out false; Alex retracts commitment to the prejacent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "retraction"), ("modal", "might")]
    comment := "Might allows distancing from the prejacent: the retraction succeeds. Contrast with the must-variant. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean mightRetraction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def must_no_retraction : LinguisticExample :=
  { id := "vonfintelgillies2010_must_no_retraction"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex: It must be raining. Billy: (opens curtains) No it isn't. You were wrong. Alex: I was not! Look, I didn't say it WAS raining. I only said it must be raining. Stop picking on me!"
    discourseSegments := ["Alex: It must be raining.", "Billy: (opens curtains) No it isn't. You were wrong.", "Alex: I was not! Look, I didn't say it WAS raining. I only said it must be raining. Stop picking on me!"]
    glossedTokens := []
    translation := ""
    context := "Alex asserted a must-claim; the prejacent turns out false; Alex attempts the might-style retraction."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "retraction"), ("modal", "must")]
    comment := "Argument 4.3.3: must does not allow the retraction escape that might allows — must is not weak. VF&G 2021 (Observation 3, exx. (6)/(10)) reuse this datum: 'only' fails to rescue must, evidence that must sits at the top of the epistemic scale. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean noRetraction and mustOnlyIncompatibility (the latter was a verbatim duplicate of this dialogue)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hedging : LinguisticExample :=
  { id := "vonfintelgillies2010_hedging"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is probably raining."
    discourseSegments := []
    glossedTokens := []
    translation := "It is probably raining."
    context := "Speaker is pretty sure rain explains the wet gear but feels a twinge of doubt and wants to hedge."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "hedging")]
    comment := "Argument 4.3.4: when hedging is wanted, speakers reach for 'probably', not 'must'. If must were weak, must should be the natural hedge. UNVERIFIED detail: the migrated Phenomena file's notes were internally inconsistent on which form is preferred; this row follows its judgment field ('(c) preferred for hedging, not (b)'). Migrated from Phenomena/Modality/EpistemicEvidentiality.lean hedgingPreference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hey_wait_a_minute : LinguisticExample :=
  { id := "vonfintelgillies2010_hey_wait_a_minute"
    source := ⟨"von-fintel-gillies-2010", "UNVERIFIED (22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex: It must be raining. Billy: Hey! Wait a minute. Whaddya mean, must? Aren't you looking outside?"
    discourseSegments := ["Alex: It must be raining.", "Billy: Hey! Wait a minute. Whaddya mean, must? Aren't you looking outside?"]
    glossedTokens := []
    translation := ""
    context := "Billy challenges Alex's use of must while Alex is looking out the window."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "hwam_test")]
    comment := "The 'Hey! Wait a minute' test (von Fintel 2004) diagnoses presuppositions. Billy targets the evidential signal: the presupposition that the speaker's kernel does not directly settle the prejacent. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean heyWaitAMinute."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [keys_drawer, john_left, john_home, mount_toby, billy_sees_rain, billy_wet_gear, chris_ball, cant_mastermind, cant_sunshine, cant_sun_gear, must_be_hungry, modus_ponens, must_perhaps, might_retraction, must_no_retraction, hedging, hey_wait_a_minute]

end VonFintelGillies2010.Examples
