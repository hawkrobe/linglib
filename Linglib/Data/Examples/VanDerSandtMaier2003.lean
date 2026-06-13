import Linglib.Data.Examples.Schema

/-!
# `VanDerSandtMaier2003` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerSandtMaier2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerSandtMaier2003.Examples`.
-/

namespace VanDerSandtMaier2003.Examples

open Data.Examples

def vdsm2003_ex6_positive : LinguisticExample :=
  { id := "vdsm2003_ex6_positive"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is unhappy. Mary IS happy."
    discourseSegments := ["Mary is unhappy.", "Mary IS happy."]
    glossedTokens := []
    translation := "Mary is unhappy. Mary IS happy."
    context := "Positive denial (paper §2.1): the correcting utterance is syntactically positive — the denial IS the correction. Demonstrates that denial is a discourse operation (non-monotonic correction of contextual information), not a syntactic one (negation)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "propositional"), ("surface_polarity", "positive")]
    comment := "Migrated from Phenomena/Negation/Denial.lean maryHappy_positive. Retracts the at-issue content 'Mary is unhappy' with no negation in the denial utterance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex30b_king : LinguisticExample :=
  { id := "vdsm2003_ex30b_king"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED (30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king of France is bald. The king of France is NOT bald. France does not have a king."
    discourseSegments := ["The king of France is bald.", "The king of France is NOT bald.", "France does not have a king."]
    glossedTokens := []
    translation := "The king of France is bald. The king of France is NOT bald. France does not have a king."
    context := "Presuppositional denial: the correction targets the existence presupposition of the definite ('France has a king'), not the predication. The assertion falls with the presupposition."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "presuppositional"), ("surface_polarity", "negative"), ("scenario", "kingOfFrance")]
    comment := "Migrated from Phenomena/Negation/Denial.lean kingBald_presuppositional. Same scenario family as the worked LDRT derivation of (49)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex29b_possible : LinguisticExample :=
  { id := "vdsm2003_ex29b_possible"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED (29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that the pope is right. It is not POSSIBLE. It is NECESSARY that the pope is right."
    discourseSegments := ["It is possible that the pope is right.", "It is not POSSIBLE.", "It is NECESSARY that the pope is right."]
    glossedTokens := []
    translation := "It is possible that the pope is right. It is not POSSIBLE. It is NECESSARY that the pope is right."
    context := "Scalar implicature denial: 'possible' literally means ◇p with scalar implicature ¬□p. The correction 'necessary' retracts the implicature while the literal meaning survives (□p entails ◇p)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "implicature"), ("surface_polarity", "negative"), ("scenario", "modal")]
    comment := "Migrated from Phenomena/Negation/Denial.lean possible_necessary (paper §2.2 ex 11 / §2.4 ex 29b). Same scenario family as the worked LDRT derivation of (68)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex13_lady : LinguisticExample :=
  { id := "vdsm2003_ex13_lady"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED (13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That was a lady I kissed last night. That wasn't a lady I kissed last night. It was my wife."
    discourseSegments := ["That was a lady I kissed last night.", "That wasn't a lady I kissed last night.", "It was my wife."]
    glossedTokens := []
    translation := "That was a lady I kissed last night. That wasn't a lady I kissed last night. It was my wife."
    context := "Connotation denial (paper category E, mapped to the implicature layer): the correction retracts the social-role/formality connotation of 'lady'; the literal content (the speaker kissed a woman) survives."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "implicature"), ("surface_polarity", "negative"), ("scenario", "lady")]
    comment := "Migrated from Phenomena/Negation/Denial.lean lady_wife. Same scenario family as the worked LDRT derivation of (69)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex19_still_propositional : LinguisticExample :=
  { id := "vdsm2003_ex19_still_propositional"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED (19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John still lives in Paris. John does NOT still live in Paris. He did live there but has moved."
    discourseSegments := ["John still lives in Paris.", "John does NOT still live in Paris.", "He did live there but has moved."]
    glossedTokens := []
    translation := "John still lives in Paris. John does NOT still live in Paris. He did live there but has moved."
    context := "Propositional reading of the 'still' denial: the correction retracts the at-issue content 'John lives in Paris now' while the presupposition of 'still' ('John lived in Paris before') survives."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "propositional"), ("surface_polarity", "negative")]
    comment := "Migrated from Phenomena/Negation/Denial.lean still_propositional. Minimal pair with (20): identical denial utterance, disambiguated by the correction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex20_still_presuppositional : LinguisticExample :=
  { id := "vdsm2003_ex20_still_presuppositional"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John still lives in Paris. John does NOT still live in Paris. He has never set foot in France."
    discourseSegments := ["John still lives in Paris.", "John does NOT still live in Paris.", "He has never set foot in France."]
    glossedTokens := []
    translation := "John still lives in Paris. John does NOT still live in Paris. He has never set foot in France."
    context := "Presuppositional reading of the 'still' denial: the correction retracts the presupposition of 'still' ('John lived in Paris before')."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "presuppositional"), ("surface_polarity", "negative")]
    comment := "Migrated from Phenomena/Negation/Denial.lean still_presuppositional. Minimal pair with (19): identical denial utterance, disambiguated by the correction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex49_kf_discourse : LinguisticExample :=
  { id := "vdsm2003_ex49_kf_discourse"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED §3.5 (49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The King of France walks in the park. No, he doesn't. France doesn't have a king."
    discourseSegments := ["The King of France walks in the park.", "No, he doesn't.", "France doesn't have a king."]
    glossedTokens := []
    translation := "The King of France walks in the park. No, he doesn't. France doesn't have a king."
    context := "Worked presuppositional-denial derivation: the correction conflicts with both the existence presupposition and the at-issue predication, so RA* moves both under a single negation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "presuppositional"), ("surface_polarity", "negative"), ("scenario", "kingOfFrance")]
    comment := "The paper's worked LDRT example for presuppositional denial; formalized as the kingOfFrance scenario in Studies/VanDerSandtMaier2003.lean §1."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex68_modal_discourse : LinguisticExample :=
  { id := "vdsm2003_ex68_modal_discourse"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED §4.4 (68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible the Pope is right. No, it's not POssible. It's NECessary that he's right."
    discourseSegments := ["It is possible the Pope is right.", "No, it's not POssible.", "It's NECessary that he's right."]
    glossedTokens := []
    translation := "It is possible the Pope is right. No, it's not POssible. It's NECessary that he's right."
    context := "Worked implicature-denial derivation: only the scalar implicature ¬□p conflicts with the correction □p; the at-issue ◇p and the presupposition survive RA*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "implicature"), ("surface_polarity", "negative"), ("scenario", "modal")]
    comment := "The paper's worked LDRT example for implicature denial; formalized as the modal scenario in Studies/VanDerSandtMaier2003.lean §2 and §4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vdsm2003_ex69_lady_discourse : LinguisticExample :=
  { id := "vdsm2003_ex69_lady_discourse"
    source := ⟨"van-der-sandt-maier-2003", "UNVERIFIED §4.4 (69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now, THAT's a nice lady. Yes, she is. But she's not a LAdy. She's my WIfe."
    discourseSegments := ["Now, THAT's a nice lady.", "Yes, she is.", "But she's not a LAdy.", "She's my WIfe."]
    glossedTokens := []
    translation := "Now, THAT's a nice lady. Yes, she is. But she's not a LAdy. She's my WIfe."
    context := "Worked connotation-denial derivation: the correction targets only the stranger connotation of 'a lady'; the literal predications (lady, nice) and the deictic presupposition survive RA*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial_type", "implicature"), ("surface_polarity", "negative"), ("scenario", "lady")]
    comment := "The paper's worked LDRT example for connotation denial; formalized as the lady scenario in Studies/VanDerSandtMaier2003.lean §3. The affirmation σ₂ is monotonic merge and omitted from the formalization."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [vdsm2003_ex6_positive, vdsm2003_ex30b_king, vdsm2003_ex29b_possible, vdsm2003_ex13_lady, vdsm2003_ex19_still_propositional, vdsm2003_ex20_still_presuppositional, vdsm2003_ex49_kf_discourse, vdsm2003_ex68_modal_discourse, vdsm2003_ex69_lady_discourse]

end VanDerSandtMaier2003.Examples
