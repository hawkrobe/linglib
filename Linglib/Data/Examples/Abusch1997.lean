import Linglib.Data.Examples.Schema

/-!
# `Abusch1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Abusch1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Abusch1997.Examples`.
-/

namespace Abusch1997.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "abusch1997_ex1"
    source := ⟨"abusch-1997", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The defendant was actually watching the Simpsons at the time of the crime. According to the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."
    discourseSegments := ["The defendant was actually watching the Simpsons at the time of the crime.", "According to the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."]
    glossedTokens := []
    translation := "The defendant was actually watching the Simpsons at the time of the crime. According to the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."
    context := "Past-shifted (backward-shifted) reading: the embedded `was` (in 'he was in the laboratory') is anaphoric to the time of the crime introduced in the first sentence. Time of the defendant being in the laboratory precedes the jurors' believing time. Abusch's diagnostic for the Independent Theory's anaphoric account of embedded past tense."
    judgment := .acceptable
    alternatives := []
    readings := [("past-shifted (defendant in lab before jurors' believing)", .acceptable)]
    paperFeatures := []
    comment := "Abusch 1997 ex (1), Linguistics and Philosophy 20 p. 2. Two-sentence discourse establishing the time-of-the-crime antecedent; the second sentence's embedded past picks up that antecedent rather than the matrix `believed` event. Cornerstone of the anaphoric (vs. SOT-deletion) account of past-under-past."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2 : LinguisticExample :=
  { id := "abusch1997_ex2"
    source := ⟨"abusch-1997", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed it was raining."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary believed it was raining."
    context := "Simultaneous reading. The embedded `was raining` is anaphoric to the matrix `believed`, yielding a reading where the raining is co-temporal with the believing. Abusch's contrast with (1): both readings derived by the Independent Theory via anaphora to different antecedents."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (raining at believing time)", .acceptable), ("past-shifted (raining before believing)", .acceptable)]
    paperFeatures := []
    comment := "Abusch 1997 ex (2), p. 3. Footnote 2 attributes the simultaneous-reading shape to Enç 1987 (cited as 'Eng 1987'). Standard past-under-past minimal example."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3_ULC : LinguisticExample :=
  { id := "abusch1997_ex3_ULC"
    source := ⟨"abusch-1997", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found an ostrich in his apartment yesterday. Just before he opened the door, he thought that a burglar attacked him."
    discourseSegments := ["John found an ostrich in his apartment yesterday.", "Just before he opened the door, he thought that a burglar attacked him."]
    glossedTokens := []
    translation := "John found an ostrich in his apartment yesterday. Just before he opened the door, he thought that a burglar attacked him."
    context := "Upper Limit Constraint (ULC) foil. The Independent Theory would predict a forward-shifted reading (the attack co-temporal with the later opening, hence after the thinking) via anaphora to the previous sentence's time of opening, paraphrasable as 'When I open the door, a burglar will attack me'. This reading is UNAVAILABLE: embedded past cannot denote a time later than the matrix event. Motivates the §7 ULC."
    judgment := .acceptable
    alternatives := []
    readings := [("past-shifted (attack before thinking)", .acceptable), ("forward-shifted (attack co-temporal with later opening, after thinking)", .ungrammatical)]
    paperFeatures := []
    comment := "Abusch 1997 ex (3), p. 4. The decisive counterexample to the pure Independent Theory: the predicted forward-shifted reading (paraphrased by ex (4) 'When I open the door, a burglar will attack me') is unavailable. Motivates the Upper Limit Constraint: embedded R cannot exceed matrix E."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8_doubleAccess : LinguisticExample :=
  { id := "abusch1997_ex8_doubleAccess"
    source := ⟨"abusch-1997", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary is pregnant."
    context := "Double-access (present-under-past). The pregnancy must include BOTH the utterance time and John's believing time. The embedded present cannot have a purely future-shifted reading (despite the future-orientation usually available to present tense). Motivates Abusch's §3 de re analysis of the embedded present."
    judgment := .acceptable
    alternatives := []
    readings := [("double-access (pregnancy includes utterance + believing)", .acceptable), ("future-shifted (pregnancy only at believing, not utterance)", .ungrammatical)]
    paperFeatures := []
    comment := "Abusch 1997 ex (8), p. 5. Cornerstone present-under-past example. Sharvit 2003 ex (3) descends from this. The double-access constraint is one of two phenomena (alongside the ULC of ex 3) that the pure Independent Theory cannot derive; Abusch addresses both via de re belief + acquaintance relations."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1, ex2, ex3_ULC, ex8_doubleAccess]

end Abusch1997.Examples
