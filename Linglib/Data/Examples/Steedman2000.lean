import Linglib.Data.Examples.Schema

/-!
# `Steedman2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Steedman2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Steedman2000.Examples`.
-/

namespace Steedman2000.Examples

open Data.Examples

def ex_96 : LinguisticExample :=
  { id := "steedman2000_96"
    source := ⟨"steedman-2000", "(96)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) irgendjemand auf jeden gespannt ist."
    discourseSegments := []
    glossedTokens := [("(Weil)", "(since)"), ("irgendjemand", "someone"), ("auf", "on"), ("jeden", "everybody"), ("gespannt", "curious"), ("ist", "is")]
    translation := "Since someone is curious about everybody."
    context := "German verb-final subordinate clause; the quantified PP precedes the predicate-tense cluster."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book. Steedman credits the German contrast to Kayne (1998), following Bayer (1990, 1996). The verb-raising classification follows Steedman's compositional story: 'gespannt ist' can form by composition and 'auf jeden' then combines with the whole thing to take scope over the tensed verb."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_97 : LinguisticExample :=
  { id := "steedman2000_97"
    source := ⟨"steedman-2000", "(97)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) jemand versucht hat jeden reinzulegen."
    discourseSegments := []
    glossedTokens := [("(Weil)", "(since)"), ("jemand", "someone"), ("versucht", "tried"), ("hat", "has"), ("jeden", "everyone"), ("reinzulegen", "cheat")]
    translation := "Since someone has tried to cheat everyone."
    context := "German verb-final subordinate clause; the quantified object follows the matrix verb cluster."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book. Although 'versucht hat' can compose, it cannot combine with 'reinzulegen' until 'jeden' has combined with it, so 'jeden' cannot take scope over tense or inverse scope over 'jemand'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_98a : LinguisticExample :=
  { id := "steedman2000_98a"
    source := ⟨"steedman-2000", "(98a)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan vee boeken hee willen lezen"
    discourseSegments := []
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("vee", "many"), ("boeken", "books"), ("hee", "has"), ("willen", "wanted"), ("lezen", "read")]
    translation := "that Jan wanted to read many books"
    context := "West Flemish subordinate clause in the verb-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book: 'many books' can take wider scope than 'wanted'. Steedman cites Haegeman and van Riemsdijk (1986, 444-445) and Haegeman (1992, 202) for verb-projection-raising effects on scope in West Flemish and Zurich German."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_98b : LinguisticExample :=
  { id := "steedman2000_98b"
    source := ⟨"steedman-2000", "(98b)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan hee willen vee boeken lezen"
    discourseSegments := []
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("hee", "has"), ("willen", "wanted"), ("vee", "many"), ("boeken", "books"), ("lezen", "read")]
    translation := "that Jan wanted to read many books"
    context := "West Flemish subordinate clause in the verb-projection-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book; minimal pair with (98a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_99a : LinguisticExample :=
  { id := "steedman2000_99a"
    source := ⟨"steedman-2000", "(99a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan veel liederen probeert te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("veel", "many"), ("liederen", "songs"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    translation := "because Jan tries to sing many songs"
    context := "Dutch subordinate clause with an equi verb, verb-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book; Steedman's own extension of the pattern to Dutch equi verbs."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_99b : LinguisticExample :=
  { id := "steedman2000_99b"
    source := ⟨"steedman-2000", "(99b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan probeert veel liederen te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("probeert", "tries"), ("veel", "many"), ("liederen", "songs"), ("te", "to"), ("zingen", "sing")]
    translation := "because Jan tries to sing many songs"
    context := "Dutch subordinate clause with an equi verb, verb-projection-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book; minimal pair with (99a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_100a : LinguisticExample :=
  { id := "steedman2000_100a"
    source := ⟨"steedman-2000", "(100a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand alle liederen probeert te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("alle", "every"), ("liederen", "song"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    translation := "because someone tries to sing every song"
    context := "Dutch subordinate clause, verb-raising word order, two quantified arguments."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_100b : LinguisticExample :=
  { id := "steedman2000_100b"
    source := ⟨"steedman-2000", "(100b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand probeert alle liederen te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("probeert", "tries"), ("alle", "every"), ("liederen", "song"), ("te", "to"), ("zingen", "sing")]
    translation := "because someone tries to sing every song"
    context := "Dutch subordinate clause, verb-projection-raising word order, two quantified arguments."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book: these verbs under this word order 'limit scope inversion similarly to Bayer's (97)'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_4 : LinguisticExample :=
  { id := "steedman2000_ch7_4"
    source := ⟨"steedman-2000", "ch. 7 (4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "[Ken-ga Naomi-o], [Erika-ga Sara-o] tazuneta"
    discourseSegments := []
    glossedTokens := [("Ken-ga", "Ken-NOM"), ("Naomi-o", "Naomi-ACC"), ("Erika-ga", "Erika-NOM"), ("Sara-o", "Sara-ACC"), ("tazuneta", "visit-PST.CONCL")]
    translation := "Ken visited Naomi, and Erika, Sara"
    context := "Japanese (pure SOV): backward gapping — the nonstandard subject-object argument clusters conjoin and the verb surfaces only in the final conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "backward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean japanese_backward; example number verified against scratch/steedman2000.pdf ch. 7. The book glosses the verb visit-PAST.CONCL (conclusive form)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_5 : LinguisticExample :=
  { id := "steedman2000_ch7_5"
    source := ⟨"steedman-2000", "ch. 7 (5)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ken-ga Naomi-o tazunete, Erika-ga Sara-o"
    discourseSegments := []
    glossedTokens := [("Ken-ga", "Ken-NOM"), ("Naomi-o", "Naomi-ACC"), ("tazunete", "visit-PST.ADV"), ("Erika-ga", "Erika-NOM"), ("Sara-o", "Sara-ACC")]
    translation := "Ken visited Naomi, and Erika, Sara"
    context := "Japanese (pure SOV): forward gapping — the verb in the first conjunct with a verbless second conjunct — is excluded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "forward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean japanese_forward_bad; example number verified against scratch/steedman2000.pdf ch. 7. The book glosses tazunete as visit-PAST.ADV (adverbial -te form). Minimal pair with ch. 7 (4): SOV languages allow only backward gapping (Ross's generalization)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_11 : LinguisticExample :=
  { id := "steedman2000_ch7_11"
    source := ⟨"steedman-2000", "ch. 7 (11)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "...dat [Jan Syntactic Structures en Piet Aspects] gelezen heeft"
    discourseSegments := []
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Syntactic Structures", "Syntactic Structures"), ("en", "and"), ("Piet", "Piet"), ("Aspects", "Aspects"), ("gelezen", "read.PTCP"), ("heeft", "has")]
    translation := "that Jan read Syntactic Structures and Piet Aspects"
    context := "Dutch subordinate clause (SOV): backward gapping — conjoined subject-object clusters precede the shared verb cluster."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "backward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean dutch_sub_backward; example number verified against scratch/steedman2000.pdf ch. 7, where the full sentence is 'Ik geloof dat Jan Syntactic Structures en Piet Aspects gelezen heeft.' The book credits the example to van Oirsouw (1982, 555, example (8b)), apart from the verbs being in the 'German' order, as is common in standard Dutch with the auxiliary hebben."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_19 : LinguisticExample :=
  { id := "steedman2000_ch7_19"
    source := ⟨"steedman-2000", "ch. 7 (19)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "Chonaic [Eoghan Siobhán] agus [Eoghnai Ciaran]"
    discourseSegments := []
    glossedTokens := [("Chonaic", "saw"), ("Eoghan", "Eoghan"), ("Siobhán", "Siobhán"), ("agus", "and"), ("Eoghnai", "Eoghnai"), ("Ciaran", "Ciaran")]
    translation := "Eoghan saw Siobhán, and Eoghnai, Ciaran"
    context := "Irish (pure VSO): forward gapping — the initial verb is shared by conjoined subject-object argument clusters."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "forward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean irish_forward; example number verified against scratch/steedman2000.pdf ch. 7. Steedman credits the VSO observation to Dowty (1988)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_20 : LinguisticExample :=
  { id := "steedman2000_ch7_20"
    source := ⟨"steedman-2000", "ch. 7 (20)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "[Eoghan Siobhán] agus chonaic [Eoghnai Ciaran]"
    discourseSegments := []
    glossedTokens := [("Eoghan", "Eoghan"), ("Siobhán", "Siobhán"), ("agus", "and"), ("chonaic", "saw"), ("Eoghnai", "Eoghnai"), ("Ciaran", "Ciaran")]
    translation := "Eoghan saw Siobhán, and Eoghnai, Ciaran"
    context := "Irish (pure VSO): backward gapping — verbless first conjunct with the verb in the second conjunct — is excluded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "backward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean irish_backward_bad; example number verified against scratch/steedman2000.pdf ch. 7. Minimal pair with ch. 7 (19): the construction Ross (1970) held to be generally disallowed in strictly verb-initial languages."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_21 : LinguisticExample :=
  { id := "steedman2000_ch7_21"
    source := ⟨"steedman-2000", "ch. 7 (21)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Wil jij een ijsje en Marietje limonade?"
    discourseSegments := []
    glossedTokens := [("Wil", "want"), ("jij", "you"), ("een", "an"), ("ijsje", "ice-cream"), ("en", "and"), ("Marietje", "Marietje"), ("limonade", "lemonade")]
    translation := "Do you want an ice-cream, and Marietje lemonade?"
    context := "Dutch main clause (verb-initial yes/no question, conforming to the VSO pattern per Steedman): forward gapping, the mirror image of the backward-gapping subordinate clauses."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "forward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean dutch_main_forward; example number verified against scratch/steedman2000.pdf ch. 7, where Steedman credits van Oirsouw (1987, 58). The prior Lean file encoded Dutch main clauses as SVO ('Main is V2 ≈ VSO'); the book analyzes Dutch main-clause coordination as conforming to the VSO pattern, so wordOrder is recorded as VSO here."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_41 : LinguisticExample :=
  { id := "steedman2000_ch7_41"
    source := ⟨"steedman-2000", "ch. 7 (41)/(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dexter ate bread, and Warren, potatoes"
    discourseSegments := []
    glossedTokens := []
    translation := "Dexter ate bread, and Warren ate potatoes"
    context := "English (SVO): forward gapping — the verb in the first conjunct is shared by the verbless right conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SVO"), ("gappingDirection", "forward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean english_forward; example numbers verified against scratch/steedman2000.pdf ch. 7. The Lean primaryText 'Dexter ate bread, and Warren, potatoes' matches the chapter-opening running text; the numbered examples vary the verb form and object: (41) 'Dexter eats beans, and Warren, potatoes', (62) 'Dexter eats bread, and Warren, potatoes'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch7_63 : LinguisticExample :=
  { id := "steedman2000_ch7_63"
    source := ⟨"steedman-2000", "ch. 7 (63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Warren, potatoes and Dexter bought bread"
    discourseSegments := []
    glossedTokens := []
    translation := "Warren bought potatoes, and Dexter bought bread"
    context := "English (SVO): backward gapping — verbless left conjunct with the verb in the right conjunct — is excluded by universal principles."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SVO"), ("gappingDirection", "backward")]
    comment := "Migrated from Phenomena/Ellipsis/Gapping.lean english_backward_bad with the verb corrected against scratch/steedman2000.pdf ch. 7 (63): the book's sentence is '*Warren, potatoes and Dexter bought bread' (the Lean file had laundered it to 'ate bread' and added a comma before 'and')."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_96, ex_97, ex_98a, ex_98b, ex_99a, ex_99b, ex_100a, ex_100b, ch7_4, ch7_5, ch7_11, ch7_19, ch7_20, ch7_21, ch7_41, ch7_63]

end Steedman2000.Examples
