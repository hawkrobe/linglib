import Linglib.Data.Examples.Schema

/-!
# `Arka2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Arka2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Arka2013.Examples`.
-/

namespace Arka2013.Examples

open Data.Examples

def ex_3 : LinguisticExample :=
  { id := "arka2013_3"
    source := ⟨"arka-2013", "(3)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("datang", "come")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("S/he came.", .acceptable), ("S/he is coming.", .acceptable), ("S/he will come.", .acceptable)]
    paperFeatures := [("tam", "contextual")]
    comment := "Contextual TAM: the bare verb is anchored by context alone."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_4a : LinguisticExample :=
  { id := "arka2013_4a"
    source := ⟨"arka-2013", "(4a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (besok)."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("besok", "tomorrow")]
    translation := "S/he will come tomorrow."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("frame", "S<E-R"), ("adjunct", "besok")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_4b : LinguisticExample :=
  { id := "arka2013_4b"
    source := ⟨"arka-2013", "(4b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (kemarin)."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("kemarin", "yesterday")]
    translation := "He came in yesterday."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("frame", "E-R<S"), ("adjunct", "kemarin")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_4c : LinguisticExample :=
  { id := "arka2013_4c"
    source := ⟨"arka-2013", "(4c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (sekarang)."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("sekarang", "now")]
    translation := "She is coming now."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("frame", "E-R-S"), ("adjunct", "sekarang")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_5a : LinguisticExample :=
  { id := "arka2013_5a"
    source := ⟨"arka-2013", "(5a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sudah pergi (sekarang)."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("sudah", "PERF"), ("pergi", "go"), ("sekarang", "now")]
    translation := "S/he has left (now)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sudah"), ("frame", "E<S,R")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_5b : LinguisticExample :=
  { id := "arka2013_5b"
    source := ⟨"arka-2013", "(5b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sudah pergi kemarin."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("sudah", "PERF"), ("pergi", "go"), ("kemarin", "yesterday")]
    translation := "S/he (had) already left yesterday."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sudah"), ("frame", "E<R<S"), ("adjunct", "kemarin")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6a : LinguisticExample :=
  { id := "arka2013_6a"
    source := ⟨"arka-2013", "(6a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (sedang) me-mukul-i kepala=nya sendiri."
    discourseSegments := []
    glossedTokens := [("Ali", "A."), ("sedang", "PROG"), ("me-mukul-i", "AV.hit-I"), ("kepala=nya", "head=3sg.poss"), ("sendiri", "self")]
    translation := "Ali is beating his own head."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sedang"), ("aspect", "progressive"), ("marking", "applicative -i")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6b : LinguisticExample :=
  { id := "arka2013_6b"
    source := ⟨"arka-2013", "(6b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (sedang) me-mukul-mukul kepala=nya sendiri."
    discourseSegments := []
    glossedTokens := [("Ali", "Ali"), ("sedang", "PROG"), ("me-mukul-mukul", "AV.hit-RED"), ("kepala=nya", "head=3sg.poss"), ("sendiri", "self")]
    translation := "Ali is beating his own head."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sedang"), ("aspect", "progressive"), ("marking", "reduplication")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7 : LinguisticExample :=
  { id := "arka2013_7"
    source := ⟨"arka-2013", "(7)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali tidak masuk-masuk ke rumah."
    discourseSegments := []
    glossedTokens := [("Ali", "Ali"), ("tidak", "NEG"), ("masuk-masuk", "enter-RED"), ("ke", "to"), ("rumah", "house")]
    translation := "Ali didn't enter the house (while he's expected to do so)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marking", "reduplication"), ("meaning", "unrealised expectation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_8 : LinguisticExample :=
  { id := "arka2013_8"
    source := ⟨"arka-2013", "(8)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia makan sambil menonton TV."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("makan", "eat"), ("sambil", "while"), ("menonton", "AV.watch"), ("TV", "TV")]
    translation := "He was/is eating while watching TV."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "progressive"), ("tam", "contextual")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_10 : LinguisticExample :=
  { id := "arka2013_10"
    source := ⟨"arka-2013", "(10)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mereka (akan) datang."
    discourseSegments := []
    glossedTokens := [("Mereka", "3p"), ("akan", "FUT"), ("datang", "come")]
    translation := "They will come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("frame", "S<E-R"), ("withAux", "acceptable"), ("clause", "root")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_11a : LinguisticExample :=
  { id := "arka2013_11a"
    source := ⟨"arka-2013", "(11a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mereka ingin [datang besok]."
    discourseSegments := []
    glossedTokens := [("Mereka", "3p"), ("ingin", "want"), ("datang", "come"), ("besok", "tomorrow")]
    translation := "They want to come tomorrow."
    context := ""
    judgment := .acceptable
    alternatives := [("Mereka ingin [akan datang besok].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "ingin")]
    comment := "(11b) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_11c : LinguisticExample :=
  { id := "arka2013_11c"
    source := ⟨"arka-2013", "(11c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya tahu [bahwa mereka akan datang]."
    discourseSegments := []
    glossedTokens := [("Saya", "1s"), ("tahu", "know"), ("bahwa", "that"), ("mereka", "3p"), ("akan", "FUT"), ("datang", "come")]
    translation := "I know that they will come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("matrix", "tahu"), ("subordinator", "bahwa")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_12a : LinguisticExample :=
  { id := "arka2013_12a"
    source := ⟨"arka-2013", "(12a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia akan/sudah/sedang makan."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("akan/sudah/sedang", "FUT/PERF/PROG"), ("makan", "eat")]
    translation := "S/he will eat/has eaten/is eating."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("withAux", "acceptable"), ("clause", "root")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_12b : LinguisticExample :=
  { id := "arka2013_12b"
    source := ⟨"arka-2013", "(12b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya menyuruh dia [makan]."
    discourseSegments := []
    glossedTokens := [("Saya", "1s"), ("menyuruh", "AV.ask"), ("dia", "3s"), ("makan", "eat")]
    translation := "I asked him to eat."
    context := ""
    judgment := .acceptable
    alternatives := [("Saya menyuruh dia [akan/sudah/sedang makan].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "menyuruh")]
    comment := "(12c) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_13a : LinguisticExample :=
  { id := "arka2013_13a"
    source := ⟨"arka-2013", "(13a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu mendorong saya [ _ jatuh]."
    discourseSegments := []
    glossedTokens := [("Orang", "person"), ("itu", "that"), ("mendorong", "AV.push"), ("saya", "1s"), ("jatuh", "fall")]
    translation := "The person pushed me (and as a result I) fell off."
    context := ""
    judgment := .acceptable
    alternatives := [("Orang itu medorong saya [ _ akan/sedang/sudah jatuh].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "mendorong")]
    comment := "(13b) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_14a : LinguisticExample :=
  { id := "arka2013_14a"
    source := ⟨"arka-2013", "(14a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (sambil) menangis."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("sambil", "while"), ("menangis", "AV.cry")]
    translation := "S/he came while crying."
    context := ""
    judgment := .acceptable
    alternatives := [("Dia datang [(sambil) sedang menangis].", .questionable)]
    readings := []
    paperFeatures := [("withAux", "questionable"), ("adjunct", "sambil")]
    comment := "(14b) is marked ?*."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_15a : LinguisticExample :=
  { id := "arka2013_15a"
    source := ⟨"arka-2013", "(15a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya belajar [menembak]."
    discourseSegments := []
    glossedTokens := [("Saya", "1s"), ("belajar", "study"), ("menembak", "AV.shoot")]
    translation := "I'm learning to shoot."
    context := ""
    judgment := .acceptable
    alternatives := [("Saya belajar bisa [menembak].", .questionable)]
    readings := []
    paperFeatures := [("withAux", "questionable"), ("matrix", "belajar")]
    comment := "(15b) is marked ?*."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_15c : LinguisticExample :=
  { id := "arka2013_15c"
    source := ⟨"arka-2013", "(15c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya belajar agar (bisa) menembak."
    discourseSegments := []
    glossedTokens := [("Saya", "1s"), ("belajar", "study"), ("agar", "so.that"), ("bisa", "able"), ("menembak", "AV.shoot")]
    translation := "I am learning so that I can shoot."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("withAux", "acceptable"), ("subordinator", "agar")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_18a : LinguisticExample :=
  { id := "arka2013_18a"
    source := ⟨"arka-2013", "(18a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "...di jalan banyak sapi yang sedang memakan rumput."
    discourseSegments := []
    glossedTokens := [("di", "at"), ("jalan", "road"), ("banyak", "plenty"), ("sapi", "cow"), ("yang", "REL"), ("sedang", "PROG"), ("memakan", "AV.eat"), ("rumput", "grass")]
    translation := "...along the way many cows that eat grass."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sedang"), ("voice", "AV")]
    comment := "Google-attested; the actor voice verb with sedang."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_18b : LinguisticExample :=
  { id := "arka2013_18b"
    source := ⟨"arka-2013", "(18b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dari salah satu swalayan, petugas menemukan makanan jenis roti yang kemasan dan isi=nya telah rusak dan diduga sudah dimakan tikus."
    discourseSegments := []
    glossedTokens := []
    translation := "In one of the supermarkets, the officers found kind of bread/biscuits in boxes whose packages had been tampered and contents were already eaten by mice."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sudah"), ("voice", "passive")]
    comment := "Google-attested; the passive verb with sudah."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34a : LinguisticExample :=
  { id := "arka2013_34a"
    source := ⟨"arka-2013", "(34a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', tanya=nya."
    discourseSegments := []
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("tanya=nya", "ask=NYA")]
    translation := "'Who is that?', he asked."
    context := ""
    judgment := .acceptable
    alternatives := [("'Siapa itu?' akan tanyanya (nanti).", .ungrammatical)]
    readings := [("he asked", .acceptable), ("he will ask", .unacceptable)]
    paperFeatures := [("nominalised", "true"), ("axis", "past"), ("predicate", "nominal"), ("withAux", "ungrammatical")]
    comment := "(34c) is the starred alternative: the nominalised verb takes no auxiliary."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_34b : LinguisticExample :=
  { id := "arka2013_34b"
    source := ⟨"arka-2013", "(34b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', tanya=nya nanti."
    discourseSegments := []
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("tanya=nya", "ask=NYA"), ("nanti", "later")]
    translation := "'Who is that?', he will ask later."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalised", "true"), ("axis", "future"), ("adjunct", "nanti")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_34d : LinguisticExample :=
  { id := "arka2013_34d"
    source := ⟨"arka-2013", "(34d)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', dia akan (ber)tanya (nanti)."
    discourseSegments := []
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("dia", "3"), ("akan", "FUT"), ("(ber)tanya", "BER-ask"), ("nanti", "later")]
    translation := "'Who is that?', he will ask later."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("clause", "root")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_35a : LinguisticExample :=
  { id := "arka2013_35a"
    source := ⟨"arka-2013", "(35a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan beli=nya?"
    discourseSegments := []
    glossedTokens := [("Kapan", "when"), ("beli=nya", "buy=NYA")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("kapan akan beli=nya?", .ungrammatical)]
    readings := [("When did you buy it?", .acceptable), ("When are you going to buy it?", .unacceptable)]
    paperFeatures := [("nominalised", "true"), ("axis", "past"), ("predicate", "nominal"), ("withAux", "ungrammatical")]
    comment := "(35b) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_35c : LinguisticExample :=
  { id := "arka2013_35c"
    source := ⟨"arka-2013", "(35c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan kamu akan beli?"
    discourseSegments := []
    glossedTokens := [("Kapan", "when"), ("kamu", "2s"), ("akan", "FUT"), ("beli", "buy")]
    translation := "When will you buy?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("clause", "root")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_36a : LinguisticExample :=
  { id := "arka2013_36a"
    source := ⟨"arka-2013", "(36a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan lahirnya?"
    discourseSegments := []
    glossedTokens := [("Kapan", "when"), ("lahir=nya", "birth=3s")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Kapan akan lahirnya?", .ungrammatical)]
    readings := [("When was s/he born?", .acceptable), ("When is s/he going to be born?", .unacceptable)]
    paperFeatures := [("nominalised", "true"), ("axis", "past"), ("predicate", "nominal"), ("withAux", "ungrammatical")]
    comment := "(36b) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_36c : LinguisticExample :=
  { id := "arka2013_36c"
    source := ⟨"arka-2013", "(36c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan ia akan lahir?"
    discourseSegments := []
    glossedTokens := [("Kapan", "when"), ("ia", "3s"), ("akan", "FUT"), ("lahir", "birth")]
    translation := "When will s/he be born?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("clause", "root")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_37a : LinguisticExample :=
  { id := "arka2013_37a"
    source := ⟨"arka-2013", "(37a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "kamu harus datang."
    discourseSegments := []
    glossedTokens := [("kamu", "2"), ("harus", "must"), ("datang", "come")]
    translation := "You should come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "harus"), ("nominalised", "false"), ("soa", "future"), ("evaluation", "deontic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_37b : LinguisticExample :=
  { id := "arka2013_37b"
    source := ⟨"arka-2013", "(37b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "harus=nya kamu datang."
    discourseSegments := []
    glossedTokens := [("harus=nya", "must=NYA"), ("kamu", "2"), ("datang", "come")]
    translation := "You should have come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "harus"), ("nominalised", "true"), ("soa", "past"), ("evaluation", "counterfactual")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_38a : LinguisticExample :=
  { id := "arka2013_38a"
    source := ⟨"arka-2013", "(38a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ia bisa menangis"
    discourseSegments := []
    glossedTokens := [("Ia", "she"), ("bisa", "can"), ("menangis", "cry")]
    translation := "S/he can cry."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "bisa"), ("nominalised", "false"), ("soa", "future"), ("evaluation", "epistemic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_38b : LinguisticExample :=
  { id := "arka2013_38b"
    source := ⟨"arka-2013", "(38b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "bisa=nya menangis"
    discourseSegments := []
    glossedTokens := [("bisa=nya", "can=3s"), ("menangis", "cry")]
    translation := "Crying was/is the thing s/he could do."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "bisa"), ("nominalised", "true"), ("soa", "past"), ("evaluation", "past ability")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_39a : LinguisticExample :=
  { id := "arka2013_39a"
    source := ⟨"arka-2013", "(39a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ia mau pulang."
    discourseSegments := []
    glossedTokens := [("Ia", "3s"), ("mau", "wish"), ("pulang", "go.home")]
    translation := "S/he wants/wanted to go home."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "mau"), ("nominalised", "false"), ("soa", "future")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_39b : LinguisticExample :=
  { id := "arka2013_39b"
    source := ⟨"arka-2013", "(39b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "mau=nya pulang."
    discourseSegments := []
    glossedTokens := [("mau=nya", "wish=DEF"), ("pulang", "go.home")]
    translation := "The/his/her/my wish was/is to go home (but for some reason (s)he/I couldn't)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "mau"), ("nominalised", "true"), ("soa", "present/past"), ("evaluation", "counterfactual")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_40a : LinguisticExample :=
  { id := "arka2013_40a"
    source := ⟨"arka-2013", "(40a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "tampak=nya [ada orang datang]"
    discourseSegments := []
    glossedTokens := [("tampak=nya", "appear=DEF"), ("ada", "exist"), ("orang", "person"), ("datang", "come")]
    translation := "It appears that there are people coming."
    context := ""
    judgment := .acceptable
    alternatives := [("sedang tampak=nya [ada orang datang].", .ungrammatical)]
    readings := []
    paperFeatures := [("nominalised", "true"), ("withAux", "ungrammatical"), ("evidential", "visual"), ("predicate", "nominal")]
    comment := "(40b) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_41 : LinguisticExample :=
  { id := "arka2013_41"
    source := ⟨"arka-2013", "(41)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tampak ada orang datang"
    discourseSegments := []
    glossedTokens := [("Tampak", "appear"), ("ada", "exist"), ("orang", "people"), ("datang", "come")]
    translation := "It is visible that there are people coming."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalised", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_42a : LinguisticExample :=
  { id := "arka2013_42a"
    source := ⟨"arka-2013", "(42a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sakit."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("sakit", "ill")]
    translation := "She was ill."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_42b : LinguisticExample :=
  { id := "arka2013_42b"
    source := ⟨"arka-2013", "(42b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sakit kata=nya."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("sakit", "ill"), ("kata=nya", "word=DEF")]
    translation := "She was ill, I heard."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("nominalised", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_43a : LinguisticExample :=
  { id := "arka2013_43a"
    source := ⟨"arka-2013", "(43a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kamu pembohong kata=nya"
    discourseSegments := []
    glossedTokens := [("Kamu", "2"), ("pembohong", "PEN.lie"), ("kata=nya", "word=DEF")]
    translation := "You're a liar, I heard."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("nominalised", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_43b : LinguisticExample :=
  { id := "arka2013_43b"
    source := ⟨"arka-2013", "(43b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kamu pembohong keluh=nya"
    discourseSegments := []
    glossedTokens := [("Kamu", "2"), ("pembohong", "PEN.lie"), ("keluh=nya", "word=3POSS")]
    translation := "You're a liar, s/he complained."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "none"), ("nominalised", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_44a : LinguisticExample :=
  { id := "arka2013_44a"
    source := ⟨"arka-2013", "(44a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia tidur."
    discourseSegments := []
    glossedTokens := [("Dia", "3s"), ("tidur", "sleep")]
    translation := "S/he is sleeping."
    context := ""
    judgment := .acceptable
    alternatives := [("Dia adalah tidur.", .ungrammatical)]
    readings := []
    paperFeatures := [("predicate", "verbal"), ("adalah", "ungrammatical")]
    comment := "(44b) is the starred alternative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_45a : LinguisticExample :=
  { id := "arka2013_45a"
    source := ⟨"arka-2013", "(45a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (adalah) guru itu."
    discourseSegments := []
    glossedTokens := [("Ali", "Ali"), ("adalah", "be"), ("guru", "teacher"), ("itu", "the")]
    translation := "Ali is the teacher."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("adalah", "acceptable")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_45b : LinguisticExample :=
  { id := "arka2013_45b"
    source := ⟨"arka-2013", "(45b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Guru itu (adalah) Ali."
    discourseSegments := []
    glossedTokens := []
    translation := "The teacher is Ali."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("adalah", "acceptable")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_46a : LinguisticExample :=
  { id := "arka2013_46a"
    source := ⟨"arka-2013", "(46a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[ _ tidur] (adalah) mau=nya"
    discourseSegments := []
    glossedTokens := [("tidur", "sleep"), ("adalah", "be"), ("mau=nya", "want=DEF")]
    translation := "To sleep was the wish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("adalah", "acceptable")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_46b : LinguisticExample :=
  { id := "arka2013_46b"
    source := ⟨"arka-2013", "(46b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mau=nya (adalah) [ _ tidur]"
    discourseSegments := []
    glossedTokens := [("Mau=nya", "want=DEF"), ("adalah", "be"), ("tidur", "sleep")]
    translation := "The/my wish was to sleep."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("adalah", "acceptable")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_47a : LinguisticExample :=
  { id := "arka2013_47a"
    source := ⟨"arka-2013", "(47a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali bukan/*tidak guru itu."
    discourseSegments := []
    glossedTokens := [("Ali", "Ali"), ("bukan", "NEG"), ("guru", "teacher"), ("itu", "that")]
    translation := "Ali is not the teacher."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("bukan", "acceptable"), ("tidak", "ungrammatical")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_47b : LinguisticExample :=
  { id := "arka2013_47b"
    source := ⟨"arka-2013", "(47b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Guru itu bukan/*tidak Ali."
    discourseSegments := []
    glossedTokens := []
    translation := "The teacher is not Ali."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("bukan", "acceptable"), ("tidak", "ungrammatical")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48a : LinguisticExample :=
  { id := "arka2013_48a"
    source := ⟨"arka-2013", "(48a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[_ tidur] bukan/*tidak mau=nya"
    discourseSegments := []
    glossedTokens := [("tidur", "sleep"), ("bukan", "NEG"), ("mau=nya", "want=DEF")]
    translation := "To sleep was not the/his/her wish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("bukan", "acceptable"), ("tidak", "ungrammatical")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_48b : LinguisticExample :=
  { id := "arka2013_48b"
    source := ⟨"arka-2013", "(48b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mau=nya bukan / tidak tidur"
    discourseSegments := []
    glossedTokens := [("Mau=nya", "want=DEF"), ("bukan/tidak", "NEG"), ("tidur", "sleep")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The/his/her/my wish was not to sleep.", .acceptable), ("It is the/her/his/your wish that (I/you/(s)he) would not sleep (but I did sleep).", .acceptable)]
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("bukan", "acceptable"), ("tidak", "acceptable")]
    comment := "tidak negates the internal clause headed by tidur."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_3, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_7, ex_8, ex_10, ex_11a, ex_11c, ex_12a, ex_12b, ex_13a, ex_14a, ex_15a, ex_15c, ex_18a, ex_18b, ex_34a, ex_34b, ex_34d, ex_35a, ex_35c, ex_36a, ex_36c, ex_37a, ex_37b, ex_38a, ex_38b, ex_39a, ex_39b, ex_40a, ex_41, ex_42a, ex_42b, ex_43a, ex_43b, ex_44a, ex_45a, ex_45b, ex_46a, ex_46b, ex_47a, ex_47b, ex_48a, ex_48b]

end Arka2013.Examples
