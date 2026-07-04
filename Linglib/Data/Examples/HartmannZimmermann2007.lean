import Linglib.Data.Examples.Schema

/-!
# `HartmannZimmermann2007` — typed example data

Auto-generated from `Linglib/Data/Examples/HartmannZimmermann2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartmannZimmermann2007.Examples`.
-/

namespace HartmannZimmermann2007.Examples

open Data.Examples

def ex3a : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex3a"
    source := ⟨"hartmann-zimmermann-2007", "(3a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kandè cee ta-kèe dafà kiifii."
    discourseSegments := []
    glossedTokens := [("Kandè", "Kande"), ("cee", "PRT"), ("ta-kèe", "3SG-REL.CONT"), ("dafà", "cooking"), ("kiifii", "fish")]
    translation := "KANDE is cooking the fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "subject"), ("stabilizer", "cee"), ("host_tone", "L"), ("stab_tone", "H")]
    comment := "Polar tone: the host Kandè ends low, so the stabilizer surfaces high."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3b : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex3b"
    source := ⟨"hartmann-zimmermann-2007", "(3b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kiifii nèe Kande ta-kèe dafàawaa."
    discourseSegments := []
    glossedTokens := [("Kiifii", "fish"), ("nèe", "PRT"), ("Kande", "Kande"), ("ta-kèe", "3SG-REL.CONT"), ("dafàawaa", "cooking")]
    translation := "Kande is cooking the FISH."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "nonSubject"), ("stabilizer", "nee"), ("host_tone", "H"), ("stab_tone", "L")]
    comment := "Polar tone: the host Kiifii ends high (unmarked vowel), so the stabilizer surfaces low."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex8"
    source := ⟨"hartmann-zimmermann-2007", "(8)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Audù zâi tàfi Jamùs."
    discourseSegments := []
    glossedTokens := [("Audù", "Audu"), ("zâi", "FUT.3SG"), ("tàfi", "go"), ("Jamùs", "Germany")]
    translation := "Audu will go to Germany."
    context := "Answer to: Wàaneenèe zâi tàfi Jamùs? 'Who will go to Germany?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "subject"), ("stabilizer", "none"), ("tam", "future")]
    comment := "Subject focus with no overt marking: the future TAM has no Relative form, so the (vacuous) fronting is invisible — 'subject foci are syntactically and morphologically unmarked in the future, habitual and subjunctive aspects' (p. 4)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17a1 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex17a1"
    source := ⟨"hartmann-zimmermann-2007", "(17 A1)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Daudàa nee ya-kèe kirà-ntà."
    discourseSegments := []
    glossedTokens := [("Daudàa", "Dauda"), ("nee", "PRT"), ("ya-kèe", "3SG-REL.CONT"), ("kirà-ntà", "call-her")]
    translation := "Dauda is calling her."
    context := "Answer to: Wàa ya-kèe kirà-ntà? 'Who is calling her?'"
    judgment := .acceptable
    alternatives := [("Daudàa ya-kèe kirà-ntà.", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "newInfo"), ("focused", "subject"), ("stabilizer", "nee"), ("tam", "continuous")]
    comment := "The particle is parenthesized-optional in the paper; the alternative records the particle-less variant."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17a2 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex17a2"
    source := ⟨"hartmann-zimmermann-2007", "(17 A2)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Daudàa ya-nàa kirà-ntà."
    discourseSegments := []
    glossedTokens := [("Daudàa", "Dauda"), ("ya-nàa", "3SG-CONT"), ("kirà-ntà", "call-her")]
    translation := "Dauda is calling her."
    context := "Answer to: Wàa ya-kèe kirà-ntà? 'Who is calling her?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "newInfo"), ("focused", "subject"), ("stabilizer", "none"), ("tam", "continuous")]
    comment := "Infelicitous as an answer to the subject wh-question: focused subjects cannot be realised in situ (paper §2.2.2); the General-mode auxiliary betrays the absence of movement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex22 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex22"
    source := ⟨"hartmann-zimmermann-2007", "(22)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kiifii nèe Kandè takèe dafàawaa."
    discourseSegments := []
    glossedTokens := [("Kiifii", "fish"), ("nèe", "PRT"), ("Kandè", "Kande"), ("takèe", "3SG-REL.CONT"), ("dafàawaa", "cooking")]
    translation := "Kande is cooking the FISH."
    context := "Answer to: Mèenee nèe Kandè ta-kèe dafàawaa? 'What is Kande cooking?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "newInfo"), ("focused", "nonSubject"), ("stabilizer", "nee")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex23"
    source := ⟨"randell-bature-schuh-1998", "HB 1.11"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(23)"⟩
    language := "haus1257"
    primaryText := "Naa tahoo dàgà Bir̃nin Ƙwànni."
    discourseSegments := []
    glossedTokens := [("Naa", "1SG.PERF"), ("tahoo", "come"), ("dàgà", "from"), ("Bir̃nin", "Birnin"), ("Ƙwànni", "Konni")]
    translation := "I came from BIRNIN KONNI."
    context := "Answer to: Dàgà wànè gàrii ka zoo? 'From which city do you come?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "newInfo"), ("focused", "nonSubject"), ("stabilizer", "none")]
    comment := "In-situ new-information focus with no morphosyntactic reflex at all — the witness for the BFR refutation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex24"
    source := ⟨"hartmann-zimmermann-2007", "(24)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Aa'àa, màatar̃-sa cèe ta mutù."
    discourseSegments := []
    glossedTokens := [("Aa'àa", "no"), ("màatar̃-sa", "wife.of-3M"), ("cèe", "PRT"), ("ta", "3SG.REL.PERF"), ("mutù", "die")]
    translation := "No, it was HIS WIFE who died."
    context := "Corrective reply to: Tsoohowar̃-sà cee ta mutù? 'Was it his mother who died?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "corrective"), ("focused", "subject"), ("stabilizer", "cee")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex25"
    source := ⟨"randell-bature-schuh-1998", "HB 3.03"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(25)"⟩
    language := "haus1257"
    primaryText := "A'a, zân biyaa shâ bìyar̃ nèe."
    discourseSegments := []
    glossedTokens := [("A'a", "no"), ("zân", "FUT.1SG"), ("biyaa", "pay"), ("shâ bìyar̃", "fifteen"), ("nèe", "PRT")]
    translation := "No, I will pay FIFTEEN."
    context := "Corrective reply to: Nair̃àa àshir̃in zaa kà biyaa in yaa yi makà. 'It is twenty Naira that you will pay if he makes it for you.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "corrective"), ("focused", "nonSubject"), ("stabilizer", "nee")]
    comment := "In-situ focus with the sentence-final particle nèe — a stabilizer without fronting or Relative morphology."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex26"
    source := ⟨"randell-bature-schuh-1998", "HB 1.10"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(26)"⟩
    language := "haus1257"
    primaryText := "Tô, zân iyà bî ta baayansà?"
    discourseSegments := []
    glossedTokens := [("Tô", "alright"), ("zân", "FUT.1SG"), ("iyà", "can"), ("bî", "follow"), ("ta", "in"), ("baayansà", "back.of.him")]
    translation := "Alright, but can I pass BEHIND him?"
    context := "Contrastive reply to: In mùtûm yanàa yîn sallàa, baa àa bî ta gàbansà. 'If a man is praying, you shouldn't pass in front of him.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "contrastive"), ("focused", "nonSubject"), ("stabilizer", "none")]
    comment := "baayansà 'behind him' contrasts with the preceding utterance's ta gàbansà 'in front of him'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex27"
    source := ⟨"randell-bature-schuh-1998", "HB 2.03"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(27)"⟩
    language := "haus1257"
    primaryText := "Koo hiir̃a baa àa yî, sai dai cî kawài a-kèe ta yî."
    discourseSegments := []
    glossedTokens := [("Koo", "and"), ("hiir̃a", "chatting"), ("baa àa", "NEG.4SG.CONT"), ("yî", "do"), ("sai", "PRT"), ("dai", "PRT"), ("cî", "eat"), ("kawài", "only"), ("a-kèe", "4SG-REL.CONT"), ("ta", "keep.on"), ("yî", "do")]
    translation := "And no one is chatting, it is only EATING that is going on."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "contrastive"), ("focused", "nonSubject"), ("stabilizer", "none")]
    comment := "The fronted nominalised verb cî 'eating' contrasts with hiir̃a 'chatting'; the exhaustive flavour comes from kawài 'only' (paper §3.2.3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex29"
    source := ⟨"randell-bature-schuh-1998", "HB 1.10"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(29)"⟩
    language := "haus1257"
    primaryText := "Gùdaa nakèe sô!"
    discourseSegments := []
    glossedTokens := [("Gùdaa", "full"), ("nakèe", "1SG.REL.CONT"), ("sô", "want")]
    translation := "I want a WHOLE."
    context := "Answer to: Gùdaa koo ɓaarìi? '(Do you want) a whole or a half?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "selective"), ("focused", "nonSubject"), ("stabilizer", "none")]
    comment := "The paper's gloss reads 1sg.rel.perf, an apparent erratum: the kèe formative is the Relative continuous (cf. the paper's exx. 16, 22, 27)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex30"
    source := ⟨"jaggar-2001", "p. 498"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(30)"⟩
    language := "haus1257"
    primaryText := "Zân shaa shaayìi."
    discourseSegments := []
    glossedTokens := [("Zân", "FUT.1SG"), ("shaa", "drink"), ("shaayìi", "tea")]
    translation := "I will drink TEA."
    context := "Answer to: Kòofii zaa-kà shaa koo kùwa shaayìi? 'Will you drink coffee or tea?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "selective"), ("focused", "nonSubject"), ("stabilizer", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex3a, ex3b, ex8, ex17a1, ex17a2, ex22, ex23, ex24, ex25, ex26, ex27, ex29, ex30]

end HartmannZimmermann2007.Examples
