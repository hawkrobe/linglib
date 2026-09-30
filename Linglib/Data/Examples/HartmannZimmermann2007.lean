module

public import Linglib.Data.Examples.Schema

/-!
# `HartmannZimmermann2007` — typed example data

Auto-generated from `Linglib/Data/Examples/HartmannZimmermann2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartmannZimmermann2007.Examples`.
-/

@[expose] public section

namespace HartmannZimmermann2007.Examples

open Data.Examples

def ex3a : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex3a"
    source := ⟨"hartmann-zimmermann-2007", "(3a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kandè cee ta-kèe dafà kiifii."
    glossedTokens := [("Kandè", "Kande"), ("cee", "PRT"), ("ta-kèe", "3SG-REL.CONT"), ("dafà", "cooking"), ("kiifii", "fish")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "subject"), ("stabilizer", "cee"), ("host_tone", "L"), ("stab_tone", "H")] }

def ex3b : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex3b"
    source := ⟨"hartmann-zimmermann-2007", "(3b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kiifii nèe Kande ta-kèe dafàawaa."
    glossedTokens := [("Kiifii", "fish"), ("nèe", "PRT"), ("Kande", "Kande"), ("ta-kèe", "3SG-REL.CONT"), ("dafàawaa", "cooking")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "nonSubject"), ("stabilizer", "nee"), ("host_tone", "H"), ("stab_tone", "L")] }

def ex8 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex8"
    source := ⟨"hartmann-zimmermann-2007", "(8)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Audù zâi tàfi Jamùs."
    glossedTokens := [("Audù", "Audu"), ("zâi", "FUT.3SG"), ("tàfi", "go"), ("Jamùs", "Germany")]
    context := "Answer to: Wàaneenèe zâi tàfi Jamùs? 'Who will go to Germany?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "subject"), ("stabilizer", "none"), ("tam", "future")] }

def ex17a1 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex17a1"
    source := ⟨"hartmann-zimmermann-2007", "(17 A1)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Daudàa nee ya-kèe kirà-ntà."
    glossedTokens := [("Daudàa", "Dauda"), ("nee", "PRT"), ("ya-kèe", "3SG-REL.CONT"), ("kirà-ntà", "call-her")]
    context := "Answer to: Wàa ya-kèe kirà-ntà? 'Who is calling her?'"
    judgment := .acceptable
    alternatives := [("Daudàa ya-kèe kirà-ntà.", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "newInfo"), ("focused", "subject"), ("stabilizer", "nee"), ("tam", "continuous")] }

def ex17a2 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex17a2"
    source := ⟨"hartmann-zimmermann-2007", "(17 A2)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Daudàa ya-nàa kirà-ntà."
    glossedTokens := [("Daudàa", "Dauda"), ("ya-nàa", "3SG-CONT"), ("kirà-ntà", "call-her")]
    context := "Answer to: Wàa ya-kèe kirà-ntà? 'Who is calling her?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "newInfo"), ("focused", "subject"), ("stabilizer", "none"), ("tam", "continuous")] }

def ex22 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex22"
    source := ⟨"hartmann-zimmermann-2007", "(22)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kiifii nèe Kandè takèe dafàawaa."
    glossedTokens := [("Kiifii", "fish"), ("nèe", "PRT"), ("Kandè", "Kande"), ("takèe", "3SG-REL.CONT"), ("dafàawaa", "cooking")]
    context := "Answer to: Mèenee nèe Kandè ta-kèe dafàawaa? 'What is Kande cooking?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "newInfo"), ("focused", "nonSubject"), ("stabilizer", "nee")] }

def ex23 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex23"
    source := ⟨"randell-bature-schuh-1998", "HB 1.11"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(23)"⟩
    language := "haus1257"
    primaryText := "Naa tahoo dàgà Bir̃nin Ƙwànni."
    glossedTokens := [("Naa", "1SG.PERF"), ("tahoo", "come"), ("dàgà", "from"), ("Bir̃nin", "Birnin"), ("Ƙwànni", "Konni")]
    context := "Answer to: Dàgà wànè gàrii ka zoo? 'From which city do you come?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "newInfo"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex24 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex24"
    source := ⟨"hartmann-zimmermann-2007", "(24)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Aa'àa, màatar̃-sa cèe ta mutù."
    glossedTokens := [("Aa'àa", "no"), ("màatar̃-sa", "wife.of-3M"), ("cèe", "PRT"), ("ta", "3SG.REL.PERF"), ("mutù", "die")]
    context := "Corrective reply to: Tsoohowar̃-sà cee ta mutù? 'Was it his mother who died?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "corrective"), ("focused", "subject"), ("stabilizer", "cee")] }

def ex25 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex25"
    source := ⟨"randell-bature-schuh-1998", "HB 3.03"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(25)"⟩
    language := "haus1257"
    primaryText := "A'a, zân biyaa shâ bìyar̃ nèe."
    glossedTokens := [("A'a", "no"), ("zân", "FUT.1SG"), ("biyaa", "pay"), ("shâ bìyar̃", "fifteen"), ("nèe", "PRT")]
    context := "Corrective reply to: Nair̃àa àshìr̃in zaa kà biyaa in yaa yi makà. 'It is twenty Naira that you will pay if he makes it for you.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "corrective"), ("focused", "nonSubject"), ("stabilizer", "nee")] }

def ex26 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex26"
    source := ⟨"randell-bature-schuh-1998", "HB 1.10"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(26)"⟩
    language := "haus1257"
    primaryText := "Tô, zân iyà bî ta baayansà?"
    glossedTokens := [("Tô", "alright"), ("zân", "FUT.1SG"), ("iyà", "can"), ("bî", "follow"), ("ta", "in"), ("baayansà", "back.of.him")]
    context := "Contrastive reply to: In mùtûm yanàa yîn sallàa, baa àa bî ta gàbansà. 'If a man is praying, you shouldn't pass in front of him.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "contrastive"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex27 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex27"
    source := ⟨"randell-bature-schuh-1998", "HB 2.03"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(27)"⟩
    language := "haus1257"
    primaryText := "Koo hiir̃a baa àa yî, sai dai cî kawài a-kèe ta yî."
    glossedTokens := [("Koo", "and"), ("hiir̃a", "chatting"), ("baa àa", "NEG.4SG.CONT"), ("yî", "do"), ("sai", "PRT"), ("dai", "PRT"), ("cî", "eat"), ("kawài", "only"), ("a-kèe", "4SG-REL.CONT"), ("ta", "keep.on"), ("yî", "do")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "contrastive"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex29 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex29"
    source := ⟨"randell-bature-schuh-1998", "HB 1.10"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(29)"⟩
    language := "haus1257"
    primaryText := "Gùdaa nakèe sô!"
    glossedTokens := [("Gùdaa", "full"), ("nakèe", "1SG.REL.CONT"), ("sô", "want")]
    context := "Answer to: Gùdaa koo ɓaarìi? '(Do you want) a whole or a half?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "selective"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex30 : LinguisticExample :=
  { id := "hartmannzimmermann2007_ex30"
    source := ⟨"jaggar-2001", "p. 498"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(30)"⟩
    language := "haus1257"
    primaryText := "Zân shaa shaayìi."
    glossedTokens := [("Zân", "FUT.1SG"), ("shaa", "drink"), ("shaayìi", "tea")]
    context := "Answer to: Kòofii zaa-kà shaa koo kùwa shaayìi? 'Will you drink coffee or tea?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "selective"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def all : List LinguisticExample := [ex3a, ex3b, ex8, ex17a1, ex17a2, ex22, ex23, ex24, ex25, ex26, ex27, ex29, ex30]

end HartmannZimmermann2007.Examples
