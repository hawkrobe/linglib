module

public import Linglib.Data.Examples.Schema

/-!
# `CoonKeine2021` — typed example data

Auto-generated from `Linglib/Data/Examples/CoonKeine2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CoonKeine2021.Examples`.
-/

@[expose] public section

namespace CoonKeine2021.Examples

open Data.Examples

def ex_3a : LinguisticExample :=
  { id := "coonkeine2021_3a"
    source := ⟨"coon-keine-2021", "(3a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zu-k harakina-ri liburua saldu d-i-o-zu."
    glossedTokens := [("Zu-k", "you-ERG"), ("harakina-ri", "butcher-DAT"), ("liburua", "book.ABS"), ("saldu", "sold"), ("d-i-o-zu", "3ABS-AUX-3DAT-2ERG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_3b : LinguisticExample :=
  { id := "coonkeine2021_3b"
    source := ⟨"laka-1993", "p. 27"⟩
    reportedIn := some ⟨"coon-keine-2021", "(3b)"⟩
    language := "basq1248"
    primaryText := "Zu-k ni-ri liburua saldu d-i-da-zu."
    glossedTokens := [("Zu-k", "you-ERG"), ("ni-ri", "me-DAT"), ("liburua", "book.ABS"), ("saldu", "sold"), ("d-i-da-zu", "3ABS-AUX-1DAT-2ERG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "1"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_3c : LinguisticExample :=
  { id := "coonkeine2021_3c"
    source := ⟨"laka-1993", "p. 27"⟩
    reportedIn := some ⟨"coon-keine-2021", "(3c)"⟩
    language := "basq1248"
    primaryText := "Zu-k harakina-ri ni saldu n-(a)i-o-zu."
    glossedTokens := [("Zu-k", "you-ERG"), ("harakina-ri", "butcher-DAT"), ("ni", "me.ABS"), ("saldu", "sold"), ("n-(a)i-o-zu", "1ABS-AUX-3DAT-2ERG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_3d : LinguisticExample :=
  { id := "coonkeine2021_3d"
    source := ⟨"coon-keine-2021", "(3d)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Haiek ni-ri zu saldu z-ai-da-te."
    glossedTokens := [("Haiek", "they.ERG"), ("ni-ri", "me-DAT"), ("zu", "you.ABS"), ("saldu", "sold"), ("z-ai-da-te", "2ABS-AUX-1DAT-3ERG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "1"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_10b : LinguisticExample :=
  { id := "coonkeine2021_10b"
    source := ⟨"coon-keine-2021", "(10b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Gaizki iruditzen -zai-t zu-k harakina-ri ni sal-tze-a."
    glossedTokens := [("Gaizki", "wrong"), ("iruditzen", "look.IPFV"), ("-zai-t", "3ABS-AUX-1DAT"), ("zu-k", "you-ERG"), ("harakina-ri", "butcher-DAT"), ("ni", "me.ABS"), ("sal-tze-a", "sell-NMLZ-ART.ABS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "nonfinite"), ("probe", "none"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_10c : LinguisticExample :=
  { id := "coonkeine2021_10c"
    source := ⟨"coon-keine-2021", "(10c)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zu-k harakina-ri ni sal-tze-n probatu d-u-zu."
    glossedTokens := [("Zu-k", "you-ERG"), ("harakina-ri", "butcher-DAT"), ("ni", "me.ABS"), ("sal-tze-n", "sell-NMLZ-LOC"), ("probatu", "attempted"), ("d-u-zu", "3ABS-AUX-2ERG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "nonfinite"), ("probe", "none"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_37a : LinguisticExample :=
  { id := "coonkeine2021_37a"
    source := ⟨"coon-keine-2021", "(37a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Ni Itxaso-ri gustatzen n-atzai-o."
    glossedTokens := [("Ni", "me.ABS"), ("Itxaso-ri", "Itxaso-DAT"), ("gustatzen", "like.IPFV"), ("n-atzai-o", "1ABS-AUX-3DAT")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datAbs"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_37b : LinguisticExample :=
  { id := "coonkeine2021_37b"
    source := ⟨"coon-keine-2021", "(37b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Itxaso ni-ri etortzen -zai-t."
    glossedTokens := [("Itxaso", "Itxaso.ABS"), ("ni-ri", "me-DAT"), ("etortzen", "come.IPFV"), ("-zai-t", "3ABS-AUX-1DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "absDat"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("lowerOpaque", "yes"), ("aftermath", "clitic")] }

def ex_41 : LinguisticExample :=
  { id := "coonkeine2021_41"
    source := ⟨"coon-keine-2021", "(41)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zu-k merkataria-ri liburuak saldu d-i-zki-o-zu."
    glossedTokens := [("Zu-k", "you-ERG"), ("merkataria-ri", "merchant-DAT"), ("liburuak", "book.PL.ABS"), ("saldu", "sold"), ("d-i-zki-o-zu", "3ABS-AUX-PL-3DAT-2ERG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "3"), ("lowerNumber", "pl"), ("aftermath", "clitic")] }

def ex_50 : LinguisticExample :=
  { id := "coonkeine2021_50"
    source := ⟨"rezac-2008", "p. 81"⟩
    reportedIn := some ⟨"coon-keine-2021", "(50)"⟩
    language := "basq1248"
    primaryText := "Itxaso-ri zu-k gustatzen d-i-o-zu."
    glossedTokens := [("Itxaso-ri", "Itxaso-DAT"), ("zu-k", "you-ERG"), ("gustatzen", "like.IPFV"), ("d-i-o-zu", "3ABS-AUX-3DAT-2ERG")]
    context := ""
    judgment := .acceptable
    alternatives := [("*zu (you.ABS)", .ungrammatical)]
    readings := []
    paperFeatures := [("construction", "repair"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "2"), ("lowerNumber", "sg"), ("lowerShielded", "yes"), ("aftermath", "clitic")] }

def ex_24 : LinguisticExample :=
  { id := "coonkeine2021_24"
    source := ⟨"bonet-1991", "p. 178"⟩
    reportedIn := some ⟨"coon-keine-2021", "(24)"⟩
    language := "stan1289"
    primaryText := "En Josep, te 'l va recomenar la Mireia."
    glossedTokens := [("En", "the"), ("Josep", "Josep"), ("te", "2DAT.CL"), ("'l", "3ACC.CL"), ("va recomenar", "recommended"), ("la", "the"), ("Mireia", "Mireia")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "2"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_28 : LinguisticExample :=
  { id := "coonkeine2021_28"
    source := ⟨"bonet-1991", "p. 179"⟩
    reportedIn := some ⟨"coon-keine-2021", "(28)"⟩
    language := "stan1289"
    primaryText := "A en Josep, te li va recomanar la Mireia."
    glossedTokens := [("A", "to"), ("en", "the"), ("Josep", "Josep"), ("te", "2ACC.CL"), ("li", "3DAT.CL"), ("va recomanar", "recommended"), ("la", "the"), ("Mireia", "Mireia")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_31_2_1 : LinguisticExample :=
  { id := "coonkeine2021_31_2_1"
    source := ⟨"bonet-1991", "p. 179"⟩
    reportedIn := some ⟨"coon-keine-2021", "(31)"⟩
    language := "stan1289"
    primaryText := "Te'm van recomanar per a la feina."
    glossedTokens := [("Te'm", "2CL.1CL"), ("van recomanar", "recommended"), ("per a", "for"), ("la", "the"), ("feina", "job")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("2 > 1", .acceptable), ("1 > 2", .acceptable)]
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "2"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_31_1_2 : LinguisticExample :=
  { id := "coonkeine2021_31_1_2"
    source := ⟨"bonet-1991", "p. 179"⟩
    reportedIn := some ⟨"coon-keine-2021", "(31)"⟩
    language := "stan1289"
    primaryText := "Te'm van recomanar per a la feina."
    glossedTokens := [("Te'm", "2CL.1CL"), ("van recomanar", "recommended"), ("per a", "for"), ("la", "the"), ("feina", "job")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("2 > 1", .acceptable), ("1 > 2", .acceptable)]
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "1"), ("higherNumber", "sg"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_44a : LinguisticExample :=
  { id := "coonkeine2021_44a"
    source := ⟨"stegovec-2020", "p. 264"⟩
    reportedIn := some ⟨"coon-keine-2021", "(44a)"⟩
    language := "slov1268"
    primaryText := "Mama mu ga bo predstavila."
    glossedTokens := [("Mama", "Mom"), ("mu", "3M.DAT"), ("ga", "3M.ACC"), ("bo", "will"), ("predstavila", "introduce")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "branching"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_44a_me : LinguisticExample :=
  { id := "coonkeine2021_44a_me"
    source := ⟨"stegovec-2020", "p. 264"⟩
    reportedIn := some ⟨"coon-keine-2021", "(44a)"⟩
    language := "slov1268"
    primaryText := "Mama mu me bo predstavila."
    glossedTokens := [("Mama", "Mom"), ("mu", "3M.DAT"), ("me", "1ACC"), ("bo", "will"), ("predstavila", "introduce")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "branching"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_44a_te : LinguisticExample :=
  { id := "coonkeine2021_44a_te"
    source := ⟨"stegovec-2020", "p. 264"⟩
    reportedIn := some ⟨"coon-keine-2021", "(44a)"⟩
    language := "slov1268"
    primaryText := "Mama mu te bo predstavila."
    glossedTokens := [("Mama", "Mom"), ("mu", "3M.DAT"), ("te", "2ACC"), ("bo", "will"), ("predstavila", "introduce")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "branching"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_44b : LinguisticExample :=
  { id := "coonkeine2021_44b"
    source := ⟨"stegovec-2020", "p. 264"⟩
    reportedIn := some ⟨"coon-keine-2021", "(44b)"⟩
    language := "slov1268"
    primaryText := "Mama ga mu bo predstavila."
    glossedTokens := [("Mama", "Mom"), ("ga", "3M.ACC"), ("mu", "3M.DAT"), ("bo", "will"), ("predstavila", "introduce")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reverse"), ("probe", "branching"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_44b_mi : LinguisticExample :=
  { id := "coonkeine2021_44b_mi"
    source := ⟨"stegovec-2020", "p. 264"⟩
    reportedIn := some ⟨"coon-keine-2021", "(44b)"⟩
    language := "slov1268"
    primaryText := "Mama ga mi bo predstavila."
    glossedTokens := [("Mama", "Mom"), ("ga", "3M.ACC"), ("mi", "1DAT"), ("bo", "will"), ("predstavila", "introduce")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reverse"), ("probe", "branching"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_44b_ti : LinguisticExample :=
  { id := "coonkeine2021_44b_ti"
    source := ⟨"stegovec-2020", "p. 264"⟩
    reportedIn := some ⟨"coon-keine-2021", "(44b)"⟩
    language := "slov1268"
    primaryText := "Mama ga ti bo predstavila."
    glossedTokens := [("Mama", "Mom"), ("ga", "3M.ACC"), ("ti", "2DAT"), ("bo", "will"), ("predstavila", "introduce")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reverse"), ("probe", "branching"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_46a : LinguisticExample :=
  { id := "coonkeine2021_46a"
    source := ⟨"anagnostopoulou-2003", "p. 311"⟩
    reportedIn := some ⟨"coon-keine-2021", "(46a)"⟩
    language := "stan1290"
    primaryText := "Paul me lui présentera."
    glossedTokens := [("Paul", "Paul"), ("me", "CL.1SG"), ("lui", "CL.3SG"), ("présentera", "will.introduce")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_46b : LinguisticExample :=
  { id := "coonkeine2021_46b"
    source := ⟨"anagnostopoulou-2003", "p. 311"⟩
    reportedIn := some ⟨"coon-keine-2021", "(46b)"⟩
    language := "stan1290"
    primaryText := "Paul me présentera à lui."
    glossedTokens := [("Paul", "Paul"), ("me", "CL.1SG"), ("présentera", "will.introduce"), ("à", "to"), ("lui", "him")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "repair"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("higherShielded", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_48a : LinguisticExample :=
  { id := "coonkeine2021_48a"
    source := ⟨"anagnostopoulou-2017b", "pp. 3004, 3006"⟩
    reportedIn := some ⟨"coon-keine-2021", "(48a)"⟩
    language := "mode1248"
    primaryText := "Tha tu se stilune."
    glossedTokens := [("Tha", "FUT"), ("tu", "CL.GEN.3SG.M"), ("se", "CL.ACC.2SG"), ("stilune", "send.3PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ditransitive"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "clitic")] }

def ex_48b : LinguisticExample :=
  { id := "coonkeine2021_48b"
    source := ⟨"anagnostopoulou-2017b", "pp. 3004, 3006"⟩
    reportedIn := some ⟨"coon-keine-2021", "(48b)"⟩
    language := "mode1248"
    primaryText := "Tha tu stilune esena."
    glossedTokens := [("Tha", "FUT"), ("tu", "CL.GEN.3SG.M"), ("stilune", "send.3PL"), ("esena", "you.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "repair"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "2"), ("lowerNumber", "sg"), ("lowerShielded", "yes"), ("aftermath", "clitic")] }

def ex_51a : LinguisticExample :=
  { id := "coonkeine2021_51a"
    source := ⟨"coon-keine-2021", "(51a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du bist Martin."
    glossedTokens := [("Du", "you.NOM"), ("bist", "are"), ("Martin", "Martin.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "2"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "germanPresent")] }

def ex_51b : LinguisticExample :=
  { id := "coonkeine2021_51b"
    source := ⟨"coon-keine-2021", "(51b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Martin ist du."
    glossedTokens := [("Martin", "Martin.NOM"), ("ist", "is"), ("du", "you.NOM")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "germanPresent")] }

def ex_52a : LinguisticExample :=
  { id := "coonkeine2021_52a"
    source := ⟨"coon-keine-2021", "(52a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Kinder sind der Baum."
    glossedTokens := [("Die", "the"), ("Kinder", "children.NOM"), ("sind", "are"), ("der", "the"), ("Baum", "tree.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "pl"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "germanPresent")] }

def ex_52b : LinguisticExample :=
  { id := "coonkeine2021_52b"
    source := ⟨"coon-keine-2021", "(52b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria ist die Bäume."
    glossedTokens := [("Maria", "Maria.NOM"), ("ist", "is"), ("die", "the"), ("Bäume", "trees.NOM")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "germanPresent")] }

def ex_54a : LinguisticExample :=
  { id := "coonkeine2021_54a"
    source := ⟨"coon-keine-2021", "(54a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Martin scheint du zu sein."
    glossedTokens := [("Martin", "Martin.NOM"), ("scheint", "seems"), ("du", "you.NOM"), ("zu", "to"), ("sein", "be")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "nonfinite"), ("probe", "none"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "germanPresent")] }

def ex_54b : LinguisticExample :=
  { id := "coonkeine2021_54b"
    source := ⟨"coon-keine-2021", "(54b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria scheint die Bäume zu sein."
    glossedTokens := [("Maria", "Maria.NOM"), ("scheint", "seems"), ("die", "the"), ("Bäume", "trees.NOM"), ("zu", "to"), ("sein", "be")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "nonfinite"), ("probe", "none"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "germanPresent")] }

def fn32_ia : LinguisticExample :=
  { id := "coonkeine2021_fn32_ia"
    source := ⟨"coon-keine-2021", "fn. 32 (ia)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Martin war ich."
    glossedTokens := [("Martin", "Martin.NOM"), ("war", "was.3SG/1SG"), ("ich", "I.NOM")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "germanPast")] }

def ex_68a : LinguisticExample :=
  { id := "coonkeine2021_68a"
    source := ⟨"bhatia-bhatt-2019", "p. 3"⟩
    reportedIn := some ⟨"coon-keine-2021", "(68a)"⟩
    language := "hind1269"
    primaryText := "aaj-se mẼ Ramesh hũ:"
    glossedTokens := [("aaj-se", "today-from"), ("mẼ", "I"), ("Ramesh", "Ramesh"), ("hũ:", "be.PRS.1SG")]
    context := "A Bollywood movie where two people are swapping identities."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "1"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "hindiPresent")] }

def ex_68b : LinguisticExample :=
  { id := "coonkeine2021_68b"
    source := ⟨"bhatia-bhatt-2019", "p. 3"⟩
    reportedIn := some ⟨"coon-keine-2021", "(68b)"⟩
    language := "hind1269"
    primaryText := "aaj-se Ramesh mẼ hai"
    glossedTokens := [("aaj-se", "today-from"), ("Ramesh", "Ramesh"), ("mẼ", "I"), ("hai", "be.PRS.3SG")]
    context := "A Bollywood movie where someone is swapping identities with me."
    judgment := .ungrammatical
    alternatives := [("aaj-se Ramesh mẼ hũ:", .ungrammatical)]
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "hindiPresent")] }

def ex_69a : LinguisticExample :=
  { id := "coonkeine2021_69a"
    source := ⟨"coon-keine-2021", "(69a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "is naaTak-mẽ do log Ram hẼ"
    glossedTokens := [("is", "this"), ("naaTak-mẽ", "play-in"), ("do", "two"), ("log", "people"), ("Ram", "Ram"), ("hẼ", "be.PRS.3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "pl"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "hindiPresent")] }

def ex_69b : LinguisticExample :=
  { id := "coonkeine2021_69b"
    source := ⟨"coon-keine-2021", "(69b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "is naaTak-mẽ Ram do paatr hai"
    glossedTokens := [("is", "this"), ("naaTak-mẽ", "play-in"), ("Ram", "Ram"), ("do", "two"), ("paatr", "characters"), ("hai", "be.PRS.3SG")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "hindiPresent")] }

def fn34_i : LinguisticExample :=
  { id := "coonkeine2021_fn34_i"
    source := ⟨"bhatia-bhatt-2019", "p. 6"⟩
    reportedIn := some ⟨"coon-keine-2021", "fn. 34 (i)"⟩
    language := "hind1269"
    primaryText := "us din mẼ Ramesh tha: aur Ramesh mẼ tha:"
    glossedTokens := [("us", "that"), ("din", "day"), ("mẼ", "I"), ("Ramesh", "Ramesh"), ("tha:", "be.PST.M.SG"), ("aur", "and"), ("Ramesh", "Ramesh"), ("mẼ", "I"), ("tha:", "be.PST.M.SG")]
    context := "A Bollywood movie where I swapped identities with Ramesh."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "hindiPast")] }

def ex_70a : LinguisticExample :=
  { id := "coonkeine2021_70a"
    source := ⟨"coon-keine-2021", "(70a)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Eu sou ele."
    glossedTokens := [("Eu", "I"), ("sou", "am"), ("ele", "he")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "1"), ("higherNumber", "sg"), ("lower", "3"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "portuguesePresent")] }

def ex_70b : LinguisticExample :=
  { id := "coonkeine2021_70b"
    source := ⟨"coon-keine-2021", "(70b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Ele é eu."
    glossedTokens := [("Ele", "he"), ("é", "is"), ("eu", "I")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "portuguesePresent")] }

def ex_71 : LinguisticExample :=
  { id := "coonkeine2021_71"
    source := ⟨"coon-keine-2021", "(71)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann er þú."
    glossedTokens := [("Hann", "he.NOM"), ("er", "is.3SG"), ("þú", "you.SG.NOM")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("higher", "3"), ("lower", "2")] }

def ex_72 : LinguisticExample :=
  { id := "coonkeine2021_72"
    source := ⟨"coon-keine-2021", "(72)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann er trén."
    glossedTokens := [("Hann", "he.NOM"), ("er", "is.3SG"), ("trén", "trees.NOM")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "copula"), ("higher", "3"), ("lower", "3"), ("lowerNumber", "pl")] }

def ex_73 : LinguisticExample :=
  { id := "coonkeine2021_73"
    source := ⟨"sigurdsson-holmberg-2008", "p. 260"⟩
    reportedIn := some ⟨"coon-keine-2021", "(73)"⟩
    language := "icel1247"
    primaryText := "að henni líkaði þeir"
    glossedTokens := [("að", "that"), ("henni", "her.DAT"), ("líkaði", "liked.3SG"), ("þeir", "they.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("higher", "3"), ("lower", "3"), ("lowerNumber", "pl")] }

def ex_74 : LinguisticExample :=
  { id := "coonkeine2021_74"
    source := ⟨"sigurdsson-1996", "p. 1"⟩
    reportedIn := some ⟨"coon-keine-2021", "(74)"⟩
    language := "icel1247"
    primaryText := "Henni leiddust strákarnir."
    glossedTokens := [("Henni", "her.DAT"), ("leiddust", "bored.3PL"), ("strákarnir", "the.boys.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "3"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "icelandicMediopassivePast")] }

def ex_76a : LinguisticExample :=
  { id := "coonkeine2021_76a"
    source := ⟨"sigurdsson-holmberg-2008", "p. 270"⟩
    reportedIn := some ⟨"coon-keine-2021", "(76a)"⟩
    language := "icel1247"
    primaryText := "Henni leiddumst við."
    glossedTokens := [("Henni", "her.DAT"), ("leiddumst", "bored.1PL"), ("við", "we.NOM")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "icelandicMediopassivePast")] }

def ex_76b : LinguisticExample :=
  { id := "coonkeine2021_76b"
    source := ⟨"sigurdsson-1996", "p. 33"⟩
    reportedIn := some ⟨"coon-keine-2021", "(76b)"⟩
    language := "icel1247"
    primaryText := "Henni líkaðir þú."
    glossedTokens := [("Henni", "her.DAT"), ("líkaðir", "like.2SG"), ("þú", "you.SG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "2"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "icelandicLikaPast")] }

def ex_77 : LinguisticExample :=
  { id := "coonkeine2021_77"
    source := ⟨"sigurdsson-holmberg-2008", "p. 271"⟩
    reportedIn := some ⟨"coon-keine-2021", "(77)"⟩
    language := "icel1247"
    primaryText := "Hún vonaðist auðvitað til að leiðast við ekki mikið."
    glossedTokens := [("Hún", "she"), ("vonaðist", "hoped"), ("auðvitað", "of.course"), ("til", "for"), ("að", "to"), ("leiðast", "find.boring.INF"), ("við", "we.NOM"), ("ekki", "not"), ("mikið", "much")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "nonfinite"), ("probe", "none"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "icelandicMediopassivePast")] }

def ex_78a : LinguisticExample :=
  { id := "coonkeine2021_78a"
    source := ⟨"hrafnbjargarson-2002", "p. 2"⟩
    reportedIn := some ⟨"coon-keine-2021", "(78a)"⟩
    language := "icel1247"
    primaryText := "Mér þykja þau góð í fótbolta."
    glossedTokens := [("Mér", "me.DAT"), ("þykja", "think.3PL"), ("þau", "they.NOM"), ("góð", "good"), ("í", "in"), ("fótbolta", "soccer")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "1"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "3"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "icelandicThykjaPresent")] }

def ex_78b_agree : LinguisticExample :=
  { id := "coonkeine2021_78b_agree"
    source := ⟨"hrafnbjargarson-2002", "p. 2"⟩
    reportedIn := some ⟨"coon-keine-2021", "(78b)"⟩
    language := "icel1247"
    primaryText := "Ykkur þyki ég góður í fótbolta."
    glossedTokens := [("Ykkur", "you.PL.DAT"), ("þyki", "think.1SG"), ("ég", "I.NOM"), ("góður", "good"), ("í", "in"), ("fótbolta", "soccer")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "2"), ("higherNumber", "pl"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("aftermath", "agreement"), ("paradigm", "icelandicThykjaPresent")] }

def ex_78b : LinguisticExample :=
  { id := "coonkeine2021_78b"
    source := ⟨"hrafnbjargarson-2002", "p. 2"⟩
    reportedIn := some ⟨"coon-keine-2021", "(78b)"⟩
    language := "icel1247"
    primaryText := "Ykkur þykir ég góður í fótbolta."
    glossedTokens := [("Ykkur", "you.PL.DAT"), ("þykir", "think.3SG"), ("ég", "I.NOM"), ("góður", "good"), ("í", "in"), ("fótbolta", "soccer")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "2"), ("higherNumber", "pl"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "sg"), ("lowerShielded", "yes"), ("aftermath", "agreement"), ("paradigm", "icelandicThykjaPresent")] }

def ex_84a : LinguisticExample :=
  { id := "coonkeine2021_84a"
    source := ⟨"sigurdsson-holmberg-2008", "p. 270"⟩
    reportedIn := some ⟨"coon-keine-2021", "(84a)"⟩
    language := "icel1247"
    primaryText := "Henni virtust þið eitthvað einkennilegir."
    glossedTokens := [("Henni", "her.DAT"), ("virtust", "seemed.2PL/3PL"), ("þið", "you.PL.NOM"), ("eitthvað", "somewhat"), ("einkennilegir", "strange")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "2"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "icelandicMediopassivePast")] }

def ex_84b : LinguisticExample :=
  { id := "coonkeine2021_84b"
    source := ⟨"sigurdsson-holmberg-2008", "p. 270"⟩
    reportedIn := some ⟨"coon-keine-2021", "(84b)"⟩
    language := "icel1247"
    primaryText := "Henni virtumst við eitthvað einkennilegir."
    glossedTokens := [("Henni", "her.DAT"), ("virtumst", "seemed.1PL"), ("við", "we.NOM"), ("eitthvað", "somewhat"), ("einkennilegir", "strange")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "datNom"), ("probe", "weak"), ("higher", "3"), ("higherNumber", "sg"), ("higherOpaque", "yes"), ("lower", "1"), ("lowerNumber", "pl"), ("aftermath", "agreement"), ("paradigm", "icelandicMediopassivePast")] }

def ex_86 : LinguisticExample :=
  { id := "coonkeine2021_86"
    source := ⟨"sigurdsson-2004a", "p. 86"⟩
    reportedIn := some ⟨"coon-keine-2021", "(86)"⟩
    language := "icel1247"
    primaryText := "Þeir mundu vera taldir vera sagðir hafa verið kosnir."
    glossedTokens := [("Þeir", "they.NOM.M.PL"), ("mundu", "would"), ("vera", "be"), ("taldir", "believed.NOM.M.PL"), ("vera", "be"), ("sagðir", "said.NOM.M.PL"), ("hafa", "have"), ("verið", "been"), ("kosnir", "elected.NOM.M.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participles"), ("higher", "3"), ("higherNumber", "pl")] }

def fn37_i : LinguisticExample :=
  { id := "coonkeine2021_fn37_i"
    source := ⟨"sigurdsson-2006", "p. 223"⟩
    reportedIn := some ⟨"coon-keine-2021", "fn. 37 (i)"⟩
    language := "icel1247"
    primaryText := "Það erum bara við."
    glossedTokens := [("Það", "it"), ("erum", "are.1PL"), ("bara", "only"), ("við", "we.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "expletive"), ("lower", "1"), ("lowerNumber", "pl")] }

def all : List LinguisticExample := [ex_3a, ex_3b, ex_3c, ex_3d, ex_10b, ex_10c, ex_37a, ex_37b, ex_41, ex_50, ex_24, ex_28, ex_31_2_1, ex_31_1_2, ex_44a, ex_44a_me, ex_44a_te, ex_44b, ex_44b_mi, ex_44b_ti, ex_46a, ex_46b, ex_48a, ex_48b, ex_51a, ex_51b, ex_52a, ex_52b, ex_54a, ex_54b, fn32_ia, ex_68a, ex_68b, ex_69a, ex_69b, fn34_i, ex_70a, ex_70b, ex_71, ex_72, ex_73, ex_74, ex_76a, ex_76b, ex_77, ex_78a, ex_78b_agree, ex_78b, ex_84a, ex_84b, ex_86, fn37_i]

end CoonKeine2021.Examples
