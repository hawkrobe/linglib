import Linglib.Data.Examples.Schema

/-!
# `BejarRezac2009` — typed example data

Auto-generated from `Linglib/Data/Examples/BejarRezac2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BejarRezac2009.Examples`.
-/

namespace BejarRezac2009.Examples

open Data.Examples

def br2009_2a : LinguisticExample :=
  { id := "br2009_2a"
    source := ⟨"bejar-rezac-2009", "(2a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi zintudan"
    discourseSegments := []
    glossedTokens := [("ikusi", "seen"), ("z-in-t-u-da-n", "2-X-PL-have-1-PAST")]
    translation := "I saw you."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "1>2 = 2"), ("context", "inverse")]
    comment := "The core slot tracks the IA: a 2nd-person object fully checks the [u-3-2] probe."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_2b : LinguisticExample :=
  { id := "br2009_2b"
    source := ⟨"bejar-rezac-2009", "(2b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi ninduen"
    discourseSegments := []
    glossedTokens := [("ikusi", "seen"), ("n-ind-u-en", "1-X-have-PAST")]
    translation := "He saw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "3>1 = 1"), ("context", "inverse")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_2c : LinguisticExample :=
  { id := "br2009_2c"
    source := ⟨"bejar-rezac-2009", "(2c)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusininduzun"
    discourseSegments := []
    glossedTokens := [("ikusi", "seen"), ("n-ind-u-zu-n", "1-X-have-2-PAST")]
    translation := "You saw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "2>1 = 1"), ("context", "inverse")]
    comment := "With (2a): no ranking of person values decides between two SAP arguments — the IA wins both times."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_2d : LinguisticExample :=
  { id := "br2009_2d"
    source := ⟨"bejar-rezac-2009", "(2d)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi nuen"
    discourseSegments := []
    glossedTokens := [("ikusi", "seen"), ("n-u-en", "1-have-PAST")]
    translation := "I saw him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "1>3 = 1"), ("context", "direct")]
    comment := "The 3rd-person IA leaves the [u2] residue, which the SAP EA checks on cycle II: displacement to the EA."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_3 : LinguisticExample :=
  { id := "br2009_3"
    source := ⟨"bejar-rezac-2009", "(3)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik neure burua ikusten nuen."
    discourseSegments := []
    glossedTokens := [("Ni-k", "1-E"), ("neure", "my.own"), ("buru-a", "head-the.A"), ("ikusten", "seeing"), ("n-u-en", "1-have-PAST")]
    translation := "I saw myself."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case and binding unaffected")]
    comment := "Ergative displacement changes neither case marking nor binding: agreement displacement is not movement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_15 : LinguisticExample :=
  { id := "br2009_15"
    source := ⟨"bejar-rezac-2009", "(15)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zuk etsaiari misilak / *ni saldu dizkiozu."
    discourseSegments := []
    glossedTokens := [("Zu-k", "you-E"), ("etsaia-ri", "enemy-D"), ("misil-ak", "missile-A.PL"), ("ni", "me.A"), ("saldu", "sold"), ("d-i-zki-o-zu", "X-have-PL-3.D-2.E")]
    translation := "You have sold the missiles / *me to the enemy."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("constraint", "Person Case Constraint")]
    comment := "With a dative goal absorbing the π-probe, a 1st-person theme is unlicensable — the PLC at work."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_t9_3_1 : LinguisticExample :=
  { id := "br2009_t9_3_1"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "niñdduen"
    discourseSegments := []
    glossedTokens := [("n-iñdd-u-en", "1.SG-INV-have-PAST")]
    translation := "He had me."
    context := "Bizkaian dialect of Bolivar."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "3>1"), ("repair", "added probe (INV)")]
    comment := "The INV slot spells out the added probe that licenses the EA in inverse contexts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_10 : LinguisticExample :=
  { id := "br2009_10"
    source := ⟨"bejar-rezac-2009", "(10)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "sijakiona chochote"
    discourseSegments := []
    glossedTokens := [("si-ja-ki-ona", "1.SG-NEG-7-see"), ("chochote", "anything")]
    translation := "I haven't seen anything."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("probe", "flat [u-3]"), ("agreement", "object and subject independent")]
    comment := "A flat probe is fully checked by any IA: no person-hierarchy interaction, every context inverse."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_17a : LinguisticExample :=
  { id := "br2009_17a"
    source := ⟨"bejar-rezac-2009", "(17a)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-in"
    discourseSegments := []
    glossedTokens := [("g-waabm-in", "2-see-1.INV")]
    translation := "I see you."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "1>2 = 2"), ("context", "inverse")]
    comment := "Nishnaabemwin (Odawa/Eastern Ojibwe): 2nd person is most specified ([u-3-1-2]), so the 2nd-person IA wins."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_17b : LinguisticExample :=
  { id := "br2009_17b"
    source := ⟨"bejar-rezac-2009", "(17b)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-i"
    discourseSegments := []
    glossedTokens := [("g-waabm-i", "2-see-DFLT.1")]
    translation := "You see me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "2>1 = 2"), ("context", "direct")]
    comment := "The 1st-person IA leaves the [u2] segment, checked by the 2nd-person EA on cycle II."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_17c : LinguisticExample :=
  { id := "br2009_17c"
    source := ⟨"bejar-rezac-2009", "(17c)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "n-waabm-ig"
    discourseSegments := []
    glossedTokens := [("n-waabm-ig", "1-see-3.INV")]
    translation := "He sees me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "3>1 = 1"), ("context", "inverse")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_17d : LinguisticExample :=
  { id := "br2009_17d"
    source := ⟨"bejar-rezac-2009", "(17d)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-ig"
    discourseSegments := []
    glossedTokens := [("g-waabm-ig", "2-see-3.INV")]
    translation := "He sees you."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "3>2 = 2"), ("context", "inverse")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_18a : LinguisticExample :=
  { id := "br2009_18a"
    source := ⟨"bejar-rezac-2009", "(18a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "m-xedav-s"
    discourseSegments := []
    glossedTokens := [("m-xedav-s", "1.I-see-X")]
    translation := "He sees me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "3>1 = 1"), ("morphology", "first-cycle m-")]
    comment := "1sg spelled m- when the probe is valued on cycle I (IA controls)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_18b : LinguisticExample :=
  { id := "br2009_18b"
    source := ⟨"bejar-rezac-2009", "(18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-xedav"
    discourseSegments := []
    glossedTokens := [("v-xedav", "1.II-see")]
    translation := "I see him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "1>3 = 1"), ("morphology", "second-cycle v-")]
    comment := "Same 1sg value spelled v- when valued on cycle II — a second-cycle effect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_29a : LinguisticExample :=
  { id := "br2009_29a"
    source := ⟨"bejar-rezac-2009", "(29a)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "bé chusath tsé paréna:va:n"
    discourseSegments := []
    glossedTokens := [("bé", "I.N"), ("chu-s-ath", "be.M.SG-1.SG.N-2.SG.E/A"), ("tsé", "you.N"), ("paréna:va:n", "teaching")]
    translation := "I am teaching you."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "1>2"), ("context", "direct"), ("IA case", "unmarked")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_29b : LinguisticExample :=
  { id := "br2009_29b"
    source := ⟨"bejar-rezac-2009", "(29b)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsé chukh me paréna:va:n"
    discourseSegments := []
    glossedTokens := [("tsé", "you.N"), ("chu-kh", "be.M.SG-2.SG.N"), ("me", "me.D"), ("paréna:va:n", "teaching")]
    translation := "You are teaching me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("combination", "2>1"), ("context", "inverse"), ("IA case", "R-Case (dative form)")]
    comment := "The inverse-context IA takes the special R-Case; the sole agreement slot tracks the EA."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def br2009_30b : LinguisticExample :=
  { id := "br2009_30b"
    source := ⟨"bejar-rezac-2009", "(30b)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsé yikh me hava:lé karné tUm'séndi dUs'"
    discourseSegments := []
    glossedTokens := [("tsé", "you.N"), ("yi-kh", "come.FUT-2.SG.N"), ("me", "me.D"), ("hava:lé", "handover"), ("karné", "do.INF.ABL"), ("tUm'séndi", "he.GEN"), ("dUs'", "by")]
    translation := "You will be handed over to me by him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "passivization"), ("result", "R-Case disappears")]
    comment := "R-Case vanishes under passivization, unlike the inherent dative (30a) — it is structural, tied to the inverse configuration."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [br2009_2a, br2009_2b, br2009_2c, br2009_2d, br2009_3, br2009_15, br2009_t9_3_1, br2009_10, br2009_17a, br2009_17b, br2009_17c, br2009_17d, br2009_18a, br2009_18b, br2009_29a, br2009_29b, br2009_30b]

end BejarRezac2009.Examples
