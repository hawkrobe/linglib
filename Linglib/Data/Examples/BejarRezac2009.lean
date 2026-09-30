module

public import Linglib.Data.Examples.Schema

/-!
# `BejarRezac2009` — typed example data

Auto-generated from `Linglib/Data/Examples/BejarRezac2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BejarRezac2009.Examples`.
-/

@[expose] public section

namespace BejarRezac2009.Examples

def br2009_2a : Datum :=
  { id := "br2009_2a"
    source := ⟨"bejar-rezac-2009", "(2a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi zintudan"
    glossedTokens := [("ikusi", "seen"), ("z-in-t-u-da-n", "2-X-PL-have-1-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("controller", "2"), ("context", "inverse")] }

def br2009_2b : Datum :=
  { id := "br2009_2b"
    source := ⟨"bejar-rezac-2009", "(2b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi ninduen"
    glossedTokens := [("ikusi", "seen"), ("n-ind-u-en", "1-X-have-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("controller", "1"), ("context", "inverse")] }

def br2009_2c : Datum :=
  { id := "br2009_2c"
    source := ⟨"bejar-rezac-2009", "(2c)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi ninduzun"
    glossedTokens := [("ikusi", "seen"), ("n-ind-u-zu-n", "1-X-have-2-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("controller", "1"), ("context", "inverse")] }

def br2009_2d : Datum :=
  { id := "br2009_2d"
    source := ⟨"bejar-rezac-2009", "(2d)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi nuen"
    glossedTokens := [("ikusi", "seen"), ("n-u-en", "1-have-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("controller", "1"), ("context", "direct")] }

def br2009_3 : Datum :=
  { id := "br2009_3"
    source := ⟨"bejar-rezac-2009", "(3)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik neure burua ikusten nuen."
    glossedTokens := [("Ni-k", "1-E"), ("neure", "my.own"), ("buru-a", "head-the.A"), ("ikusten", "seeing"), ("n-u-en", "1-have-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("controller", "1"), ("diagnostic", "case and binding unaffected")] }

def br2009_15 : Datum :=
  { id := "br2009_15"
    source := ⟨"bejar-rezac-2009", "(15)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zuk etsaiari misilak / *ni saldu dizkiozu."
    glossedTokens := [("Zu-k", "you-E"), ("etsaia-ri", "enemy-D"), ("misil-ak", "missile-A.PL"), ("ni", "me.A"), ("saldu", "sold"), ("d-i-zki-o-zu", "X-have-PL-3.D-2.E")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("constraint", "Person Case Constraint")] }

def br2009_t9_3_1 : Datum :=
  { id := "br2009_t9_3_1"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "niñdduen"
    glossedTokens := [("n-iñdd-u-en", "1.SG-INV-have-PAST")]
    context := "Bizkaian dialect of Bolivar."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("repair", "added probe (INV)")] }

def br2009_10 : Datum :=
  { id := "br2009_10"
    source := ⟨"bejar-rezac-2009", "(10)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "sijakiona chochote"
    glossedTokens := [("si-ja-ki-ona", "1.SG-NEG-7-see"), ("chochote", "anything")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("probe", "flat [u-3]"), ("agreement", "object and subject independent")] }

def br2009_17a : Datum :=
  { id := "br2009_17a"
    source := ⟨"bejar-rezac-2009", "(17a)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-in"
    glossedTokens := [("g-waabm-in", "2-see-1.INV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("controller", "2"), ("context", "inverse")] }

def br2009_17b : Datum :=
  { id := "br2009_17b"
    source := ⟨"bejar-rezac-2009", "(17b)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-i"
    glossedTokens := [("g-waabm-i", "2-see-DFLT.1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("controller", "2"), ("context", "direct")] }

def br2009_17c : Datum :=
  { id := "br2009_17c"
    source := ⟨"bejar-rezac-2009", "(17c)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "n-waabm-ig"
    glossedTokens := [("n-waabm-ig", "1-see-3.INV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("controller", "1"), ("context", "inverse")] }

def br2009_17d : Datum :=
  { id := "br2009_17d"
    source := ⟨"bejar-rezac-2009", "(17d)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-ig"
    glossedTokens := [("g-waabm-ig", "2-see-3.INV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "2"), ("controller", "2"), ("context", "inverse")] }

def br2009_18a : Datum :=
  { id := "br2009_18a"
    source := ⟨"bejar-rezac-2009", "(18a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "m-xedav-s"
    glossedTokens := [("m-xedav-s", "1.I-see-X")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("controller", "1"), ("morphology", "first-cycle m-")] }

def br2009_18b : Datum :=
  { id := "br2009_18b"
    source := ⟨"bejar-rezac-2009", "(18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-xedav"
    glossedTokens := [("v-xedav", "1.II-see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("controller", "1"), ("morphology", "second-cycle v-")] }

def br2009_29a : Datum :=
  { id := "br2009_29a"
    source := ⟨"bejar-rezac-2009", "(29a)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "bé chusath tsé paréna:va:n"
    glossedTokens := [("bé", "I.N"), ("chu-s-ath", "be.M.SG-1.SG.N-2.SG.E/A"), ("tsé", "you.N"), ("paréna:va:n", "teaching")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("context", "direct"), ("IA case", "unmarked")] }

def br2009_29b : Datum :=
  { id := "br2009_29b"
    source := ⟨"bejar-rezac-2009", "(29b)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsé chukh me paréna:va:n"
    glossedTokens := [("tsé", "you.N"), ("chu-kh", "be.M.SG-2.SG.N"), ("me", "me.D"), ("paréna:va:n", "teaching")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("context", "inverse"), ("IA case", "R-Case (dative form)")] }

def br2009_30b : Datum :=
  { id := "br2009_30b"
    source := ⟨"bejar-rezac-2009", "(30b)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsé yikh me hava:lé karné tUm'séndi dUs'"
    glossedTokens := [("tsé", "you.N"), ("yi-kh", "come.FUT-2.SG.N"), ("me", "me.D"), ("hava:lé", "handover"), ("karné", "do.INF.ABL"), ("tUm'séndi", "he.GEN"), ("dUs'", "by")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "passivization"), ("result", "R-Case disappears")] }

def all : List Datum := [br2009_2a, br2009_2b, br2009_2c, br2009_2d, br2009_3, br2009_15, br2009_t9_3_1, br2009_10, br2009_17a, br2009_17b, br2009_17c, br2009_17d, br2009_18a, br2009_18b, br2009_29a, br2009_29b, br2009_30b]

end BejarRezac2009.Examples
