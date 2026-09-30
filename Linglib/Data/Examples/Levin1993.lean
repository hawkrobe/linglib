module

public import Linglib.Data.Examples.Schema

/-!
# `Levin1993` — typed example data

Auto-generated from `Linglib/Data/Examples/Levin1993.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Levin1993.Examples`.
-/

@[expose] public section

namespace Levin1993.Examples

open Data.Examples

def ci_break : Datum :=
  { id := "levin1993_ci_break"
    source := ⟨"levin-1993", "(22), p. 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The little boy broke the window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The window broke.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "break"), ("levin_class", "45.1"), ("alternation", "causativeInchoative")] }

def mid_break : Datum :=
  { id := "levin1993_mid_break"
    source := ⟨"levin-1993", "(13b), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Crystal vases break easily."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "break"), ("levin_class", "45.1"), ("alternation", "middle")] }

def con_break : Datum :=
  { id := "levin1993_con_break"
    source := ⟨"levin-1993", "(14b), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Janet broke at the vase."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "break"), ("levin_class", "45.1"), ("alternation", "conative")] }

def bppa_break : Datum :=
  { id := "levin1993_bppa_break"
    source := ⟨"levin-1993", "(16b), p. 7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Janet broke Bill on the finger."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Janet broke Bill's finger.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "break"), ("levin_class", "45.1"), ("alternation", "bodyPartPossessorAscension")] }

def ci_cut : Datum :=
  { id := "levin1993_ci_cut"
    source := ⟨"levin-1993", "(23b), p. 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The string cut."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Margaret cut the string.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "cut"), ("levin_class", "21.1"), ("alternation", "causativeInchoative")] }

def mid_cut : Datum :=
  { id := "levin1993_mid_cut"
    source := ⟨"levin-1993", "(13a), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bread cuts easily."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cut"), ("levin_class", "21.1"), ("alternation", "middle")] }

def con_cut : Datum :=
  { id := "levin1993_con_cut"
    source := ⟨"levin-1993", "(14a), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Margaret cut at the bread."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cut"), ("levin_class", "21.1"), ("alternation", "conative")] }

def bppa_cut : Datum :=
  { id := "levin1993_bppa_cut"
    source := ⟨"levin-1993", "(15b), p. 7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Margaret cut Bill on the arm."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Margaret cut Bill's arm.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "cut"), ("levin_class", "21.1"), ("alternation", "bodyPartPossessorAscension")] }

def ci_hit : Datum :=
  { id := "levin1993_ci_hit"
    source := ⟨"levin-1993", "(25b), p. 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The door hit."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Carla hit the door.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "hit"), ("levin_class", "18.1"), ("alternation", "causativeInchoative")] }

def mid_hit : Datum :=
  { id := "levin1993_mid_hit"
    source := ⟨"levin-1993", "(13d), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Door frames hit easily."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hit"), ("levin_class", "18.1"), ("alternation", "middle")] }

def con_hit : Datum :=
  { id := "levin1993_con_hit"
    source := ⟨"levin-1993", "(14d), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carla hit at the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hit"), ("levin_class", "18.1"), ("alternation", "conative")] }

def bppa_hit : Datum :=
  { id := "levin1993_bppa_hit"
    source := ⟨"levin-1993", "(18b), p. 7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carla hit Bill on the back."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Carla hit Bill's back.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "hit"), ("levin_class", "18.1"), ("alternation", "bodyPartPossessorAscension")] }

def ci_touch : Datum :=
  { id := "levin1993_ci_touch"
    source := ⟨"levin-1993", "(24b), p. 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The cat touched."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Terry touched the cat.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "touch"), ("levin_class", "20"), ("alternation", "causativeInchoative")] }

def mid_touch : Datum :=
  { id := "levin1993_mid_touch"
    source := ⟨"levin-1993", "(13c), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Cats touch easily."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "touch"), ("levin_class", "20"), ("alternation", "middle")] }

def con_touch : Datum :=
  { id := "levin1993_con_touch"
    source := ⟨"levin-1993", "(14c), p. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Terry touched at the cat."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "touch"), ("levin_class", "20"), ("alternation", "conative")] }

def bppa_touch : Datum :=
  { id := "levin1993_bppa_touch"
    source := ⟨"levin-1993", "(17b), p. 7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Terry touched Bill on the shoulder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Terry touched Bill's shoulder.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "touch"), ("levin_class", "20"), ("alternation", "bodyPartPossessorAscension")] }

def con_push : Datum :=
  { id := "levin1993_con_push"
    source := ⟨"levin-1993", "§1.3 (95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I pushed at/on/against the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I pushed the table.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "push"), ("levin_class", "12"), ("alternation", "conative")] }

def loc_spray : Datum :=
  { id := "levin1993_loc_spray"
    source := ⟨"levin-1993", "§2.3.1 (125), p. 51"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jack sprayed paint on the wall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Jack sprayed the wall with paint.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "spray"), ("levin_class", "9.7"), ("alternation", "locative")] }

def loc_load : Datum :=
  { id := "levin1993_loc_load"
    source := ⟨"levin-1993", "§9.7 (52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jessica loaded boxes on the wagon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Jessica loaded the wagon with boxes.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "load"), ("levin_class", "9.7"), ("alternation", "locative")] }

def dat_give : Datum :=
  { id := "levin1993_dat_give"
    source := ⟨"levin-1993", "UNVERIFIED constructed; give ∈ alternating GIVE VERBS, §2.1 (115) and §13.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She gave a book to him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("She gave him a book.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "give"), ("levin_class", "13.1"), ("alternation", "dative")] }

def dat_send : Datum :=
  { id := "levin1993_dat_send"
    source := ⟨"levin-1993", "§11.1 (129)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nora sent the book to Peter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Nora sent Peter the book.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "send"), ("levin_class", "11.1"), ("alternation", "dative")] }

def ben_carve : Datum :=
  { id := "levin1993_ben_carve"
    source := ⟨"levin-1993", "§2.2 (121), p. 49"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha carved a toy for the baby."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Martha carved the baby a toy.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "carve"), ("levin_class", "26.1"), ("alternation", "benefactive")] }

def ss_radiate : Datum :=
  { id := "levin1993_ss_radiate"
    source := ⟨"levin-1993", "§1.1.3 (36), p. 32"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Heat radiates from the sun."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The sun radiates heat.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "radiate"), ("levin_class", "43.4"), ("alternation", "substanceSource")] }

def mp_carve : Datum :=
  { id := "levin1993_mp_carve"
    source := ⟨"levin-1993", "§2.4.1 (147), p. 56"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha carved a toy out of the piece of wood."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Martha carved the piece of wood into a toy.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "carve"), ("levin_class", "26.1"), ("alternation", "materialProduct")] }

def uo_eat : Datum :=
  { id := "levin1993_uo_eat"
    source := ⟨"levin-1993", "§1.2.1 (38), p. 33"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mike ate the cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Mike ate.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "eat"), ("levin_class", "39.1"), ("alternation", "unspecifiedObject")] }

def uo_devour : Datum :=
  { id := "levin1993_uo_devour"
    source := ⟨"levin-1993", "§39.4 (652)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Cynthia devoured."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Cynthia devoured the pizza.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "devour"), ("levin_class", "39.4"), ("alternation", "unspecifiedObject")] }

def uro_meet : Datum :=
  { id := "levin1993_uro_meet"
    source := ⟨"levin-1993", "§1.2.4 (59), p. 36"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anne met Cathy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Anne and Cathy met.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "meet"), ("levin_class", "36.3"), ("alternation", "understoodReciprocalObject")] }

def ti_develop : Datum :=
  { id := "levin1993_ti_develop"
    source := ⟨"levin-1993", "§6.1 (321), p. 89"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A problem developed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("There developed a problem.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "develop"), ("levin_class", "48.1.1"), ("alternation", "thereInsertion")] }

def ti_appear : Datum :=
  { id := "levin1993_ti_appear"
    source := ⟨"levin-1993", "§6.1 (322), p. 89"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A ship appeared on the horizon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("There appeared a ship on the horizon.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "appear"), ("levin_class", "48.1.1"), ("alternation", "thereInsertion")] }

def li_live : Datum :=
  { id := "levin1993_li_live"
    source := ⟨"levin-1993", "§6.2 (335), p. 92"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An old woman lives in the woods."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("In the woods lives an old woman.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "live"), ("levin_class", "47.1"), ("alternation", "locativeInversion")] }

def is_break : Datum :=
  { id := "levin1993_is_break"
    source := ⟨"levin-1993", "§3.3 (275), p. 80"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David broke the window with a hammer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The hammer broke the window.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "break"), ("levin_class", "45.1"), ("alternation", "instrumentSubject")] }

def is_eat : Datum :=
  { id := "levin1993_is_eat"
    source := ⟨"levin-1993", "§3.3 (276), p. 80"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The spoon ate the ice cream."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Doug ate the ice cream with a spoon.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "eat"), ("levin_class", "39.1"), ("alternation", "instrumentSubject")] }

def ia_run : Datum :=
  { id := "levin1993_ia_run"
    source := ⟨"levin-1993", "§1.1.2.2 (25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The scientist ran the rats through the maze."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The rats ran through the maze.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "run"), ("levin_class", "51.3.2"), ("alternation", "inducedAction")] }

def ia_walk : Datum :=
  { id := "levin1993_ia_walk"
    source := ⟨"levin-1993", "UNVERIFIED constructed; walk ∈ §1.1.2.2 (23) RUN VERBS (some)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dog walked."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("She walked the dog.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "walk"), ("levin_class", "51.3.2"), ("alternation", "inducedAction")] }

def ia_appear : Datum :=
  { id := "levin1993_ia_appear"
    source := ⟨"levin-1993", "(8), p. 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The magician appeared a rabbit out of his hat."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("A rabbit appeared out of the magician's hat.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "appear"), ("levin_class", "48.1.1"), ("alternation", "inducedAction")] }

def ubpo_wave : Datum :=
  { id := "levin1993_ubpo_wave"
    source := ⟨"levin-1993", "§1.2.2 (40), p. 34"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The departing passenger waved his hand at the crowd."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The departing passenger waved at the crowd.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "wave"), ("levin_class", "40.3.2"), ("alternation", "understoodBodyPartObject")] }

def uro_wash : Datum :=
  { id := "levin1993_uro_wash"
    source := ⟨"levin-1993", "UNVERIFIED constructed; wash ∈ §1.2.3 (47a) DRESS VERBS"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill washed himself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Bill washed.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "wash"), ("levin_class", "41.1.1"), ("alternation", "understoodReflexiveObject")] }

def tt_turn : Datum :=
  { id := "levin1993_tt_turn"
    source := ⟨"levin-1993", "§2.4.3 (159)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The witch turned him into a frog."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The witch turned him from a prince into a frog.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "turn"), ("levin_class", "26.6"), ("alternation", "totalTransformation")] }

def way_elbow : Datum :=
  { id := "levin1993_way_elbow"
    source := ⟨"levin-1993", "UNVERIFIED constructed; X's way attested for unergative and transitive verbs, §7.4 (365)–(366)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She elbowed her way through the crowd."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "elbow"), ("levin_class", "51.3.2"), ("alternation", "wayConstruction")] }

def co_laugh : Datum :=
  { id := "levin1993_co_laugh"
    source := ⟨"levin-1993", "§40.2 (686)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paul laughed a cheerful laugh."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Paul laughed.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "laugh"), ("levin_class", "40.2"), ("alternation", "cognateObject")] }

def co_grunt : Datum :=
  { id := "levin1993_co_grunt"
    source := ⟨"levin-1993", "§7.1 (350)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?Heather grunted a disinterested grunt."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := [("Heather grunted.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "grunt"), ("levin_class", "37.3"), ("alternation", "cognateObject")] }

def co_jump : Datum :=
  { id := "levin1993_co_jump"
    source := ⟨"levin-1993", "§51.3.2 (998)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The horse jumped a high jump."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jump"), ("levin_class", "51.3.2"), ("alternation", "cognateObject")] }

def dp_run : Datum :=
  { id := "levin1993_dp_run"
    source := ⟨"levin-1993", "UNVERIFIED constructed; run ∈ §7.8 (405) RUN VERBS"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She ran to the store."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "run"), ("levin_class", "51.3.2"), ("alternation", "directionalPhrase")] }

def vp_break : Datum :=
  { id := "levin1993_vp_break"
    source := ⟨"levin-1993", "UNVERIFIED constructed; cf. §5.1 (306)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The window was broken by the boy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "break"), ("levin_class", "45.1"), ("alternation", "verbalPassive")] }

def vp_give : Datum :=
  { id := "levin1993_vp_give"
    source := ⟨"levin-1993", "UNVERIFIED constructed; cf. §5.1 (306)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given to her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "give"), ("levin_class", "13.1"), ("alternation", "verbalPassive")] }

def vp_eat : Datum :=
  { id := "levin1993_vp_eat"
    source := ⟨"levin-1993", "UNVERIFIED constructed; cf. §5.1 (306)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cake was eaten."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "eat"), ("levin_class", "39.1"), ("alternation", "verbalPassive")] }

def vp_see : Datum :=
  { id := "levin1993_vp_see"
    source := ⟨"levin-1993", "UNVERIFIED constructed; cf. §5.1 (306)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ship was seen on the horizon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "see"), ("levin_class", "30.1"), ("alternation", "verbalPassive")] }

def vp_measure : Datum :=
  { id := "levin1993_vp_measure"
    source := ⟨"levin-1993", "§54.1 (1030)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Ten pounds was weighed by the package."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("The package weighed ten pounds.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "weigh"), ("levin_class", "54.1"), ("alternation", "verbalPassive")] }

def pp_sleep : Datum :=
  { id := "levin1993_pp_sleep"
    source := ⟨"levin-1993", "§5.2 (311)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This bed was slept in by George Washington."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("George Washington slept in this bed.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "sleep"), ("levin_class", "40.4"), ("alternation", "prepositionalPassive")] }

def pp_talk : Datum :=
  { id := "levin1993_pp_talk"
    source := ⟨"levin-1993", "UNVERIFIED constructed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The matter was talked about."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "talk"), ("levin_class", "37.5"), ("alternation", "prepositionalPassive")] }

def sw_swarm : Datum :=
  { id := "levin1993_sw_swarm"
    source := ⟨"levin-1993", "§2.3.4 (139)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bees are swarming in the garden."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The garden is swarming with bees.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "swarm"), ("levin_class", "47.5.1"), ("alternation", "swarm")] }

def sw_crawl : Datum :=
  { id := "levin1993_sw_crawl"
    source := ⟨"levin-1993", "UNVERIFIED constructed; crawl ∈ §2.3.4 (138f) SWARM VERBS"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ants crawled on the counter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The counter crawled with ants.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "crawl"), ("levin_class", "47.5.1"), ("alternation", "swarm")] }

def all : List Datum := [ci_break, mid_break, con_break, bppa_break, ci_cut, mid_cut, con_cut, bppa_cut, ci_hit, mid_hit, con_hit, bppa_hit, ci_touch, mid_touch, con_touch, bppa_touch, con_push, loc_spray, loc_load, dat_give, dat_send, ben_carve, ss_radiate, mp_carve, uo_eat, uo_devour, uro_meet, ti_develop, ti_appear, li_live, is_break, is_eat, ia_run, ia_walk, ia_appear, ubpo_wave, uro_wash, tt_turn, way_elbow, co_laugh, co_grunt, co_jump, dp_run, vp_break, vp_give, vp_eat, vp_see, vp_measure, pp_sleep, pp_talk, sw_swarm, sw_crawl]

end Levin1993.Examples
