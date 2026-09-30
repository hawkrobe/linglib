module

public import Linglib.Data.Examples.Schema

/-!
# `Karlsson2017` — typed example data

Auto-generated from `Linglib/Data/Examples/Karlsson2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Karlsson2017.Examples`.
-/

@[expose] public section

namespace Karlsson2017.Examples

def neg1 : Datum :=
  { id := "karlsson2017_neg1"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "En lähetä tekstiviestiä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def neg2 : Datum :=
  { id := "karlsson2017_neg2"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Pekka ei nähnyt Leenaa."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def neg3 : Datum :=
  { id := "karlsson2017_neg3"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "En tunne noita miehiä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "finite"), ("case", "part")] }

def neg4 : Datum :=
  { id := "karlsson2017_neg4"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "En ole tavannut häntä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("clause", "finite"), ("case", "part")] }

def ex_2a_read_part : Datum :=
  { id := "karlsson2017_2a_read_part"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Tyttö luki kirjaa."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def ex_2a_read_tot : Datum :=
  { id := "karlsson2017_2a_read_tot"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Tyttö luki kirjan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def ex_2a_drive_part : Datum :=
  { id := "karlsson2017_2a_drive_part"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän ajaa autoa."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def ex_2a_drive_tot : Datum :=
  { id := "karlsson2017_2a_drive_tot"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän ajaa auton talliin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def ex_2a_shoot_part : Datum :=
  { id := "karlsson2017_2a_shoot_part"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Metsästäjä ampui lintua."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def ex_2a_shoot_tot : Datum :=
  { id := "karlsson2017_2a_shoot_tot"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Metsästäjä ampui linnun."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def ex_2b_love : Datum :=
  { id := "karlsson2017_2b_love"
    source := ⟨"karlsson-2017", "12.2.2 (2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Rakastan tuota miestä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def ex_2b_interest : Datum :=
  { id := "karlsson2017_2b_interest"
    source := ⟨"karlsson-2017", "12.2.2 (2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Suomi kiinnostaa minua."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("clause", "finite"), ("case", "part")] }

def ex_2b_fear : Datum :=
  { id := "karlsson2017_2b_fear"
    source := ⟨"karlsson-2017", "12.2.2 (2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Pelkäätkö koiria?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "indefinite"), ("nominal", "plural"), ("clause", "finite"), ("case", "part")] }

def ex_3_icecream_part : Datum :=
  { id := "karlsson2017_3_icecream_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ostan jäätelöä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def ex_3_icecream_tot : Datum :=
  { id := "karlsson2017_3_icecream_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ostan jäätelön."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def ex_3_beer_part : Datum :=
  { id := "karlsson2017_3_beer_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Simo juo olutta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "singular"), ("clause", "finite"), ("case", "part")] }

def ex_3_beer_tot : Datum :=
  { id := "karlsson2017_3_beer_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Simo juo oluen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def ex_3_people_part : Datum :=
  { id := "karlsson2017_3_people_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Näen ihmisiä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "plural"), ("clause", "finite"), ("case", "part")] }

def ex_3_people_tot : Datum :=
  { id := "karlsson2017_3_people_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Näen ihmiset."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "finite"), ("case", "nom")] }

def ex_3_guests_part : Datum :=
  { id := "karlsson2017_3_guests_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Tuula tapaa vieraita."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "plural"), ("clause", "finite"), ("case", "part")] }

def ex_3_guests_tot : Datum :=
  { id := "karlsson2017_3_guests_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Tuula tapaa vieraat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "finite"), ("case", "nom")] }

def tot_message : Datum :=
  { id := "karlsson2017_tot_message"
    source := ⟨"karlsson-2017", "13.3.1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Lähetän tekstiviestin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.1"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def tot_milk : Datum :=
  { id := "karlsson2017_tot_milk"
    source := ⟨"karlsson-2017", "13.3.1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Silja joi maidon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.1"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def tot_car_imp : Datum :=
  { id := "karlsson2017_tot_car_imp"
    source := ⟨"karlsson-2017", "13.3.1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Osta auto."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.1"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "imperative"), ("case", "nom")] }

def tot_computers : Datum :=
  { id := "karlsson2017_tot_computers"
    source := ⟨"karlsson-2017", "13.3.1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Tietokoneet hankittiin halvalla."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.1"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "passive"), ("case", "nom")] }

def tot_cars : Datum :=
  { id := "karlsson2017_tot_cars"
    source := ⟨"karlsson-2017", "13.3.1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ostamme autot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.1"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "finite"), ("case", "nom")] }

def acc_took : Datum :=
  { id := "karlsson2017_acc_took"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Risto vei minut elokuviin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("clause", "finite"), ("case", "acc")] }

def acc_take_imp : Datum :=
  { id := "karlsson2017_acc_take_imp"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Vie minut elokuviin!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("clause", "imperative"), ("case", "acc")] }

def acc_taken : Datum :=
  { id := "karlsson2017_acc_taken"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Minut vietiin elokuviin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("clause", "passive"), ("case", "acc")] }

def acc_whom : Datum :=
  { id := "karlsson2017_acc_whom"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Kenet näit?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("clause", "finite"), ("case", "acc")] }

def pl_articles : Datum :=
  { id := "karlsson2017_pl_articles"
    source := ⟨"karlsson-2017", "13.3.2 (2)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luen artikkelit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "finite"), ("case", "nom")] }

def pl_children_imp : Datum :=
  { id := "karlsson2017_pl_children_imp"
    source := ⟨"karlsson-2017", "13.3.2 (2)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Vie lapset tarhaan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "imperative"), ("case", "nom")] }

def pl_children_pass : Datum :=
  { id := "karlsson2017_pl_children_pass"
    source := ⟨"karlsson-2017", "13.3.2 (2)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Lapset vietiin tarhaan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "plural"), ("clause", "passive"), ("case", "nom")] }

def num_articles : Datum :=
  { id := "karlsson2017_num_articles"
    source := ⟨"karlsson-2017", "13.3.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luen kaksi artikkelia."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "numeral"), ("clause", "finite"), ("case", "nom")] }

def num_children_imp : Datum :=
  { id := "karlsson2017_num_children_imp"
    source := ⟨"karlsson-2017", "13.3.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Vie nuo kolme lasta ulos."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "numeral"), ("clause", "imperative"), ("case", "nom")] }

def num_children_pass : Datum :=
  { id := "karlsson2017_num_children_pass"
    source := ⟨"karlsson-2017", "13.3.2 (3)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Kolme lasta vietiin tarhaan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "numeral"), ("clause", "passive"), ("case", "nom")] }

def sg_camera : Datum :=
  { id := "karlsson2017_sg_camera"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ostan digikameran."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def sg_child : Datum :=
  { id := "karlsson2017_sg_child"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Isä vie lapsen tarhaan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def sg_window : Datum :=
  { id := "karlsson2017_sg_window"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sylvi avaa ikkunan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "finite"), ("case", "gen")] }

def sg_paper_imp : Datum :=
  { id := "karlsson2017_sg_paper_imp"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Osta lehti!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "imperative"), ("case", "nom")] }

def sg_book_pass : Datum :=
  { id := "karlsson2017_sg_book_pass"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ostettiin kirja."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "passive"), ("case", "nom")] }

def sg_dog_pass : Datum :=
  { id := "karlsson2017_sg_dog_pass"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Koira vietiin pois."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "passive"), ("case", "nom")] }

def sg_book_must : Datum :=
  { id := "karlsson2017_sg_book_must"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Minun täytyy ostaa kirja."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "obligation"), ("case", "nom")] }

def sg_house_inf : Datum :=
  { id := "karlsson2017_sg_house_inf"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "On vaikea ostaa talo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "singular"), ("clause", "infinitival"), ("case", "nom")] }

def all : List Datum := [neg1, neg2, neg3, neg4, ex_2a_read_part, ex_2a_read_tot, ex_2a_drive_part, ex_2a_drive_tot, ex_2a_shoot_part, ex_2a_shoot_tot, ex_2b_love, ex_2b_interest, ex_2b_fear, ex_3_icecream_part, ex_3_icecream_tot, ex_3_beer_part, ex_3_beer_tot, ex_3_people_part, ex_3_people_tot, ex_3_guests_part, ex_3_guests_tot, tot_message, tot_milk, tot_car_imp, tot_computers, tot_cars, acc_took, acc_take_imp, acc_taken, acc_whom, pl_articles, pl_children_imp, pl_children_pass, num_articles, num_children_imp, num_children_pass, sg_camera, sg_child, sg_window, sg_paper_imp, sg_book_pass, sg_dog_pass, sg_book_must, sg_house_inf]

end Karlsson2017.Examples
