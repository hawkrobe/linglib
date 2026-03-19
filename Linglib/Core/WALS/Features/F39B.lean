import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 39B: Inclusive/Exclusive Forms in Pama-Nyungan
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 39B`.

Chapter 39, 71 languages.
-/

namespace Core.WALS.F39B

/-- WALS 39B values. -/
inductive InclusiveExclusiveFormsInPamaNyungan where
  | noInclusiveExclusiveOpposition  -- No inclusive/exclusive opposition (31 languages)
  | inclusiveAndExclusiveDifferentiated  -- Inclusive and exclusive differentiated (40 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 39B dataset (71 languages). -/
def allData : List (Datapoint InclusiveExclusiveFormsInPamaNyungan) :=
  [ { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "arr", language := "Arrernte", iso := "", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "bxj", language := "Bayungu", iso := "bxj", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "dhl", language := "Dhalandji", iso := "dhl", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ggd", language := "Gugadj", iso := "ggd", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "gny", language := "Gunya", iso := "gyy", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "guf", language := "Gupapuyngu", iso := "guf", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "vka", language := "Kariera", iso := "vka", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "kyt", language := "Kaytej", iso := "gbb", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "lnj", language := "Linngithig", iso := "lnj", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "mrj", language := "Mirniny", iso := "nju", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "mdb", language := "Mudburra", iso := "dmw", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ngr", language := "Ngarinyeri", iso := "nay", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "nlr", language := "Ngarla", iso := "nrk", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nlu", language := "Ngarluma", iso := "nrl", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "nly", language := "Nyamal", iso := "nly", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "bly", language := "Palyku", iso := "nad", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ump", language := "Umpila", iso := "ump", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wkw", language := "Wagawaga", iso := "wkw", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wgg", language := "Wangkangurru", iso := "wgg", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wbt", language := "Wanman", iso := "wbt", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wgu", language := "Warrongo", iso := "wrg", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wru", language := "Warumungu", iso := "wrm", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wwr", language := "Woiwurrung", iso := "wyi", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "ylr", language := "Yalarnnga", iso := "ylr", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ylb", language := "Yulparija", iso := "mpj", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .inclusiveAndExclusiveDifferentiated }
  ]

-- Count verification
theorem total_count : allData.length = 71 := by native_decide

theorem count_noInclusiveExclusiveOpposition :
    (allData.filter (·.value == .noInclusiveExclusiveOpposition)).length = 31 := by native_decide
theorem count_inclusiveAndExclusiveDifferentiated :
    (allData.filter (·.value == .inclusiveAndExclusiveDifferentiated)).length = 40 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F39B
