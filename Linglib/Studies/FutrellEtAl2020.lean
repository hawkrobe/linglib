/-!
# Crosslinguistic Dependency Length Data
[futrell-gibson-2020]

Table 2 of [futrell-gibson-2020] ("Dependency locality as an explanatory
principle for word order", *Language* 96(2):371–412): for each of the 46
languages measured over Universal Dependencies 2.1 corpora, the proportion
of head-final dependencies and the mean dependency length per word at
sentence lengths 10, 15, and 20. The paper reads the table together with
its scatterplots: more head-final languages have longer dependencies, and
the languages with especially long dependencies are predominantly
head-final ones such as Japanese, Korean, and Turkish.

Values are scaled integers — permille for the head-final proportion, ×100
for dependency lengths (mirroring the table's two decimal places) — so
that downstream list computations kernel-`decide`. UD language codes are
linglib annotation for cross-study joins (`Studies/LevshinaEtAl2023`);
they are not printed in the table, but match the language keys of the
paper's analysis pipeline, the CLIQS codebase its footnote cites
(<https://github.com/langprocgroup/cliqs/>, `typology3.csv`).
-/

namespace FutrellEtAl2020

/-- One row of Table 2: head-final proportion and mean per-word dependency
lengths for one UD 2.1 language. -/
structure DepLengthRow where
  /-- Language name as printed in the table (e.g. "Norwegian (B)"). -/
  language : String
  /-- UD language code (linglib annotation, not part of the table). -/
  isoCode : String
  /-- Proportion of head-final dependencies, permille (881 = 0.881). -/
  propHeadFinal1000 : Nat
  /-- Mean dependency length per word at sentence length 10, ×100. -/
  depLengthAt10_100 : Nat
  /-- Mean dependency length per word at sentence length 15, ×100. -/
  depLengthAt15_100 : Nat
  /-- Mean dependency length per word at sentence length 20, ×100. -/
  depLengthAt20_100 : Nat
  deriving Repr, DecidableEq

/-- Table 2, in the paper's row order (descending head-final proportion). -/
def table2 : List DepLengthRow := [
  { language := "Korean", isoCode := "ko", propHeadFinal1000 := 881,
    depLengthAt10_100 := 201, depLengthAt15_100 := 249, depLengthAt20_100 := 284 },
  { language := "Japanese", isoCode := "ja", propHeadFinal1000 := 809,
    depLengthAt10_100 := 170, depLengthAt15_100 := 198, depLengthAt20_100 := 226 },
  { language := "Turkish", isoCode := "tr", propHeadFinal1000 := 778,
    depLengthAt10_100 := 199, depLengthAt15_100 := 236, depLengthAt20_100 := 261 },
  { language := "Hindi", isoCode := "hi", propHeadFinal1000 := 763,
    depLengthAt10_100 := 188, depLengthAt15_100 := 226, depLengthAt20_100 := 257 },
  { language := "Urdu", isoCode := "ur", propHeadFinal1000 := 745,
    depLengthAt10_100 := 186, depLengthAt15_100 := 227, depLengthAt20_100 := 249 },
  { language := "Hungarian", isoCode := "hu", propHeadFinal1000 := 726,
    depLengthAt10_100 := 178, depLengthAt15_100 := 213, depLengthAt20_100 := 240 },
  { language := "Mandarin", isoCode := "zh", propHeadFinal1000 := 661,
    depLengthAt10_100 := 203, depLengthAt15_100 := 251, depLengthAt20_100 := 298 },
  { language := "Basque", isoCode := "eu", propHeadFinal1000 := 587,
    depLengthAt10_100 := 177, depLengthAt15_100 := 210, depLengthAt20_100 := 229 },
  { language := "Ancient Greek", isoCode := "grc", propHeadFinal1000 := 566,
    depLengthAt10_100 := 234, depLengthAt15_100 := 274, depLengthAt20_100 := 308 },
  { language := "Latin", isoCode := "la", propHeadFinal1000 := 547,
    depLengthAt10_100 := 227, depLengthAt15_100 := 272, depLengthAt20_100 := 299 },
  { language := "Northern Sami", isoCode := "sme", propHeadFinal1000 := 542,
    depLengthAt10_100 := 185, depLengthAt15_100 := 220, depLengthAt20_100 := 262 },
  { language := "Dutch", isoCode := "nl", propHeadFinal1000 := 533,
    depLengthAt10_100 := 207, depLengthAt15_100 := 248, depLengthAt20_100 := 274 },
  { language := "Afrikaans", isoCode := "af", propHeadFinal1000 := 524,
    depLengthAt10_100 := 216, depLengthAt15_100 := 248, depLengthAt20_100 := 278 },
  { language := "Finnish", isoCode := "fi", propHeadFinal1000 := 521,
    depLengthAt10_100 := 167, depLengthAt15_100 := 192, depLengthAt20_100 := 216 },
  { language := "Latvian", isoCode := "lv", propHeadFinal1000 := 513,
    depLengthAt10_100 := 171, depLengthAt15_100 := 193, depLengthAt20_100 := 216 },
  { language := "Estonian", isoCode := "et", propHeadFinal1000 := 508,
    depLengthAt10_100 := 184, depLengthAt15_100 := 213, depLengthAt20_100 := 232 },
  { language := "German", isoCode := "de", propHeadFinal1000 := 500,
    depLengthAt10_100 := 204, depLengthAt15_100 := 245, depLengthAt20_100 := 281 },
  { language := "Modern Greek", isoCode := "el", propHeadFinal1000 := 472,
    depLengthAt10_100 := 159, depLengthAt15_100 := 186, depLengthAt20_100 := 202 },
  { language := "English", isoCode := "en", propHeadFinal1000 := 460,
    depLengthAt10_100 := 167, depLengthAt15_100 := 193, depLengthAt20_100 := 210 },
  { language := "Danish", isoCode := "da", propHeadFinal1000 := 420,
    depLengthAt10_100 := 172, depLengthAt15_100 := 201, depLengthAt20_100 := 213 },
  { language := "Swedish", isoCode := "sv", propHeadFinal1000 := 420,
    depLengthAt10_100 := 166, depLengthAt15_100 := 193, depLengthAt20_100 := 213 },
  { language := "Slovenian", isoCode := "sl", propHeadFinal1000 := 419,
    depLengthAt10_100 := 173, depLengthAt15_100 := 195, depLengthAt20_100 := 219 },
  { language := "Slovak", isoCode := "sk", propHeadFinal1000 := 412,
    depLengthAt10_100 := 165, depLengthAt15_100 := 185, depLengthAt20_100 := 210 },
  { language := "Norwegian (B)", isoCode := "nb", propHeadFinal1000 := 401,
    depLengthAt10_100 := 163, depLengthAt15_100 := 190, depLengthAt20_100 := 208 },
  { language := "Persian", isoCode := "fa", propHeadFinal1000 := 401,
    depLengthAt10_100 := 226, depLengthAt15_100 := 265, depLengthAt20_100 := 288 },
  { language := "Norwegian (N)", isoCode := "nn", propHeadFinal1000 := 390,
    depLengthAt10_100 := 163, depLengthAt15_100 := 192, depLengthAt20_100 := 206 },
  { language := "Czech", isoCode := "cs", propHeadFinal1000 := 389,
    depLengthAt10_100 := 169, depLengthAt15_100 := 194, depLengthAt20_100 := 213 },
  { language := "Italian", isoCode := "it", propHeadFinal1000 := 384,
    depLengthAt10_100 := 150, depLengthAt15_100 := 180, depLengthAt20_100 := 188 },
  { language := "Croatian", isoCode := "hr", propHeadFinal1000 := 380,
    depLengthAt10_100 := 168, depLengthAt15_100 := 189, depLengthAt20_100 := 206 },
  { language := "French", isoCode := "fr", propHeadFinal1000 := 374,
    depLengthAt10_100 := 151, depLengthAt15_100 := 175, depLengthAt20_100 := 189 },
  { language := "Portuguese", isoCode := "pt", propHeadFinal1000 := 373,
    depLengthAt10_100 := 155, depLengthAt15_100 := 181, depLengthAt20_100 := 200 },
  { language := "Bulgarian", isoCode := "bg", propHeadFinal1000 := 372,
    depLengthAt10_100 := 156, depLengthAt15_100 := 181, depLengthAt20_100 := 197 },
  { language := "Gothic", isoCode := "got", propHeadFinal1000 := 372,
    depLengthAt10_100 := 197, depLengthAt15_100 := 234, depLengthAt20_100 := 275 },
  { language := "Catalan", isoCode := "ca", propHeadFinal1000 := 371,
    depLengthAt10_100 := 155, depLengthAt15_100 := 178, depLengthAt20_100 := 194 },
  { language := "Ukrainian", isoCode := "uk", propHeadFinal1000 := 368,
    depLengthAt10_100 := 161, depLengthAt15_100 := 189, depLengthAt20_100 := 206 },
  { language := "Galician", isoCode := "gl", propHeadFinal1000 := 365,
    depLengthAt10_100 := 150, depLengthAt15_100 := 220, depLengthAt20_100 := 210 },
  { language := "Russian", isoCode := "ru", propHeadFinal1000 := 358,
    depLengthAt10_100 := 156, depLengthAt15_100 := 181, depLengthAt20_100 := 207 },
  { language := "Serbian", isoCode := "sr", propHeadFinal1000 := 349,
    depLengthAt10_100 := 160, depLengthAt15_100 := 182, depLengthAt20_100 := 200 },
  { language := "Church Slavonic", isoCode := "cu", propHeadFinal1000 := 341,
    depLengthAt10_100 := 200, depLengthAt15_100 := 241, depLengthAt20_100 := 272 },
  { language := "Vietnamese", isoCode := "vi", propHeadFinal1000 := 339,
    depLengthAt10_100 := 165, depLengthAt15_100 := 195, depLengthAt20_100 := 212 },
  { language := "Spanish", isoCode := "es", propHeadFinal1000 := 332,
    depLengthAt10_100 := 145, depLengthAt15_100 := 171, depLengthAt20_100 := 186 },
  { language := "Polish", isoCode := "pl", propHeadFinal1000 := 325,
    depLengthAt10_100 := 156, depLengthAt15_100 := 180, depLengthAt20_100 := 205 },
  { language := "Hebrew", isoCode := "he", propHeadFinal1000 := 314,
    depLengthAt10_100 := 154, depLengthAt15_100 := 181, depLengthAt20_100 := 195 },
  { language := "Romanian", isoCode := "ro", propHeadFinal1000 := 301,
    depLengthAt10_100 := 160, depLengthAt15_100 := 179, depLengthAt20_100 := 195 },
  { language := "Indonesian", isoCode := "id", propHeadFinal1000 := 244,
    depLengthAt10_100 := 148, depLengthAt15_100 := 175, depLengthAt20_100 := 194 },
  { language := "Arabic", isoCode := "ar", propHeadFinal1000 := 103,
    depLengthAt10_100 := 140, depLengthAt15_100 := 168, depLengthAt20_100 := 193 } ]

example : table2.length = 46 := rfl

end FutrellEtAl2020
