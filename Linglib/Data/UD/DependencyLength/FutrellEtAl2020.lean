import Linglib.Data.UD.DependencyLength.Schema

/-!
# FutrellEtAl2020 — dependency length by language (generated)
[futrell-levy-gibson-2020]

Auto-generated from `Linglib/Data/UD/DependencyLength/FutrellEtAl2020.json` by
`scripts/gen_ud_deplength.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

Table 2 of the paper: for each of the 46 languages with more than 1500 sentences in Universal
Dependencies 2.1, the proportion of head-final dependencies and the mean dependency length per
word at sentence lengths 10, 15 and 20, with content words heading function words as in the UD
annotation. The language codes are UD codes matching the keys of the paper's analysis pipeline
(CLIQS, typology3.csv).
-/

namespace Data.UD.DependencyLength.FutrellEtAl2020

/-- The 46 languages of Table 2, in the paper's row order. -/
def rows : List Row :=
  [⟨"Korean", "ko", 881, 201, 249, 284⟩,
   ⟨"Japanese", "ja", 809, 170, 198, 226⟩,
   ⟨"Turkish", "tr", 778, 199, 236, 261⟩,
   ⟨"Hindi", "hi", 763, 188, 226, 257⟩,
   ⟨"Urdu", "ur", 745, 186, 227, 249⟩,
   ⟨"Hungarian", "hu", 726, 178, 213, 240⟩,
   ⟨"Mandarin", "zh", 661, 203, 251, 298⟩,
   ⟨"Basque", "eu", 587, 177, 210, 229⟩,
   ⟨"Ancient Greek", "grc", 566, 234, 274, 308⟩,
   ⟨"Latin", "la", 547, 227, 272, 299⟩,
   ⟨"Northern Sami", "sme", 542, 185, 220, 262⟩,
   ⟨"Dutch", "nl", 533, 207, 248, 274⟩,
   ⟨"Afrikaans", "af", 524, 216, 248, 278⟩,
   ⟨"Finnish", "fi", 521, 167, 192, 216⟩,
   ⟨"Latvian", "lv", 513, 171, 193, 216⟩,
   ⟨"Estonian", "et", 508, 184, 213, 232⟩,
   ⟨"German", "de", 500, 204, 245, 281⟩,
   ⟨"Modern Greek", "el", 472, 159, 186, 202⟩,
   ⟨"English", "en", 460, 167, 193, 210⟩,
   ⟨"Danish", "da", 420, 172, 201, 213⟩,
   ⟨"Swedish", "sv", 420, 166, 193, 213⟩,
   ⟨"Slovenian", "sl", 419, 173, 195, 219⟩,
   ⟨"Slovak", "sk", 412, 165, 185, 210⟩,
   ⟨"Norwegian (B)", "nb", 401, 163, 190, 208⟩,
   ⟨"Persian", "fa", 401, 226, 265, 288⟩,
   ⟨"Norwegian (N)", "nn", 390, 163, 192, 206⟩,
   ⟨"Czech", "cs", 389, 169, 194, 213⟩,
   ⟨"Italian", "it", 384, 150, 180, 188⟩,
   ⟨"Croatian", "hr", 380, 168, 189, 206⟩,
   ⟨"French", "fr", 374, 151, 175, 189⟩,
   ⟨"Portuguese", "pt", 373, 155, 181, 200⟩,
   ⟨"Bulgarian", "bg", 372, 156, 181, 197⟩,
   ⟨"Gothic", "got", 372, 197, 234, 275⟩,
   ⟨"Catalan", "ca", 371, 155, 178, 194⟩,
   ⟨"Ukrainian", "uk", 368, 161, 189, 206⟩,
   ⟨"Galician", "gl", 365, 150, 220, 210⟩,
   ⟨"Russian", "ru", 358, 156, 181, 207⟩,
   ⟨"Serbian", "sr", 349, 160, 182, 200⟩,
   ⟨"Church Slavonic", "cu", 341, 200, 241, 272⟩,
   ⟨"Vietnamese", "vi", 339, 165, 195, 212⟩,
   ⟨"Spanish", "es", 332, 145, 171, 186⟩,
   ⟨"Polish", "pl", 325, 156, 180, 205⟩,
   ⟨"Hebrew", "he", 314, 154, 181, 195⟩,
   ⟨"Romanian", "ro", 301, 160, 179, 195⟩,
   ⟨"Indonesian", "id", 244, 148, 175, 194⟩,
   ⟨"Arabic", "ar", 103, 140, 168, 193⟩]

end Data.UD.DependencyLength.FutrellEtAl2020
