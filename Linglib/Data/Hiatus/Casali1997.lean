module

public import Linglib.Data.Hiatus.Schema

/-!
# Casali1997 — hiatus resolution sample (generated)
[casali-1997]

Auto-generated from `Linglib/Data/Hiatus/Casali1997.json` by
`scripts/gen_hiatus.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

The languages the paper's Section 2 lists for each of its four generalizations about which vowel
elides: the first vowel between two lexical words, the second vowel before a function word, the
first vowel after a prefix of at least a consonant and a vowel, and either vowel between a root and
a suffix. A language the paper introduces with 'possibly' is tentative.
-/

@[expose] public section

namespace Data.Hiatus.Casali1997

open Data.Hiatus

/-- The paper's reports of which vowel elides, one row per language and juncture. -/
def rows : List ElisionRow := [
  ⟨"Au", .lexicalLexical, .first, false⟩,
  ⟨"Babole", .lexicalLexical, .first, false⟩,
  ⟨"Bemba", .lexicalLexical, .first, false⟩,
  ⟨"Bobangi", .lexicalLexical, .first, false⟩,
  ⟨"Bolia", .lexicalLexical, .first, false⟩,
  ⟨"Central Kambari", .lexicalLexical, .first, false⟩,
  ⟨"Chicano Spanish", .lexicalLexical, .first, false⟩,
  ⟨"Chumburung", .lexicalLexical, .first, false⟩,
  ⟨"Ebira", .lexicalLexical, .first, false⟩,
  ⟨"Efik", .lexicalLexical, .first, false⟩,
  ⟨"Eggon", .lexicalLexical, .first, false⟩,
  ⟨"Emai", .lexicalLexical, .first, false⟩,
  ⟨"Engenni", .lexicalLexical, .first, false⟩,
  ⟨"Etsako", .lexicalLexical, .first, false⟩,
  ⟨"Ghotuo", .lexicalLexical, .first, false⟩,
  ⟨"Gichode", .lexicalLexical, .first, false⟩,
  ⟨"Gonja", .lexicalLexical, .first, false⟩,
  ⟨"Igbo", .lexicalLexical, .first, false⟩,
  ⟨"Igede", .lexicalLexical, .first, false⟩,
  ⟨"Isekiri", .lexicalLexical, .first, false⟩,
  ⟨"Isoko", .lexicalLexical, .first, false⟩,
  ⟨"Ivie", .lexicalLexical, .first, false⟩,
  ⟨"Izi", .lexicalLexical, .first, false⟩,
  ⟨"Krachi", .lexicalLexical, .first, false⟩,
  ⟨"Lamba", .lexicalLexical, .first, false⟩,
  ⟨"Lokəə", .lexicalLexical, .first, false⟩,
  ⟨"Logo", .lexicalLexical, .first, false⟩,
  ⟨"LuGanda", .lexicalLexical, .first, false⟩,
  ⟨"Lulobo", .lexicalLexical, .first, false⟩,
  ⟨"Malakmalak", .lexicalLexical, .first, false⟩,
  ⟨"Nawuri", .lexicalLexical, .first, false⟩,
  ⟨"Nupe", .lexicalLexical, .first, false⟩,
  ⟨"Ogbia", .lexicalLexical, .first, false⟩,
  ⟨"Ogoja Yala", .lexicalLexical, .first, false⟩,
  ⟨"Ogori", .lexicalLexical, .first, false⟩,
  ⟨"Owon Afa", .lexicalLexical, .first, false⟩,
  ⟨"Pero", .lexicalLexical, .first, false⟩,
  ⟨"Sango", .lexicalLexical, .first, false⟩,
  ⟨"Urhobo", .lexicalLexical, .first, false⟩,
  ⟨"Yakata", .lexicalLexical, .first, false⟩,
  ⟨"Yoruba", .lexicalLexical, .first, false⟩,
  ⟨"Zulu", .lexicalLexical, .first, false⟩,
  ⟨"Basque", .lexicalFunction, .second, false⟩,
  ⟨"Dangme", .lexicalFunction, .second, false⟩,
  ⟨"Emai", .lexicalFunction, .second, false⟩,
  ⟨"Etsako", .lexicalFunction, .second, false⟩,
  ⟨"Ewe", .lexicalFunction, .second, false⟩,
  ⟨"Isekiri", .lexicalFunction, .second, false⟩,
  ⟨"Isoko", .lexicalFunction, .second, false⟩,
  ⟨"Ivie", .lexicalFunction, .second, false⟩,
  ⟨"Mundani", .lexicalFunction, .second, false⟩,
  ⟨"Sango", .lexicalFunction, .second, false⟩,
  ⟨"Shona", .lexicalFunction, .second, false⟩,
  ⟨"Vata", .lexicalFunction, .second, false⟩,
  ⟨"Efik", .lexicalFunction, .second, true⟩,
  ⟨"Ogoja Yala", .lexicalFunction, .second, true⟩,
  ⟨"Avatime", .prefixRoot, .first, false⟩,
  ⟨"Babole", .prefixRoot, .first, false⟩,
  ⟨"Bemba", .prefixRoot, .first, false⟩,
  ⟨"Bobangi", .prefixRoot, .first, false⟩,
  ⟨"Chagga", .prefixRoot, .first, false⟩,
  ⟨"Chichewa", .prefixRoot, .first, false⟩,
  ⟨"Chiyao", .prefixRoot, .first, false⟩,
  ⟨"Diola-Fogny", .prefixRoot, .first, false⟩,
  ⟨"Ila", .prefixRoot, .first, false⟩,
  ⟨"Kamba", .prefixRoot, .first, false⟩,
  ⟨"KiYaka", .prefixRoot, .first, false⟩,
  ⟨"Kongo", .prefixRoot, .first, false⟩,
  ⟨"Lamba", .prefixRoot, .first, false⟩,
  ⟨"LuGanda", .prefixRoot, .first, false⟩,
  ⟨"Lugisu", .prefixRoot, .first, false⟩,
  ⟨"Pero", .prefixRoot, .first, false⟩,
  ⟨"Shona", .prefixRoot, .first, false⟩,
  ⟨"Si-Luyana", .prefixRoot, .first, false⟩,
  ⟨"SiSwati", .prefixRoot, .first, false⟩,
  ⟨"Tsonga", .prefixRoot, .first, false⟩,
  ⟨"Uma Juman", .prefixRoot, .first, false⟩,
  ⟨"West Tarangan", .prefixRoot, .first, false⟩,
  ⟨"Xhosa", .prefixRoot, .first, false⟩,
  ⟨"Yakata", .prefixRoot, .first, false⟩,
  ⟨"Yoruba", .prefixRoot, .first, false⟩,
  ⟨"Zulu", .prefixRoot, .first, false⟩,
  ⟨"Santee Dakota", .prefixRoot, .first, true⟩,
  ⟨"Afar", .rootSuffix, .first, false⟩,
  ⟨"Aghem", .rootSuffix, .first, false⟩,
  ⟨"Avatime", .rootSuffix, .first, false⟩,
  ⟨"Daga", .rootSuffix, .first, false⟩,
  ⟨"Diola-Fogny", .rootSuffix, .first, false⟩,
  ⟨"Igede", .rootSuffix, .first, false⟩,
  ⟨"Iraqw", .rootSuffix, .first, false⟩,
  ⟨"KiYaka", .rootSuffix, .first, false⟩,
  ⟨"Lamba", .rootSuffix, .first, false⟩,
  ⟨"LuGanda", .rootSuffix, .first, false⟩,
  ⟨"Moba", .rootSuffix, .first, false⟩,
  ⟨"Nawuri", .rootSuffix, .first, false⟩,
  ⟨"Nupe", .rootSuffix, .first, false⟩,
  ⟨"Niaboua", .rootSuffix, .first, false⟩,
  ⟨"Ogbia", .rootSuffix, .first, false⟩,
  ⟨"Santee Dakota", .rootSuffix, .first, false⟩,
  ⟨"Shilluk", .rootSuffix, .first, false⟩,
  ⟨"Shona", .rootSuffix, .first, false⟩,
  ⟨"Tabla", .rootSuffix, .first, false⟩,
  ⟨"Tsonga", .rootSuffix, .first, false⟩,
  ⟨"Vata", .rootSuffix, .first, false⟩,
  ⟨"Afar", .rootSuffix, .second, false⟩,
  ⟨"Aghem", .rootSuffix, .second, false⟩,
  ⟨"Avatime", .rootSuffix, .second, false⟩,
  ⟨"Basque", .rootSuffix, .second, false⟩,
  ⟨"Chichewa", .rootSuffix, .second, false⟩,
  ⟨"Dangme", .rootSuffix, .second, false⟩,
  ⟨"Daga", .rootSuffix, .second, false⟩,
  ⟨"Diola-Fogny", .rootSuffix, .second, false⟩,
  ⟨"Edo", .rootSuffix, .second, false⟩,
  ⟨"Kagate", .rootSuffix, .second, false⟩,
  ⟨"Lulobo", .rootSuffix, .second, false⟩,
  ⟨"Niaboua", .rootSuffix, .second, false⟩,
  ⟨"Okpe", .rootSuffix, .second, false⟩,
  ⟨"Vata", .rootSuffix, .second, false⟩]

end Data.Hiatus.Casali1997
