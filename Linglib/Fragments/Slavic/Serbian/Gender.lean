import Linglib.Features.Gender.Basic

/-!
# Bosnian/Croatian/Serbian nouns by gender and humanness

The nouns of [adamson-anagnostopoulou-2025]'s Bosnian/Croatian/Serbian examples with their
grammatical gender and whether they denote humans; neuter nouns are mass or collective.

## References

* [adamson-anagnostopoulou-2025]
-/

namespace Serbian.Gender

/-- A noun with its grammatical gender and whether it denotes a human. -/
structure Noun where
  form : String
  gloss : String
  gender : _root_.Gender
  human : Bool
  deriving DecidableEq, Repr

def muskarac : Noun := ⟨"muškarac", "man", .masculine, true⟩
def zena : Noun := ⟨"žena", "woman", .feminine, true⟩
def covek : Noun := ⟨"čovek", "person, man", .masculine, true⟩
def znanje : Noun := ⟨"znanje", "knowledge", .neuter, false⟩
def intuicija : Noun := ⟨"intuicija", "intuition", .feminine, false⟩
def selo : Noun := ⟨"selo", "village", .neuter, false⟩
def brdo : Noun := ⟨"brdo", "hill", .neuter, false⟩
def knjiga : Noun := ⟨"knjiga", "book", .feminine, false⟩
def pesak : Noun := ⟨"pesak", "sand", .masculine, false⟩
def mleko : Noun := ⟨"mleko", "milk", .neuter, false⟩

end Serbian.Gender
