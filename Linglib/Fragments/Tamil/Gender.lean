import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Gender.Basic

/-!
# Tamil noun gender

Tamil divides nouns into rationals, the male and female humans and deities, and the
non-rational rest: three genders, masculine, feminine and neuter, shown by third-person
agreement on the verb. In the singular the three are distinct; in the plural the two
rational genders share one form against the neuter ([asher-1985]; [corbett-1991]).

## References

* [R. E. Asher, *Tamil* (1985)][asher-1985]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

namespace Tamil.Gender

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- A Tamil noun with the agreement it takes and the two semantic facts the gender tracks:
whether the referent is rational, and whether the gender comes from the referent's sex. -/
structure Noun where
  form : String
  gloss : String
  /-- The agreement the noun takes. -/
  attestedGender : Value
  /-- Whether the referent is rational: a human or a deity. -/
  rational : Bool
  /-- Whether the gender comes from the referent's sex. -/
  isNaturalGender : Bool
  deriving DecidableEq, Repr

abbrev Noun.gender (n : Noun) : Value := n.attestedGender

def aaN : Noun := ⟨"aaN", "man", .masc, true, true⟩
def civaN : Noun := ⟨"CivaN", "Shiva", .masc, true, true⟩
def peN : Noun := ⟨"peN", "woman", .fem, true, true⟩
def kaali : Noun := ⟨"kaali", "Kali", .fem, true, true⟩
def maram : Noun := ⟨"maram", "tree", .neut, false, false⟩
def viiTu : Noun := ⟨"viiTu", "house", .neut, false, false⟩
def raaman : Noun := ⟨"raaman", "Raman", .masc, true, true⟩
def murukan : Noun := ⟨"murukan", "Murugan", .masc, true, true⟩
def akkaa : Noun := ⟨"akkaa", "elder sister", .fem, true, true⟩
def tankacci : Noun := ⟨"tankacci", "younger sister", .fem, true, true⟩
def annan : Noun := ⟨"annan", "elder brother", .masc, true, true⟩
def naay : Noun := ⟨"naay", "dog", .neut, false, false⟩
def puune : Noun := ⟨"puune", "cat", .neut, false, false⟩

def allNouns : List Noun :=
  [aaN, civaN, peN, kaali, maram, viiTu, raaman, murukan, akkaa, tankacci, annan, naay, puune]

/-- Third-person singular verb agreement: *-aan* masculine, *-aaL* feminine, *-atu* neuter. -/
inductive SgConcord where
  | aan
  | aaL
  | atu
  deriving DecidableEq, Repr, Fintype

/-- Third-person plural verb agreement: one form for rationals, one for neuters. -/
inductive PlConcord where
  | rational
  | neuter
  deriving DecidableEq, Repr, Fintype

def Value.sgConcord : Value → SgConcord
  | .masc => .aan
  | .fem => .aaL
  | .neut => .atu

def Value.plConcord : Value → PlConcord
  | .masc | .fem => .rational
  | .neut => .neuter

/-- The gender system: fully labelled, neuter the default. -/
def system : Gender.System Value where
  label
    | .masc => some .masculine
    | .fem => some .feminine
    | .neut => some .neuter
  default := .neut

/-- Every noun gets its controller gender. -/
def assigned : Gender.System.Assigned Noun Value := { system with assign := Noun.gender }

/-- Singular verb agreement alone distinguishes the three genders. -/
theorem faithful_sgConcord : Gender.Faithful (λ (g : Value) (_ : Unit) => g.sgConcord) := by
  decide

end Tamil.Gender
