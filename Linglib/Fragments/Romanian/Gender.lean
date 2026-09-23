module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Romanian noun gender

Agreeing adjectives such as *bun* 'good' show two forms in the singular, *-Ø* and *-ă*, and
two in the plural, *-i* and *-e*, but nouns fall into three sets by the forms they take
across the two numbers: *bărbat* 'man' (*-Ø*, *-i*), *fată* 'girl' (*-ă*, *-e*) and *scaun*
'chair' (*-Ø*, *-e*), the last the disputed neuter or ambigeneric gender
([mallinson-1984]; [corbett-1991]).

## References

* [G. Mallinson, *Rumanian* (1984)][mallinson-1984]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

@[expose] public section

namespace Romanian.Gender

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine
  | .neut => .neuter

/-- A Romanian noun with its controller gender, the gender of its referents where it has one,
and whether it denotes an animate. -/
structure Noun extends GenderedNoun Value where
  /-- Whether the noun denotes an animate. -/
  animate : Bool
  deriving DecidableEq, Repr

def barbat : Noun := ⟨⟨⟨"bărbat", "man"⟩, .masc, some .masculine⟩, true⟩
def fata : Noun := ⟨⟨⟨"fată", "girl"⟩, .fem, some .feminine⟩, true⟩
def scaun : Noun := ⟨⟨⟨"scaun", "chair"⟩, .neut, none⟩, false⟩
def femeie : Noun := ⟨⟨⟨"femeie", "woman"⟩, .fem, some .feminine⟩, true⟩
def baiat : Noun := ⟨⟨⟨"băiat", "boy"⟩, .masc, some .masculine⟩, true⟩
def usa : Noun := ⟨⟨⟨"uşă", "door"⟩, .fem, none⟩, false⟩
def perete : Noun := ⟨⟨⟨"perete", "wall"⟩, .masc, none⟩, false⟩
def masa : Noun := ⟨⟨⟨"masă", "table"⟩, .fem, none⟩, false⟩
def nuc : Noun := ⟨⟨⟨"nuc", "walnut tree"⟩, .masc, none⟩, false⟩
def prun : Noun := ⟨⟨⟨"prun", "plum tree"⟩, .masc, none⟩, false⟩
def frigider : Noun := ⟨⟨⟨"frigider", "refrigerator"⟩, .neut, none⟩, false⟩
def televizor : Noun := ⟨⟨⟨"televizor", "television"⟩, .neut, none⟩, false⟩

def allNouns : List Noun :=
  [barbat, fata, scaun, femeie, baiat, usa, perete, masa, nuc, prun, frigider, televizor]

/-- The endings of *bun* 'good'. -/
inductive AdjForm where
  | zero
  | ă
  | i
  | e
  deriving DecidableEq, Repr, Fintype

/-- The ending an agreeing adjective takes with each gender, in each number. -/
def Value.adjForm (g : Value) (plural : Bool) : AdjForm :=
  match g, plural with
  | .masc, false => .zero
  | .masc, true => .i
  | .fem, false => .ă
  | .fem, true => .e
  | .neut, false => .zero
  | .neut, true => .e

/-- Taking both numbers together, the adjective distinguishes all three genders. -/
theorem faithful_adjForm : Gender.Faithful Value.adjForm := by decide

end Romanian.Gender
