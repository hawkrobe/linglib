import Linglib.Syntax.Comparative
import Linglib.Syntax.Clause.Chaining
import Linglib.Fragments.Japanese.Comparison
import Linglib.Fragments.Korean.Comparison
import Linglib.Fragments.Turkish.Comparison
import Linglib.Fragments.HindiUrdu.Comparison
import Linglib.Fragments.Mandarin.Comparison
import Linglib.Fragments.English.Comparison
import Linglib.Fragments.Korean.MedialVerbs
import Linglib.Fragments.Turkish.MedialVerbs

/-!
# Stassen (1985): Comparison and Universal Grammar

This file formalizes [stassen-1985]'s typology of comparative constructions and its
explanation by temporal chaining. A comparative construction assigns the standard NP derived
or fixed case, and a fixed-case standard is the direct object of a verb of exceeding or an
adverbial in a spatial case; the six types are `Type1985`, read off a construction's anatomy
by `type1985`: separative, allative and locative for adverbial standards in ablative,
allative and locative case, exceed for direct-object standards, and particle and conjoined
for derived-case standards with and without a standard marker. The typology of
[stassen-2013] collapses the three spatial types into one locational type
(`toWALS_type1985`).

Temporal chains are balanced, both predicates keeping their rank, or deranked, one predicate
reduced, either only in same-subject chains or regardless of subject identity, and an
absolutely deranked consecutive chain reduces its anterior or its posterior predicate; the
chain types are `ChainType`. The book's thesis is that a language's comparative is modelled
on its temporal chains, `Models`, and its universals relating the two typologies are the
consequences: derived-case comparatives arise from balancing and fixed-case comparatives from
deranking (`universal1`), exceed comparatives from conditional and adverbial comparatives
from absolute deranking (`universal2`), the three spatial types from anterior, posterior and
simultaneous absolute deranking (`universal3`), and conjoined comparatives from balanced
simultaneous chains (`universal4`). Over the fragments, the balancing/deranking cut of a
clause-chaining system is read off the finiteness of its medial verb (`strategy`), and
Korean and Turkish, whose comparison and clause-chaining fragments both exist, have
separative comparatives and deranked chains, as the thesis requires (`korean_consistent`,
`turkish_consistent`).

## Implementation notes

The book is held only in a lending library, so its language lists and page locators were not
checked and the study keeps only what the fragments derive; the per-language chaining
types of the book's sample are not transcribed. The clause-chaining substrate records the
finiteness of medial verbs but neither the same-subject conditionality of deranking nor the
anterior/posterior orientation of the deranked predicate, so `ChainType` is not read off a
fragment beyond its strategy. The Principle of Parallel Chaining and the diachronic pathway
from a negated conjunction to a comparative are described in the book and not formalized.

## References

* [stassen-1985]
* [stassen-2013]
-/

namespace Stassen1985

open Comparative Clause.Chaining

/-! ### The six comparative types -/

/-- The comparative types of [stassen-1985]: the three adverbial types by the spatial case of
the standard, the exceed type, and the two derived-case types. -/
inductive Type1985
  | separative
  | allative
  | locative
  | exceed
  | conjoined
  | particle
  deriving DecidableEq, Repr, Fintype

namespace Type1985

/-- The type of [stassen-2013], which collapses the adverbial types into one. -/
def toWALS : Type1985 → ComparativeType
  | .separative | .allative | .locative => .locational
  | .exceed => .exceed
  | .conjoined => .conjoined
  | .particle => .particle

/-- The case assignment of a type: derived for the conjoined and particle types. -/
def caseAssignment : Type1985 → CaseAssignment
  | .conjoined | .particle => .derived
  | _ => .fixed

/-- The encoding of a fixed-case standard. -/
def fixedEncoding : Type1985 → Option FixedCaseEncoding
  | .exceed => some .directObject
  | .separative | .allative | .locative => some .adverbial
  | .conjoined | .particle => none

/-- The spatial case of an adverbial standard. -/
def spatialCase : Type1985 → Option Case
  | .separative => some .abl
  | .allative => some .all
  | .locative => some .loc
  | _ => none

/-- Derived case is exactly the conjoined and particle types. -/
theorem caseAssignment_eq_derived_iff :
    ∀ t : Type1985, t.caseAssignment = .derived ↔ t = .particle ∨ t = .conjoined := by decide

/-- Adverbial encoding is exactly the spatial triad. -/
theorem fixedEncoding_eq_adverbial_iff :
    ∀ t : Type1985, t.fixedEncoding = some .adverbial ↔ t.spatialCase.isSome := by decide

end Type1985

/-- The type of a construction, read off its anatomy: `none` for an adverbial standard in a
non-spatial case, such as the Finnish partitive. -/
def type1985 (c : Comparative) : Option Type1985 :=
  match c.caseAssignment, c.fixedEncoding, c.standardCase with
  | .derived, _, _ => some (if c.standardMarker.isSome then .particle else .conjoined)
  | .fixed, some .directObject, _ => some .exceed
  | .fixed, _, some .abl => some .separative
  | .fixed, _, some .all => some .allative
  | .fixed, _, some .loc => some .locative
  | .fixed, _, _ => none

/-- The type of a construction collapses to the type its anatomy derives in the typology of
[stassen-2013]. -/
theorem toWALS_type1985 {c : Comparative} {t : Type1985} (h : type1985 c = some t) :
    t.toWALS = c.type := by
  obtain ⟨m, ca, fe, sc, _, _⟩ := c
  cases ca
  · cases hm : m.isSome <;> simp_all [type1985, Comparative.type, Type1985.toWALS] <;>
      (subst h; rfl)
  · rcases fe with _ | _ | _ <;> rcases sc with _ | k <;> (try cases k) <;>
      simp_all [type1985, Comparative.type, Type1985.toWALS] <;> (subst h; rfl)

/-- The case assignment of a construction's type is the construction's. -/
theorem caseAssignment_type1985 {c : Comparative} {t : Type1985} (h : type1985 c = some t) :
    t.caseAssignment = c.caseAssignment := by
  obtain ⟨m, ca, fe, sc, _, _⟩ := c
  cases ca
  · cases hm : m.isSome <;> simp_all [type1985, Type1985.caseAssignment] <;> (subst h; rfl)
  · rcases fe with _ | _ | _ <;> rcases sc with _ | k <;> (try cases k) <;>
      simp_all [type1985, Type1985.caseAssignment] <;> (subst h; rfl)

/-- The spatial case of an adverbial type is the case of the construction's standard. -/
theorem spatialCase_type1985 {c : Comparative} {t : Type1985} (h : type1985 c = some t)
    (hs : t.spatialCase.isSome) : t.spatialCase = c.standardCase := by
  obtain ⟨m, ca, fe, sc, _, _⟩ := c
  cases ca
  · cases hm : m.isSome <;> simp_all [type1985, Type1985.spatialCase] <;>
      (subst h; simp at hs)
  · rcases fe with _ | _ | _ <;> rcases sc with _ | k <;> (try cases k) <;>
      simp_all [type1985, Type1985.spatialCase] <;>
      (subst h; first | rfl | simp at hs)

/-! ### Temporal chaining -/

/-- The strategies for encoding a temporal chain: both predicates keep their structural rank,
or one is reduced. -/
inductive Strategy
  | balancing
  | deranking
  deriving DecidableEq, Repr, Fintype

/-- The chain types of the book's typology of temporal chaining: balanced consecutive and
simultaneous chains, deranking conditioned on subject identity, and absolute deranking of the
anterior or the posterior predicate of a consecutive chain or of a simultaneous chain. -/
inductive ChainType
  | balancedConsecutive
  | balancedSimultaneous
  | conditionallyDeranked
  | anteriorDeranked
  | posteriorDeranked
  | simultaneousDeranked
  deriving DecidableEq, Repr, Fintype

namespace ChainType

/-- The strategy of a chain type. -/
def strategy : ChainType → Strategy
  | .balancedConsecutive | .balancedSimultaneous => .balancing
  | _ => .deranking

/-- A chain type deranks regardless of subject identity. -/
def Absolute : ChainType → Prop
  | .anteriorDeranked | .posteriorDeranked | .simultaneousDeranked => True
  | _ => False

instance : DecidablePred Absolute := λ ct => by cases ct <;> simp only [Absolute] <;> infer_instance

/-- A chain type is simultaneous rather than consecutive. -/
def Simultaneous : ChainType → Prop
  | .balancedSimultaneous | .simultaneousDeranked => True
  | _ => False

instance : DecidablePred Simultaneous := λ ct => by
  cases ct <;> simp only [Simultaneous] <;> infer_instance

end ChainType

/-- The book's thesis: a comparative construction is modelled on a temporal chain. Particle
comparatives are modelled on balanced chains of either temporality, conjoined comparatives on
balanced simultaneous chains, exceed comparatives on conditionally deranked chains, and the
three adverbial comparatives on absolutely deranked chains with the anterior predicate, the
posterior predicate, or the simultaneous predicate reduced. -/
inductive Models : ChainType → Type1985 → Prop
  | particleConsecutive : Models .balancedConsecutive .particle
  | particleSimultaneous : Models .balancedSimultaneous .particle
  | conjoined : Models .balancedSimultaneous .conjoined
  | exceed : Models .conditionallyDeranked .exceed
  | separative : Models .anteriorDeranked .separative
  | allative : Models .posteriorDeranked .allative
  | locative : Models .simultaneousDeranked .locative

instance (ct : ChainType) (t : Type1985) : Decidable (Models ct t) := by
  cases ct <;> cases t <;> first
    | exact isTrue (by constructor)
    | exact isFalse (by intro h; cases h)

/-- Every comparative type is modelled on some chain type. -/
theorem exists_models : ∀ t : Type1985, ∃ ct, Models ct t := by decide

/-- Universal 1: a derived-case comparative is modelled on a balanced chain and a fixed-case
comparative on a deranked one. -/
theorem universal1 :
    ∀ ct t, Models ct t → (t.caseAssignment = .derived ↔ ct.strategy = .balancing) := by
  decide

/-- Universal 2: an exceed comparative is modelled on conditional deranking and an adverbial
comparative on absolute deranking. -/
theorem universal2 :
    ∀ ct t, Models ct t →
      (t = .exceed → ct = .conditionallyDeranked) ∧
        (t.fixedEncoding = some .adverbial → ct.Absolute) := by
  decide

/-- Universal 3: separative, allative and locative comparatives are modelled on absolutely
deranked chains with, respectively, the anterior predicate, the posterior predicate and the
simultaneous predicate reduced. -/
theorem universal3 :
    ∀ ct t, Models ct t →
      (t = .separative ↔ ct = .anteriorDeranked) ∧ (t = .allative ↔ ct = .posteriorDeranked) ∧
        (t = .locative ↔ ct = .simultaneousDeranked) := by
  decide

/-- Universal 4: a conjoined comparative is modelled on a balanced simultaneous chain. -/
theorem universal4 : ∀ ct t, Models ct t → t = .conjoined → ct = .balancedSimultaneous := by
  decide

/-! ### The fragments -/

/-- The strategy of a clause-chaining system: deranking when its medial verb is non-finite. -/
def strategy (s : System) : Strategy :=
  if s.medialVerbForm = .Fin then .balancing else .deranking

/-- The separative constructions of the fragments: the ablative standards of Japanese, Korean,
Turkish and Hindi-Urdu. -/
theorem separative_fragments :
    ∀ c ∈ [Japanese.Comparison.yori, Korean.Comparison.boda, Turkish.Comparison.dan,
      HindiUrdu.Comparison.se], type1985 c = some .separative := by
  decide

theorem mandarin_exceed : type1985 Mandarin.Comparison.bi = some .exceed := by decide

theorem english_particle : type1985 English.Comparison.than = some .particle := by decide

/-- Korean has a separative comparative and deranked chains: the chain type its comparative is
modelled on has the strategy its clause-chaining fragment shows. -/
theorem korean_consistent :
    ∀ ct, Models ct .separative → ct.strategy = strategy Korean.chaining := by
  decide

/-- Turkish likewise. -/
theorem turkish_consistent :
    ∀ ct, Models ct .separative → ct.strategy = strategy Turkish.MedialVerbs.chaining := by
  decide

end Stassen1985
