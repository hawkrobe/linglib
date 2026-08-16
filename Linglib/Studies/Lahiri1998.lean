import Linglib.Semantics.Focus.Particles
import Linglib.Logic.Natural.World
import Linglib.Semantics.Polarity.Licensing
import Linglib.Fragments.Hindi.PolarityItems
import Linglib.Data.Examples.Lahiri1998

/-!
# Lahiri 1998 — Focus and negative polarity in Hindi

Hindi NPIs (*koii bhii* 'anyone', *ek bhii* 'even one', *kuch bhii*
'anything', *zaraa bhii* 'even a little') are morphologically an
indefinite plus the focus particle *bhii* 'even' (paper (1), p. 58).
[lahiri-1998] derives their distribution — as NPIs and as free-choice
items — compositionally: *bhii* contributes the scalar implicature
([karttunen-peters-1979]) that the assertion is least likely among the
focus alternatives, and the weak indefinite sits at the bottom of the
entailment scale. In UE contexts every alternative entails the
assertion, making it the *most* likely — the implicature is
contradicted (§7.4). In DE contexts entailment reverses and the
implicature is satisfiable. Free-choice readings arise where the
implicature is satisfiable in generic and possibility-modal contexts
(§5, §7.6); *ek bhii*'s cardinality alternatives vs *koii bhii*'s
contextual-property alternatives explain their contrasts (§8). The
judged stimuli live in `Data/Examples/Lahiri1998.json`
(`Examples.ex6a`, …).
-/

namespace Lahiri1998

open Focus.Particles (evenPresup LikelihoodMonotone)
open Entailment (World entails pnot)
open Polarity
open Data.Examples (LinguisticExample)

/-! ### Morphological decomposition (paper (1), p. 58)

Every item in the paradigm is a weak indefinite plus *bhii*. The kind
of alternatives an item activates (cardinality vs contextually salient
properties, §8) is a lexical property, stored on the fragment entries
in `Hindi.PolarityItems`. (*kahiiN bhii*'s licensed uses in the paper
are correlatives, §4.4, an environment not modeled here.) -/

/-- A row of the paper's decomposition table (1): base indefinite and
the *bhii*-compound, with the paper's glosses. -/
structure NPIDecomposition where
  base : String
  baseGloss : String
  npiForm : String
  npiGloss : String
  deriving Repr

/-- The paper's decomposition table ((1), p. 58). -/
def hindiNPIs : List NPIDecomposition :=
  [ ⟨"ek", "one", "ek bhii", "any, even one"⟩
  , ⟨"koii", "someone", "koii bhii", "anyone, any (count)"⟩
  , ⟨"kuch", "something, a little", "kuch bhii", "anything, any (mass)"⟩
  , ⟨"zaraa", "a little", "zaraa bhii", "even a little"⟩
  , ⟨"kabhii", "sometime", "kabhii bhii", "anytime, ever"⟩
  , ⟨"kahiiN", "somewhere", "kahiiN bhii", "anywhere"⟩ ]

/-- Morphological uniformity: every NPI form is its base plus *bhii*. -/
theorem npiForm_eq_base_bhii :
    ∀ d ∈ hindiNPIs, d.npiForm = d.base ++ " bhii" := by decide

/-! ### The cardinality model

The scale `∃x[n(x) ∧ VP(x)]` over the 4-world semantics of
`Entailment.Basic`: w0 = at least three entities satisfy the VP,
w1 = exactly two, w2 = exactly one, w3 = none. -/

/-- At least one entity satisfies the VP (Bool form). -/
def atLeastOneB : (World → Bool) := λ w => w != .w3

/-- At least two entities satisfy the VP (Bool form). -/
def atLeastTwoB : (World → Bool) := λ w => w == .w0 || w == .w1

/-- At least three entities satisfy the VP (Bool form). -/
def atLeastThreeB : (World → Bool) := λ w => w == .w0

/-- At least one entity satisfies the VP. True at w0, w1, w2. -/
def atLeastOne : Set World := {w | atLeastOneB w = true}

/-- At least two entities satisfy the VP. True at w0, w1. -/
def atLeastTwo : Set World := {w | atLeastTwoB w = true}

/-- At least three entities satisfy the VP. True at w0 only. -/
def atLeastThree : Set World := {w | atLeastThreeB w = true}

/-! ### Weakness of `one` (§7.4, eq. 70)

`one` is the weakest cardinality predicate: every `atLeastN`
proposition entails `atLeastOne`, and not conversely. -/

theorem two_entails_one : entails atLeastTwo atLeastOne := by
  intro w hw
  simp [atLeastOne, atLeastOneB, atLeastTwo, atLeastTwoB] at *
  rcases hw with h | h <;> simp [h]
theorem three_entails_one : entails atLeastThree atLeastOne := by
  intro w hw
  simp [atLeastOne, atLeastOneB, atLeastThree, atLeastThreeB] at *
  simp [hw]
theorem three_entails_two : entails atLeastThree atLeastTwo := by
  intro w hw
  simp [atLeastThree, atLeastThreeB, atLeastTwo, atLeastTwoB] at *
  left; exact hw

/-- The entailment is strict: `atLeastOne` does not entail stronger predicates. -/
theorem one_not_entails_two : ¬ entails atLeastOne atLeastTwo := by
  intro h
  have hw : (.w2 : World) ∈ atLeastOne := by simp [atLeastOne, atLeastOneB]
  have := h hw
  simp [atLeastTwo, atLeastTwoB] at this
theorem one_not_entails_three : ¬ entails atLeastOne atLeastThree := by
  intro h
  have hw : (.w2 : World) ∈ atLeastOne := by simp [atLeastOne, atLeastOneB]
  have := h hw
  simp [atLeastThree, atLeastThreeB] at this

/-! ### The implicature clash (§7.4, eqs. 66–79)

In UE, each alternative entails the assertion, so a monotone
likelihood ordering makes the assertion most likely — but EVEN demands
it be least likely. Under negation the entailments reverse and EVEN is
satisfiable. -/

section ImplicatureClash

/-- UE pattern: all alternatives entail the assertion — fatal for EVEN. -/
theorem ue_alt_entails_assertion :
    entails atLeastTwo atLeastOne ∧
    entails atLeastThree atLeastOne :=
  ⟨two_entails_one, three_entails_one⟩

/-- DE pattern: the assertion entails all alternatives — EVEN is
satisfiable. -/
theorem de_assertion_entails_alt :
    entails (pnot atLeastOne) (pnot atLeastTwo) ∧
    entails (pnot atLeastOne) (pnot atLeastThree) := by
  refine ⟨?_, ?_⟩
  · intro w hw hw'
    exact hw (two_entails_one hw')
  · intro w hw hw'
    exact hw (three_entails_one hw')

/-- In UE the assertion does NOT entail the alternatives. -/
theorem ue_not_reverse :
    ¬ entails atLeastOne atLeastTwo ∧
    ¬ entails atLeastOne atLeastThree :=
  ⟨one_not_entails_two, one_not_entails_three⟩

/-- In DE the alternatives do NOT entail the assertion. -/
theorem de_not_reverse :
    ¬ entails (pnot atLeastTwo) (pnot atLeastOne) ∧
    ¬ entails (pnot atLeastThree) (pnot atLeastOne) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (.w2 : World) ∈ pnot atLeastTwo := by
      simp [pnot, atLeastTwo, atLeastTwoB, Set.mem_compl_iff]
    have h2 := h h1
    simp [pnot, atLeastOne, atLeastOneB] at h2
  · intro h
    have h1 : (.w1 : World) ∈ pnot atLeastThree := by
      simp [pnot, atLeastThree, atLeastThreeB, Set.mem_compl_iff]
    have h2 := h h1
    simp [pnot, atLeastOne, atLeastOneB] at h2

end ImplicatureClash

/-! ### The clash through the EVEN presupposition -/

/-- An EVEN scalar implicature is contradicted whenever the assertion
is entailed by an alternative: the alternative is then at most as
likely, but EVEN requires the assertion to be strictly less likely. -/
theorem even_clash_abstract {W : Type*}
    (lt le : Set W → Set W → Prop)
    (hMono : LikelihoodMonotone le)
    (hCompat : ∀ a b, lt a b → le b a → False)
    {assertion alt : Set W}
    (hEntails : alt ⊆ assertion)
    (hEven : lt assertion alt) :
    False :=
  hCompat assertion alt hEven (hMono hEntails)

/-- In UE, the EVEN presupposition for *ek bhii* is contradicted
(§7.4, eqs. 68–71). -/
theorem ekBhii_even_clash_UE
    (lt le : Set World → Set World → Prop)
    (hMono : LikelihoodMonotone le)
    (hCompat : ∀ a b, lt a b → le b a → False)
    (hEven : evenPresup lt atLeastOne [atLeastTwo, atLeastThree]) :
    False :=
  even_clash_abstract lt le hMono hCompat two_entails_one
    (hEven atLeastTwo (by simp))

/-- In DE, the EVEN presupposition for *ek bhii nahiiN* is satisfiable:
the negated assertion entails each negated alternative (§7.4,
eqs. 76–79). -/
theorem ekBhii_even_ok_DE :
    entails (pnot atLeastOne) (pnot atLeastTwo) ∧
    entails (pnot atLeastOne) (pnot atLeastThree) :=
  de_assertion_entails_alt

/-! ### NPI data (§4, §6)

Licensing judgments from [lahiri-1998] §4 and §6 (stimuli in
`Data/Examples/Lahiri1998.json`), paired with this study's analysis of
each environment: *bhii* + indefinite is licensed in DE contexts and
blocked in UE contexts. The adversative rescue in (31b) is
[kadmon-landman-1993]'s "settle for less". -/

/-- A judged example paired with the licensing context of the analysis
(`none` = unlicensed environment). -/
structure HindiNPIDatum where
  ex : LinguisticExample
  context : Option LicensingContext

/-- The §4/§6 judgment data with per-environment analyses. -/
def allHindiNPIData : List HindiNPIDatum :=
  [ ⟨Examples.ex6a, none⟩, ⟨Examples.ex6b, some .negation⟩
  , ⟨Examples.ex6c, none⟩, ⟨Examples.ex6d, some .negation⟩
  , ⟨Examples.ex7a, none⟩, ⟨Examples.ex7b, some .negation⟩
  , ⟨Examples.ex8a, none⟩, ⟨Examples.ex8b, some .negation⟩
  , ⟨Examples.ex9a, none⟩, ⟨Examples.ex9b, some .negation⟩
  , ⟨Examples.ex10a, some .conditionalAntecedent⟩, ⟨Examples.ex10c, none⟩
  , ⟨Examples.ex11a, some .universalRestrictor⟩, ⟨Examples.ex12a, none⟩
  , ⟨Examples.ex29a, some .adversative⟩, ⟨Examples.ex29b, some .adversative⟩
  , ⟨Examples.ex29c, some .denyVerb⟩, ⟨Examples.ex29d, none⟩
  , ⟨Examples.ex31a, none⟩, ⟨Examples.ex31b, some .adversative⟩
  , ⟨Examples.ex32a, some .beforeClause⟩
  , ⟨Examples.ex34a, some .question⟩
  , ⟨Examples.ex41a, some .negation⟩ ]

/-- A DE-or-question licenser, derived from `LicensingContext.properties`: the
context's Strawson row supplies Zwarts strength, or it licenses by
entropy (questions license via negative bias rather than pure DE). -/
abbrev isDEOrQuestion (c : LicensingContext) : Prop :=
  (c.properties.strawsonSignature.toDEStrength).isSome ∨
    c.properties.mechanism = .byEntropy

/-- The datum's context is some DE-or-question licenser. -/
def hasDELicenser (d : HindiNPIDatum) : Prop :=
  match d.context with
  | none => False
  | some c => isDEOrQuestion c

instance : DecidablePred hasDELicenser := fun d => by
  unfold hasDELicenser
  cases d.context <;> infer_instance

/-- The analysis licenses exactly the acceptable data: a datum has a
licensing context iff the paper judges its example acceptable. -/
theorem licensed_iff_acceptable :
    ∀ d ∈ allHindiNPIData,
      (d.context.isSome ↔ d.ex.judgment = .acceptable) := by decide

/-- Every acceptable datum's licensing context is DE (or a question):
the distribution follows the implicature-clash prediction. -/
theorem grammatical_contexts_are_de :
    ∀ d ∈ allHindiNPIData,
      d.ex.judgment = .acceptable → hasDELicenser d := by decide

/-! ### Free choice in generic and modal contexts (§5)

Hindi NPIs are free-choice items in generic sentences and under
possibility modals, but not under necessity modals; the GEN
restriction is a strengthening environment, so the EVEN implicature is
satisfiable there (§7.6, eqs. 95–98). -/

/-- A judged free-choice example paired with the environment tested. -/
structure FCDatum where
  ex : LinguisticExample
  contextType : LicensingContext

/-- The §5 free-choice data. -/
def allFCData : List FCDatum :=
  [ ⟨Examples.ex35a, .generic⟩, ⟨Examples.ex35b, .generic⟩
  , ⟨Examples.ex35d, .generic⟩, ⟨Examples.ex35e, .generic⟩
  , ⟨Examples.ex36a, .modalPossibility⟩, ⟨Examples.ex36b, .modalPossibility⟩
  , ⟨Examples.ex36c, .modalPossibility⟩
  , ⟨Examples.ex36d, .modalNecessity⟩, ⟨Examples.ex36e, .modalNecessity⟩
  , ⟨Examples.ex39a, .imperative⟩, ⟨Examples.ex39b, .imperative⟩
  , ⟨Examples.ex40a, .imperative⟩, ⟨Examples.ex40b, .imperative⟩ ]

/-- Generics and possibility modals license FC readings. -/
theorem generic_and_possibility_license :
    ∀ d ∈ allFCData,
      (d.contextType = .generic ∨ d.contextType = .modalPossibility) →
        d.ex.judgment = .acceptable := by decide

/-- Necessity modals block FC readings. -/
theorem necessity_blocks :
    ∀ d ∈ allFCData, d.contextType = .modalNecessity →
      d.ex.judgment ≠ .acceptable := by decide

/-! ### The ek bhii / koii bhii contrast (§8)

The first approximation treats *koii bhii* and *ek bhii* as
equivalent, but *ek* activates cardinality alternatives (other
numerals) while *koii* activates contextually salient properties —
only the latter yield free-choice readings ((99), repeating
`Examples.ex36a`/`ex36b`), and cardinality alternatives clash with
explicit numerals ((100)). -/

open Hindi.PolarityItems (koiiBhii koiiNahiin bhiiItems)

/-- With an explicit numeral, *koii bhii* is fine and *ek bhii* is
blocked ((100a) vs (100b)). -/
theorem numeral_contrast :
    Examples.ex100a.judgment = .acceptable ∧
    Examples.ex100b.judgment ≠ .acceptable := by decide

/-- §8's contrast is lexical: the fragment's *ek bhii* activates
cardinality alternatives, *koii bhii* contextual properties. -/
theorem contrast_is_lexical :
    Hindi.PolarityItems.ekBhii.alternativeType = .cardinality ∧
    koiiBhii.alternativeType = .contextualProperty := ⟨rfl, rfl⟩

/-- The imperative asymmetry ((39) vs (40)): the cardinality-alternative
items are exactly the ones whose attested contexts exclude imperatives. -/
theorem cardinality_items_resist_imperatives :
    ∀ i ∈ bhiiItems, i.alternativeType = .cardinality →
      .imperative ∉ i.licensingContexts := by decide

/-! ### Fragment grounding

The fragment entries in `Hindi.PolarityItems` store the distribution
this study derives: DE environments for NPI readings, generic/modal
environments for FC readings, necessity modals excluded ((36d)). -/

/-- The fragment's *koii bhii* matches the analysis: a dual NPI/FC item
with indefinite + *even* morphology, licensed under negation ((6b)) and
in generics ((35a)) but not under necessity modals ((36d)). -/
theorem koiiBhii_fragment_grounded :
    koiiBhii.licensor = some .weak ∧
    koiiBhii.freeChoice = true ∧
    koiiBhii.morphology = .indefPlusEven ∧
    .negation ∈ koiiBhii.licensingContexts ∧
    .generic ∈ koiiBhii.licensingContexts ∧
    .modalNecessity ∉ koiiBhii.licensingContexts := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide

/-- The fragment's *koii nahiiN* is a strength-licensed NPI with
indefinite + negation morphology — the non-*bhii* route. -/
theorem koiiNahiin_fragment_grounded :
    koiiNahiin.licensor = some .weak ∧
    koiiNahiin.morphology = .indefPlusNeg :=
  ⟨rfl, rfl⟩

end Lahiri1998
