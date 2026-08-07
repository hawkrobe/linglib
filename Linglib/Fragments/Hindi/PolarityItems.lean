import Linglib.Semantics.Polarity.Licensing

/-!
# Hindi Polarity-Sensitive Items

Hindi builds NPIs from weak indefinites plus the particle *bhii* 'even'
([lahiri-1998] (1), p. 58): *koii bhii* 'anyone', *ek bhii* 'even one',
*kuch bhii* 'anything', *zaraa bhii* 'even a little', *kabhii bhii*
'ever'. All are dual NPI/FC items — strength-licensed in DE contexts,
free-choice in generics and possibility modals but not necessity modals
([lahiri-1998] §5) — and the cardinality-alternative items (*ek bhii*,
*zaraa bhii*) resist imperatives (§5.4). *koii nahiiN* is the
indefinite + negation route. Attested contexts follow [lahiri-1998]
§4–5; cf. [haspelmath-1997] on the *koii* series.
-/

namespace Hindi.PolarityItems

open Semantics.Polarity

/-- *koii nahiiN* — negative indefinite, koii + negation:
'koii nahiiN aayaa' (nobody came). -/
def koiiNahiin : Item :=
  { form := "koii nahiiN"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , alternativeType := .contextualProperty }

/-- *koii bhii* 'anyone' — dual NPI/FCI with contextual-property
alternatives ([lahiri-1998] (6), (10)–(12), (29), (31b), (32), (34) for
the DE uses; (35), (36b), (39b) for free choice; necessity modals are
out, (36d)). -/
def koiiBhii : Item :=
  { form := "koii bhii"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .universalRestrictor, .adversative,
       .denyVerb, .beforeClause, .question, .generic, .modalPossibility,
       .imperative]
  , morphology := .indefPlusEven
  , alternativeType := .contextualProperty }

/-- *ek bhii* 'even one' — dual NPI/FCI with cardinality alternatives;
degraded in imperatives ([lahiri-1998] (7), (10d), (11a), (29a), (29f),
(34b), (35d), (36a); imperative (40b)). -/
def ekBhii : Item :=
  { form := "ek bhii"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .universalRestrictor, .adversative,
       .denyVerb, .question, .generic, .modalPossibility]
  , morphology := .indefPlusEven
  , alternativeType := .cardinality }

/-- *kuch bhii* 'anything, any (mass)' ([lahiri-1998] (8), (10f), (34c),
(35c), (39a)). -/
def kuchBhii : Item :=
  { form := "kuch bhii"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .question, .generic, .imperative]
  , morphology := .indefPlusEven
  , alternativeType := .contextualProperty }

/-- *zaraa bhii* 'even a little' — measure (cardinality) alternatives;
degraded in imperatives ([lahiri-1998] (9), (10e), §4.5, (34d), (35e);
imperative (40a)). -/
def zaraaBhii : Item :=
  { form := "zaraa bhii"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .adversative, .question, .generic]
  , morphology := .indefPlusEven
  , alternativeType := .cardinality }

/-- *kabhii bhii* 'ever, anytime' ([lahiri-1998] (36c)). -/
def kabhiiBhii : Item :=
  { form := "kabhii bhii"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility]
  , morphology := .indefPlusEven
  , alternativeType := .contextualProperty }

/-- The *bhii*-compound entries. -/
def bhiiItems : List Item := [koiiBhii, ekBhii, kuchBhii, zaraaBhii, kabhiiBhii]

/-- Every attested context of every entry is predicted licensed. -/
theorem hindi_licensing_sound :
    ∀ e ∈ koiiNahiin :: bhiiItems, ∀ c ∈ e.licensingContexts, c.licenses e := by
  decide

/-- The *bhii*-compounds are uniformly indefinite + *even* dual
NPI/FC items. -/
theorem bhii_items_uniform :
    ∀ e ∈ bhiiItems,
      e.morphology = .indefPlusEven ∧ e.licensor = some .weak ∧
        e.freeChoice = true := by decide

end Hindi.PolarityItems
