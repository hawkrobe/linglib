/-!
# Core Types for Genericity

Shared vocabulary for the study of generic sentences, used across
`Phenomena/Generics/` data files and `Theories/` study files.

The two types here capture the organizing axes of the field as surveyed
in the introduction to *Genericity* (Mari, Beyssade, Del Prete, OUP 2013):

1. **GenericForm**: what DP form expresses the generic meaning?
   The introduction spends 30 pages on this distinction (§1.1, §1.3.1).
2. **GenericReading**: what kind of generalization is being expressed?
   @cite{krifka-2013}'s descriptive/definitional split (ch. 15).
-/

namespace Features.Genericity

/-- The principal linguistic forms that express generic meaning.

    This four-way distinction is the organizing axis of the field:
    cross-linguistic patterns, scope behavior, and theoretical status
    all depend on which form is used.

    | Form | Example | Carlson | Chierchia | Krifka 2004 |
    |------|---------|---------|----------|-------------|
    | IS   | "A madrigal is polyphonic" | — | GEN quantifier | GEN over properties |
    | BP   | "Dogs bark"               | Name of kind | ∩(property) | Property + type shift |
    | DS   | "The lion is a predator"   | — | ι over kind  | ι over property |
    | DP   | "Les chiens aboient" (Fr.) | — | ∩(property) | — |
-/
inductive GenericForm where
  /-- Indefinite singular: "A madrigal is polyphonic."
      Tends toward definitional readings (@cite{krifka-2013}).
      Expresses rules (Cohen 2001a). Cannot be used for
      direct kind predication (*"A dinosaur is extinct"). -/
  | indefiniteSingular
  /-- Bare plural: "Dogs bark" / "Madrigals are popular."
      Both descriptive and definitional readings available.
      Kind-denoting on Carlson/Chierchia; property-denoting on Krifka 2004.
      Scopeless (@cite{carlson-1977}). -/
  | barePlural
  /-- Definite singular: "The lion is a predator."
      Limited to well-established kinds (@cite{krifka-etal-1995}).
      Blocked by modification (*"The tall lion is a predator"). -/
  | definiteSingular
  /-- Definite plural: "Les chiens aboient" (Fr.), "I cani abbaiano" (It.)
      Romance-language kind reference via the plural definite article.
      Patterns partly with BPs, partly with DSs.
      @cite{dayal-2004} analyzes as ι applied to the plural kind. -/
  | definitePlural
  deriving DecidableEq, Repr

/-- Type of generic reading (@cite{krifka-2013}, ch. 15).

    The descriptive/definitional distinction is orthogonal to `GenericForm`:
    BPs can express both, while ISs strongly prefer definitional.

    Formally, descriptive generics restrict the set of possible *worlds*
    (DES update), while definitional generics restrict the set of admissible
    *interpretations* (DEF update). See `Phenomena/Generics/Studies/Krifka2013.lean`
    for the two-index formalization. -/
inductive GenericReading where
  /-- Descriptive: empirical generalization about the world.
      "Dogs bark" — in normal worlds where there are dogs, they bark.
      Amenable to threshold/RSA treatment (@cite{tessler-goodman-2019}). -/
  | descriptive
  /-- Definitional: restricts admissible interpretations.
      "A madrigal is polyphonic" — only interpretations where madrigals
      are polyphonic count as admissible.
      NOT reducible to prevalence thresholds. -/
  | definitional
  deriving DecidableEq, Repr

end Features.Genericity
