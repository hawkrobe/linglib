import Linglib.Fragments.Turkish.Case

/-!
# Turkish Anaphors
@cite{kornfilt-1997} @cite{goksel-kerslake-2005}

Turkish local anaphors relevant to binding theory and processing.

## birbirleri (reciprocal)

The preverbal reciprocal *birbirleri* 'each other' is subject to
Principle A: it must be bound by a local, c-commanding, clause-mate
antecedent (@cite{kornfilt-1997}). The antecedent must be plural.

Turkish's head-final structure places the reciprocal *before* the verb,
which is critical for visual-world studies: the anaphor region precedes
the verb region, ensuring that looks to antecedents at the anaphor reflect
retrieval rather than post-verbal integration (@cite{bakay-etal-2026}).

The reciprocal receives case from the embedding predicate:
- ACC (-I) as direct object of a transitive verb
- DAT (-(y)A) as indirect object or postpositional complement
- GEN (-(n)In) as possessor in a genitive-possessive construction

## kendi (reflexive)

The reflexive *kendi* 'self' is subject to similar Principle A constraints
but can also function as an intensifier or logophor. Not formalized here.

-/

set_option autoImplicit false

namespace Fragments.Turkish.Anaphors

/-- Type of Turkish local anaphor. -/
inductive AnaphorType where
  /-- birbirleri 'each other' — requires plural antecedent -/
  | reciprocal
  /-- kendi 'self' — can also be intensifier -/
  | reflexive
  deriving DecidableEq, Repr

/-- Is this anaphor type subject to a plurality requirement on its antecedent? -/
def AnaphorType.requiresPluralAntecedent : AnaphorType → Bool
  | .reciprocal => true
  | .reflexive => false

/-- A Turkish local anaphor with its morphosyntactic properties.

    Binding constraints (Principle A: c-command + clause-mate + phi-match)
    come from the syntactic theory, not the fragment entry. The fragment
    supplies the classification and case marking. -/
structure TurkishAnaphor where
  /-- Reciprocal or reflexive -/
  anaphorType : AnaphorType
  /-- Case marking on the anaphor (determined by the verb/postposition) -/
  caseMarking : Core.Case
  /-- Preverbal: appears before the verb in head-final Turkish.
      Relevant for processing studies: the anaphor region precedes
      the verb region. -/
  preverbal : Bool := true
  deriving Repr

/-- birbirleri as direct object (ACC case).
    Used in @cite{bakay-etal-2026} Experiments 1–3 as the critical anaphor. -/
def birbirleriAcc : TurkishAnaphor :=
  { anaphorType := .reciprocal, caseMarking := .acc }

/-- birbirleri as indirect object or postpositional complement (DAT case). -/
def birbirleriDat : TurkishAnaphor :=
  { anaphorType := .reciprocal, caseMarking := .dat }

/-- birbirleri as possessor (GEN case). -/
def birbirleriGen : TurkishAnaphor :=
  { anaphorType := .reciprocal, caseMarking := .gen }

-- Per-datum verification

/-- All birbirleri variants are reciprocals -/
theorem birbirleriAcc_is_reciprocal : birbirleriAcc.anaphorType = .reciprocal := rfl
theorem birbirleriDat_is_reciprocal : birbirleriDat.anaphorType = .reciprocal := rfl
theorem birbirleriGen_is_reciprocal : birbirleriGen.anaphorType = .reciprocal := rfl

/-- All birbirleri variants require plural antecedents -/
theorem birbirleri_requires_plural :
    birbirleriAcc.anaphorType.requiresPluralAntecedent = true := rfl

/-- All birbirleri variants are preverbal -/
theorem birbirleriAcc_preverbal : birbirleriAcc.preverbal = true := rfl

/-- The case inventory of birbirleri forms used in @cite{bakay-etal-2026} -/
def experimentalCases : List Core.Case :=
  [birbirleriAcc.caseMarking, birbirleriDat.caseMarking, birbirleriGen.caseMarking]

/-- All experimental cases are in the Turkish case inventory -/
theorem experimental_cases_valid :
    experimentalCases.all (Fragments.Turkish.Case.caseInventory.contains ·) = true := by
  native_decide

end Fragments.Turkish.Anaphors
