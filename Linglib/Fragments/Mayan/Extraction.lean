module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Mayan extraction morphology

In most Mayan languages the focusing, questioning or relativization of a transitive subject
changes the verb: it takes the Agent Focus form, which lacks the Set A marker and carries a
suffix of its own, so that a clause with two arguments is inflected like an intransitive
([stiebels-2006], [polian-2017]). The form is obligatory in the languages with the ergative
extraction constraint, optional in Tsotsil, and absent in Chol and Tseltal. Several languages
also mark the extraction of non-core arguments and adjuncts, K'iche' and Kaqchikel with the
particle *wi* and Mam with the enclitic =(y)a', and which classes of adjunct license the marker
varies. The sites an extraction morphology distinguishes are the core arguments by their role
and the adjuncts by their class; each language's `Extraction.realize` records the reflexes an
extraction from each site licenses.

## Main declarations

* `Mayan.VerbForm`: the transitive and Agent Focus forms, with `Mayan.VerbForm.HasSetA`.
* `Mayan.Adjunct`, `Mayan.ExtractionSite`: the adjunct classes and the extraction sites the
  marking distinguishes.

## References

* [polian-2017]
* [stiebels-2006]
-/

@[expose] public section

namespace Mayan

/-- The two forms of a transitive verb: the canonical transitive and the Agent Focus form
that transitive-subject extraction selects wherever a language has it. -/
inductive VerbForm where
  | transitive
  | agentFocus
  deriving DecidableEq, Repr, Fintype

/-- The form bears Set A: the canonical transitive does, while the Agent Focus form is
inflected as an intransitive and bears only Set B ([polian-2017]). -/
def VerbForm.HasSetA (f : VerbForm) : Prop := f = .transitive

instance : DecidablePred VerbForm.HasSetA := fun f ↦ inferInstanceAs (Decidable (f = _))

/-- The classes of non-core argument and adjunct that Mayan extraction morphology
distinguishes. Comitatives, which the K'ichean particle also tracks, are not carried. -/
inductive Adjunct where
  | instrument | benefactive | dative | locative | reason | purpose | manner | temporal
  deriving DecidableEq, Repr, Fintype

/-- The site of an extraction at the granularity the marking distinguishes: a core argument by
its role, or an adjunct by its class. A fragment whose sources document core-argument
extraction only indexes `realize` by `ArgumentRole`. -/
inductive ExtractionSite where
  | core (r : ArgumentRole)
  | adjunct (a : Adjunct)
  deriving DecidableEq, Repr, Fintype

end Mayan
