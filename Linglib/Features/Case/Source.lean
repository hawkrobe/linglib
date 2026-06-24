import Linglib.Features.Case.Basic

/-!
# Case assignment provenance — the neutral source ontology
[marantz-1991] [kalin-2018] [woolford-2006]

`Case.Source` is the coarsened *provenance* of an assigned case — the
dimension on which the formalized assignment accounts agree that a case
"comes from" somewhere. It is **not** a theory-neutral universal: it is the
common quotient that Marantz dependent case (`Syntax/Case/Dependent.lean`'s
`CaseSource`) and Kalin hybrid licensing (`Syntax/Case/Licensing.lean`'s
`LicensingOutcome`) both map *into* (`toNeutral`), so a cross-theory
comparison can ask whether two accounts agree on *provenance*, not merely on
the surface case. Each account keeps its own finer source enum; `Source` is
where they become commensurable.

Living in `Features/` — below the assignment theories — lets both theories
project into it (and lets a future pooled comparison name it). The
structural-vs-inherent split lives here, on the *provenance*, not on the
inventory cell (`Features/Case/Basic.lean`): whether a given case, e.g.
ergative, is "structural" is a contested claim about its *source*
([woolford-2006]), which different accounts answer differently — so it is
not a property of the `Case` value.
-/

namespace Case

/-- The provenance of an assigned case, coarsened across the formalized
    accounts:

    * `structural` — valued by configuration or Agree (Marantz `dependent`,
      Chomskyan `agree`, Kalin primary/secondary licensing);
    * `inherent` — lexical/quirky, θ-associated (Marantz `lexical`, Kalin
      `byLexical`);
    * `default` — elsewhere / last-resort unmarked case;
    * `uncased` — no source valued the nominal: the crash (Kalin
      `unlicensed`, a Case-Filter violation).

    A *total* assignment account never produces `uncased`; a licensing
    account can. -/
inductive Source where
  | structural
  | inherent
  | default
  | uncased
  deriving DecidableEq, Repr, Inhabited

/-- The case was valued by configuration or Agree. The structural-vs-inherent
    distinction is a property of the *source*, not of the `Case` cell. -/
def Source.IsStructural (s : Source) : Prop := s = .structural

instance (s : Source) : Decidable s.IsStructural :=
  inferInstanceAs (Decidable (s = .structural))

/-- The derivation crashed: no source valued the nominal. Distinguishes a
    licensing account (which can fail) from a total assignment account. -/
def Source.IsCrash (s : Source) : Prop := s = .uncased

instance (s : Source) : Decidable s.IsCrash :=
  inferInstanceAs (Decidable (s = .uncased))

end Case
