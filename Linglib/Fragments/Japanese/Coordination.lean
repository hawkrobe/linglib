import Linglib.Syntax.Category.Coordinator

/-!
# Japanese coordinators

Japanese coordinates noun phrases with enclitic particles: *to* 'and', on the first conjunct,
which is also the comitative marker, so that Japanese is a with-language in Stassen's terms;
*mo* 'and', on each conjunct, which is also the additive particle 'too' and the universal
particle of the indeterminate quantifiers (*dare-mo* 'everyone'); and *ka* 'or', which is also
the question particle and the existential particle of the indeterminate quantifiers (*dare-ka*
'someone'). Mitrović and Sauerland take *to* for the J particle and *mo* for the μ particle of
their decomposition of conjunction; the indeterminate quantifiers built on *mo* and *ka* are in
`Fragments/Japanese/Determiners.lean`.

## Main definitions

* `Japanese.Coordination.to_`, `Japanese.Coordination.mo`, `Japanese.Coordination.ka` — the
  three particles

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
* [stassen-2000]
-/

namespace Japanese.Coordination

/-- *to* 'and', enclitic on the first conjunct, also the comitative 'with'. -/
def to_ : Coordinator :=
  { form := "to", gloss := "and; with", role := .j, kind := .bound .after .clitic }

/-- *mo* 'and', enclitic on each conjunct, also the additive 'too' and the universal particle
of the indeterminates. -/
def mo : Coordinator :=
  { form := "mo", gloss := "also, too; and; every", role := .mu, kind := .bound .after .clitic,
    alsoAdditive := true, alsoQuantifier := true }

/-- *ka* 'or', enclitic, also the question particle and the existential particle of the
indeterminates. -/
def ka : Coordinator :=
  { form := "ka", gloss := "or; question; some", role := .disj, kind := .bound .after .clitic,
    alsoQuantifier := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [to_, mo, ka]

end Japanese.Coordination
