module

public import Linglib.Fragments.Japanese.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Japanese indefinite pronouns

Japanese builds its indefinite series on the indeterminate pronouns with a particle: *-ka*
(*dare-ka* 'someone'), *-mo* (*dare-mo* 'nobody' with clausemate negation, and without negation
the universal 'everyone') and *-demo* (*dare-demo* 'anyone'). A member of a series is the series
applied to an interrogative of `Japanese.Pronouns`, which derives its form, category and basis;
the person row is entered.

## References

* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

namespace Japanese.Indefinites

/-! ### The series -/

/-- The *ka*-series: the particle *-ka* after the indeterminate. -/
def ka : InterrogativePronoun → IndefinitePronoun := IndefinitePronoun.ofInterrogative (· ++ "-ka")

/-- The *mo*-series: the particle *-mo* after the indeterminate. -/
def mo : InterrogativePronoun → IndefinitePronoun := IndefinitePronoun.ofInterrogative (· ++ "-mo")

/-- The *demo*-series: *-demo* after the indeterminate. -/
def demo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-demo")

/-! ### The person row -/

/-- *dare-ka* 'someone'. -/
def dareKa : IndefinitePronoun := ka Pronouns.dare

/-- *dare-mo* 'nobody' under clausemate negation. -/
def dareMo : IndefinitePronoun := mo Pronouns.dare

/-- *dare-demo* 'anyone'. -/
def dareDemo : IndefinitePronoun := demo Pronouns.dare

end Japanese.Indefinites
