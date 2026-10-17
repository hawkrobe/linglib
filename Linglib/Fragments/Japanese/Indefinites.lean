module

public import Linglib.Fragments.Japanese.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Japanese indefinite pronouns

Japanese builds its indefinite series on the indeterminate pronouns with a particle: *-ka*
(*dare-ka* 'someone'), *-mo* (*dare-mo* 'nobody' with clausemate negation, and without negation
the universal 'everyone') and *-demo* (*dare-demo* 'anyone'). A member of a series is its marker
applied to an interrogative of `Japanese.Pronouns`, which derives its form, category and basis;
each series is entered with its person member.

## References

* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

namespace Japanese.Indefinites

/-! ### The markers -/

/-- The *-ka* marker puts the particle *-ka* after the indeterminate. -/
def ka : InterrogativePronoun → IndefinitePronoun := IndefinitePronoun.ofInterrogative (· ++ "-ka")

/-- The *-mo* marker puts the particle *-mo* after the indeterminate. -/
def mo : InterrogativePronoun → IndefinitePronoun := IndefinitePronoun.ofInterrogative (· ++ "-mo")

/-- The *-demo* marker puts *-demo* after the indeterminate. -/
def demo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-demo")

/-! ### The person row -/

/-- *dare-ka* 'someone'. -/
def dareKa : IndefinitePronoun := ka Pronouns.dare

/-- *dare-mo* 'nobody' under clausemate negation. -/
def dareMo : IndefinitePronoun := mo Pronouns.dare

/-- *dare-demo* 'anyone'. -/
def dareDemo : IndefinitePronoun := demo Pronouns.dare

/-! ### The series -/

/-- The *-ka* series. -/
def kaSeries : IndefinitePronoun.Series := ⟨"-ka", [dareKa]⟩

/-- The *-mo* series. -/
def moSeries : IndefinitePronoun.Series := ⟨"-mo", [dareMo]⟩

/-- The *-demo* series. -/
def demoSeries : IndefinitePronoun.Series := ⟨"-demo", [dareDemo]⟩

end Japanese.Indefinites
