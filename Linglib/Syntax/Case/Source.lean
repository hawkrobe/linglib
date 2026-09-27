module

public import Linglib.Syntax.Case.Basic

/-!
# Case assignment provenance

`Case.Source` is the coarsened provenance of an assigned case, the dimension on which the
formalized accounts of case assignment agree that a case comes from somewhere. It is not a
theory-neutral universal but the common quotient of their finer mechanisms: `Case.Mechanism` of
`Syntax/Case/Dependent.lean` projects onto it, and so does the Agree-based licensing of
[kalin-2018] through the mechanisms it is read as (`Syntax/Minimalist/Case/Licensing.lean`). Two
accounts can then be asked whether they agree on provenance, not merely on the surface case.

The structural-inherent split lives here, on the provenance, not on the inventory cell of
`Syntax/Case/Basic.lean`: whether a given case, such as the ergative, is structural is a contested
claim about its source ([woolford-2006]), which different accounts answer differently, so it is
not a property of the `Case` value.

## References

* [marantz-1991]
* [kalin-2018]
* [woolford-2006]
-/

@[expose] public section

namespace Case

/-- The provenance of an assigned case, coarsened across the formalized
    accounts:

    * `structural` — valued by configuration or Agree (Marantz `dependent`,
      Chomskyan `agree`, Kalin primary/secondary licensing);
    * `inherent` — lexical/quirky, θ-associated (Marantz `lexical`, Kalin
      `byLexical`);
    * `default` — elsewhere / last-resort unmarked case.

    Failure to assign is not a provenance and is not a cell here: an account
    that can fail reports it as `Case.Assignment.unassigned`. -/
inductive Source where
  | structural
  | inherent
  | default
  deriving DecidableEq, Repr, Inhabited

/-- The case was valued by configuration or Agree. The structural-vs-inherent
    distinction is a property of the *source*, not of the `Case` cell. -/
def Source.IsStructural (s : Source) : Prop := s = .structural

instance (s : Source) : Decidable s.IsStructural :=
  inferInstanceAs (Decidable (s = .structural))

end Case
