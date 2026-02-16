import Linglib.Theories.Syntax.Minimalism.Core.VerbalDecomposition

/-!
# Applicative Heads (Pylkkänen 2008)

Applicative heads introduce applied arguments (benefactives, goals,
sources) into the verbal structure. The high/low distinction determines
whether the applied argument relates to the event as a whole (high)
or to the theme (low).

## References

- Pylkkänen, L. (2008). *Introducing Arguments*. MIT Press.
- Cuervo, M. C. (2003). *Datives at Large*. PhD dissertation, MIT.
-/

namespace Minimalism

/-- High vs low applicatives (Pylkkänen 2008).

    - **High**: Above VP, relates applied argument to the event
      (affected/benefactive: "I baked him a cake")
    - **Low**: Below VP, relates applied argument to the theme
      (transfer/source: "I sent him a letter") -/
inductive ApplType where
  | high   -- Above VP: affected/benefactive (Pylkkänen 2008)
  | low    -- Below VP: transfer/source (Pylkkänen 2008)
  deriving DecidableEq, BEq, Repr

end Minimalism
