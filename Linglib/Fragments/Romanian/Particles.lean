module

public import Mathlib.Tactic.DeriveFintype

/-!
# Romanian polarity particles

Romanian has three polarity particles (`Romanian.PolarityParticle`): the positive *da*, the
negative *nu*, and *ba*, which contradicts what it responds to and does not stand alone, being
followed by *da*, *nu* or a clause: *Ana nu a plecat. — Ba da, a plecat* 'Ana didn't leave. —
You are wrong, she did' ([farkas-bruce-2010]). What each particle marks is analysed in
`FarkasBruce2010`.

## References

* [farkas-bruce-2010]
-/

@[expose] public section

namespace Romanian

/-- The Romanian polarity particles. -/
inductive PolarityParticle where
  /-- *da* 'yes': *Ana a plecat.* 'Ana left.' — *Da.* -/
  | da
  /-- *nu* 'no': *Ana nu a plecat.* 'Ana didn't leave.' — *Nu, n-a plecat.* -/
  | nu
  /-- *ba*, contradicting: *Ana a plecat.* — *Ba nu, n-a plecat.* 'No, she didn't.' -/
  | ba
  deriving DecidableEq, Repr, Fintype

/-- The spelling of a polarity particle. -/
def PolarityParticle.form : PolarityParticle → String
  | .da => "da"
  | .nu => "nu"
  | .ba => "ba"

end Romanian
