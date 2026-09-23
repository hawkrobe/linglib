module

public import Linglib.Semantics.Tense.Connective

/-!
# Japanese temporal connectives

Lexical entries for the Japanese temporal connectives *mae* 'before' and *ato* 'after'. A
*mae*-clause takes the non-past tense even under a past matrix and an *ato*-clause the past,
the asymmetry that [arregui-kusumoto-1998] and [ogihara-steinert-threlkeld-2024] analyse.

## References

* [ogihara-1996]
* [arregui-kusumoto-1998]
* [ogihara-steinert-threlkeld-2024]
-/

@[expose] public section

namespace Japanese.TemporalConnectives

open Tense

/-- *mae* (前) 'before', with a non-past complement. -/
def mae : Connective := { form := "前", relation := .before }

/-- *ato* (後) 'after', with a past complement. -/
def ato : Connective := { form := "後", relation := .after }

end Japanese.TemporalConnectives
