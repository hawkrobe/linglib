import Linglib.Semantics.Evidential.Defs

/-!
# Georgian evidentiality

Georgian has no grammatical evidentials: the perfect (the "first evidential" screeve) is used
for past events the speaker did not witness but infers from a present result or was told
about, yet this is an extension of its resultative meaning alongside present-perfect, negated
past and optative uses, so Aikhenvald treats it as an evidentiality strategy rather than
evidentiality proper. WALS codes the language as having direct and indirect evidentials.

## References

* [aikhenvald-2004], §2.1.2, §4.2
* [de-haan-2013]
-/

namespace Georgian.Evidentiality

/-- No evidentials proper; the perfect is an evidentiality strategy. -/
def evidentials : List Evidential := []

end Georgian.Evidentiality
