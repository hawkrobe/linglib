import Linglib.Syntax.Negation

/-!
# Greek negation

Standard Modern Greek has two sentential negation markers in complementary distribution by
mood: *dhen* (δεν) negates indicative clauses, and *min* (μην) negates imperatives and
subjunctive clauses, the clauses of non-veridical environments. The analysis of the two as
standard and modal negation, and of their non-negative uses, is [tsiakmakis-2025]'s and lives
in that study.

## References

* [tsiakmakis-2025]
-/

namespace Greek.StandardModern.Negation

/-- *dhen* (δεν), the negator of indicative clauses. -/
def dhen : Syntax.Negation.Marker := { pieces := [[.free "dhen"]] }

/-- *min* (μην), the negator of imperatives and subjunctive clauses. -/
def min : Syntax.Negation.Marker := { pieces := [[.free "min"]] }

end Greek.StandardModern.Negation
