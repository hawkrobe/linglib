import Linglib.Morphology.Paradigm.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Subsingleton

/-!
# Morphomes: syncretism classes with no natural characterization
[herce-2023] [aronoff-1994]

A realization map `p : Cell → F` assigns a form to each paradigm cell. Its
**syncretism** relation — cells receiving the same form — is exactly
mathlib's kernel setoid `Setoid.ker p`, and the syncretism classes are its
equivalence classes. A **morphome** ([aronoff-1994] coined the term) is a
systematic syncretism that does not define a natural class; [herce-2023]
adopts the working definition "a systematic morphological syncretism which
does not define a (syntactically or semantically) natural class" (Trommer
2016, quoted approvingly).

Naturalness is a **parameter** `Natural : Set Cell → Prop`, not stipulated
here. [herce-2023] operationalizes a natural class as one "coextensive with
a value (e.g. SG) or conjunction of values (e.g. 1SG)" and treats
naturalness as *gradient*, so `Natural` is best read as a threshold slice of
that scale; the value-or-conjunction predicate is its canonical
instantiation, supplied by the consumer (see `Studies/Herce2023.lean`).
Systematicity — recurrence of the pattern under more than one exponent or
allomorph — is a separate criterion the consumer establishes.

The vocabulary here is deliberately just "morphome": [herce-2023] rejects
Round's rhizomorphome ~ metamorphome ~ meromorphome subdivision as needless
jargon, and "metasyncretism" does not appear in the book.

## Main declarations

* `Morphology.syncretism` — the syncretism setoid of a realization map
  (`Setoid.ker`)
* `Morphology.syncretismClass` — the class (fiber) of a given cell
* `Morphology.IsMorphome` — a nontrivial syncretism class failing `Natural`
-/

namespace Morphology

variable {Cell F : Type*}

/-- The **syncretism** relation of a realization map `p`: two cells are
syncretic iff `p` assigns them the same form. Exactly the kernel setoid
`Setoid.ker p`; its equivalence classes are the paradigm's syncretism
patterns. -/
abbrev syncretism (p : Cell → F) : Setoid Cell := Setoid.ker p

/-- The syncretism class of a cell `a`: every cell realized as `a` is. -/
def syncretismClass (p : Cell → F) (a : Cell) : Set Cell := {x | p x = p a}

theorem syncretismClass_mem_classes (p : Cell → F) (a : Cell) :
    syncretismClass p a ∈ (syncretism p).classes :=
  Setoid.mem_classes (syncretism p) a

/-- A **morphome** ([herce-2023]): a syncretism class of `p` that groups
more than one cell (`Set.Nontrivial`) yet is not a `Natural` class — a
grouping visible only in the realization, with no phonological, syntactic,
or semantic characterization ([aronoff-1994]'s "morphology by itself").
`Natural` is a parameter (see the module docstring). -/
def IsMorphome (p : Cell → F) (Natural : Set Cell → Prop) (c : Set Cell) : Prop :=
  c ∈ (syncretism p).classes ∧ c.Nontrivial ∧ ¬ Natural c

/-- The syncretism class of `a` is a morphome once it is nontrivial and
unnatural — the shape a concrete paradigm instantiates. -/
theorem isMorphome_syncretismClass (p : Cell → F) (Natural : Set Cell → Prop)
    (a : Cell) (hnt : (syncretismClass p a).Nontrivial)
    (hnat : ¬ Natural (syncretismClass p a)) :
    IsMorphome p Natural (syncretismClass p a) :=
  ⟨syncretismClass_mem_classes p a, hnt, hnat⟩

end Morphology
