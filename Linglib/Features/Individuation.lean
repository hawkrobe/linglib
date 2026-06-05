import Mathlib.Order.Nat
import Mathlib.Tactic.DeriveFintype

/-!
# The scale of individuation
[grimm-2018] [sutton-filip-2021]

Individuation types: equivalence classes of nominal descriptions by
individuation properties, linearly ordered from entities with no
perceptible minimal units to fully independent individuals
([grimm-2018] (17)/(19)). Graduated from `Studies/Grimm2018.lean` on
gaining its second consumer: [grimm-2018] partitions the scale into
grammatical countability classes by order-preserving maps;
[sutton-filip-2021] organizes count/mass *lexicalization options* by the
same notional classes (granulars are the pivotal type: count as English
*lentil*, mass as English *rice* or Czech *čočka*). The mereotopological
content of the middle types (units clumped together vs. connected but
separable) is the `SelfConnected` apparatus of `Core/Mereotopology.lean`.
-/

set_option autoImplicit false

/-- Individuation types ([grimm-2018] (17)/(19)): the scale
    substance < granular aggregate < collective aggregate < individual. -/
inductive IndividuationType where
  /-- No perceptible minimal units (liquids, substances: *water*, *mud*). -/
  | substance
  /-- Perceptible units, typically not separated from one another
      (*rice*, *sand*, *lentils*). -/
  | granularAggregate
  /-- Perceptible units, separated but spatially or functionally connected
      (*ants*, *cherries*; functional aggregates: *furniture*). -/
  | collectiveAggregate
  /-- Independent, free-standing units (*dog*, *chair*). -/
  | individualEntity
  deriving DecidableEq, Repr, Fintype

namespace IndividuationType

/-- Numeric embedding preserving the individuation order. -/
def toNat : IndividuationType → Nat
  | .substance => 0
  | .granularAggregate => 1
  | .collectiveAggregate => 2
  | .individualEntity => 3

instance : LinearOrder IndividuationType :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

end IndividuationType
