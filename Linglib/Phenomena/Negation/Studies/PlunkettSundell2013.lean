/-!
# Plunkett & Sundell 2013: Disagreement without incompatible contents
@cite{plunkett-sundell-2013}

Plunkett, D. & Sundell, T. (2013). Disagreement and the semantics of
normative and evaluative terms. *Philosophers' Imprint* 13(23), 1–37.

## Defining commitment

In a *metalinguistic negotiation* — a dispute that "employs competing
metalinguistic usages of an expression, and that reflects a
disagreement about the proper deployment of linguistic
representations" (P&S 2013 p.3) — the disputants A and B literally
express **mutually consistent contents**. The disagreement is genuine
but does NOT consist in expressing incompatible propositions.

Canonical case (paper p.18, attributed to Ludlow 2008):
> A: Secretariat is an athlete.
> B: No, Secretariat is not an athlete.

P&S argue that A's 'athlete' has a different extension from B's
'athlete' (broad vs. narrow athleticism), so the propositions A and B
literally express are **jointly satisfiable**: A's "Secretariat
∈ athlete₍A₎" can be true at the same world as B's "Secretariat
∉ athlete₍B₎". Plunkett & Sundell (paper p.18): "the connection
between genuine disagreement and sameness of meaning is broken."

## K-G's disagreement (paper §6, p.33-34)

K-G argues against P&S's diagnosis. On K-G's account, A and B express
literally **incompatible appropriateness contents on a SHARED standard**
(see `KirkGiannini2024.lean` §4). The disagreement is about which
appropriateness standard for 'athlete' should be operative; A asserts
"appropriate(athlete, S)" and B asserts "¬ appropriate(athlete, S)" on
the same `S`, which are contradictories.

The two analyses make incompatible claims about the SHAPE of the
metalinguistic-negotiation phenomenon. P&S → consistent contents; K-G
→ incompatible contents on a shared standard. This stub encodes P&S's
commitment so the inequality theorem can be stated in K-G's file.

## Note on scope

Stub formalisation. Encodes P&S's "consistent contents" diagnosis as a
predicate on disputes; K-G's `KirkGiannini2024.lean` will host the
refutation theorem. Does not formalize P&S's broader normative
account of metalinguistic negotiation as a category.
-/

set_option autoImplicit false

namespace PlunkettSundell2013

/-- A metalinguistic dispute between two speakers A and B over a
    target individual `t` and a predicate slot. The propositions are
    parameterised on each speaker's idiolectal extension of the
    contested term. -/
structure MetalinguisticDispute (Entity W : Type) where
  /-- Target individual (e.g., Secretariat). -/
  target : Entity
  /-- A's idiolectal extension of the contested predicate. -/
  predA : Entity → W → Prop
  /-- B's idiolectal extension of the contested predicate. -/
  predB : Entity → W → Prop

/-- A's expressed proposition: target instantiates predicate-as-A-uses-it. -/
def MetalinguisticDispute.assertionA {Entity W : Type}
    (d : MetalinguisticDispute Entity W) (w : W) : Prop :=
  d.predA d.target w

/-- B's expressed proposition (the denial): target does NOT instantiate
    predicate-as-B-uses-it. -/
def MetalinguisticDispute.assertionB {Entity W : Type}
    (d : MetalinguisticDispute Entity W) (w : W) : Prop :=
  ¬ d.predB d.target w

/-- **P&S 2013's defining commitment: in a metalinguistic negotiation,
    A's and B's literal contents are jointly satisfiable.**

    Because A and B use different extensions for the contested predicate
    (`predA ≠ predB`), there exists a world where A's assertion holds
    AND B's denial holds. Their disagreement is NOT a clash of
    incompatible propositions in the standard truth-conditional sense.
-/
def MetalinguisticDispute.consistentContents {Entity W : Type}
    (d : MetalinguisticDispute Entity W) : Prop :=
  ∃ w : W, d.assertionA w ∧ d.assertionB w

/-- **The classic Secretariat case.** When A's broader extension
    includes the target and B's narrower extension excludes it at the
    same world, P&S's `consistentContents` is witnessed. -/
theorem metalinguistic_negotiation_consistent_contents
    {Entity W : Type} (d : MetalinguisticDispute Entity W) (w : W)
    (hA : d.predA d.target w) (hB : ¬ d.predB d.target w) :
    d.consistentContents :=
  ⟨w, hA, hB⟩

/-- **Structural property of `consistentContents`: extensional
    difference is a precondition.** When `predA = predB`
    (e.g. when a competing analysis commits to a SHARED standard for
    both speakers), P&S's `consistentContents` necessarily fails. The
    proof unfolds `assertionA`/`assertionB` to expose the underlying
    `predA d.target w ∧ ¬ predB d.target w` shape, then derives a
    contradiction from the predicate identity.

    This lemma is the structural skeleton of any cross-framework
    refutation of P&S: a competing analysis that commits to
    `predA = predB` automatically produces a counterexample to
    `consistentContents`. K-G's `applyApprop`-chain analysis (which
    uses a single shared `AppropStandard`) is exactly such a competitor;
    see `KirkGiannini2024.kg_refutes_plunkett_sundell`. -/
theorem MetalinguisticDispute.consistentContents_excludes_shared_standard
    {Entity W : Type} (d : MetalinguisticDispute Entity W)
    (hShared : d.predA = d.predB) :
    ¬ d.consistentContents := by
  intro ⟨w, hA, hB⟩
  unfold MetalinguisticDispute.assertionA at hA
  unfold MetalinguisticDispute.assertionB at hB
  rw [hShared] at hA
  exact hB hA

end PlunkettSundell2013
