import Linglib.Discourse.CommonGround
import Linglib.Discourse.Roles

/-!
# Discourse Commitments
@cite{krifka-2015} @cite{brandom-1994} @cite{gunlogson-2001}

Commitment slates, source × force tagging, and the speaker-indexed
`S⊢φ` constructor.
-/

namespace Discourse

namespace Commitment

/-! ### Commitment Slates -/

/-- An agent's public discourse commitments (@cite{krifka-2015},
    @cite{brandom-1994}): a list of propositions the agent has
    publicly committed to. -/
structure CommitmentSlate (W : Type*) where
  /-- The propositions the agent is publicly committed to. -/
  commitments : List (W → Prop)

namespace CommitmentSlate

variable {W : Type*}

/-- The empty commitment slate. -/
def empty : CommitmentSlate W := ⟨[]⟩

/-- Add a commitment to the slate. -/
def add (s : CommitmentSlate W) (p : W → Prop) : CommitmentSlate W :=
  ⟨p :: s.commitments⟩

/-- Worlds compatible with every committed proposition. -/
def toContextSet (s : CommitmentSlate W) : W → Prop :=
  λ w => ∀ p ∈ s.commitments, p w

/-- The slate entails `p` iff every compatible world satisfies `p`. -/
def entails (s : CommitmentSlate W) (p : W → Prop) : Prop :=
  ∀ w, (∀ q ∈ s.commitments, q w) → p w

theorem empty_trivial (w : W) : (empty : CommitmentSlate W).toContextSet w := by
  intro p hp
  exact absurd hp (List.not_mem_nil)

theorem add_restricts (s : CommitmentSlate W) (p : W → Prop) (w : W) :
    (s.add p).toContextSet w → s.toContextSet w := by
  intro h q hq
  exact h q (List.mem_cons_of_mem p hq)

theorem add_entails (s : CommitmentSlate W) (p : W → Prop) (w : W) :
    (s.add p).toContextSet w → p w := by
  intro h
  exact h p List.mem_cons_self

end CommitmentSlate

/-! ### Source-Marked Commitments -/

/-- The source of a discourse commitment: self-generated commitments
    can be challenged by the addressee; other-generated commitments
    can be challenged by the speaker. -/
inductive CommitmentSource where
  | selfGenerated
  | otherGenerated
  deriving DecidableEq, Repr, Inhabited

/-- The modal force of a commitment: doxastic (act-as-if-believe) or
    preferential (act-as-if-effectively-prefer, @cite{condoravdi-lauer-2012},
    @cite{lauer-2013}). -/
inductive CommitmentForce where
  | doxastic
  | preferential
  deriving DecidableEq, Repr, Inhabited

/-- A commitment tagged with epistemic source and modal force.
    `source × force` is @cite{deo-2025-bara}'s 2×2 cross. -/
structure TaggedCommitment (W : Type*) where
  content : W → Prop
  source : CommitmentSource
  commitmentForce : CommitmentForce := .doxastic

/-- A source-tagged commitment slate. -/
structure TaggedSlate (W : Type*) where
  commitments : List (TaggedCommitment W)

namespace TaggedSlate

variable {W : Type*}

/-- The empty tagged slate. -/
def empty : TaggedSlate W := ⟨[]⟩

/-- Add a tagged commitment. -/
def add (s : TaggedSlate W) (p : W → Prop) (src : CommitmentSource)
    (force : CommitmentForce := .doxastic) : TaggedSlate W :=
  ⟨⟨p, src, force⟩ :: s.commitments⟩

/-- Self-generated commitments (any force). -/
def selfGenerated (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.source == .selfGenerated) |>.map (·.content)

/-- Other-generated commitments (any force). -/
def otherGenerated (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.source == .otherGenerated) |>.map (·.content)

/-- Doxastic commitments (any source). -/
def doxasticContents (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.commitmentForce == .doxastic) |>.map (·.content)

/-- Preferential commitments (any source). The input to a joint-preferences
    set when intersected across agents (@cite{deo-2025-bara}). -/
def preferentialContents (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.commitmentForce == .preferential) |>.map (·.content)

/-- Convert to a plain (untagged) commitment slate. -/
def toSlate (s : TaggedSlate W) : CommitmentSlate W :=
  ⟨s.commitments.map (·.content)⟩

/-- Convert to context set (ignoring source tags). -/
def toContextSet (s : TaggedSlate W) : W → Prop :=
  s.toSlate.toContextSet

end TaggedSlate

/-! ### Grade typeclasses -/

/-- The support predicate of a commitment grade `G`: which grades count
    as "actively committing". For `Prop`: identity. For `Bool`:
    `· = true`. For `ℝ_≥0`: `· > 0`. -/
class HasSupport (G : Type*) where
  support : G → Prop

/-- A commitment grade with a complement operation. Used to construct
    the "no" branch of bipolar questions. -/
class CommitmentGrade (G : Type*) extends HasSupport G where
  complement : G → G

instance : HasSupport Prop where
  support := id

instance : CommitmentGrade Prop where
  complement := Not

-- No `Bool` instance by default — consumers needing decidable grades
-- declare locally. Anderson 2021's distributional CommonGround provides
-- `HasSupport ℝ` at its own site.

/-! ### Speaker-Indexed Commitments -/

/-! `IndexedWeightedCommitment W G` is the polymorphic
commitment type. Three axes:

* `committer : DiscourseRole` — who is committing.
* `force : CommitmentForce` — doxastic vs preferential.
* `weight : W → G` (commit) or `content : W → Prop` (refuse).

The `G = Prop` specialisation is `IndexedCommitment W`.
-/

/-- A polymorphic indexed commitment. -/
inductive IndexedWeightedCommitment (W : Type*) (G : Type*) where
  /-- `S⊢φ` with per-world grade in G. -/
  | commit (committer : DiscourseRole) (force : CommitmentForce)
           (weight : W → G)
  /-- `¬S⊢φ`: agent explicitly NOT committed to `φ`. -/
  | refuse (committer : DiscourseRole) (force : CommitmentForce)
           (content : W → Prop)

namespace IndexedWeightedCommitment

variable {W G : Type*}

/-- The committing agent. -/
def committer : IndexedWeightedCommitment W G → DiscourseRole
  | .commit c _ _ => c
  | .refuse c _ _ => c

/-- The commitment force. -/
def force : IndexedWeightedCommitment W G → CommitmentForce
  | .commit _ f _ => f
  | .refuse _ f _ => f

/-- True for `commit`, false for `refuse`. -/
def IsCommit : IndexedWeightedCommitment W G → Prop
  | .commit _ _ _ => True
  | .refuse _ _ _ => False

instance : DecidablePred (@IsCommit W G) := fun ic => by
  cases ic <;> (unfold IsCommit; infer_instance)

/-- Project to the context-set constraint: a `commit` excludes
    worlds where `support (weight w)` fails; a `refuse` imposes no
    exclusion. -/
def toCommitment [HasSupport G] :
    IndexedWeightedCommitment W G → (W → Prop)
  | .commit _ _ weight => fun w => HasSupport.support (weight w)
  | .refuse _ _ _ => fun _ => True

@[simp]
theorem toCommitment_commit [HasSupport G]
    (c : DiscourseRole) (f : CommitmentForce) (weight : W → G) (w : W) :
    (IndexedWeightedCommitment.commit c f weight).toCommitment w =
      HasSupport.support (weight w) := rfl

@[simp]
theorem toCommitment_refuse [HasSupport G]
    (c : DiscourseRole) (f : CommitmentForce) (φ : W → Prop) (w : W) :
    (IndexedWeightedCommitment.refuse (G := G) c f φ).toCommitment w = True := rfl

end IndexedWeightedCommitment

/-- Binary speaker-indexed commitment (Krifka 2015 default). -/
abbrev IndexedCommitment (W : Type*) := IndexedWeightedCommitment W Prop

namespace IndexedCommitment

variable {W : Type*}

/-- Smart constructor for the doxastic binary commit case. -/
abbrev commit (committer : DiscourseRole) (content : W → Prop) :
    IndexedCommitment W :=
  IndexedWeightedCommitment.commit committer .doxastic content

/-- Smart constructor for the doxastic binary refuse case. -/
abbrev refuse (committer : DiscourseRole) (content : W → Prop) :
    IndexedCommitment W :=
  IndexedWeightedCommitment.refuse committer .doxastic content

/-- Propositional content of the commitment. -/
def content : IndexedCommitment W → (W → Prop)
  | IndexedWeightedCommitment.commit _ _ φ => φ
  | IndexedWeightedCommitment.refuse _ _ φ => φ

/-- Project to the context-set constraint. `commit` projects to its
    content; `refuse` projects to `True`. -/
def toCommitment : IndexedCommitment W → (W → Prop)
  | IndexedWeightedCommitment.commit _ _ φ => φ
  | IndexedWeightedCommitment.refuse _ _ _ => fun _ => True

end IndexedCommitment

end Commitment

/-! ### HasContextSet Instance -/

open CommonGround in
/-- A commitment slate projects to a context set. -/
instance {W : Type*} : HasContextSet (Commitment.CommitmentSlate W) W where
  toContextSet s := λ w => s.toContextSet w

end Discourse
