/-!
# Long Distance Agree
@cite{szabolcsi-2009}

A minimal formalization of the Long Distance Agree (LDA) configuration
that @cite{szabolcsi-2009} proposes for cross-clausal feature valuation
of unvalued φ-features on a pronominal goal.

## Background

Standard syntactic Agree applies between a probe and goal in the same
phase (a clause-bounded local relation). LDA relaxes the locality
requirement: a probe in the matrix clause can value the unvalued
φ-features of a goal in the embedded clause, provided the intervening
C head is non-defective for LDA. The proposal originates in
@cite{szabolcsi-2009} and is extended to controlled subject pronouns
in @cite{satik-2019} and @cite{allotey-2021}.

## Key idea

Three conditions jointly license LDA:
1. The probe carries valued φ-features.
2. The goal carries unvalued φ-features ([D, uφ] — a minimal pronoun
   in the @cite{kratzer-2009} / @cite{landau-2015} sense).
3. The C head intervening between probe and goal is non-defective —
   it does not block the Agree relation.

This file states the configuration and its licensing condition. It
deliberately does *not* commit to a specific theory of what makes a
C head defective, what counts as the probe (v vs. T vs. Asp), or the
internal structure of the φ-feature bundle. Those are the moving parts
that distinguish particular implementations (Szabolcsi's, Satik's,
Allotey's), and they belong in study files rather than the core
mechanism.
-/

namespace Syntax.Minimalism.LongDistanceAgree

/-- The configuration parameters that determine whether a probe can
    enter into an LDA relation with a goal across a clause boundary. -/
structure LDAConfig where
  /-- The probe (matrix v/T/Asp) carries valued φ-features. -/
  probeHasValuedPhi   : Bool
  /-- The goal (embedded D head) carries unvalued φ-features. -/
  goalHasUnvaluedPhi  : Bool
  /-- The intervening C head blocks LDA (i.e., is defective for it).
      `false` means the C head is transparent and LDA proceeds. -/
  cIsDefectiveBlocker : Bool
  deriving DecidableEq, Repr

/-- LDA is licensed iff probe and goal both have the appropriate
    feature profile and the intervening C is non-blocking. -/
def LDAConfig.licenses (cfg : LDAConfig) : Bool :=
  cfg.probeHasValuedPhi && cfg.goalHasUnvaluedPhi && !cfg.cIsDefectiveBlocker

/-- A blocking C head defeats LDA regardless of probe/goal feature
    configuration. -/
theorem blocking_c_defeats_LDA (cfg : LDAConfig) (h : cfg.cIsDefectiveBlocker = true) :
    cfg.licenses = false := by
  simp [LDAConfig.licenses, h]

/-- A goal lacking unvalued φ-features has nothing to receive a value;
    LDA fails. -/
theorem valued_goal_has_no_LDA_target
    (cfg : LDAConfig) (h : cfg.goalHasUnvaluedPhi = false) :
    cfg.licenses = false := by
  simp [LDAConfig.licenses, h]

/-- A probe lacking valued φ-features has nothing to transmit;
    LDA fails. -/
theorem unvalued_probe_cannot_LDA
    (cfg : LDAConfig) (h : cfg.probeHasValuedPhi = false) :
    cfg.licenses = false := by
  simp [LDAConfig.licenses, h]

end Syntax.Minimalism.LongDistanceAgree
