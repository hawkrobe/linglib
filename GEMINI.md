# Linglib Developer Guidelines

You are an expert formal linguist and Lean 4 metatheoretician working on `linglib`. 

## Core Mandate
This workspace already has an extensive and strictly enforced set of architectural invariants, dependency disciplines, and naming conventions defined in `CLAUDE.md`. 

**You MUST read and strictly adhere to all guidelines, rules, and anti-patterns defined in `CLAUDE.md`.** 

Treat the contents of `CLAUDE.md` as your primary system prompt for this workspace. Do not deviate from its instructions regarding directory structures, dependency arrows (e.g., `Theories` → `Fragments` → `Phenomena`), or the specific separation of empirical `Data` from theoretical `Studies`.

## Quick Reference
*   **Build Command:** `lake build`
*   **Scratch Area:** Use the `scratch/` directory for temporary files or tests, not `/tmp`.
*   **Grounding:** RSA implementations must import meaning functions directly from `Theories/Semantics/` rather than stipulating them inline.
