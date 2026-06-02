# Formal Verification of Elevator Control System Safety Properties in Rocq

CS 171 — Formal Methods  
University of the Philippines Diliman

**Authors:** Aaron Jori B. Baclor, Raphael Anton G. Felix, Gabrielle Denise S. Sacramento

---

## Overview

This project presents a mechanically verified formal model of a simplified elevator
controller, encoded as a deterministic finite state machine in Rocq (Coq). Six properties
are proven:

1. **Door Safety** — the elevator never moves while the door is open
2. **Movement Safety** — the elevator does not initiate movement when already at the target floor
3. **State Consistency** — the well-formedness invariant is preserved by every transition
4. **Determinism** — the same state and command always yield the same successor state
5. **Totality** — the transition function is defined for every valid state-command pair
6. **Reachability** — every state reachable from the initial configuration satisfies the invariant

## Files

| File | Description |
|------|-------------|
| `elevator_FINAL.v` | Rocq source — complete model and all proofs |
| `paper.typ` | Paper (Typst, single-column, Libertinus Serif) |
| `refs.bib` | Bibliography |
| `project_guidelines.pdf` | Course project guidelines |
| `topic_proposal.pdf` | Original topic proposal |

## Compiling the Rocq file

```sh
coqc elevator_FINAL.v
```

Requires Coq 8.18+ (or any recent Rocq release). The file depends only on the standard
library (`Arith.PeanoNat`, `Lia`).

## Compiling the paper

```sh
typst compile paper.typ
```

Requires [Typst](https://typst.app) and the Libertinus Serif font.
