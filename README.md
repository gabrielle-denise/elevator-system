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

## Repository Structure

```
elevator-system/
├── elevator.v             # Rocq source — complete model and all proofs
├── paper/                 # Paper and related documents
│   ├── paper.typ          # Paper (Typst, single-column, Libertinus Serif)
│   ├── refs.bib           # Bibliography
│   ├── project_guidelines.pdf
│   └── topic_proposal.pdf
├── lessons/               # LF (Software Foundations) lesson files for Rocq 9.0
│   ├── _CoqProject
│   ├── Makefile
│   └── *.v
├── probset/               # Problem set files
│   ├── ps1.v              # Problem set 1 template
│   ├── ps2.v              # Problem set 2 template
│   ├── ps1_filled.v       # Problem set 1 with answers
│   ├── ps2_filled.v       # Problem set 2 with answers
│   ├── gpt/               # Generated answer files
│   │   ├── ps1_answers.v
│   │   └── ps2_answers.v
│   └── img/               # Reference images for problems
└── presentation/          # Presentation slides and supporting files
    ├── index.html
    ├── presentation.md
    ├── speaker-notes.md
    ├── deck-stage.js
    └── Elevator Rocq.html
```

## Compiling the Rocq elevator proof

```sh
coqc elevator_FINAL.v
```

Requires Rocq 9.0+ (or Coq 8.18+). The file depends only on the standard
library (`Arith.PeanoNat`, `Lia`).

## Compiling the lessons (Rocq 9.0)

The `lessons/` folder contains the LF (Logical Foundations) library needed to
run the problem sets. You need **Rocq 9.0** installed.

```sh
cd lessons
make
```

## Running the problem sets

The problem sets import from the compiled `lessons/` library. After running `make`
in `lessons/`, compile from the repo root:

```sh
# Using Rocq 9.0 coqc directly:
coqc -R lessons LF probset/ps1_filled.v
coqc -R lessons LF probset/ps2_filled.v

# Or compile the answer files:
coqc -R lessons LF probset/gpt/ps1_answers.v
coqc -R lessons LF -R probset/gpt PS probset/gpt/ps2_answers.v
```

**On WSL with Rocq Platform 9.0 installed on Windows**, use the Windows binary
with the `-coqlib` flag (since the WSL-installed Coq may be an older version):

```sh
COQC="/mnt/c/Rocq-Platform~9.0~2025.08/bin/coqc.exe"
COQLIB="C:/Rocq-Platform~9.0~2025.08/lib/coq"

$COQC -coqlib "$COQLIB" -R lessons LF probset/ps1_filled.v
$COQC -coqlib "$COQLIB" -R lessons LF probset/ps2_filled.v
```

And for `lessons/`, create a wrapper script:

```sh
cat > /tmp/rocqc.sh << 'EOF'
#!/bin/bash
"/mnt/c/Rocq-Platform~9.0~2025.08/bin/coqc.exe" -coqlib "C:/Rocq-Platform~9.0~2025.08/lib/coq" "$@"
EOF
chmod +x /tmp/rocqc.sh
cd lessons && COQC=/tmp/rocqc.sh make
```

## Compiling the paper

```sh
typst compile paper.typ
```

Requires [Typst](https://typst.app) and the Libertinus Serif font.
