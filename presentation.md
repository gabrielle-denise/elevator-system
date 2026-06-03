# Formal Verification of Elevator Control System Safety Properties in Rocq

**Aaron Jori B. Baclor · Raphael Anton G. Felix · Gabrielle Denise S. Sacramento**
Department of Computer Science, University of the Philippines Diliman

---

## Slide 1 — Title

**Formal Verification of Elevator Control System Safety Properties in Rocq**

- Aaron Jori B. Baclor · Raphael Anton G. Felix · Gabrielle Denise S. Sacramento
- Department of Computer Science, University of the Philippines Diliman
- Mechanically verified formal model — every proof step checked by machine

**Speaker note:** Introduce the team. Emphasize this is not just a design — it is a proof accepted by the Rocq kernel.

---

## Slide 2 — Motivation & Introduction

**Elevators are safety-critical infrastructure**

- Deployed in virtually every modern building
- Failure modes with real consequences:
  - Elevator moves while door is open → entrapment or injury
  - Movement initiated when already at destination → spurious motion
  - Undefined states from incomplete logic → unpredictable behavior

**Conventional validation falls short**

- Functional testing and simulation only explore a *finite subset* of behaviors
- Cannot rule out edge cases by construction

**Formal verification offers a principled alternative**

- Constructs a mathematical proof valid for *all* possible inputs and states
- Rocq/Coq mechanically checks every proof step against the axioms of type theory
- Prior work: SPIN, TLA+, B-Method — model checking is bounded; theorem proving is not

**Speaker note:** Testing finds bugs; proof rules out whole classes of bugs. Mention real-world fatalities from elevator failures to motivate the stakes.

---

## Slide 3 — System Overview

**Model: Deterministic Finite State Machine (DFSM)**

- 5 floors: F0, F1, F2, F3, F4
- A **state** captures the complete controller configuration at one instant
- A **transition function** δ : State × Command → State

**State Record** (f_cur, d, m, dir, f_req):

| Field | Type | Meaning |
|---|---|---|
| `current_floor` | Floor | Current position |
| `door_status` | DoorOpen \| DoorClosed | Door state |
| `movement_status` | Moving \| Idle | Motion state |
| `direction` | DirUp \| DirDown \| DirNone | Travel direction |
| `requested_floor` | Floor | Pending target |

**Five Commands:**
- `CallElevator f` — request floor f
- `OpenDoor` / `CloseDoor` — control door when stationary
- `MoveElevator` — initiate travel toward requested floor if safe
- `ArriveAtDestination` — complete an in-progress journey atomically

**Speaker note:** Using an inductive Floor type (not a raw integer) prevents out-of-range floor values *by construction* — no runtime bounds check needed. This is a key benefit of encoding the model in a type theory.

---

## Slide 4 — Formal Model: Transition Function

**δ(s, MoveElevator) — the most important case:**

```
δ(s, MoveElevator) =
  s                                           if m(s) = Moving
  s                                           if d(s) = DoorOpen
  (f_cur, Closed, Moving, Up,   f_req)        if f_cur < f_req
  (f_cur, Closed, Moving, Down, f_req)        if f_req < f_cur
  (f_cur, Closed, Idle,   None, f_req)        if f_cur = f_req
```

**δ(s, ArriveAtDestination):**

```
δ(s, ArriveAtDestination) =
  (f_req, Closed, Idle, None, f_req)          if m(s) = Moving
  s                                           if m(s) = Idle
```

**Key design choice: unsafe commands *stutter* (return s unchanged)**

- `MoveElevator` while door open → no-op
- `OpenDoor` / `CloseDoor` while moving → no-op
- `CallElevator` while moving → no-op
- Safety enforced *structurally*, not by runtime assertions

**Speaker note:** Stuttering is the critical design decision. It makes the transition function *total* (no undefined behavior) and means unsafe operations are silently rejected. This is what makes Totality and Safety provable.

---

## Slide 5 — Well-Formedness Invariant

**state_invariant(s) ≡ three conjuncts that must all hold:**

**(1) Floors in bounds:**
```
f_cur(s) ∈ [0, 4]  ∧  f_req(s) ∈ [0, 4]
```

**(2) Door interlock (core safety requirement):**
```
m(s) = Moving  ⟹  d(s) = DoorClosed
```

**(3) Directional consistency:**
```
m(s) = Idle   ∧ dir(s) = None                       OR
m(s) = Moving ∧ dir(s) = Up   ∧ f_cur < f_req       OR
m(s) = Moving ∧ dir(s) = Down ∧ f_req < f_cur
```

**Rules out impossible combinations such as:**
- Moving + DirNone
- Moving + DoorOpen
- Idle + DirUp or DirDown

**Speaker note:** Conjunct (1) is technically redundant given the inductive Floor type but is stated for explicitness. Conjunct (2) directly encodes the physical door-interlock requirement. Conjunct (3) ensures direction is a *consequence* of floor positions, not just an arbitrary flag.

---

## Slide 6 — Properties to Verify

**Six properties across two categories:**

### Safety Properties — physical correctness

| # | Property | Informal Meaning |
|---|---|---|
| 1 | **Door Safety** | The elevator never moves while the door is open |
| 2 | **Movement Safety** | No movement is initiated when already at the target floor |
| 3 | **State Consistency** | The well-formedness invariant is preserved by every transition |

### Functional Properties — specification correctness

| # | Property | Informal Meaning |
|---|---|---|
| 4 | **Determinism** | The same state and command always yield the same successor |
| 5 | **Totality** | The transition function is defined for every state-command pair |
| 6 | **Reachability** | Every state reachable from the initial state satisfies the invariant |

**Speaker note:** Properties 1–3 have direct physical interpretations. Properties 4–5 establish that the *specification itself* is well-formed — a nondeterministic or partial spec would undermine all other proofs. Property 6 is the strongest: it gives an unconditional global safety guarantee over all possible executions.

---

## Slide 7 — Assumptions & Axioms

**Model-level assumptions (explicitly stated, not proven):**

- **Single pending request** — state holds exactly one target floor; no queue
- **Abstract motion** — `MoveElevator` and `ArriveAtDestination` are atomic; no intermediate floor positions
- **Command-driven scheduler** — no assumption about which commands arrive or in what order
- **No emergency stop** — override commands are not modeled

**Axioms used from the Rocq standard library:**

- `Nat.ltb_irrefl` — ¬(n <_ℕ n) — used to prove floor_lt(f, f) = false
- `Nat.ltb_lt` — floor_lt(f, g) = true ⟺ f < g — used in state consistency
- `lia` (linear integer arithmetic) — closes arithmetic goals automatically

**What is NOT proven — by principled design:**

- *Liveness*: "the elevator eventually reaches any requested floor"
- Requires *fairness assumptions* on the command stream
- A hostile environment could send `OpenDoor` forever and never send `MoveElevator`
- Proving liveness would require temporal logic (Coq's TLA library) or coinductive traces

**Speaker note:** The no-liveness decision is not a gap — it is a deliberate scope choice. The reachability invariant fulfills the primary goal of *safety* verification: the elevator can never enter an unsafe state regardless of what commands arrive.

---

## Slide 8 — Main Theorems

**Theorem 1 — Door Safety:**
```
∀ s, c.  inv(s)  ∧  δ(s, c).status = Moving
         ⟹  δ(s, c).door = DoorClosed
```

**Theorem 2 — Movement Safety:**
```
∀ s.  inv(s)  ∧  f_cur(s) = f_req(s)
      ⟹  δ(s, MoveElevator).status ≠ Moving
```

**Theorem 3 — State Consistency (Inductive Invariant):**
```
∀ s, c.  inv(s)  ⟹  inv(δ(s, c))
```

**Theorem 4 — Determinism:**
```
∀ s, c, s1, s2.  (s —c→ s1)  ∧  (s —c→ s2)  ⟹  s1 = s2
```

**Theorem 5 — Totality:**
```
∀ s, c.  ∃ s'.  s —c→ s'
```

**Theorem 6 — Reachability Invariant:**
```
∀ s.  reachable(s)  ⟹  inv(s)
```

**Corollaries of Theorem 6:**
```
∀ s.  reachable(s)  ∧  m(s) = Moving  ⟹  d(s) = DoorClosed
∀ s.  reachable(s)  ∧  m(s) = Moving  ⟹  f_cur(s) ≠ f_req(s)
```

**Speaker note:** These are the actual Rocq theorem statements translated to standard notation. Every one was accepted by the Rocq kernel — not argued informally, but machine-checked.

---

## Slide 9 — Proof Sketches

### Door Safety (~25 lines)
1. Prove helper lemma: `inv(s) ∧ m(s) = Moving ⟹ d(s) = Closed`
   - Unfold `movement_has_closed_door`; case split on Moving / Idle
2. Apply Theorem 3 (preservation) to get `inv(δ(s, c))`
3. Apply helper lemma to the successor state

### Movement Safety (~35 lines)
- Case split on `movement_status` and `door_status`
- If already Moving: transition stutters; invariant gives a strict floor inequality, contradicting `f_cur = f_req` via `lia`
- If Idle + DoorClosed: `floor_lt(f, f) = false` by `Nat.ltb_irrefl` → transition constructs Idle state directly

### State Consistency (~90 lines) — three canonical shape lemmas:
```
inv_idle:    ∀ f, d, r.  inv(f, d, Idle, None, r)
inv_up:      f < r  ⟹  inv(f, Closed, Moving, Up,   r)
inv_down:    r < f  ⟹  inv(f, Closed, Moving, Down, r)
```
- Destruct on command; each branch applies exactly one of the three shape lemmas

### Reachability (~50 lines) — structural induction on `reachable`:
- **Base case:** `initial_state = (F0, Closed, Idle, None, F0)` → `inv_idle` applies trivially
- **Inductive step:** IH gives `inv(s)`; Theorem 3 gives `inv(δ(s, c))`

**Speaker note:** The State Consistency proof is the heart of the development. The three shape lemmas are the key insight — instead of reasoning about arbitrary states, you only ever need to show that one of three canonical forms is produced by each transition branch.

---

## Slide 10 — Results & Discussion

**All 6 properties verified in Rocq — ~660 lines total**

| Property | Primary Technique | Lines |
|---|---|---|
| Door Safety | Invariant lemma + `eapply` | ~25 |
| Movement Safety | Case split + `Nat.ltb_irrefl` + `lia` | ~35 |
| State Consistency | Helper shape lemmas + `destruct cmd` | ~90 |
| Determinism | `inversion` + `reflexivity` | ~10 |
| Totality | Existential witness + `constructor` | ~6 |
| Reachability | Structural induction on `reachable` | ~50 |

**Key design insights:**

- Inductive `Floor` type makes invalid floor values *unrepresentable* — no bounds checking needed
- Stuttering transitions make δ *total* and safety *structural*
- `state_invariant` serves as both the safety specification and the induction hypothesis

**Scope limitations (deliberate):**

- No request queue, no continuous motion, no emergency stop
- No liveness — principled design choice, not an oversight

**Speaker note:** Determinism and totality are only ~16 lines combined. They feel trivial but their *formal statement* matters — they rule out accidentally partial or nondeterministic specifications that would invalidate all other proofs.

---

## Slide 11 — Conclusion

**What we built:**

- A formal Rocq model of a 5-floor elevator DFSM
- Machine-checked proofs of 6 safety and correctness properties
- Covers the essential control-logic hazards: door interlock, no-op movement, directional consistency

**What this demonstrates:**

- Interactive theorem proving is *practical* for safety-critical embedded controllers
- Proofs are unconditional — not bounded by state space size unlike model checking
- The verified Rocq artifact can be extracted to certified OCaml executable code

**Future directions:**

1. Extend state to a floor-request *queue* with a scheduling policy
2. Add liveness proofs via Coq's TLA library with explicit fairness assumptions
3. Compare with model checking (TLA+, NuSMV) on the same benchmark
4. Extract a certified OCaml controller via Rocq's `Extraction` mechanism

**Speaker note:** Return to the opening: testing finds some bugs; this proof rules out whole *classes* of elevator hazards for *all* inputs and all time — in approximately 660 lines of Rocq. That is the value proposition of interactive theorem proving for safety-critical systems.

---

## Appendix — Rocq Development Checklist

### Definitions
- `Floor`, `DoorStatus`, `MovementStatus`, `Direction`, `State`, `Command`
- `floor_to_nat`, `floor_lt`, `max_floor`
- `transition : State → Command → State`
- `state_invariant`, `floors_in_bounds`, `movement_has_closed_door`, `direction_matches_movement`
- `initial_state`, `reachable : State → Prop`

### Key Lemmas (in dependency order)
- `floor_within_bounds` — floors stay in [0, 4]
- `invariant_idle`, `invariant_moving_up`, `invariant_moving_down` — canonical shape lemmas
- `invariant_moving_closed` — bridge lemma for door safety
- `initial_state_invariant` — base case for reachability

### Theorems (in dependency order)
1. `transition_preserves_invariant` — depends on shape lemmas
2. `door_safety` — depends on (1) + `invariant_moving_closed`
3. `movement_safety` / `move_at_destination_stays_idle` — depends on `Nat.ltb_irrefl`
4. `determinism`, `totality`, `unique_successor` — trivial from `Step` definition
5. `reachable_states_satisfy_invariant` — structural induction; depends on (1) + `initial_state_invariant`
6. `reachable_door_safety`, `reachable_movement_safety`, `reachable_direction_consistency` — corollaries of (5)

---

## Timing Guide

| Section | Slides | Time |
|---|---|---|
| Title + Motivation | 1–2 | ~1.5 min |
| System Overview + Transition | 3–4 | ~2 min |
| Invariant + Properties | 5–6 | ~2 min |
| Assumptions | 7 | ~0.5 min |
| Theorems + Proof Sketches | 8–9 | ~2.5 min |
| Results + Conclusion | 10–11 | ~1.5 min |
