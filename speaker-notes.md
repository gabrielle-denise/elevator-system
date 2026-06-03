# Speaker Notes — Formal Verification of Elevator Control System Safety Properties in Rocq

> ~1,280 words total — approximately 9 min 50 sec at 130 wpm

---

## Slide 1 — Title
*A Mechanically Verified Rocq Model of a 5-Floor Elevator Controller*

"Hi everyone, we're presenting our paper on formal verification of an elevator controller in Rocq. What makes this different from a typical software project is that every safety claim we make has been mechanically verified by a theorem prover — not just tested or argued informally."

---

## Slide 2 — Motivation & Introduction
*Why Testing Is Not Enough for Safety-Critical Systems*

"Elevators are safety-critical — they're in every building and carry people daily. Failures like moving with an open door or entering undefined states have caused real injuries worldwide. The standard response is testing and simulation, but testing only covers a finite subset of possible behaviors. Edge cases slip through. Formal verification takes a different approach: instead of running the system and looking for bugs, we construct a mathematical proof that holds for all possible inputs and all possible states. Rocq — formerly Coq — gives us a mechanical checker where every proof step is verified against the axioms of type theory. This is the same approach used to verify compilers and cryptographic protocols. We're applying it to an elevator controller."

---

## Slide 3 — System Overview
*Modeling the Controller as a Deterministic Finite State Machine*

"We model the controller as a deterministic finite state machine with five floors. The complete configuration at any moment is captured by a state record with five fields: current floor, door status, movement status, direction, and requested floor. One key design decision: we use an inductive Floor type with five constructors instead of a plain integer. This means invalid floor values are unrepresentable by construction — no bounds check needed anywhere. The controller accepts five commands: CallElevator to request a floor, OpenDoor and CloseDoor for door control, MoveElevator to start travel, and ArriveAtDestination to complete a journey."

---

## Slide 4 — Transition Function
*Defining How the Controller Responds to Every Possible Command*

"The transition function delta takes a state and a command and always returns a valid next state. The critical design choice is how it handles unsafe inputs — through stuttering. If you send MoveElevator while the door is open, the function returns the current state unchanged. Same if you try to open the door while moving. The system doesn't crash or enter a bad state — it just ignores the command. This means safety is baked into the structure of the function itself, not enforced by separate runtime checks. The MoveElevator case compares the current and requested floors. If they're equal, the elevator stays idle — no spurious motion. If the current floor is lower, it moves up. If higher, it moves down."

---

## Slide 5 — Well-Formedness Invariant
*The Three Conditions Every Valid State Must Satisfy*

"State_invariant is a predicate composed of three conjuncts every valid state must satisfy. First, floors in bounds — both floors must be in zero to four. Second, the door interlock — if the elevator is moving, the door must be closed. This directly encodes the core physical safety requirement. Third, directional consistency — the recorded direction must match the actual relative floor positions. Moving with DirUp means the requested floor is strictly above the current floor, and Moving with DirDown means strictly below. Idle always pairs with DirNone. This rules out nonsensical combinations like Moving with DirNone or Idle with DirUp. This invariant plays a dual role — it's both the safety specification and the induction hypothesis for our reachability proof."

---

## Slide 6 — Properties to Verify
*Six Safety and Correctness Properties Stated as Formal Theorems*

"We verify six properties in two categories. Safety properties with direct physical meaning: Door Safety — the elevator never moves with the door open. Movement Safety — no movement when already at the target floor. State Consistency — the invariant is preserved by every transition. Functional correctness properties about the specification itself: Determinism — same state and command always yield the same successor. Totality — the function is defined for every state-command pair. And finally Reachability — every state reachable from the initial configuration satisfies the invariant. That last one is the strongest result: it gives an unconditional global safety guarantee over all possible command sequences."

---

## Slide 7 — Assumptions & Axioms
*What the Model Guarantees and What It Deliberately Leaves Out*

"Our model makes four deliberate simplifications: single pending request — no queue; abstract motion — MoveElevator and ArriveAtDestination are atomic; command-driven — no constraints on what the environment sends; and no emergency stop. One property notably absent is liveness — the guarantee that the elevator eventually reaches any requested floor. This was intentional. Because our model is command-driven, a hostile environment could send OpenDoor forever and never send MoveElevator. Proving liveness requires explicit fairness assumptions about the command stream, which would require temporal logic or coinductive traces. We chose to stay within the current model and focus on safety, which is fully provable without fairness assumptions."

---

## Slide 8 — Main Theorems
*The Six Properties as Formally Stated Rocq Theorems*

"Here are the six theorems as formally stated in Rocq. Theorem 1: if a transition produces a moving state, that state has a closed door. Theorem 2: if current floor equals requested floor, MoveElevator produces an idle state. Theorem 3: the invariant is preserved by every transition. Theorem 4: the same state and command always yield the same successor. Theorem 5: for every state and command, a successor state exists. Theorem 6: every reachable state satisfies the invariant — from which we derive three corollaries giving global door safety, movement safety, and directional consistency."

---

## Slide 9 — Proof Sketches
*Key Lemmas and Proof Strategies for Each Property*

"Door Safety reduces to one helper lemma: any state satisfying the invariant that is Moving must have a closed door. We then apply State Consistency to get that the successor satisfies the invariant, and apply the lemma to it. Movement Safety works by case analysis. When the elevator is idle with a closed door, the transition evaluates floor_lt on equal floors. By Nat.ltb_irrefl, both comparisons return false, so the result is idle. State Consistency is the heaviest proof at around 90 lines. The key insight is three canonical shape lemmas — one for idle states, one for moving up, one for moving down. Once you have these, the main proof just destructs on the command and applies whichever shape matches. Reachability is structural induction on the reachable derivation. Base case: the initial state is idle, so inv_idle closes it immediately. Inductive step: apply State Consistency to the inductive hypothesis."

---

## Slide 10 — Results & Discussion
*All Six Properties Verified in ~660 Lines of Rocq*

"All six properties verified, around 660 lines total. State Consistency is the heaviest at 90 lines, Reachability at 50, and Determinism plus Totality together take only 16. The model has known limitations — single request, atomic motion, no emergency stop, no liveness — but all of these are deliberate. The model captures exactly the control-logic hazards that motivated the work: door interlock, no-op movement, and directional consistency. All six properties hold against this model without qualification."

---

## Slide 11 — Conclusion
*What Was Proven, What Was Not, and Where to Go Next*

"To summarize: we built a formally verified Rocq model of a 5-floor elevator controller and machine-checked six properties covering safety, correctness, and reachability. The proofs are not informal arguments — they are certificates accepted by the Rocq kernel. For future work: the most natural extension is a request queue, followed by liveness proofs using Coq's TLA library with explicit fairness assumptions. Comparing against TLA+ or NuSMV on the same spec would also be interesting. And Rocq's extraction facility could generate a certified OCaml controller directly from the verified model. Thank you — happy to take questions."
