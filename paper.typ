#import "@preview/charged-ieee:0.1.3": ieee

#show: ieee.with(
  title: [Formal Verification of Elevator Control System Safety Properties in Rocq],
  abstract: [
    Elevator systems are safety-critical infrastructure found in virtually every modern building,
    where incorrect controller behavior can cause serious injury or fatality. Common failure modes
    include elevator motion while doors are open, movement when already at the destination floor,
    and undefined system states arising from incomplete or ambiguous control logic. In this paper,
    we present a mechanically verified formal model of a simplified elevator controller modeled as a
    deterministic finite state machine with five floors. We encode the model in Rocq (Coq), an
    interactive theorem prover based on the Calculus of Inductive Constructions, and formally prove
    six key properties: Door Safety, Movement Safety, State Consistency, Determinism, Totality,
    and Reachability. Safety properties are established via case analysis on the transition function;
    State Consistency is proven as an inductive invariant preserved by every transition; and
    Reachability is proven by structural induction, showing that every state reachable from the
    initial configuration satisfies the invariant. Our results demonstrate that interactive theorem
    proving is a practical and rigorous approach to establishing strong correctness guarantees for
    safety-critical embedded controllers.
  ],
  authors: (
    (
      name: "Aaron Jori B. Baclor",
      department: [Department of Computer Science],
      organization: [University of the Philippines Diliman],
      location: [Quezon City, Philippines],
      email: "abbaclor1@up.edu.ph",
    ),
    (
      name: "Raphael Anton G. Felix",
      department: [Department of Computer Science],
      organization: [University of the Philippines Diliman],
      location: [Quezon City, Philippines],
      email: "rgfelix@up.edu.ph",
    ),
    (
      name: "Gabrielle Denise S. Sacramento",
      department: [Department of Computer Science],
      organization: [University of the Philippines Diliman],
      location: [Quezon City, Philippines],
      email: "gssacramento@up.edu.ph",
    ),
  ),
  index-terms: ("formal verification", "theorem proving", "Rocq", "elevator safety", "finite state machine", "safety-critical systems"),
  bibliography: bibliography("refs.bib"),
)

= Introduction

Elevator systems are among the most widely deployed safety-critical embedded controllers in
the built environment. A modern elevator responds to floor requests, manages door interlocks,
and controls motor direction — all subject to strict safety requirements. Failures in these
systems are not merely inconvenient: incidents of elevators moving with doors open, doors
closing on occupants, or systems entering unhandled states have caused fatalities worldwide
@baier2008principles. Despite this, the majority of elevator controllers are validated
primarily through functional testing and simulation, techniques that can only explore a finite
subset of possible behaviors.

Formal verification offers a principled alternative: rather than searching for bugs by running
the system, we construct mathematical proofs of correctness that hold for _all_ possible
inputs and states. Interactive theorem provers such as Rocq (Coq) @coq2024 provide a
mechanical checking infrastructure in which every proof step is verified against the axioms
of the underlying type theory. This approach has been used to verify compilers @leroy2009formal,
operating systems, and cryptographic protocols, yet its application to elevator controllers
remains relatively unexplored in the teaching literature.

Prior work on elevator verification has largely relied on model checking with tools such as
SPIN or TLA+, which automatically explore state spaces but are limited to finite (and often
small) models @baier2008principles. The B-Method @abrial1996elevator has been applied to
specify elevator control in the Event-B formalism, but mechanical proof was not always carried
through to completion. In contrast, Rocq proofs constitute unconditional mathematical
guarantees — the kernel accepts a proof only if every step is type-correct — and the
resulting artifacts can be extracted to certified executable code.

In this paper, we present a formal Rocq model of a simplified 5-floor elevator controller and
mechanically verify six properties that span both safety and correctness concerns:

+ *Door Safety*: the elevator never moves while the door is open.
+ *Movement Safety*: the elevator does not initiate movement if already at the target floor.
+ *State Consistency*: every reachable state satisfies a well-formedness invariant.
+ *Determinism*: the same state and command always yield the same successor state.
+ *Totality*: the transition function is defined for every valid state-command pair.
+ *Reachability*: all states reachable from the initial state satisfy the safety invariant.

Properties 1–3 are safety properties with direct physical interpretations; Properties 4–5 are
functional correctness properties about the specification itself; Property 6 establishes that
the invariant is closed under execution from the designated initial configuration. The complete
Rocq development is included alongside this paper in the file #raw("elevator_FINAL.v").

The remainder of this paper is organized as follows. Section II defines the formal model and
states the six properties as Rocq theorems. Section III presents the proof results and
discusses the proof techniques and challenges. Section IV concludes with a summary and
directions for future work.

= Property Specification

== System Model

We model the elevator controller as a deterministic finite state machine (DFSM). A state
captures the complete observable configuration of the controller at any point in time, and a
transition function maps a state and a command to a successor state.

*Types.* We define five inductive types representing the core abstractions of the system:

```coq
Inductive Floor : Type := F0 | F1 | F2 | F3 | F4.

Inductive DoorStatus    : Type := DoorOpen | DoorClosed.
Inductive MovementStatus : Type := Moving | Idle.
Inductive Direction      : Type := DirUp | DirDown | DirNone.

Record State : Type := mkState {
  current_floor    : Floor;
  door_status      : DoorStatus;
  movement_status  : MovementStatus;
  direction        : Direction;
  requested_floor  : Floor
}.
```

Using an inductive `Floor` type with five constructors (F0 through F4) prevents invalid floor
values _by construction_: there is no `floor_to_nat` value outside the range $[0,4]$, and no
guard on input is needed to keep floors in bounds. The state separates `MovementStatus` from
`Direction` so that the predicate _currently moving_ and the predicate _direction of travel_
are orthogonal; the invariant then rules out combinations such as `Moving` with `DirNone` or
`Idle` with `DirUp`.

*Commands.* The controller accepts five commands:

```coq
Inductive Command : Type :=
| CallElevator       : Floor -> Command
| OpenDoor           : Command
| CloseDoor          : Command
| MoveElevator       : Command
| ArriveAtDestination : Command.
```

`CallElevator f` requests floor `f`. `OpenDoor` and `CloseDoor` control the door when the
elevator is stationary. `MoveElevator` initiates travel toward the requested floor if safe.
`ArriveAtDestination` completes an in-progress journey, placing the elevator at the
requested floor.

*Transition Function.* The transition function `transition : State → Command → State` is
defined by case analysis over the command:

```coq
Definition transition (s : State) (cmd : Command) : State :=
  match cmd with
  | CallElevator target =>
      match movement_status s with
      | Moving => s
      | Idle   => mkState (current_floor s) (door_status s)
                          Idle DirNone target
      end
  | OpenDoor =>
      match movement_status s with
      | Moving => s
      | Idle   => mkState (current_floor s) DoorOpen
                          Idle DirNone (requested_floor s)
      end
  | CloseDoor =>
      match movement_status s with
      | Moving => s
      | Idle   => mkState (current_floor s) DoorClosed
                          Idle DirNone (requested_floor s)
      end
  | MoveElevator =>
      match movement_status s with
      | Moving  => s
      | Idle    =>
          match door_status s with
          | DoorOpen   => s
          | DoorClosed =>
              if floor_lt (current_floor s) (requested_floor s) then
                mkState (current_floor s) DoorClosed Moving
                        DirUp (requested_floor s)
              else if floor_lt (requested_floor s) (current_floor s) then
                mkState (current_floor s) DoorClosed Moving
                        DirDown (requested_floor s)
              else
                mkState (current_floor s) DoorClosed
                        Idle DirNone (requested_floor s)
          end
      end
  | ArriveAtDestination =>
      match movement_status s with
      | Moving => mkState (requested_floor s) DoorClosed
                          Idle DirNone (requested_floor s)
      | Idle   => s
      end
  end.
```

The helper `floor_lt f g` is `Nat.ltb (floor_to_nat f) (floor_to_nat g)`. Unsafe commands
_stutter_ — they return the state unchanged — enforcing the following safety constraints by
construction: (a) calling a new floor while moving is ignored; (b) opening or closing the
door while moving is ignored; (c) moving while the door is open is ignored; and (d) issuing
`MoveElevator` when already at the requested floor leaves the elevator idle rather than
starting spurious motion. `ArriveAtDestination` while already idle is also a no-op.

== Well-Formedness Invariant

The well-formedness predicate `state_invariant` is composed of three independent sub-predicates:

```coq
Definition floors_in_bounds (s : State) : Prop :=
  floor_to_nat (current_floor s)   <= max_floor /\
  floor_to_nat (requested_floor s) <= max_floor.

Definition movement_has_closed_door (s : State) : Prop :=
  match movement_status s with
  | Moving => door_status s = DoorClosed
  | Idle   => True
  end.

Definition direction_matches_movement (s : State) : Prop :=
  match movement_status s, direction s with
  | Idle,   DirNone => True
  | Moving, DirUp   =>
      floor_to_nat (current_floor s) < floor_to_nat (requested_floor s)
  | Moving, DirDown =>
      floor_to_nat (requested_floor s) < floor_to_nat (current_floor s)
  | _, _ => False
  end.

Definition state_invariant (s : State) : Prop :=
  floors_in_bounds s /\
  movement_has_closed_door s /\
  direction_matches_movement s.
```

The three conjuncts enforce: (1) both floors lie within the valid range $[0, 4]$ — this is
trivially satisfied by the inductive `Floor` type but is included for explicitness; (2) the
elevator cannot be in motion unless the door is closed, directly encoding the core
door-interlock safety requirement; and (3) the recorded direction of travel is consistent
with the relative positions of the current and requested floors, ruling out states such as
`DirUp` when the elevator is already above its destination.

== Safety Properties

*Property 1 — Door Safety.* If the transition function places the elevator in a moving state,
then the door in that state is closed:

```coq
Theorem door_safety : forall s cmd,
  state_invariant s ->
  movement_status (transition s cmd) = Moving ->
  door_status (transition s cmd) = DoorClosed.
```

An equivalent formulation makes the implication more direct:

```coq
Theorem transition_into_moving_requires_closed_door :
  forall s cmd,
    state_invariant s ->
    movement_status (transition s cmd) = Moving ->
    door_status (transition s cmd) = DoorClosed.
```

*Property 2 — Movement Safety.* If the elevator is already at the requested floor, the
`MoveElevator` command leaves it idle:

```coq
Theorem move_at_destination_stays_idle : forall s,
  state_invariant s ->
  current_floor s = requested_floor s ->
  movement_status (transition s MoveElevator) = Idle.
```

The contrapositive is also stated explicitly:

```coq
Theorem movement_safety : forall s,
  state_invariant s ->
  current_floor s = requested_floor s ->
  movement_status (transition s MoveElevator) <> Moving.
```

*Property 3 — State Consistency.* The well-formedness invariant is preserved by every
transition:

```coq
Theorem transition_preserves_invariant : forall s cmd,
  state_invariant s -> state_invariant (transition s cmd).
```

Individual corollaries extract each conjunct separately:

```coq
Theorem floors_valid_after_transition : forall s cmd,
  state_invariant s -> floors_in_bounds (transition s cmd).

Theorem direction_consistency_after_transition : forall s cmd,
  state_invariant s -> direction_matches_movement (transition s cmd).
```

== Functional Properties

*Property 4 — Determinism.* We define an operational step relation so that determinism can
be stated in the standard relational form:

```coq
Inductive Step : State -> Command -> State -> Prop :=
| Step_transition : forall s cmd, Step s cmd (transition s cmd).

Theorem determinism : forall s cmd s1 s2,
  Step s cmd s1 -> Step s cmd s2 -> s1 = s2.
```

The stronger statement that each (state, command) pair has a _unique_ successor is:

```coq
Theorem unique_successor : forall s cmd,
  exists! s', Step s cmd s'.
```

*Property 5 — Totality.* The step relation is defined for every state-command pair:

```coq
Theorem totality : forall s cmd,
  exists s', Step s cmd s'.
```

== Reachability

The initial state places the elevator at floor F0, idle, with the door closed and no pending
request:

```coq
Definition initial_state : State :=
  mkState F0 DoorClosed Idle DirNone F0.
```

Reachable states are defined inductively as those obtained from the initial state by zero or
more transitions:

```coq
Inductive reachable : State -> Prop :=
| reachable_initial : reachable initial_state
| reachable_step    : forall s cmd,
    reachable s -> reachable (transition s cmd).
```

*Property 6 — Reachability.* Every reachable state satisfies the full invariant, and
consequently both safety properties hold globally:

```coq
Theorem reachable_states_satisfy_invariant : forall s,
  reachable s -> state_invariant s.

Theorem reachable_door_safety : forall s,
  reachable s ->
  movement_status s = Moving ->
  door_status s = DoorClosed.

Theorem reachable_movement_safety : forall s,
  reachable s ->
  movement_status s = Moving ->
  current_floor s <> requested_floor s.

Theorem reachable_direction_consistency : forall s,
  reachable s -> direction_matches_movement s.
```

= Results and Discussion

== Summary of Verification Results

All six properties were successfully verified in Rocq. @tbl-results summarizes each property,
the primary proof technique, and the approximate complexity of the proof.

#figure(
  table(
    columns: (auto, auto, auto),
    inset: 6pt,
    align: (left, left, center),
    table.header([*Property*], [*Proof Technique*], [*Approx. Lines*]),
    [Door Safety],       [Invariant + `invariant_moving_closed`; `eapply`],   [~25],
    [Movement Safety],   [Case analysis on `m`, `d`; `Nat.ltb_irrefl`; `lia`],[~35],
    [State Consistency], [Helper lemmas; `destruct cmd`; `apply invariant_*`],[~90],
    [Determinism],       [`inversion`; `reflexivity`],                         [~10],
    [Totality],          [Existential witness; `constructor`],                 [~6],
    [Reachability],      [Structural induction on `reachable`; `eapply`],     [~50],
  ),
  caption: [Summary of verified properties.],
) <tbl-results>

== Door Safety

The Door Safety proof reduces to a lemma `invariant_moving_closed`, which states that any
state satisfying `state_invariant` that is also in a `Moving` status must have `DoorClosed`:

```coq
Lemma invariant_moving_closed : forall s,
  state_invariant s ->
  movement_status s = Moving ->
  door_status s = DoorClosed.
```

The proof destructs the `state_invariant` conjunction and unfolds `movement_has_closed_door`.
When `movement_status s = Moving`, the second conjunct directly yields `door_status s =
DoorClosed`; the `Idle` case is discharged by `discriminate` on the `Moving` hypothesis.

`door_safety` then combines `transition_preserves_invariant` with `invariant_moving_closed`:
the successor state satisfies the invariant (by preservation), and if that successor is in a
`Moving` status, the lemma applies. `transition_into_moving_requires_closed_door` is a
definitional alias proven by `apply door_safety`.

== Movement Safety

The Movement Safety proof proceeds by case analysis on the `movement_status` and `door_status`
of the current state. If the elevator is already `Moving`, the `MoveElevator` transition
stutters (returns `s`), and the `state_invariant` hypothesis on `s` provides `direction_matches_movement`.
When `direction s = DirUp` or `DirDown`, the invariant conjunct yields a strict inequality
between `current_floor` and `requested_floor`, but `current_floor s = requested_floor s`
gives equality — `lia` derives a contradiction. The `DirNone` case is excluded by the
invariant since `Moving` with `DirNone` is `False`.

If the elevator is `Idle` and the door is `DoorOpen`, the transition stutters. If the door
is `DoorClosed`, the `MoveElevator` case evaluates `floor_lt (current_floor s) (requested_floor s)`.
Because `current_floor s = requested_floor s`, both `floor_lt` calls reduce to `false` via
`Nat.ltb_irrefl`, so the transition constructs an `Idle` state directly.

== State Consistency

The `transition_preserves_invariant` proof is the most substantial in the development.
Three helper lemmas first establish that specific state shapes satisfy `state_invariant`:

```coq
Lemma invariant_idle : forall cf d req,
  state_invariant (mkState cf d Idle DirNone req).

Lemma invariant_moving_up : forall cf req,
  floor_to_nat cf < floor_to_nat req ->
  state_invariant (mkState cf DoorClosed Moving DirUp req).

Lemma invariant_moving_down : forall cf req,
  floor_to_nat req < floor_to_nat cf ->
  state_invariant (mkState cf DoorClosed Moving DirDown req).
```

Each lemma unfolds all three sub-predicates and dispatches goals with `floor_within_bounds`
and `auto`. The main theorem then destructs the command:

- `CallElevator`, `OpenDoor`, `CloseDoor`: if `Moving`, the transition stutters and the
  input invariant suffices; if `Idle`, the result is an idle state, so `invariant_idle` applies.
- `MoveElevator`: if `Moving` or `DoorOpen`, stutter. Otherwise, `floor_lt` is evaluated.
  A `true` result for `floor_lt cf req` means `Nat.ltb_lt` yields `cf < req`, so
  `invariant_moving_up` closes the goal; the symmetric case uses `invariant_moving_down`;
  both comparisons `false` means `cf = req` and `invariant_idle` applies.
- `ArriveAtDestination`: if `Moving`, the result is `mkState req DoorClosed Idle DirNone req`,
  which `invariant_idle` handles; if `Idle`, stutter.

The individual corollaries `floors_valid_after_transition` and
`direction_consistency_after_transition` simply project the relevant conjunct from the
invariant returned by `transition_preserves_invariant`.

== Determinism and Totality

Both properties follow from the construction of the `Step` relation as a thin wrapper around
`transition`. Determinism destructs both `Step` hypotheses with `inversion`, which unifies
both successor states with `transition s cmd`, and `reflexivity` closes the goal. Totality
existentially witnesses `transition s cmd` and uses `constructor` to discharge `Step s cmd
(transition s cmd)`. `unique_successor` combines both: `exists (transition s cmd)` is
demonstrated by `constructor`, and uniqueness is delegated to `determinism`.

While these proofs are trivial in Rocq, their formal statement is meaningful. They rule out
specifications that are accidentally nondeterministic (e.g., defined via a relation rather
than a function) or partial (e.g., using `option State` without handling all cases).
Establishing these properties formally ensures that the specification is fit for reasoning.

== Reachability

The `reachable_states_satisfy_invariant` proof proceeds by structural induction on the
`reachable` derivation. The base case applies `initial_state_invariant`, which in turn
invokes `invariant_idle` — the initial state `mkState F0 DoorClosed Idle DirNone F0` is
trivially well-formed. The inductive step applies `transition_preserves_invariant` to the
inductive hypothesis, showing that one more transition maintains the invariant.

The three corollaries `reachable_door_safety`, `reachable_movement_safety`, and
`reachable_direction_consistency` each combine `reachable_states_satisfy_invariant` with the
corresponding invariant lemma via `eapply`. This establishes that the safety properties are
not only preserved by individual transitions but hold _universally_ over all states that can
ever arise during execution, providing the strongest possible correctness guarantee for the
model.

== Limitations and Scope

The current model has several deliberate simplifications:

- *Single pending request*: The state holds only one target floor. A production controller
  must queue multiple concurrent requests, requiring a more complex state representation
  (e.g., a list of pending floors and a scheduling policy).
- *Abstract floor movement*: The `MoveElevator` command sets the elevator in motion and
  `ArriveAtDestination` completes the journey atomically. Physical systems have continuous
  motion with intermediate floor positions; the model abstracts over the mechanics and
  focuses on the control logic transitions.
- *No emergency stop*: Commands such as emergency halt or door-open-in-motion override
  are not modeled. These would require additional state flags and transition rules.
- *No liveness*: The model does not prove that the elevator will _eventually_ reach any
  requested floor under a fair scheduler. Establishing liveness would require embedding
  the model in a temporal logic and adding fairness assumptions about command delivery;
  the reachability result instead provides a safety-only closure guarantee.

Despite these limitations, the model captures the essential control-logic hazards that
motivate formal verification: the door-movement interlock, same-floor no-op movement, and
directional consistency. All six properties are verified against this model without
qualification.

= Conclusion

We have presented a formal Rocq model of a 5-floor elevator controller and mechanically
verified six properties covering safety, functional correctness, and reachability. The Door
Safety and Movement Safety properties establish critical safeguards against hazardous elevator
behavior. State Consistency is captured as an inductive invariant proven to hold after every
transition. Determinism and Totality follow from the functional design of the transition
relation wrapped in an operational step predicate. Reachability is proven by structural
induction on the derivation of reachable states, showing that the invariant — and therefore
both safety properties — hold universally over all states that can arise from the initial
configuration.

The development demonstrates that interactive theorem proving in Rocq is accessible and
effective for small-to-medium safety-critical controllers. The proofs are machine-checked —
not merely argued informally — and together span approximately 660 lines of Rocq source.

Several directions for future work are apparent. First, extending the model to support a
queue of floor requests would more faithfully reflect real elevator controllers and would
expose interesting correctness properties around scheduling fairness. Second, adding a
liveness proof — showing that a fair command sequence eventually services any pending
request — would require embedding the model in a temporal logic framework such as
Coq's TLA library or using coinductive techniques. Third, applying model checking tools such
as TLA+ or NuSMV to the same specification would allow a direct comparison of the two
verification paradigms on the same benchmark. Fourth, Rocq's program extraction facility
could be used to derive a certified OCaml implementation of the controller from the verified
specification, producing executable controller logic with machine-checked safety guarantees.
