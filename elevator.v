From Coq Require Import Arith.PeanoNat Lia.

(*
  Elevator Control System Safety Verification

  This file models a simplified elevator controller as a deterministic
  finite state machine and proves safety, consistency, determinism,
  totality, and reachability invariants.
*)

(* Floors *)

(*
  We model a building with five valid floors: F0 through F4.

  Using an inductive type prevents invalid floor values by construction.
  We still define a numeric interpretation so we can talk about bounds,
  ordering, and direction.
*)
Inductive Floor : Type :=
| F0
| F1
| F2
| F3
| F4.

Definition floor_to_nat (f : Floor) : nat :=
  match f with
  | F0 => 0
  | F1 => 1
  | F2 => 2
  | F3 => 3
  | F4 => 4
  end.

Definition max_floor : nat := 4.

Definition floor_lt (f g : Floor) : bool :=
  Nat.ltb (floor_to_nat f) (floor_to_nat g).

Lemma floor_within_bounds :
  forall f : Floor,
    floor_to_nat f <= max_floor.
Proof.
  intro f.
  destruct f; unfold max_floor; simpl; repeat constructor.
Qed.

(* Elevator state components *)

Inductive DoorStatus : Type :=
| DoorOpen
| DoorClosed.

Inductive MovementStatus : Type :=
| Moving
| Idle.

Inductive Direction : Type :=
| DirUp
| DirDown
| DirNone.

(*
  A complete elevator state contains:

  - current_floor: where the elevator currently is
  - door_status: whether the door is open or closed
  - movement_status: whether the elevator is moving or idle
  - direction: current movement direction
  - requested_floor: destination requested by the user/controller
*)
Record State : Type := mkState
{
  current_floor : Floor;
  door_status : DoorStatus;
  movement_status : MovementStatus;
  direction : Direction;
  requested_floor : Floor
}.

(* Commands *)

(*
  Commands accepted by the controller.

  CallElevator f:
    request floor f.

  OpenDoor:
    open the door, but only if idle.

  CloseDoor:
    close the door, but only if idle.

  MoveElevator:
    begin movement toward the requested floor, if safe.

  ArriveAtDestination:
    complete movement and place the elevator at the requested floor.
*)
Inductive Command : Type :=
| CallElevator : Floor -> Command
| OpenDoor : Command
| CloseDoor : Command
| MoveElevator : Command
| ArriveAtDestination : Command.

(* Transition function *)

(*
  The transition function is deterministic and total by construction:
  for every state and every command, it returns exactly one next state.

  Unsafe commands stutter, meaning they return the same state.

  Important safety choices:

  - Calling a new floor while moving is ignored.
  - Opening or closing the door while moving is ignored.
  - Moving while the door is open is ignored.
  - Moving when already at the requested floor keeps the elevator idle.
  - Arriving at the destination sets the elevator idle at the request.
*)
Definition transition (s : State) (cmd : Command) : State :=
  match cmd with
  | CallElevator target =>
      match movement_status s with
      | Moving => s
      | Idle =>
          mkState
            (current_floor s)
            (door_status s)
            Idle
            DirNone
            target
      end

  | OpenDoor =>
      match movement_status s with
      | Moving => s
      | Idle =>
          mkState
            (current_floor s)
            DoorOpen
            Idle
            DirNone
            (requested_floor s)
      end

  | CloseDoor =>
      match movement_status s with
      | Moving => s
      | Idle =>
          mkState
            (current_floor s)
            DoorClosed
            Idle
            DirNone
            (requested_floor s)
      end

  | MoveElevator =>
      match movement_status s with
      | Moving => s
      | Idle =>
          match door_status s with
          | DoorOpen => s
          | DoorClosed =>
              if floor_lt (current_floor s) (requested_floor s) then
                mkState
                  (current_floor s)
                  DoorClosed
                  Moving
                  DirUp
                  (requested_floor s)
              else if floor_lt (requested_floor s) (current_floor s) then
                mkState
                  (current_floor s)
                  DoorClosed
                  Moving
                  DirDown
                  (requested_floor s)
              else
                mkState
                  (current_floor s)
                  DoorClosed
                  Idle
                  DirNone
                  (requested_floor s)
          end
      end

  | ArriveAtDestination =>
      match movement_status s with
      | Moving =>
          mkState
            (requested_floor s)
            DoorClosed
            Idle
            DirNone
            (requested_floor s)
      | Idle => s
      end
  end.

(* Invariants *)

(*
  Floor bound invariant.

  Since Floor is finite, this is true for every state, but we still keep
  it as part of the invariant because the project explicitly asks for
  floor validity.
*)
Definition floors_in_bounds (s : State) : Prop :=
  floor_to_nat (current_floor s) <= max_floor /\
  floor_to_nat (requested_floor s) <= max_floor.

(*
  Door safety invariant.

  If the elevator is moving, the door must be closed.
*)
Definition movement_has_closed_door (s : State) : Prop :=
  match movement_status s with
  | Moving => door_status s = DoorClosed
  | Idle => True
  end.

(*
  Direction consistency invariant.

  - If idle, direction must be None.
  - If moving up, current floor must be below requested floor.
  - If moving down, requested floor must be below current floor.
  - Moving with DirNone is invalid.
  - Idle with DirUp or DirDown is invalid.
*)
Definition direction_matches_movement (s : State) : Prop :=
  match movement_status s, direction s with
  | Idle, DirNone => True
  | Moving, DirUp =>
      floor_to_nat (current_floor s) <
      floor_to_nat (requested_floor s)
  | Moving, DirDown =>
      floor_to_nat (requested_floor s) <
      floor_to_nat (current_floor s)
  | _, _ => False
  end.

(*
  Full state invariant.
*)
Definition state_invariant (s : State) : Prop :=
  floors_in_bounds s /\
  movement_has_closed_door s /\
  direction_matches_movement s.

(* Helper lemmas for constructing invariant states *)

Lemma floors_always_in_bounds :
  forall s : State,
    floors_in_bounds s.
Proof.
  intros [cf d m dir req].
  unfold floors_in_bounds.
  simpl.
  split; apply floor_within_bounds.
Qed.

Lemma invariant_idle :
  forall cf d req,
    state_invariant (mkState cf d Idle DirNone req).
Proof.
  intros cf d req.
  unfold state_invariant,
         floors_in_bounds,
         movement_has_closed_door,
         direction_matches_movement.
  simpl.
  repeat split; try apply floor_within_bounds; auto.
Qed.

Lemma invariant_moving_up :
  forall cf req,
    floor_to_nat cf < floor_to_nat req ->
    state_invariant (mkState cf DoorClosed Moving DirUp req).
Proof.
  intros cf req Hlt.
  unfold state_invariant,
         floors_in_bounds,
         movement_has_closed_door,
         direction_matches_movement.
  simpl.
  repeat split; try apply floor_within_bounds; auto.
Qed.

Lemma invariant_moving_down :
  forall cf req,
    floor_to_nat req < floor_to_nat cf ->
    state_invariant (mkState cf DoorClosed Moving DirDown req).
Proof.
  intros cf req Hlt.
  unfold state_invariant,
         floors_in_bounds,
         movement_has_closed_door,
         direction_matches_movement.
  simpl.
  repeat split; try apply floor_within_bounds; auto.
Qed.

(* State consistency preservation *)

(*
  Main preservation theorem:

  If a state satisfies the invariant, then after any command, the next
  state also satisfies the invariant.
*)
Theorem transition_preserves_invariant :
  forall s cmd,
    state_invariant s ->
    state_invariant (transition s cmd).
Proof.
  intros [cf d m dir req] cmd Hinv.
  destruct cmd as [target | | | |]; simpl.

  - (* CallElevator *)
    destruct m.
    + exact Hinv.
    + apply invariant_idle.

  - (* OpenDoor *)
    destruct m.
    + exact Hinv.
    + apply invariant_idle.

  - (* CloseDoor *)
    destruct m.
    + exact Hinv.
    + apply invariant_idle.

  - (* MoveElevator *)
    destruct m.
    + exact Hinv.
    + destruct d.
      * exact Hinv.
      * destruct (floor_lt cf req) eqn:Hup.
        -- apply invariant_moving_up.
           unfold floor_lt in Hup.
           apply Nat.ltb_lt in Hup.
           exact Hup.
        -- destruct (floor_lt req cf) eqn:Hdown.
           ++ apply invariant_moving_down.
              unfold floor_lt in Hdown.
              apply Nat.ltb_lt in Hdown.
              exact Hdown.
           ++ apply invariant_idle.

  - (* ArriveAtDestination *)
    destruct m.
    + apply invariant_idle.
    + exact Hinv.
Qed.

Theorem state_consistency_after_transition :
  forall s cmd,
    state_invariant s ->
    state_invariant (transition s cmd).
Proof.
  apply transition_preserves_invariant.
Qed.

Theorem floors_valid_after_transition :
  forall s cmd,
    state_invariant s ->
    floors_in_bounds (transition s cmd).
Proof.
  intros s cmd Hinv.
  pose proof (transition_preserves_invariant s cmd Hinv) as Hnext.
  unfold state_invariant in Hnext.
  destruct Hnext as [Hfloors [_ _]].
  exact Hfloors.
Qed.

Theorem direction_consistency_after_transition :
  forall s cmd,
    state_invariant s ->
    direction_matches_movement (transition s cmd).
Proof.
  intros s cmd Hinv.
  pose proof (transition_preserves_invariant s cmd Hinv) as Hnext.
  unfold state_invariant in Hnext.
  destruct Hnext as [_ [_ Hdir]].
  exact Hdir.
Qed.

(* Door safety *)

Lemma invariant_moving_closed :
  forall s,
    state_invariant s ->
    movement_status s = Moving ->
    door_status s = DoorClosed.
Proof.
  intros [cf d m dir req] Hinv Hmoving.
  unfold state_invariant, movement_has_closed_door in Hinv.
  simpl in *.
  destruct Hinv as [_ [Hdoor _]].
  destruct m.
  - exact Hdoor.
  - discriminate Hmoving.
Qed.

Theorem door_safety :
  forall s cmd,
    state_invariant s ->
    movement_status (transition s cmd) = Moving ->
    door_status (transition s cmd) = DoorClosed.
Proof.
  intros s cmd Hinv Hmoving.
  eapply invariant_moving_closed.
  - apply transition_preserves_invariant.
    exact Hinv.
  - exact Hmoving.
Qed.

Theorem transition_into_moving_requires_closed_door :
  forall s cmd,
    state_invariant s ->
    movement_status (transition s cmd) = Moving ->
    door_status (transition s cmd) = DoorClosed.
Proof.
  apply door_safety.
Qed.

(* Movement safety *)

(*
  If the elevator is already at the requested floor, then the MoveElevator
  command cannot make it move.
*)
Theorem move_at_destination_stays_idle :
  forall s,
    state_invariant s ->
    current_floor s = requested_floor s ->
    movement_status (transition s MoveElevator) = Idle.
Proof.
  intros [cf d m dir req] Hinv Heq.
  simpl in Heq.
  subst req.
  simpl.

  unfold state_invariant, direction_matches_movement in Hinv.
  destruct Hinv as [_ [_ Hdir]].

  destruct m.
  - destruct dir; simpl in Hdir; try lia; contradiction.
  - destruct d.
    + reflexivity.
    + unfold floor_lt.
      rewrite Nat.ltb_irrefl.
      reflexivity.
Qed.

Theorem movement_safety :
  forall s,
    state_invariant s ->
    current_floor s = requested_floor s ->
    movement_status (transition s MoveElevator) <> Moving.
Proof.
  intros s Hinv Heq Hmoving.
  pose proof (move_at_destination_stays_idle s Hinv Heq) as Hidle.
  rewrite Hidle in Hmoving.
  discriminate Hmoving.
Qed.

Lemma invariant_moving_not_at_destination :
  forall s,
    state_invariant s ->
    movement_status s = Moving ->
    current_floor s <> requested_floor s.
Proof.
  intros [cf d m dir req] Hinv Hmoving Heq.
  simpl in *.
  subst req.

  unfold state_invariant, direction_matches_movement in Hinv.
  destruct Hinv as [_ [_ Hdir]].

  destruct m.
  - destruct dir; simpl in Hdir; try lia; contradiction.
  - discriminate Hmoving.
Qed.

Theorem no_moving_at_requested_floor_after_transition :
  forall s cmd,
    state_invariant s ->
    movement_status (transition s cmd) = Moving ->
    current_floor (transition s cmd) <>
    requested_floor (transition s cmd).
Proof.
  intros s cmd Hinv Hmoving.
  eapply invariant_moving_not_at_destination.
  - apply transition_preserves_invariant.
    exact Hinv.
  - exact Hmoving.
Qed.

(* Step relation, determinism, and totality *)

(*
  Although transition is already a function, we define an operational
  step relation because determinism and totality are often stated over
  relations in formal semantics.
*)
Inductive Step : State -> Command -> State -> Prop :=
| Step_transition :
    forall s cmd,
      Step s cmd (transition s cmd).

Theorem determinism :
  forall s cmd s1 s2,
    Step s cmd s1 ->
    Step s cmd s2 ->
    s1 = s2.
Proof.
  intros s cmd s1 s2 Hstep1 Hstep2.
  inversion Hstep1; subst.
  inversion Hstep2; subst.
  reflexivity.
Qed.

Theorem totality :
  forall s cmd,
    exists s',
      Step s cmd s'.
Proof.
  intros s cmd.
  exists (transition s cmd).
  constructor.
Qed.

Theorem unique_successor :
  forall s cmd,
    exists! s',
      Step s cmd s'.
Proof.
  intros s cmd.
  exists (transition s cmd).
  split.
  - constructor.
  - intros y Hy.
    eapply determinism.
    + constructor.
    + exact Hy.
Qed.

(* Reachability *)

(*
  Initial state:

  The elevator starts at floor F0, closed, idle, with no direction,
  and with destination F0.
*)
Definition initial_state : State :=
  mkState F0 DoorClosed Idle DirNone F0.

Lemma initial_state_invariant :
  state_invariant initial_state.
Proof.
  unfold initial_state.
  apply invariant_idle.
Qed.

(*
  Reachable states are states obtained from the initial state by zero
  or more transitions.
*)
Inductive reachable : State -> Prop :=
| reachable_initial :
    reachable initial_state
| reachable_step :
    forall s cmd,
      reachable s ->
      reachable (transition s cmd).

Theorem reachable_states_satisfy_invariant :
  forall s,
    reachable s ->
    state_invariant s.
Proof.
  intros s Hreach.
  induction Hreach.
  - apply initial_state_invariant.
  - apply transition_preserves_invariant.
    exact IHHreach.
Qed.

Theorem reachable_door_safety :
  forall s,
    reachable s ->
    movement_status s = Moving ->
    door_status s = DoorClosed.
Proof.
  intros s Hreach Hmoving.
  eapply invariant_moving_closed.
  - apply reachable_states_satisfy_invariant.
    exact Hreach.
  - exact Hmoving.
Qed.

Theorem reachable_movement_safety :
  forall s,
    reachable s ->
    movement_status s = Moving ->
    current_floor s <> requested_floor s.
Proof.
  intros s Hreach Hmoving.
  eapply invariant_moving_not_at_destination.
  - apply reachable_states_satisfy_invariant.
    exact Hreach.
  - exact Hmoving.
Qed.

Theorem reachable_direction_consistency :
  forall s,
    reachable s ->
    direction_matches_movement s.
Proof.
  intros s Hreach.
  pose proof (reachable_states_satisfy_invariant s Hreach) as Hinv.
  unfold state_invariant in Hinv.
  destruct Hinv as [_ [_ Hdir]].
  exact Hdir.
Qed.