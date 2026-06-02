(** * Elevator Control System: Formal Safety Verification in Coq/Rocq
    CS 171 — Formal Methods
    Aaron Jori B. Baclor, Raphael Anton G. Felix, Gabrielle Denise S. Sacramento *)

Require Import Arith Lia List Bool.
Import ListNotations.

(* ================================================================= *)
(** ** 1. Constants and Type Definitions                               *)
(* ================================================================= *)

Definition N_FLOORS : nat := 3.

Inductive Door : Type :=
  | Open   : Door
  | Closed : Door.

Inductive Dir : Type :=
  | Up   : Dir
  | Down : Dir
  | Idle : Dir.

Inductive Cmd : Type :=
  | Req       : nat -> Cmd
  | Step      : Cmd
  | OpenDoor  : Cmd
  | CloseDoor : Cmd.

Record State : Type := mkState {
  cur  : nat;
  tgt  : nat;
  door : Door;
  dir  : Dir
}.

(* ================================================================= *)
(** ** 2. Boolean Equality Helpers                                     *)
(* ================================================================= *)

Definition door_eqb (d1 d2 : Door) : bool :=
  match d1, d2 with
  | Open,   Open   => true
  | Closed, Closed => true
  | _,      _      => false
  end.

Lemma door_eqb_iff : forall d1 d2, door_eqb d1 d2 = true <-> d1 = d2.
Proof. intros [] []; simpl; split; intro H; try reflexivity; discriminate. Qed.

Lemma door_eqb_false_iff : forall d1 d2, door_eqb d1 d2 = false <-> d1 <> d2.
Proof.
  intros [] []; simpl; split; intro H;
    try (intro Heq; discriminate);
    try reflexivity;
    try (exfalso; apply H; reflexivity).
Qed.

Lemma door_eq_dec : forall (d1 d2 : Door), {d1 = d2} + {d1 <> d2}.
Proof. decide equality. Qed.

Lemma dir_eq_dec : forall (d1 d2 : Dir), {d1 = d2} + {d1 <> d2}.
Proof. decide equality. Qed.

(* ================================================================= *)
(** ** 3. Direction Helper                                             *)
(* ================================================================= *)

Definition set_dir_for (c t : nat) : Dir :=
  if c <? t then Up
  else if t <? c then Down
  else Idle.

Lemma set_dir_for_up : forall c t, c < t -> set_dir_for c t = Up.
Proof.
  intros c t H. unfold set_dir_for.
  rewrite (proj2 (Nat.ltb_lt c t) H). reflexivity.
Qed.

Lemma set_dir_for_down : forall c t, t < c -> set_dir_for c t = Down.
Proof.
  intros c t H. unfold set_dir_for.
  assert (H1 : (c <? t) = false) by (apply Nat.ltb_nlt; lia).
  rewrite H1.
  rewrite (proj2 (Nat.ltb_lt t c) H). reflexivity.
Qed.

Lemma set_dir_for_idle : forall c, set_dir_for c c = Idle.
Proof.
  intro c. unfold set_dir_for.
  rewrite Nat.ltb_irrefl. reflexivity.
Qed.

Lemma set_dir_up_implies_lt : forall c t, set_dir_for c t = Up -> c < t.
Proof.
  intros c t H. unfold set_dir_for in H.
  destruct (c <? t) eqn:E.
  - apply Nat.ltb_lt; assumption.
  - destruct (t <? c); discriminate.
Qed.

Lemma set_dir_down_implies_lt : forall c t, set_dir_for c t = Down -> t < c.
Proof.
  intros c t H. unfold set_dir_for in H.
  destruct (c <? t); [discriminate|].
  destruct (t <? c) eqn:E; [|discriminate].
  apply Nat.ltb_lt; assumption.
Qed.

(* ================================================================= *)
(** ** 4. Well-Formedness Predicate                                    *)
(* ================================================================= *)

Definition wf (s : State) : Prop :=
  cur s < N_FLOORS /\
  tgt s < N_FLOORS /\
  (dir s <> Idle -> door s = Closed) /\
  (dir s = Up   -> tgt s > cur s) /\
  (dir s = Down -> tgt s < cur s).

(* ================================================================= *)
(** ** 5. Transition Function                                          *)
(* ================================================================= *)

Definition trans (s : State) (cmd : Cmd) : State :=
  match cmd with
  | Req n =>
      if N_FLOORS <=? n then s
      else if n =? cur s then s
      else if door_eqb (door s) Open then s
      else mkState (cur s) n (door s) (set_dir_for (cur s) n)
  | Step =>
      match dir s, door s with
      | Up, Closed =>
          let next := S (cur s) in
          let d'   := if next =? tgt s then Idle else Up in
          mkState next (tgt s) Closed d'
      | Down, Closed =>
          let next := cur s - 1 in
          let d'   := if next =? tgt s then Idle else Down in
          mkState next (tgt s) Closed d'
      | _, _ => s
      end
  | OpenDoor =>
      match dir s with
      | Idle => mkState (cur s) (tgt s) Open Idle
      | _    => s
      end
  | CloseDoor =>
      mkState (cur s) (tgt s) Closed (dir s)
  end.

(* ================================================================= *)
(** ** 6. Run Function                                                 *)
(* ================================================================= *)

Fixpoint run (s : State) (cmds : list Cmd) : State :=
  match cmds with
  | []      => s
  | c :: cs => run (trans s c) cs
  end.

Lemma run_app : forall (s : State) (l1 l2 : list Cmd),
  run s (l1 ++ l2) = run (run s l1) l2.
Proof.
  intros s l1. revert s.
  induction l1 as [| c cs IH]; intros s l2.
  - reflexivity.
  - simpl. apply IH.
Qed.

(* ================================================================= *)
(** ** 7. Property 1: Door Safety                                      *)
(*  The elevator never moves (changes floor) while the door is open.   *)
(* ================================================================= *)

Theorem door_safety :
  forall s : State,
  wf s ->
  cur (trans s Step) <> cur s ->
  door s = Closed.
Proof.
  intros s Hwf Hmoved.
  unfold trans in Hmoved.
  destruct (dir s) eqn:Hdir, (door s) eqn:Hdoor; simpl in Hmoved;
    try contradiction; try reflexivity.
  - (* dir=Up, door=Open: trans returns s, contradiction *)
    exfalso; apply Hmoved; reflexivity.
  - (* dir=Down, door=Open: trans returns s, contradiction *)
    exfalso; apply Hmoved; reflexivity.
  - (* dir=Idle, door=Open: trans returns s *)
    exfalso; apply Hmoved; reflexivity.
  - (* dir=Idle, door=Closed: trans returns s *)
    exfalso; apply Hmoved; reflexivity.
Qed.

(** Equivalent formulation: moving state has door closed. *)
Theorem door_safety_alt :
  forall s : State,
  wf s ->
  dir (trans s Step) <> Idle ->
  door (trans s Step) = Closed.
Proof.
  intros s Hwf Hmoving.
  unfold trans.
  destruct (dir s) eqn:Hdir, (door s) eqn:Hdoor; simpl; simpl in Hmoving;
    try contradiction.
  - destruct (S (cur s) =? tgt s); simpl; try contradiction; reflexivity.
  - destruct (cur s - 1 =? tgt s); simpl; try contradiction; reflexivity.
Qed.

(* ================================================================= *)
(** ** 8. Property 2: Movement Safety                                  *)
(*  The elevator does not move if already at the target floor.         *)
(* ================================================================= *)

Theorem movement_safety :
  forall s : State,
  wf s ->
  cur s = tgt s ->
  cur (trans s Step) = cur s.
Proof.
  intros s [Hcur [Htgt [Hdc [Hup Hdown]]]] Heq.
  unfold trans.
  destruct (dir s) eqn:Hdir.
  - (* Up: wf says tgt > cur, contradicts cur = tgt *)
    exfalso. specialize (Hup Hdir). lia.
  - (* Down: wf says tgt < cur, contradicts cur = tgt *)
    exfalso. specialize (Hdown Hdir). lia.
  - (* Idle: no step taken *)
    destruct (door s); reflexivity.
Qed.

(* ================================================================= *)
(** ** 9. Property 3: State Consistency (wf Preservation)             *)
(*  Every state reachable from a wf state via trans is also wf.        *)
(* ================================================================= *)

Theorem wf_preservation :
  forall (s : State) (cmd : Cmd),
  wf s -> wf (trans s cmd).
Proof.
  intros s cmd [Hcur [Htgt [Hdc [Hup Hdown]]]].
  unfold trans.
  destruct cmd as [n | | |].

  (* --- Req n --- *)
  - destruct (N_FLOORS <=? n) eqn:Hn.
    { repeat split; assumption. }
    destruct (n =? cur s) eqn:Hneq.
    { repeat split; assumption. }
    destruct (door_eqb (door s) Open) eqn:Hdoor.
    { repeat split; assumption. }
    apply Nat.leb_nle in Hn.
    apply Nat.eqb_neq in Hneq.
    apply door_eqb_false_iff in Hdoor.
    simpl. unfold wf; simpl.
    repeat split.
    + exact Hcur.
    + lia.
    + intro Hne.
      destruct (set_dir_for (cur s) n) eqn:Hsd.
      * reflexivity.
      * reflexivity.
      * exfalso; apply Hne; reflexivity.
    + intro Hdu.
      apply set_dir_up_implies_lt.
      rewrite <- Hdu. reflexivity.
    + intro Hdd.
      apply set_dir_down_implies_lt.
      rewrite <- Hdd. reflexivity.

  (* --- Step --- *)
  - destruct (dir s) eqn:Hdir, (door s) eqn:Hdoord; simpl; try (repeat split; assumption).
    + (* Up / Closed *)
      assert (Htcur : tgt s > cur s) by (apply Hup; assumption).
      destruct (S (cur s) =? tgt s) eqn:Hreach; simpl.
      * apply Nat.eqb_eq in Hreach.
        repeat split; try lia.
        -- intro H; exfalso; apply H; reflexivity.
        -- intro H; discriminate.
        -- intro H; discriminate.
      * apply Nat.eqb_neq in Hreach.
        repeat split; try lia.
        -- intro; reflexivity.
        -- intro; lia.
        -- intro H; discriminate.
    + (* Down / Closed *)
      assert (Htcur : tgt s < cur s) by (apply Hdown; assumption).
      assert (Hpos  : cur s > 0) by lia.
      destruct (cur s - 1 =? tgt s) eqn:Hreach; simpl.
      * apply Nat.eqb_eq in Hreach.
        repeat split; try lia.
        -- intro H; exfalso; apply H; reflexivity.
        -- intro H; discriminate.
        -- intro H; discriminate.
      * apply Nat.eqb_neq in Hreach.
        repeat split; try lia.
        -- intro; reflexivity.
        -- intro H; discriminate.
        -- intro; lia.

  (* --- OpenDoor --- *)
  - destruct (dir s) eqn:Hdir; simpl; try (repeat split; assumption).
    (* Idle case: door opens *)
    repeat split; try assumption.
    + intro H; exfalso; apply H; reflexivity.
    + intro H; discriminate.
    + intro H; discriminate.

  (* --- CloseDoor --- *)
  - simpl. repeat split; try assumption.
    intro Hne. apply Hdc; assumption.
Qed.

(** Corollary: wf is preserved along any execution trace. *)
Corollary wf_run :
  forall (s : State) (cmds : list Cmd),
  wf s -> wf (run s cmds).
Proof.
  intros s cmds. revert s.
  induction cmds as [| c cs IH]; intros s Hwf.
  - exact Hwf.
  - simpl. apply IH. apply wf_preservation. exact Hwf.
Qed.

(* ================================================================= *)
(** ** 10. Property 4: Determinism                                     *)
(*  The transition function is deterministic by construction.          *)
(* ================================================================= *)

Theorem determinism :
  forall (s1 s2 : State) (cmd : Cmd),
  s1 = s2 ->
  trans s1 cmd = trans s2 cmd.
Proof. intros s1 s2 cmd H. subst. reflexivity. Qed.

Corollary determinism_unique :
  forall (s r1 r2 : State) (cmd : Cmd),
  r1 = trans s cmd ->
  r2 = trans s cmd ->
  r1 = r2.
Proof. intros s r1 r2 cmd H1 H2. subst. reflexivity. Qed.

(* ================================================================= *)
(** ** 11. Property 5: Totality                                        *)
(*  The transition function is defined for all (State, Cmd) pairs.     *)
(* ================================================================= *)

Theorem totality :
  forall (s : State) (cmd : Cmd),
  exists (s' : State), trans s cmd = s'.
Proof. intros s cmd. exists (trans s cmd). reflexivity. Qed.

(* ================================================================= *)
(** ** 12. Property 6: Liveness                                        *)
(*  The elevator eventually services any pending floor request.         *)
(* ================================================================= *)

(** Key lemma: k Up-steps from floor c reaches c+k, then goes Idle. *)
Lemma run_steps_up : forall k c t,
  t = c + k ->
  c + k < N_FLOORS ->
  run (mkState c t Closed Up) (repeat Step k) =
  mkState t t Closed Idle.
Proof.
  induction k as [| k' IH]; intros c t Heq Hbound.
  - simpl in *. subst. unfold trans. simpl.
    rewrite Nat.eqb_refl. reflexivity.
  - simpl. unfold trans at 1. simpl.
    destruct (S c =? t) eqn:Hreach.
    + apply Nat.eqb_eq in Hreach.
      assert (k' = 0) by lia. subst. simpl. reflexivity.
    + apply Nat.eqb_neq in Hreach.
      apply IH; lia.
Qed.

(** Key lemma: k Down-steps from floor c reaches c-k, then goes Idle. *)
Lemma run_steps_down : forall k c t,
  t + k = c ->
  c < N_FLOORS ->
  run (mkState c t Closed Down) (repeat Step k) =
  mkState t t Closed Idle.
Proof.
  induction k as [| k' IH]; intros c t Heq Hbound.
  - simpl in *. subst. unfold trans. simpl.
    rewrite Nat.eqb_refl. reflexivity.
  - simpl. unfold trans at 1. simpl.
    destruct (c - 1 =? t) eqn:Hreach.
    + apply Nat.eqb_eq in Hreach.
      assert (k' = 0) by lia. subst. simpl. reflexivity.
    + apply Nat.eqb_neq in Hreach.
      apply IH; lia.
Qed.

(** Liveness: for any wf state with pending direction, there exists a
    finite command sequence that services the request (reaches tgt,
    door open). *)
Theorem liveness :
  forall s : State,
  wf s ->
  dir s <> Idle ->
  exists cmds : list Cmd,
    cur  (run s cmds) = tgt s /\
    door (run s cmds) = Open.
Proof.
  intros s [Hcur [Htgt [Hdc [Hup Hdown]]]] Hpending.
  destruct (dir s) eqn:Hdir; [| | exfalso; apply Hpending; reflexivity].

  (* === Case: dir = Up === *)
  - specialize (Hup Hdir).
    remember (tgt s - cur s) as k.
    exists (CloseDoor :: repeat Step k ++ [OpenDoor]).
    assert (Hclose : trans s CloseDoor =
                     mkState (cur s) (tgt s) Closed Up).
    { unfold trans. rewrite Hdir.
      destruct s; simpl in *. subst. reflexivity. }
    simpl. rewrite Hclose. rewrite run_app.
    assert (Hrun : run (mkState (cur s) (tgt s) Close d Up) (repeat Step k) =
                   mkState (tgt s) (tgt s) Closed Idle).
    { apply run_steps_up; lia. }
    rewrite Hrun. simpl. unfold trans. simpl.
    split; reflexivity.

  (* === Case: dir = Down === *)
  - specialize (Hdown Hdir).
    remember (cur s - tgt s) as k.
    exists (CloseDoor :: repeat Step k ++ [OpenDoor]).
    assert (Hclose : trans s CloseDoor =
                     mkState (cur s) (tgt s) Closed Down).
    { unfold trans. rewrite Hdir.
      destruct s; simpl in *. subst. reflexivity. }
    simpl. rewrite Hclose. rewrite run_app.
    assert (Hrun : run (mkState (cur s) (tgt s) Closed Down) (repeat Step k) =
                   mkState (tgt s) (tgt s) Closed Idle).
    { apply run_steps_down; lia. }
    rewrite Hrun. simpl. unfold trans. simpl.
    split; reflexivity.
Qed.

(* End of ElevatorSystem.v *)
