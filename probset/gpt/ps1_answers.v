(* ps1_answers.v *)

From LF Require Export Basics.
From LF Require Export Lists.
From LF Require Export Logic.

(* ################################################################# *)
(* 1. CIRCUIT VERIFICATION *)

Inductive signal : Type :=
  | ON
  | OFF.

Definition not_gate (s : signal) : signal :=
  match s with
  | ON => OFF
  | OFF => ON
  end.

Definition or_gate (s1 s2 : signal) : signal :=
  match s1, s2 with
  | OFF, OFF => OFF
  | _, _ => ON
  end.

Definition and_gate (s1 s2 : signal) : signal :=
  match s1, s2 with
  | ON, ON => ON
  | _, _ => OFF
  end.

Definition xor_gate (s1 s2 : signal) : signal :=
  match s1, s2 with
  | ON, OFF => ON
  | OFF, ON => ON
  | _, _ => OFF
  end.

Definition xnor_gate (s1 s2 : signal) : signal :=
  not_gate (xor_gate s1 s2).

Definition nor_gate (s1 s2 : signal) : signal :=
  not_gate (or_gate s1 s2).

Definition nand_gate (s1 s2 : signal) : signal :=
  not_gate (and_gate s1 s2).

Definition mygate (s1 s2 s3 s4 : signal) : signal :=
  or_gate s1 (or_gate s2 (or_gate s3 s4)).

Theorem c1 : forall s1 s2 s3 s4 : signal,
  s1 = ON -> mygate s1 s2 s3 s4 = ON.
Proof.
  intros s1 s2 s3 s4 H.
  rewrite H.
  reflexivity.
Qed.

Definition mygate2 (s1 s2 : signal) : signal :=
  or_gate (and_gate s1 s2) (and_gate (not_gate s1) (not_gate s2)).

Definition equalgates (g1 g2 : signal -> signal -> signal) : Prop :=
  forall (s1 s2 : signal), g1 s1 s2 = g2 s1 s2.

Theorem c2 : equalgates mygate2 xnor_gate.
Proof.
  unfold equalgates.
  intros s1 s2.
  destruct s1; destruct s2; reflexivity.
Qed.

(* ################################################################# *)
(* 2. GAME THEORY *)

Inductive player : Type :=
  | p1
  | p2.

Inductive action : Type :=
  | betray
  | silent.

Inductive strategy : Type :=
  actionpair (a1 : action) (a2 : action).

Definition utility1 (p : player) (s : strategy) : nat :=
  match p, s with
  | p1, actionpair betray betray => 5
  | p2, actionpair betray betray => 5
  | p1, actionpair betray silent => 3
  | p2, actionpair betray silent => 0
  | p1, actionpair silent betray => 0
  | p2, actionpair silent betray => 3
  | p1, actionpair silent silent => 1
  | p2, actionpair silent silent => 1
  end.

Definition dominant_strategy (s : strategy) (u : player -> strategy -> nat): Prop :=
  forall (p : player) (s' : strategy), (u p s' <=? u p s) = true.

Theorem gt1 : dominant_strategy (actionpair betray betray) utility1.
Proof.
  unfold dominant_strategy.
  intros p s'.
  destruct p; destruct s' as [a1 a2]; destruct a1; destruct a2; reflexivity.
Qed.

Definition utility2 (p : player) (s : strategy) : nat :=
  match p, s with
  | p1, actionpair betray betray => 1
  | p2, actionpair betray betray => 1
  | p1, actionpair betray silent => 5
  | p2, actionpair betray silent => 0
  | p1, actionpair silent betray => 0
  | p2, actionpair silent betray => 5
  | p1, actionpair silent silent => 3
  | p2, actionpair silent silent => 3
  end.

Definition get_action (p : player) (s : strategy) :=
  match p, s with
  | p1, actionpair a1 a2 => a1
  | p2, actionpair a1 a2 => a2
  end.

Definition equilibrium (s : strategy) (u : player -> strategy -> nat) : Prop :=
  forall (s' : strategy),
  (get_action p2 s = get_action p2 s' -> (u p1 s' <=? u p1 s) = true)
  /\
  (get_action p1 s = get_action p1 s' -> (u p2 s' <=? u p2 s) = true).

Theorem gt2 : equilibrium (actionpair betray betray) utility2.
Proof.
  unfold equilibrium.
  intros s'.
  destruct s' as [a1 a2].
  split.
  - intro H.
    destruct a1; destruct a2; simpl in *; try reflexivity; discriminate H.
  - intro H.
    destruct a1; destruct a2; simpl in *; try reflexivity; discriminate H.
Qed.

Definition not_equilibrium (s : strategy) (u : player -> strategy -> nat) : Prop :=
  exists (s' : strategy),
  (get_action p2 s = get_action p2 s' -> (u p1 s' <=? u p1 s) = false)
  \/
  (get_action p1 s = get_action p1 s' -> (u p2 s' <=? u p2 s) = false).

Theorem gt3 : not_equilibrium (actionpair silent silent) utility2.
Proof.
  unfold not_equilibrium.
  exists (actionpair betray silent).
  left.
  intro H.
  reflexivity.
Qed.

Theorem gt4 : forall (s : strategy) (u : player -> strategy -> nat),
  dominant_strategy s u -> equilibrium s u.
Proof.
  intros s u Hdom.
  unfold equilibrium.
  intros s'.
  split.
  - intro H.
    unfold dominant_strategy in Hdom.
    apply Hdom.
  - intro H.
    unfold dominant_strategy in Hdom.
    apply Hdom.
Qed.

(* ################################################################# *)
(* 3. NATURAL NUMBERS *)

Theorem num0 : forall (n : nat), (even n = even (S n)) -> False.
Proof.
  induction n as [| n' IHn'].
  - simpl. intro H. discriminate H.
  - simpl. intro H. apply IHn'. symmetry. apply H.
Qed.

Axiom axone : forall (n : nat), ((even n = true) -> False) -> (even (S n) = true).

Theorem num1 : forall (n : nat), (even n = true) \/ ((even n = true) -> False).
Proof.
  induction n as [| n' IHn'].
  - left. reflexivity.
  - destruct IHn' as [Heven | Hodd].
    + right. intro HSn. apply (num0 n'). rewrite Heven. rewrite HSn. reflexivity.
    + left. apply axone. apply Hodd.
Qed.

(* ################################################################# *)
(* 4. LOGIC *)

Theorem logic1 : forall (A B : Prop), (A /\ B -> False) -> A -> (B -> False).
Proof.
  intros A B Hcontra HA HB.
  apply Hcontra.
  split.
  - apply HA.
  - apply HB.
Qed.

Theorem logic2 : forall (A B : Prop), (A /\ B -> False) <-> (A -> (B -> False)).
Proof.
  intros A B.
  split.
  - intros Hcontra HA HB.
    apply Hcontra.
    split; assumption.
  - intros Hcontra HAB.
    destruct HAB as [HA HB].
    apply Hcontra.
    + apply HA.
    + apply HB.
Qed.

Axiom axtwo : forall (A B : Prop), ((A -> False) -> B) -> ((B -> False) -> A).

Theorem logic3 : forall (A B C D : Prop),
  (((A -> C) /\ ((B -> False) -> D)) /\ ((C /\ D) -> False)) -> (A -> C) /\ (C -> B).
Proof.
  intros A B C D H.
  destruct H as [[HAC HBD] HCD].
  split.
  - apply HAC.
  - intro HC.
    assert ((B -> False) -> False) as HnotnotB.
    { intro HnotB.
      apply HCD.
      split.
      - apply HC.
      - apply HBD. apply HnotB. }
    pose proof (axtwo B False HnotnotB) as HB.
    apply HB.
    intro HFalse.
    apply HFalse.
Qed.

Definition excluded_middle : Prop :=
  forall (P : Prop), P \/ (P -> False).

Theorem logic4 : forall (P Q : Prop),
  excluded_middle -> (P -> False) /\ (Q -> False) -> ((P \/ Q) -> False).
Proof.
  intros P Q HEM Hnot HPQ.
  destruct Hnot as [HnotP HnotQ].
  destruct HPQ as [HP | HQ].
  - apply HnotP. apply HP.
  - apply HnotQ. apply HQ.
Qed.

(* ################################################################# *)
(* 5. COMPUTER ASSISTED EDUCATION TOOL *)

Inductive user : Type :=
  | student
  | teacher
  | admin.

Inductive file : Type :=
  | lesson
  | quiz
  | grade
  | userdata.

Inductive disk : Type :=
  | disk_a
  | disk_b
  | disk_c.

Inductive privilege : Type :=
  | read
  | write.

Definition check_disk (f : file) : disk :=
  match f with
  | lesson => disk_a
  | quiz => disk_a
  | grade => disk_b
  | userdata => disk_c
  end.

Definition check_access (u : user) (f : file) (p : privilege) : bool :=
  match u, check_disk f, p with
  | student, disk_a, read => true
  | teacher, disk_a, read => true
  | teacher, disk_a, write => true
  | teacher, disk_b, read => true
  | teacher, disk_b, write => true
  | teacher, disk_c, read => true
  | admin, disk_a, read => true
  | admin, disk_b, read => true
  | admin, disk_c, read => true
  | admin, disk_c, write => true
  | _, _, _ => false
  end.

Definition access (u : user) (f : file) (p : privilege) : Prop :=
  check_access u f p = true.

Theorem caet1 : forall u, u = teacher -> ((access u userdata write) -> False).
Proof.
  intros u Hu Haccess.
  rewrite Hu in Haccess.
  unfold access in Haccess.
  simpl in Haccess.
  discriminate Haccess.
Qed.

Theorem caet2 : forall (u : user) (p : privilege), u = admin -> access u userdata p.
Proof.
  intros u p Hu.
  rewrite Hu.
  unfold access.
  destruct p; reflexivity.
Qed.

Theorem caet3 : forall u f, ((f = quiz) \/ (f = lesson)) ->
  (access u lesson write /\ access u quiz write) -> u = teacher.
Proof.
  intros u f Hfile Haccess.
  destruct Haccess as [Hlesson Hquiz].
  destruct u.
  - unfold access in Hlesson. simpl in Hlesson. discriminate Hlesson.
  - reflexivity.
  - unfold access in Hlesson. simpl in Hlesson. discriminate Hlesson.
Qed.

Theorem caet4 : forall u, u = student -> access u lesson read /\
  access u quiz read /\ (access u lesson write -> False) /\ (access u quiz write -> False).
Proof.
  intros u Hu.
  rewrite Hu.
  unfold access.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intro H. simpl in H. discriminate H.
      * intro H. simpl in H. discriminate H.
Qed.

Theorem caet5 : forall u f, u = admin -> access u f read.
Proof.
  intros u f Hu.
  rewrite Hu.
  unfold access.
  destruct f; reflexivity.
Qed.

(* ################################################################# *)
(* 6. PERCEPTRON *)

Definition perceptron := list nat.
Definition input := list nat.

Inductive class : Type :=
  | class1
  | class2.

Fixpoint inference (p : perceptron) (i : input) : nat :=
  match p, i with
  | [], _ => 0
  | _, [] => 0
  | w :: p', x :: i' => (w * x) + inference p' i'
  end.

Definition classify (x : nat) (thresh : nat) : class :=
  match x <=? thresh with
  | true => class1
  | false => class2
  end.

Fixpoint reducesum (i : input) : nat :=
  match i with
  | [] => 0
  | x :: i' => x + reducesum i'
  end.

Definition getclass (i : input) (border : nat) : class :=
  classify (reducesum i) border.

Definition correct (p : perceptron) (thresh : nat) (border : nat) (i : input) : Prop :=
  classify (inference p i) thresh = getclass i border.

Definition trained (p : perceptron) (thresh border : nat): Prop :=
  forall (i : input), correct p thresh border i.

Theorem per1 :
  forall p thresh border, (border = 10) ->
  (forall (i : input), i = [1;1;1] \/ i = [5;5;5]) ->
  (p = [3;3;3]) -> (thresh = 10) -> trained p thresh border.
Proof.
  intros p thresh border Hborder Hdata Hp Hthresh.
  unfold trained.
  intro i.
  unfold correct, getclass.
  rewrite Hp. rewrite Hthresh. rewrite Hborder.
  destruct (Hdata i) as [Hi | Hi]; rewrite Hi; reflexivity.
Qed.

(* ################################################################# *)
(* 7. PEANO AXIOMS *)

Definition peanoax1 (X : Type) (o : X) (f : X -> X) : Prop :=
  forall (x : X), (f x = o) -> False.

Definition peanoax2 (X : Type) (f : X -> X) : Prop :=
  forall (x y : X), f x = f y -> x = y.

Definition peanoax3 (X : Type) (p : X -> X -> X) (z : X) (f : X -> X) : Prop :=
  forall (x : X), p z x = f x.

Definition peanoax4 (X : Type) (p : X -> X -> X) (f : X -> X) : Prop :=
  forall (x y : X), p x (f y) = f (p x y).

Definition peanoax5 (X : Type) (m : X -> X -> X) (z : X) : Prop :=
  forall (x : X), m x z = x.

Definition peanoax6 (X : Type) (m : X -> X -> X) (p : X -> X -> X) (z : X) (f : X -> X) : Prop :=
  forall (x y : X), m x (f y) = p (m x y) x.

Definition peanoax7 (X : Type) (l : X -> X -> Prop) (p : X -> X -> X) : Prop :=
  forall (x y : X), l x y <-> exists (n : X), (y = p x n).

Definition peanoax8 (X : Type) (o : X) (f : X -> X) : Prop :=
  forall (x : X) (P : X -> Prop), ((P o) /\ (forall x : X, P x -> P (f x))) -> forall x, P x.

Definition isapeanomodel
  (X : Type) (o : X) (z : X) (f : X -> X)
  (p : X -> X -> X) (m : X -> X -> X) (l : X -> X -> Prop) : Prop :=
  peanoax1 X o f /\
  peanoax2 X f /\
  peanoax3 X p z f /\
  peanoax4 X p f /\
  peanoax5 X m z /\
  peanoax6 X m p z f /\
  peanoax7 X l p /\
  peanoax8 X o f.

Theorem natpax1 : peanoax1 nat O S.
Proof.
  unfold peanoax1.
  intros x H.
  discriminate H.
Qed.

Theorem natpax2 : peanoax2 nat S.
Proof.
  unfold peanoax2.
  intros x y H.
  injection H as Hxy.
  apply Hxy.
Qed.

Theorem natpax3 : peanoax3 nat plus (S O) S.
Proof.
  unfold peanoax3.
  intros x.
  reflexivity.
Qed.

Theorem natpax4 : peanoax4 nat plus S.
Proof.
  unfold peanoax4.
  intros x y.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Theorem natpax5 : peanoax5 nat mult (S O).
Proof.
  unfold peanoax5.
  intros x.
  apply mult_n_1.
Qed.

Theorem natpax6 : peanoax6 nat mult plus (S O) S.
Proof.
  unfold peanoax6.
  intros x y.
  rewrite <- mult_n_Sm.
  reflexivity.
Qed.

Theorem natpax7 : peanoax7 nat le plus.
Proof.
  unfold peanoax7.
  intros x y.
  split.
  - intro Hle.
    induction Hle as [| y' Hle' IH].
    + exists 0. rewrite add_0_r. reflexivity.
    + destruct IH as [n Hn].
      exists (S n).
      rewrite Hn.
      rewrite <- plus_n_Sm.
      reflexivity.
  - intro Hexists.
    destruct Hexists as [n Hn].
    subst.
    induction n as [| n' IHn'].
    + rewrite add_0_r. apply le_n.
    + rewrite <- plus_n_Sm. apply le_S. apply IHn'.
Qed.

Theorem natpax8 : peanoax8 nat O S.
Proof.
  unfold peanoax8.
  intros x P H.
  destruct H as [Hbase Hstep].
  intro x0.
  induction x0 as [| x0' IHx0'].
  - apply Hbase.
  - apply Hstep. apply IHx0'.
Qed.

Theorem natisapeanomodel : isapeanomodel nat O (S O) S plus mult le.
Proof.
  unfold isapeanomodel.
  exact (conj natpax1 (conj natpax2 (conj natpax3 (conj natpax4 (conj natpax5 (conj natpax6 (conj natpax7 natpax8))))))).
Qed.

Definition groupaxone (X : Type) (o : X) (p : X -> X -> X) : Prop :=
  forall (x : X), exists (y : X), p x y = o.

Definition notgroupaxone (X : Type) (o : X) (p : X -> X -> X) : Prop :=
  groupaxone X o p -> False.

Theorem natisnotagroup : notgroupaxone nat O plus.
Proof.
  unfold notgroupaxone, groupaxone.
  intro Hgroup.
  destruct (Hgroup (S O)) as [y Hy].
  simpl in Hy.
  discriminate Hy.
Qed.

(* ################################################################# *)
