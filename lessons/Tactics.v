From LF Require Export Poly.


Theorem silly1 : forall (n m : nat),
  n = m -> n = m.
Proof.
  intros n m eq. apply eq.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. 
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros. apply H0. apply H. apply H1.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H. symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros. rewrite H. symmetry. apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros. rewrite H. apply H0.
Qed.

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros. rewrite H. apply H0.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  apply trans_eq with (y := [c; d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros. apply trans_eq with (y:=m). apply H0. apply H.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros. assert (H1 : m = pred (S m)). { reflexivity. }
  rewrite H1. rewrite <- H. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H. injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> n = m.
Proof.
  intros. injection H. intros. rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma injection_lemma : forall (X : Type) (l : list X) (x y : X),
  x :: l = y :: l -> x = y.
Proof.
  intros. destruct l.
  - injection H. intros. apply H0.
  - injection H. intros. apply H0.
Qed.   

Example injection_ex3 : 
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros. injection H. intros. apply injection_lemma with (l := l).
  rewrite H2. rewrite <- H0. symmetry. apply H1.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros. discriminate H.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros. discriminate H.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros. discriminate H.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros. destruct n.
  - reflexivity.
  - discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros. symmetry in H0. apply H in H0. symmetry.
  apply H0.
Qed.

Theorem specialize_example: forall n,
  (forall m, m * n = 0)
  -> n = 0.
Proof.
  intros n H. specialize H with (m := 1).
  simpl in H. rewrite add_0_r in H. apply H.
Qed.

Lemma nth_error_always_none: forall (l : list nat),
  (forall i, nth_error l i = None) ->
  l = [].
Proof.
  intros. destruct l.
  - reflexivity.
  - specialize H with (i := 0). simpl in H. discriminate H.  
Qed.  

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed.

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal. inversion eq.
Abort.

Theorem double_injective_lemma : forall n m,
  n = m -> S n = S m.
Proof.
  intros n. induction n.
  - destruct m.
    + reflexivity.
    + intros. discriminate H.
  - destruct m.
    + intros. discriminate H.
    + intros. injection H. intros. rewrite H0. reflexivity.
Qed.     

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  induction n.
  - simpl. intros m. destruct m.
    + simpl. intros. apply H.
    + intros. simpl in H. discriminate H.
  - intros. destruct m.
    + discriminate H.
    + injection H. intros. apply IHn in H0. rewrite H0.
      reflexivity.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  induction n.
  - intros. destruct m.
    + reflexivity.
    + discriminate H.
  - intros. destruct m.
    + discriminate H.
    + apply IHn in H. rewrite H. reflexivity.
Qed.   

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
Proof.
  induction n.
  - simpl. intros. destruct m.
    + reflexivity.
    + discriminate H.
  - simpl. intros. destruct m.
    + discriminate H.
    + simpl in H. rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H. injection H. intros. apply IHn in H0. rewrite H0. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. generalize dependent n. induction m.
  - intros. destruct n.
    + reflexivity.
    + discriminate H.
  - intros. destruct n.
    + discriminate H.
    + injection H. intros. apply IHm in H0. intros.
    rewrite H0. reflexivity.
Qed.    

Lemma sub_add_leb : forall n m, n <=? m = true -> (m - n) + n = m.
Proof.
  induction n.
  - destruct m.
    + reflexivity.
    + intros. simpl. rewrite add_0_r. reflexivity.
  - intros. destruct m.
    + discriminate H.
    + simpl in H. simpl. rewrite <- plus_n_Sm. rewrite IHn.
      -- reflexivity.
      -- apply H.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X), length l = n -> nth_error l n = None.
Proof.
  induction n.
  - intros. destruct l.
    + reflexivity.
    + discriminate H.  
  - intros. destruct l.
    + discriminate H.
    + simpl in H. injection H. intros. apply IHn in H0.
    simpl. apply H0.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square. assert (H: m * (n * m) = n * (m * m)).
    { 
    rewrite mul_comm. rewrite mult_assoc. reflexivity.
    }
  rewrite <- mult_assoc. rewrite <- mult_assoc. rewrite H.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3).
  - reflexivity.
  - destruct (n =? 5). reflexivity. reflexivity.
Qed.  

Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn : Heqe3.
  - apply eqb_true in Heqe3. rewrite Heqe3. reflexivity.
  - destruct (n =? 5) eqn : Heqe5.
    + apply eqb_true in Heqe5. rewrite Heqe5. reflexivity.
    + discriminate eq.
Qed.  

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b eqn : Hb.
  - destruct (f true) eqn : Hft.
    + rewrite Hft. rewrite Hft. reflexivity.
    + destruct (f false) eqn : Hff.
      -- rewrite Hft. reflexivity.
      -- rewrite <- Hff in Hft. apply Hff.
  - destruct (f false) eqn : Hff.
    + destruct (f true) eqn : Hft.
      -- apply Hft.
      -- apply Hff.
    + destruct (f false) eqn : Hff2.
      -- discriminate Hff.
      -- apply Hff2.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros. generalize dependent m. induction n.
  - destruct m.
    + reflexivity.
    + reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. apply IHn.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros. apply eqb_true in H. apply eqb_true in H0.
  rewrite H0 in H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Theorem filter_exercise : 
  forall (X : Type) (test : X -> bool)
  (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros. destruct test eqn : Htest.
  - reflexivity.
  - induction l.
    + discriminate H.
    + simpl in H. destruct (test x0) eqn : Hd in H.
      -- injection H. intros. rewrite <- H1 in Htest.
      rewrite <- Htest. rewrite <- Hd. reflexivity.
      -- apply IHl in H. discriminate H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => match (test h) with
              | false => false
              | true => forallb test t
              end
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed. 
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed. 
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed. 
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed. 

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => match (test h) with
              | true => true
              | false => existsb test t
              end
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun n => negb (test n)) l).

Example test_existsb_1' : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2' : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3' : existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4' : existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
  intros. induction l.
  - reflexivity.
  - destruct (test x) eqn : Htx. 
    + simpl. rewrite Htx. unfold existsb'. destruct ((fun n : X => negb (test n)) x) eqn : Htn.
      -- rewrite Htx in Htn. simpl in Htn. discriminate Htn.
      -- simpl. rewrite Htn. reflexivity.
    + simpl. rewrite Htx.  unfold existsb'. destruct (forallb (fun n : X => negb (test n)) (x :: l)) eqn : Htn.
      -- simpl. simpl in Htn. rewrite Htx in Htn. simpl in Htn. rewrite IHl.
      unfold existsb'. rewrite Htn. reflexivity.
      -- simpl. simpl in Htn. rewrite Htx in Htn. simpl in Htn. rewrite IHl.
      unfold existsb'. rewrite Htn. reflexivity.
Qed.   