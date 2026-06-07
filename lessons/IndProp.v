Set Warnings "-notation-overridden".
From LF Require Export Logic.


Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) : even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof. apply le_S. apply le_S. apply le_n. Qed.

Inductive clos_trans {X: Type} (R: X -> X -> Prop) : 
  X -> X -> Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
| po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  apply t_trans with (y := Cleo).
  apply t_step. apply po_SC.
  apply t_step. apply po_CM.
Qed.

Inductive clos_refl_trans {X: Type} (R: X -> X -> Prop) : 
  X -> X -> Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Definition cs (n m : nat) : Prop := csf n = m.

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example perm_refl : Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with (l2 := [2;1;3]).
  apply perm3_swap12.
  apply perm3_swap12.
Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) : ev n -> ev (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).

Module EvPlayground.
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).
End EvPlayground.

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof. intros. simpl. apply ev_SS. apply ev_SS. apply H. Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2 := [2;3;1]).
  - apply perm3_trans with (l2 := [2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with (l2 := [2;1;3]).
  apply perm3_swap12.
  apply perm3_swap23.
Qed.

Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros.
  apply perm3_trans with (l2 := [b;a;c]).
  apply perm3_swap12.
  apply perm3_swap12.
Qed.

Lemma ev_inversion : forall (n : nat),
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros. destruct H.
  - left. reflexivity.
  - right. exists n. split. reflexivity. apply H.
Qed.

Lemma le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros. destruct H.
  - left. reflexivity.
  - right. exists m. split. reflexivity. apply H.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros. apply ev_inversion in H. destruct H.
  - discriminate H.
  - destruct H. destruct H. injection H. intros. rewrite <- H1 in H0. apply H0.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros. inversion H. apply H1.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not. intros. apply ev_inversion in H.
  destruct H. discriminate H. destruct H. destruct H.
  discriminate H.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.

Theorem SSSSev__even' : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. apply ev_inversion in H. destruct H.
  - discriminate H.
  - destruct H. destruct H. apply ev_inversion in H0. destruct H0.
    + rewrite H0 in H. discriminate H.
    + destruct H0. destruct H0. rewrite H0 in H. apply ev_inversion in H1.
      -- destruct H1.
        ++ rewrite H1 in H. injection H. intros. rewrite H2. apply ev_0.
        ++ injection H. intros. destruct H1. destruct H1. rewrite <- H2 in H1. rewrite H1. apply ev_SS. apply H3.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. apply one_not_even in H3. destruct H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros. inversion H. reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros. inversion H.
Qed.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even.
  intros. 
  inversion H.
  - exists 0. reflexivity. 
Abort.

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros. induction H.
  - simpl. apply H0.
  - simpl. apply ev_SS. apply IHev.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros. induction H0.
  - simpl in H. apply H.
  - simpl in H. 
    apply evSS_ev in H.
    apply IHev in H.
    apply H.
Qed.

Lemma ev_plus_plus_lemma : forall n m p,
  n + m = n + p -> p = m.
Proof.
  intros. induction n.
  - simpl in H. symmetry in H. apply H.
  - simpl in H. injection H. intros. apply IHn in H0. apply H0.
Qed.      

Lemma ev_plus_plus_lemma2 : forall n m p,
  p = m -> n + m = n + p.
Proof.
  intros. induction n.
  - simpl. symmetry. apply H.
  - simpl. rewrite IHn. reflexivity.     
Qed.

Lemma ev_plus_plus_lemma3 : forall n,
  n + n = double n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite IHn. reflexivity.
Qed.  

Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros.
  assert (ev ((n + m) + (n + p))). {
    apply ev_sum with (n := n + m) (m := n + p). apply H. apply H0.
  }
  assert (n + m + (n + p) = n + n + (m + p)). {
    replace ((n + m) + (n + p)) with (n + (m + (n + p))).
    replace ((m + (n + p))) with ((m + n) + p).
    replace (m + n) with (n + m).
    replace (n + ((n + m) + p)) with ((n + n) + (m + p)).
    + reflexivity.
    + rewrite add_assoc. rewrite add_assoc. rewrite add_assoc. reflexivity.
    + rewrite add_comm. reflexivity. 
    + rewrite add_assoc. reflexivity.
    + rewrite add_assoc. reflexivity.
  }
  - rewrite H2 in H1. apply ev_ev__ev with (n := (n + n)) (m := (m + p)) in H1. apply H1. rewrite ev_plus_plus_lemma3. apply ev_double.
Qed.

Definition isDiagonal {X : Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> x = y.

Lemma closure_of_diagonal_is_diagonal: forall X 
  (R: X -> X -> Prop), isDiagonal R ->
  isDiagonal (clos_refl_trans R).
Proof.
  intros. unfold isDiagonal. intros. unfold isDiagonal in H.
  induction H0.
  - apply H in H0. apply H0.
  - reflexivity.
  - rewrite IHclos_refl_trans2 in IHclos_refl_trans1. apply IHclos_refl_trans1.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Lemma ev'_ev_lemma : forall n, S (S n) = n + 2.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.   

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros. split.
  - intros. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros. induction H.
    + apply ev'_0.
    + rewrite ev'_ev_lemma. apply ev'_sum. apply IHev. apply ev'_2.
Qed.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros. induction H.
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply perm3_trans with (l2 := l2). apply IHPerm3_2. apply IHPerm3_1.   
Qed.

Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
  Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros. induction H.
  - simpl in H0. destruct H0.
    + rewrite H. simpl. right. left. reflexivity.
    + destruct H.
      -- rewrite H. simpl. left. reflexivity.
      -- destruct H.
        ++ rewrite H. simpl. right. right. left. reflexivity.
        ++ destruct H.
  - simpl in H0. destruct H0.
    + rewrite H. simpl. left. reflexivity.
    + destruct H.
      -- rewrite H. simpl. right. right. left. reflexivity.
      -- destruct H.
        ++ rewrite H. simpl. right. left. reflexivity.
        ++ destruct H.
  - apply IHPerm3_1 in H0. apply IHPerm3_2 in H0. apply H0.
Qed.

Lemma Perm3_NotIn_Lemma : forall (A B C : Prop),
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros. apply H0. apply H. apply H1.  
Qed. 

Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 ->  ~ In x l1 -> ~ In x l2.
Proof.
  intros. unfold not. unfold not in H0.
  intros. induction H.
  - apply H0. simpl. simpl in H1. destruct H1.
    + rewrite H. right. left. reflexivity.
    + destruct H.
      -- rewrite H. left. reflexivity.
      -- destruct H.
        ++ rewrite H. right. right. left. reflexivity.
        ++ destruct H.
  - apply H0. simpl. simpl in H1. destruct H1.
    + rewrite H. left. reflexivity.
    + destruct H.
      -- rewrite H. right. right. left. reflexivity.
      -- destruct H. rewrite H. right. left. reflexivity. destruct H.
  - pose proof Perm3_NotIn_Lemma as Hz.
    specialize Hz with (A := In x l1 -> False).
    specialize Hz with (B := (In x l2 -> False)).
    specialize Hz with (C := In x l3 -> False).
    apply Hz in IHPerm3_1.
    + destruct IHPerm3_1.
    + apply IHPerm3_2.
    + apply H0.
    + apply H1.
Qed.  
 
Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  unfold not. intros.
  apply Perm3_In with (x := 3) in H.
  - simpl in H. destruct H.
    + discriminate H.
    + destruct H.
      -- discriminate H.
      -- destruct H.
        ++ discriminate H.
        ++ destruct H.
  - simpl. right. right. left. reflexivity.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2. 
Qed.

End Playground.

Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).
Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

Theorem O_le_n : forall n, 0 <= n.
Proof.
  intros. induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed. 

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Lemma le_plus_0 : forall a, a <= a + 0.
Proof.
  intros. destruct a.
  - simpl. apply le_n.
  - simpl. rewrite add_0_r. apply le_n.
Qed.

Lemma Sn_lemma : forall m, 1 <= S m.
Proof.
  intros. induction m.
  - apply le_n.
  - apply le_S. apply IHm.
Qed.  

Lemma Sn_lemma2 : forall n, S (S n) <= 1 -> False.
Proof.
  intros. induction n.
  - inversion H. inversion H2.
  - apply IHn. inversion H. inversion H2.
Qed.     

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. generalize dependent m. induction n.
  - intros. induction m.
    + apply le_n.
    + apply le_S. apply IHm. apply Sn_lemma.
  - intros. induction m.
    + apply Sn_lemma2 in H. destruct H.
    + inversion H.
      -- apply le_n.
      -- apply le_S. apply IHm. apply H2.
Qed.          

Theorem le_plus_l : forall a b, a <= a + b.
Proof.
  intros. generalize dependent a. induction b.
  - simpl. apply le_plus_0.
  - induction a.
    + simpl. apply O_le_n.
    + simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.   

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H. induction H0.
  - apply le_n.
  - apply le_S in H0. apply H0.
  - apply IHle. apply le_S in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.

Lemma plus_le_lemma : forall a b,
  S a + b = S (a + b).
Proof.
  intros. induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa. reflexivity.
Qed.      

Lemma plus_le_lemma2 : forall n m o,
  S n + S m <= o -> n + S m <= o.
Proof.
  intros. destruct n.
  - simpl. simpl in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
  - apply le_S in H.
    assert ( S (S n) + S m = S ( (S n) + S m)). {
      apply plus_le_lemma with (a := (S n)) (b := S m).
    }
    rewrite H0 in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.    

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros. split.
  - induction n2.
    + assert (n1 + 0 = n1). { apply add_0_r. }
      rewrite H0 in H. apply H.
    + apply IHn2.
      assert (n1 + S n2 = S(n1 + n2)). { rewrite plus_n_Sm. reflexivity. }
      rewrite H0 in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H.
      apply H.
  - generalize dependent n1. induction n2.
    + intros. apply O_le_n.
    + induction n1.
      -- intros. simpl in H. apply H.
      -- intros. apply IHn1.
        ++ apply plus_le_lemma2 in H. apply H.
Qed.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros. generalize dependent p. generalize dependent q. generalize dependent m. induction n.
  - intros. left. apply O_le_n.
  - destruct p.
    + intros. simpl in H. rewrite <- plus_le_lemma in H. 
      apply plus_le in H. destruct H. right. apply H0.
    + intros. destruct q.
      -- simpl in H. rewrite add_0_r in H. rewrite <- plus_le_lemma in H. apply plus_le in H. destruct H. left. apply H.
      -- destruct m.
        ++ right. apply O_le_n.
        ++ rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H. apply Sn_le_Sm__n_le_m in H. rewrite plus_le_lemma in H. rewrite plus_le_lemma in H. apply Sn_le_Sm__n_le_m in H. apply IHn in H. destruct H.
          --- left. apply n_le_m__Sn_le_Sm in H. apply H.
          --- right. apply n_le_m__Sn_le_Sm in H. apply H.
Qed.              

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros. induction p.
  - simpl. apply H.
  - assert (S p + n = S (p + n)). { apply plus_le_lemma. }
    assert (S p + m = S (p + m)). { apply plus_le_lemma. }
    rewrite H0. rewrite H1. apply n_le_m__Sn_le_Sm in IHp. apply IHp.
Qed.  

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros. induction p.
  - rewrite add_0_r. rewrite add_0_r. apply H.
  - rewrite <- plus_n_Sm. rewrite <- plus_n_Sm.
    apply n_le_m__Sn_le_Sm in IHp. apply IHp.
Qed.   

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros. induction p.
  - rewrite add_0_r. apply H.
  - apply le_S in IHp.
    assert (S (m + p) = m + S p). {apply plus_n_Sm. }
    rewrite H0 in IHp. apply IHp.
Qed.

Theorem lt_ge_cases : forall n m, n < m \/ n >= m.
Proof.
  intros. unfold "<". unfold ">=".
  induction n.
    - destruct m.
      + right. apply le_n.
      + left. apply Sn_lemma.
    - destruct IHn.
      + destruct m eqn : Hm.
        -- right. apply O_le_n.
        -- inversion H.
          ++ right. apply le_n.
          ++ apply n_le_m__Sn_le_Sm in H2. left. apply H2.
      + right. apply le_S. apply H.
Qed.                

Theorem n_lt_m__n_le_m : forall n m,
  n < m -> n <= m.
Proof.
  intros. intros. 
  unfold "<" in H. destruct n.
  - apply O_le_n.
  - apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.      

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros. unfold "<" in H. split.
  - unfold "<". generalize dependent m. generalize dependent n2.
    induction n1.
    + intros. simpl in H. induction n2. 
      -- apply H. 
      -- apply IHn2. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
    + intros.
      assert ((S (S n1 + n2)) = S (S n1) + n2). {
        rewrite <- plus_le_lemma. reflexivity. 
      }
      rewrite H0 in H. induction n2.
      -- rewrite add_0_r in H. apply H.
      -- apply IHn2.
        ++ rewrite <- plus_n_Sm in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
        ++ rewrite <- plus_le_lemma. reflexivity.
  - unfold "<".  assert (n1 + n2 = n2 + n1). {apply add_comm. } rewrite H0 in H. generalize dependent m. generalize dependent n1. induction n2.
    + intros. simpl in H. induction n1.
      -- apply H.
      -- apply IHn1. 
        ++ simpl. rewrite add_0_r. reflexivity.
        ++ apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
    + intros.
      assert ((S (S n2 + n1)) = S (S n2) + n1). {
        rewrite <- plus_le_lemma. reflexivity. 
      }
      rewrite H1 in H. induction n1.
      -- rewrite add_0_r in H. apply H.
      -- apply IHn1.
        ++ apply add_comm.
        ++ rewrite <- plus_n_Sm in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
        ++ rewrite <- plus_le_lemma. reflexivity.
Qed.

Lemma leb_iff_sublemma1 : forall n,
  (S (S n) <=? 1) = true -> False.
Proof.
  intros. destruct n.
  - discriminate H.
  - discriminate H.    
Qed. 

Lemma leb_iff_lemma1 : forall n m,
  (S n <=? S m) = true -> (n <=? m) = true.
Proof.
  intros. generalize dependent m. induction n.
  - destruct m.
    + intros. reflexivity.
    + intros. reflexivity.
  - destruct m.
    + intros. apply leb_iff_sublemma1 in H. destruct H.
    + intros. apply IHn in H. inversion H. reflexivity.
Qed.

Lemma leb_iff_sublemma2 : forall m,
  (0 <=? S m) = true -> (1 <=? S (S m)) = true.
Proof.
  intros. destruct m.
  + reflexivity.
  + reflexivity.
Qed. 

Lemma leb_iff_lemma2 : forall n m,
  (n <=? m) = true -> (S n <=? S m) = true.
Proof.
  intros. generalize dependent m. induction n.
  - destruct m.
    + intros. reflexivity.
    + intros. 
      assert ((0 <=? S m) = true -> (1 <=? S (S m)) = true). 
      {apply leb_iff_sublemma2. }
      apply H0. apply H.
  - destruct m.
    + intros. discriminate H.
    + intros. apply IHn. apply leb_iff_lemma1 in H. apply H.
Qed.               

Lemma leb_iff_lemma3 : forall n m,
  (n <=? m) = true -> (n <=? S m) = true.
Proof.
  intros. generalize dependent m. induction n.
  - destruct m.
    + intros. reflexivity.
    + intros. reflexivity.
  - destruct m.
    + intros. discriminate H.
    + intros. apply leb_iff_lemma2. apply IHn.
    apply leb_iff_lemma1 in H. apply H.
Qed.    

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros. generalize dependent m. induction n.
  - destruct m.
    + intros. apply le_n.
    + intros. apply O_le_n.
  - destruct m.
    + intros. discriminate H.
    + intros. apply n_le_m__Sn_le_Sm. apply IHn.
      apply leb_iff_lemma1. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> n <=? m = true.
Proof.
  - intros. generalize dependent m. induction n.
    + reflexivity.
    + destruct m.
      -- intros. inversion H.
      -- intros. apply IHn. apply Sn_le_Sm__n_le_m in H. apply H.
  (* alternative proof: inversion H.
        ++ apply leb_refl.
        ++ apply IHm in H2. apply leb_iff_lemma3 in H2. apply H2.*)
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros. split.
  - intros. apply leb_complete in H. apply H.
  - intros. apply leb_correct. apply H.
Qed.            

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros. apply leb_iff in H. apply leb_iff in H0.
  apply le_trans with (m := n) (n := m) (o := o) in H.
  apply leb_iff in H. apply H. apply H0.
Qed.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R m n o ) : R (S m) (S n) (S (S o))
  | c5 m n o (H : R m n o ) : R n m o.

Definition fR : nat -> nat -> nat :=
  fun (m n : nat) => m + n.

Theorem add_1_r : forall n, n + 1 = S n.
Proof.
  intros. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Lemma myhelpersix : forall m n : nat, fR m (S n) = S (fR m n).
Proof.
  intros. destruct m.
  - destruct n.  
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct n.
    + simpl. rewrite add_1_r. rewrite add_0_r. reflexivity.
    + simpl. rewrite <- add_1_r. 
      assert (h1 : S (S (fR m (S n))) = fR m (S n) + 1 + 1).
      {
        rewrite <- add_1_r. rewrite <- add_1_r. reflexivity.
      }
      assert (h2 : fR m (S (S n)) + 1 = fR m (S n) + 1 + 1).
      {
        rewrite <- add_1_r. rewrite add_assoc. reflexivity.
      }
      rewrite h1. rewrite h2. reflexivity. Qed.

Lemma myhelperseven : forall m n o, 
  fR (S m) (S n) = S (S o) -> fR m n = o.
Proof.
  intros. simpl in H. rewrite myhelpersix in H. injection H.
  intros. apply H0. Qed.

Lemma myhelpersevenprime : forall m n o, 
  fR m n = o -> fR (S m) (S n) = S (S o).
Proof.
  intros. simpl. rewrite myhelpersix. rewrite H. reflexivity. Qed.

Lemma myhelpereight : forall n, R 0 n n.
Proof.
  intros. induction n as [|n' IHn'].
  - simpl. apply c1.
  - simpl. apply c3. apply IHn'. Qed.

Lemma myhelpernine : forall n, R n 0 n.
Proof.
  intros. induction n as [|n' IHn'].
  - simpl. apply c1.
  - simpl. apply c2. apply IHn'. Qed.

Lemma extrahelper : forall m n, S (m + S (S n)) = S (S (S (m + n))).
Proof.
  intros. rewrite <- add_1_r. rewrite <- add_1_r. rewrite <- add_1_r.
  rewrite add_assoc. rewrite add_assoc. rewrite add_1_r. rewrite add_1_r.
  rewrite add_1_r. reflexivity. Qed.

Lemma anotherhelper : forall m n, (S (m + S n)) = S (S (m + n)).
Proof.
  intros. rewrite <- add_1_r. rewrite <- add_1_r. rewrite add_assoc.
  rewrite add_1_r. rewrite add_1_r. reflexivity. Qed.

Lemma myhelperten : forall m n, R (S m) (S n) (S (m + S n)).
Proof.
  intros. induction n as [|n' IHn'].
  - simpl. rewrite add_1_r. apply c4. apply myhelpernine.
  - simpl. rewrite extrahelper. apply c3. rewrite anotherhelper in IHn'.
    apply IHn'. Qed.

Lemma myhelpereleven : forall m n, R (S m) n (S (m + n)).
Proof.
  intros. induction n as [|n' IHn'].
  - rewrite add_0_r. apply c2. apply myhelpernine.
  - simpl. apply myhelperten. Qed.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros. split.
  - intros. induction H.
    + simpl. reflexivity.
    + simpl. rewrite IHR. reflexivity.
    + simpl. rewrite <- IHR. rewrite myhelpersix. reflexivity.
    + apply myhelpersevenprime. apply IHR.
    + rewrite add_comm. apply IHR.
  - intros. 
    assert (h1: fR m n = m + n).
    { reflexivity. }
    rewrite H in h1.
    rewrite h1.
    generalize dependent o.
    induction m as [|m' IHm'].
    + simpl. intros. apply myhelpereight.
    + simpl. intros. apply myhelpereleven. Qed.

Inductive subseq : list nat -> list nat -> Prop :=
| s0 (l : list nat) : subseq [] l
| sc (x : nat) (l1 : list nat) (l2 : list nat) : 
  subseq l1 l2 -> subseq (x :: l1) (x :: l2)
| ss (x : nat) (l1 : list nat) (l2 : list nat) :
  subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros. induction H.
  - apply s0.
  - simpl. apply sc. apply IHsubseq.
  - simpl. apply ss. apply IHsubseq.
Qed.    

Lemma subseq_trans :
  forall l1 l2 l3,
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  generalize dependent l1.
  induction H0.
  - intros. inversion H. apply s0.
  - intros. inversion H.
    + apply s0.
    + apply sc. apply IHsubseq. apply H3.
    + apply ss. apply IHsubseq. apply H3.
  - intros. apply ss. apply IHsubseq. apply H.
Qed.

Inductive total_relation : nat -> nat -> Prop :=
  | te (n : nat) : total_relation n n
  | tl (n : nat) (m : nat) : total_relation n m -> total_relation n (S m)
  | tm (n : nat) (m : nat) : total_relation n m -> total_relation (S n) m.

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
  intros. generalize dependent m. induction n.
  - induction m.
    + apply te.
    + apply tl. apply IHm.
  - induction m.
    + specialize IHn with (m := 0). apply tm. apply IHn.
    + specialize IHn with (m := (S m)). apply tl in IHm. apply IHm.
Qed.

Inductive empty_relation : nat -> nat -> Prop := 
  | er (n m : nat) : (~ (total_relation n m)) -> empty_relation n m.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
  Proof.
  intros. unfold not. intros. destruct H. unfold not in H.
  apply H. apply total_relation_is_total. Qed.
    


    




 

