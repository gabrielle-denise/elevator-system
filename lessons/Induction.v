From LF Require Export Basics.

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n as [|n' IHn'].
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.  
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IHn']. 
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed. 

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl. rewrite negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  replace (n + 0 + 0) with n.
  - reflexivity.
  - rewrite add_comm. rewrite add_0_r. reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed. 

Theorem add_shuffle3 : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros. rewrite add_comm. replace (n + p) with (p + n).
  - destruct m.
    + simpl. reflexivity.
    + simpl. rewrite add_assoc. reflexivity.
  - rewrite add_comm. reflexivity.
Qed. 

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  intros. induction n as [|n' IHn'].
  - rewrite mul_0_r. reflexivity.
  - simpl. rewrite add_comm. rewrite <- IHn'. rewrite mult_n_Sm. reflexivity.
Qed.

Theorem leb_refl : forall n : nat, (n <=? n) = true.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.  
Qed.

Theorem zero_neqb_S : forall n : nat, 0 =? (S n) = false.
Proof.
  intros. destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros. destruct b.
  - reflexivity.
  - reflexivity. 
Qed.

Theorem S_neqb_0 : forall n : nat, (S n) =? 0 = false.
Proof.
  intros. replace (S n =? 0) with (0 =? S n).
  - rewrite zero_neqb_S. reflexivity.
  - reflexivity.
Qed.  

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros. simpl. rewrite add_0_r. reflexivity.
Qed. 

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros. destruct b.
  - destruct c. reflexivity. reflexivity.
  - destruct c. reflexivity. reflexivity.    
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite add_comm. replace (p + n' * p + m * p) with ((n' * p + m * p) + p).
    + rewrite IHn'. reflexivity.
    + rewrite add_comm. rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn'. reflexivity.
Qed. 

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHb. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn. reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  intros. destruct n.
  - reflexivity.
  - reflexivity.  
Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z
  | _ => B0 b
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall b : bin, 
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros. induction b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Compute(double_bin (B0 Z)).

