
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Set Default Goal Selector "!".

Fixpoint eqb (n m:nat) : bool :=
    match n with
    |O => match m with
          |O => true
          |S m => false
          end
    |S n => match m with
          |O => false
          |S m => eqb n m
          end
    end.

Fixpoint leb (n m:nat) : bool :=
    match n with
    |O => true
    |S n => match m with
            |O => false
            |S m => leb n m
            end
    end.

Fixpoint le (n m:nat) : bool :=
    match n with
    |O => match m with
            |O => false
            |S m => true
            end
    |S n => match m with
            |O => false
            |S m => le n m
            end
    end.

Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)(at level 60, right associativity).

Definition geb (n m : nat) := leb m n.

Definition gtb (n m : nat) := le m n.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Lemma gtb_reflect : forall x y, reflect (x > y) (gtb x y).
Proof.
  Admitted.

Lemma geb_reflect : forall x y, reflect (x >= y) (geb x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Example reflect_example1: forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intros. 
  assert (R : reflect (a < 5) (a <? 5)). 
    {
      apply ltb_reflect.
    }
  destruct R.
  + lia.
  + lia.
  Qed.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(*----------------------------------------------------------------------*)

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [ ] => [i]
  | h :: t => if leb i h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  |nil => O
  |cons h t => S (length t)
  end.

Inductive sorted : list nat -> Prop :=
  |sorted_nil : sorted [ ]
  |sorted_1 : forall x, sorted [x]
  |sorted_cons : forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

Definition sorted' (al : list nat) := forall i j,
  i < j < length al -> nth i al 0 <= nth j al 0.

Definition is_a_sorting_algorithm (f : list nat -> list nat) := forall al,
  Permutation al (f al) /\ sorted (f al).

(*

Lemma lem1 : forall a y l, a > y -> sorted (y::l) -> sorted (insert a (y :: l)) -> sorted (y :: insert a l).
Proof.
  intros. induction l. 
  - simpl. apply sorted_cons.
    ++ lia.
    ++ apply sorted_1.
  - simpl. bdestruct (leb a a0).
    ++ apply sorted_cons.
        -- lia.
        -- apply sorted_cons.
            +++ apply H2.
            +++ inversion H0. apply H7.
    ++ inversion H0. apply sorted_cons. 
        -- lia. 
        -- subst. apply 
*)

Lemma insert_sorted : forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
  + apply sorted_1.
  + bdestruct (leb a x).
    - apply sorted_cons.
      ++ apply H.
      ++ apply sorted_1.
    - apply sorted_cons.
      ++ lia.
      ++ apply sorted_1.
  + bdestruct (leb a x).
    - apply sorted_cons.
      ++ apply H0.
      ++ apply sorted_cons.
          -- apply H.
          -- apply S.
    - bdestruct (leb a x).
      ++ bdestruct (leb a y).
          -- apply sorted_cons.
              +++ lia.
              +++ apply sorted_cons.
                  ---- apply H2.
                  ---- apply S.
          -- lia.
      ++ bdestruct (leb a y).
          -- apply sorted_cons.
              +++ lia.
              +++ apply sorted_cons.
                  ---- apply H2.
                  ---- apply S.
          -- apply sorted_cons.
              +++ apply H.
              +++ simpl. unfold insert in IHS. bdestruct (leb a y).
                    ----- lia. 
                    ----- apply IHS. Qed.

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intros. simpl. induction l. 
    - simpl. apply sorted_nil.
    - simpl. apply insert_sorted. apply IHl. Qed.

Check perm_skip.
Check perm_trans.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.
Check app_nil_r.
Check app_comm_cons.
Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Lemma insert_perm: forall x l, Permutation (x :: l) (insert x l).
Proof.
  induction l.
  - simpl. apply Permutation_refl.
  - simpl. bdestruct (leb x a).
    ++ apply Permutation_refl.
    ++ assert (R: Permutation (x :: a :: l) (a :: x :: l)).
        { apply perm_swap. }
       rewrite -> R. apply perm_skip. apply IHl. Qed.

Lemma lem2 : forall a x y, Permutation x y -> Permutation (insert a x) (insert a y).
Proof.
  intros. simpl. inversion H. 
  - apply Permutation_refl.
  - simpl. bdestruct (leb a x0).
    + apply perm_skip. apply perm_skip. apply H0.
    + apply perm_skip. rewrite <- insert_perm. rewrite <- insert_perm. apply perm_skip. apply H0.
  - rewrite <- insert_perm. rewrite <- insert_perm. rewrite -> H0. rewrite -> H1. apply perm_skip. apply H.
  - rewrite <- insert_perm. rewrite <- insert_perm. apply perm_skip. apply H. Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros. induction l.
  - simpl. apply Permutation_refl.
  - simpl. rewrite -> insert_perm. apply lem2. apply IHl. Qed.

Theorem insertion_sort_correct: is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intros al. 
  split.
  + apply sort_perm.
  + apply sort_sorted.
  Qed.










