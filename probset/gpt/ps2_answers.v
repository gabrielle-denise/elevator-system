(* ps2_answers.v *)
(* Problem Set 10, total of 10 pts. *)

Set Warnings "-notation-overridden".
From LF Require Import Maps.
From LF Require Export Imp.
From LF Require Export Hoare.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.

Example one :
  {{ Y = 3 }}
    X := 3
  {{ Y = X }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

Example two :
  {{ Y = X + 1 }}
    X := X + 1
  {{ Y = X }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

Example three :
  {{ Y > 0 }}
    X := Y + 3
  {{ X > 3 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

Example four :
  {{ X = 5 }}
    X := X + 1
  {{ X > 0 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

Example five :
  {{ X > 2 }}
    X := X + 1;
    X := X + 2
  {{ X > 5 }}.
Proof.
  eapply hoare_seq with (Q := {{ X > 3 }}).
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.

Axiom axone: forall X a (st : state), ((st X > a) /\ (st X <=? a) = true) -> False.

Example six :
  {{ X > 2 }}
  if X > 2 then Y := 1 else Y := 0 end
  {{ Y = 1}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update, bassertion.
      intros st H.
      destruct H as [HX Hnot].
      simpl in *.
      destruct (st X <=? 2) eqn:Hle.
      * exfalso.
        apply (axone X 2 st).
        split.
        -- apply HX.
        -- apply Hle.
      * exfalso.
        apply Hnot.
        reflexivity.
Qed.

Example seven :
  {{ X >= 0 }}
  while X > 0 do X := X - 1 end
  {{ X = 0 }}.
Proof.
  eapply hoare_consequence_pre with (P' := {{ True }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * assertion_auto''.
    + unfold "->>", bassertion.
      intros st [_ Hnot].
      simpl in *.
      destruct (st X) as [| x'].
      * reflexivity.
      * exfalso. apply Hnot. reflexivity.
  - assertion_auto''.
Qed.

Example eight :
  {{ True }}
  X := 0;
  Y := 0;
  while (~ (X = Z)) do
    X := X + 1;
    Y := Y + ((2 * X)-1)
  end
  {{ Y = Z * Z }}.
Proof.
  eapply hoare_seq with (Q := {{ X = 0 }}).
  - eapply hoare_seq with (Q := {{ Y = X * X }}).
    + eapply hoare_consequence_post.
      * apply hoare_while.
        eapply hoare_seq with (Q := {{ Y + ((2 * X) - 1) = X * X }}).
        -- eapply hoare_consequence_pre.
           ++ apply hoare_asgn.
           ++ assertion_auto''.
        -- eapply hoare_consequence_pre.
           ++ apply hoare_asgn.
           ++ unfold "->>", assertion_sub, t_update, bassertion.
              intros st H.
              destruct H as [Hinv Hguard].
              simpl in *.
              nia.
      * unfold "->>", bassertion.
        intros st H.
        destruct H as [Hinv Hnot].
        simpl in *.
        destruct (st X =? st Z) eqn:Heq.
        -- apply eqb_eq in Heq.
           rewrite Hinv. rewrite Heq. reflexivity.
        -- exfalso. apply Hnot. reflexivity.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.

Example nine :
  {{ Z > 0 }}
  X := 1;
  Y := X * (X + 1);
  while (~ (X = Z)) do
    X := X + 1;
    Y := Y + (2 * X)
  end
  {{ Y = Z * (Z + 1)}}.
Proof.
  eapply hoare_seq with (Q := {{ X = 1 /\ Z > 0 }}).
  - eapply hoare_seq with (Q := {{ Y = X * (X + 1) }}).
    + eapply hoare_consequence_post.
      * apply hoare_while.
        eapply hoare_seq with (Q := {{ Y + (2 * X) = X * (X + 1) }}).
        -- eapply hoare_consequence_pre.
           ++ apply hoare_asgn.
           ++ assertion_auto''.
        -- eapply hoare_consequence_pre.
           ++ apply hoare_asgn.
           ++ unfold "->>", assertion_sub, t_update, bassertion.
              intros st H.
              destruct H as [Hinv Hguard].
              simpl in *.
              nia.
      * unfold "->>", bassertion.
        intros st H.
        destruct H as [Hinv Hnot].
        simpl in *.
        destruct (st X =? st Z) eqn:Heq.
        -- apply eqb_eq in Heq.
           rewrite Hinv. rewrite Heq. reflexivity.
        -- exfalso. apply Hnot. reflexivity.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.

Example ten :
  {{ Z > 0 }}
  X := 1;
  Y := 0;
  while (~((X - 1) = Z)) do
    Y := Y + (2 * X);
    X := X + 1
  end
  {{ Y = Z * (Z + 1)}}.
Proof.
  eapply hoare_seq with (Q := {{ X > 0 /\ X = 1 /\ Z > 0 }}).
  - eapply hoare_seq with (Q := {{ X > 0 /\ Y = (X - 1) * X }}).
    + eapply hoare_consequence_post.
      * apply hoare_while.
        eapply hoare_seq with
          (Q := {{ X + 1 > 0 /\ Y = ((X + 1) - 1) * (X + 1) }}).
        -- eapply hoare_consequence_pre.
           ++ apply hoare_asgn.
           ++ assertion_auto''.
        -- eapply hoare_consequence_pre.
           ++ apply hoare_asgn.
           ++ unfold "->>", assertion_sub, t_update, bassertion.
              intros st H.
              destruct H as [Hpos Hinv].
              simpl in *.
              nia.
      * unfold "->>", bassertion.
        intros st H.
        destruct H as [Hinv Hnot].
        destruct Hinv as [HXpos Hinv].
        simpl in *.
        destruct (st X - 1 =? st Z) eqn:Heq.
        -- apply eqb_eq in Heq.
           rewrite Hinv.
           nia.
        -- exfalso. apply Hnot. reflexivity.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.
