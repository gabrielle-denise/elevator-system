From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X : Type) : Type :=
  | d (m : mumble)
  | e (x : X).

Check (d mumble (b a 5)).

End MumbleGrumble.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  intros. induction l as [|m l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l as [|o l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1 as [|m l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1 as [|m l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l as [|m l' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([],[])
  | (x, y) :: t => ((x :: fst (split t)), (y :: snd (split t)))
  end.

Example test_split:
  split [(1, false); (2, false)] = ([1; 2], [false; false]).
Proof. reflexivity. Qed.

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [1; 2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1]; [2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (even n) && (negb (n <=? 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) 
  (l : list X) : list X * list X :=
  ((filter test l), (filter (fun n => (negb (test n))) l)).

Example test_partition1 : partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2 : partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma map_rev_lemma : forall (X Y : Type) (f : X -> Y) (l : list X) (m : X),
  map f (l ++ [m]) = (map f l) ++ [f m].
Proof.
  intros. induction l as [|o l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.  

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l as [|m l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. rewrite map_rev_lemma. reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros. induction l as [|m l' IHl'].
  - reflexivity.  
  - simpl. rewrite <- IHl'. unfold fold_length. simpl. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun (a : X) (l' : list Y) => [f a] ++ l') l [].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros. induction l as [|m l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. unfold fold_map. simpl. reflexivity.
Qed.   

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros. unfold prod_uncurry. unfold prod_curry. reflexivity.
Qed.

Lemma surjective_pairing'' : forall (X Y : Type) (l : X * Y),
  l = (fst l, snd l).
Proof.
  intros. unfold fst. unfold snd. destruct l. reflexivity.
Qed.  

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. unfold prod_uncurry. unfold prod_curry. rewrite <- surjective_pairing''. reflexivity.
Qed.

Module Church. 

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition zero' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => zero. Definition one' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => succ zero. 
Definition two' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Example zero_church_peano : zero nat S O = 0. Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1. Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2. Proof. reflexivity. Qed.

Definition scc (n : cnat) : cnat :=
  fun X f x => f (n X f x).

Example scc_1 : scc zero = one. 
Proof. reflexivity. Qed. 
Example scc_2 : scc one = two.
Proof. reflexivity. Qed. 
Example scc_3 : scc two = three. 
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat :=
  fun X f x => n X f (m X f x).

Example plus_1 : plus zero one = one. 
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two. 
Proof. reflexivity. Qed.
Example plus_3 : plus (plus two two) three = plus one (plus three three). Proof. reflexivity. Qed.

Definition mult (n m : cnat) : cnat :=
  fun X f => n X (m X f).

Example mult_1 : mult one one = one. 
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero. Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three. 
Proof. reflexivity. Qed.

Definition exp (n m : cnat) : cnat := 
  fun X => m (X -> X) (n X).

Example exp_1 : exp two two = plus two two. 
Proof.  reflexivity. Qed.

Example exp_2 : exp three zero = one. 
Proof. reflexivity. Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one. 
Proof. reflexivity. Qed.

Compute ((exp two one) nat S 0).

Example exp_4 : (exp two three) nat S 0 = 8.
Proof. unfold exp. unfold three. unfold doit3times. reflexivity.
Qed.

Example mult_4 : (mult three two) nat S 0 = 6.
Proof. unfold mult. unfold three. unfold doit3times. unfold two. simpl. reflexivity.
Qed.

End Church.







