
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* Compute (next_weekday friday). *)


Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

 Check monday.


Inductive bool : Type :=
  | true
  | false.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | true, false => true
  | false, false => true
  | false, true => true
end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (b1, b2, b3) with 
  | (true, true, true) => true 
  | _ => false
end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check andb3.

Module TuplePlayground.
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
    : nybble.


End TuplePlayground.

Check (S (S (S (S 0)))).



Fixpoint factorial (n:nat) : nat :=
  match n with 
  | 0 => 1
  | S x => mult n (factorial x)
end.


Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.


Theorem plus_0_n :  forall n: nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H0.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Check plus_id_exercise.

Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.
