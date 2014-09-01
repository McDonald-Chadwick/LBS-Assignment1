Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition negb (b1:bool) : bool :=
  match b1 with
  | true => false
  | false => true
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => (negb b2)
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => false
  | true => b2
  end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check negb.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat):bool:=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3 ) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  |O , _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  |S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  |O => 1
  |S n' => (mult n  (factorial n'))
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m :nat) :bool :=
  match n with 
  | O => match m with
     | O => true
     | S m' => false
     end
  | S n' => match m with
     | O => false
     | S m' => beq_nat n' m'
     end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
    | O => false
    | S m' => ble_nat n' m'
    end
  end.


Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

(* Exercise: 2 starts (blt_nat) *)

Definition blt_nat (n m : nat) : bool :=
  match (beq_nat n m)  with
  | true => false
  | false => (beq_nat O (n - m))
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_1_1 : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite H.
  reflexivity. Qed.

(* Exercise: 1 star (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H_1 H_2.
  rewrite -> H_1 .
  rewrite -> H_2.
  reflexivity. Qed.

(* End Exercise *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(* Exercise: 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  rewrite <- plus_1_1.
  reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity. Qed.

(* Exercise: 1 star (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n.
  reflexivity.
  reflexivity. Qed.

Inductive bin : Type :=
  | Base : bin
  | Double (b:bin) : bin
  | DoubleOne (b:bin) : bin.

Fixpoint incbin (n : bin) : bin :=
  match n with
  | Base => DoubleOne n
  | Double n' => DoubleOne n'
  | DoubleOne n' => Double (incbin n') 
  end.

Fixpoint doubleNat (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (doubleNat n'))
  end.

Fixpoint binToNat (n : bin) : nat :=
  match n with
  | Base => O
  | Double n' => doubleNat (binToNat n')
  | DoubleOne n' => S (doubleNat (binToNat n'))
  end.

Example test_incbin1: (incbin Base) = DoubleOne (Base).
Proof. reflexivity. Qed.
Example test_incbin2: (incbin (DoubleOne Base) ) = (Double (DoubleOne Base)).
Proof. reflexivity. Qed.

Eval compute in binToNat Base.
Eval compute in binToNat (Double (DoubleOne Base)).
Eval compute in binToNat ( incbin (Double (DoubleOne Base))).
Eval compute in binToNat (incbin (incbin (incbin (incbin (incbin (incbin (incbin Base))))))).
Eval compute in incbin (incbin (incbin (incbin (incbin (incbin (incbin (incbin Base))))))).
