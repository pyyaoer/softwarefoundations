From LF Require Export Basics.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

(* Exercise: 2 stars, standard, especially useful (basic_induction) *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IH].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IH. rewrite plus_n_Sm. reflexivity.
Qed.
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
(* Exercise: 2 stars, standard (double_plus) *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite plus_n_Sm. reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqb_refl) *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (even_S) *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - rewrite IH. rewrite negb_involutive. simpl. reflexivity.
Qed.

(* Exercise: 2 stars, advanced, especially useful (add_comm_informal) *)
Theorem add_comm_informal: forall a b, a+b=b+a.
Proof.
  intros a b.
  induction a as [|a' IH].
  - simpl. induction b as [|b' IH1].
    * reflexivity.
    * simpl. rewrite <- IH1. reflexivity.
  - simpl. rewrite IH. induction b as [|b' IH2].
    * simpl. reflexivity.
    * simpl. rewrite plus_n_Sm. reflexivity.
Qed.
