(* Exercise: 1 star, standard (nandb) *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (andb3) *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (factorial) *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(* Exercise: 1 star, standard (ltb) *)
Definition ltb (n m : nat) : bool :=
  match m with
  | O => false
  | S m' => leb n m'
  end.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H1.
  rewrite H.
  rewrite H1.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (mult_n_1) *)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  rewrite <- plus_O_n.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (identity_fn_applied_twice) *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (negation_fn_applied_twice) *)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (andb_eq_orb) *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b.
  - simpl in H.
    rewrite H.
    reflexivity.
  - simpl in H.
    rewrite H.
    reflexivity.
Qed.

Module LateDays.
Inductive letter : Type :=
  | A | B | C | D | F.
Inductive modifier : Type :=
  | Plus | Natural | Minus.
Inductive grade : Type :=
  Grade (l:letter) (m:modifier).
Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)
Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
end.

(* Exercise: 1 star, standard (letter_comparison) *)
Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros l.
  destruct l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
end.

(* Exercise: 2 stars, standard (grade_comparison) *)
Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | (Grade l1 m1), (Grade l2 m2) =>
    match (letter_comparison l1 l2) with
    | Eq => modifier_comparison m1 m2
    | Lt => Lt
    | Gt => Gt
    end
end.
Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
end.

(* Exercise: 2 stars, standard (lower_letter_lowers) *)
Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  intros H.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl in H.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Exercise: 2 stars, standard (lower_grade) *)
Definition lower_grade (g : grade) : grade :=
  match g with
  | (Grade l m) => match m with
    | Plus => (Grade l Natural)
    | Natural => (Grade l Minus)
    | Minus => match l with
      | A => (Grade B Plus)
      | B => (Grade C Plus)
      | C => (Grade D Plus)
      | D => (Grade F Plus)
      | F => (Grade F Minus)
      end
    end
  end.
Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. simpl. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.

(* Exercise: 3 stars, standard (lower_grade_lowers) *)
Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intro g.
  intro H.
  destruct g as [l m].
  - destruct m.
    * simpl. rewrite letter_comparison_Eq. reflexivity.
    * simpl. rewrite letter_comparison_Eq. reflexivity.
    * destruct l.
      ** simpl. reflexivity.
      ** simpl. reflexivity.
      ** simpl. reflexivity.
      ** simpl. reflexivity.
      ** rewrite lower_grade_F_Minus. rewrite H. reflexivity.
Qed.

End LateDays.
