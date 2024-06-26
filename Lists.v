From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Notation "( x , y )" := (pair x y).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.
Fixpoint minus (n m : nat) : nat :=
         match n, m with
         | O   , _    => O
         | S _ , O    => n
         | S n', S m' => minus n' m'
         end.
Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intro p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intro p. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y).
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* Exercise: 2 stars, standard, especially useful (list_funs) *)
Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: l' => nonzeros l'
  | h :: l' => h :: (nonzeros l')
  end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: l' => match (odd h) with
    | true => h :: (oddmembers l')
    | false => oddmembers l'
    end
  end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.
Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

(* Exercise: 3 stars, advanced (alternate) *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | nil, t :: l2' => t :: l2'
  | t :: l1', nil => t :: l1'
  | t1 :: l1', t2 :: l2' => t1 :: t2 :: (alternate l1' l2')
  end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

(* Exercise: 3 stars, standard, especially useful (bag_functions) *)
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | h :: s' => match (eqb h v) with
    | true => S (count v s')
    | false => count v s'
    end
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.
Definition sum : bag -> bag -> bag :=
  alternate.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Definition add (v : nat) (s : bag) : bag :=
  v :: s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | nil => false
  | h :: s' => match (eqb h v) with
    | true => true
    | false => member v s'
    end
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 3 stars, standard, optional (bag_more_functions) *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: s' => match (eqb h v) with
    | true => s'
    | false => h:: remove_one v s'
    end
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.
Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: s' => match (eqb h v) with
    | true => remove_all v s'
    | false => h :: remove_all v s'
    end
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.
Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | h :: s1' => match (member h s2) with
    | false => false
    | true => included s1' (remove_one h s2)
    end
  end.
Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 2 stars, standard, especially useful (add_inc_count) *)
Theorem add_inc_count : forall l:bag, forall v:nat, length (v::l) = S(length l).
Proof.
intros l v. simpl. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

(* Exercise: 3 stars, standard (list_exercises) *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intro l.
  induction l as [| n l' H].
  - reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l1' H1].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite H1. rewrite app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l.
  induction l as [| n l' H].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite H. reflexivity.
Qed.
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as  [| n l1' H1].
  - simpl. rewrite app_assoc. reflexivity.
  - simpl. rewrite H1. reflexivity.
Qed.
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as  [| n l1' H1].
  - simpl. reflexivity.
  - simpl. destruct n as [|n'].
    * rewrite H1. reflexivity.
    * simpl. rewrite H1. reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqblist) *)
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
    | nil => true
    | h2::l2' => false
    end
  | h1::l1' => match l2 with
    | nil => true
    | h2::l2' => match (eqb h1 h2) with
      | true => eqblist l1' l2'
      | false => false
      end
    end
   end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intro l.
  induction l as [|n l' H].
  - simpl. reflexivity.
  - simpl. rewrite <- H. induction n as [| n' H2].
    * simpl. reflexivity.
    * simpl. rewrite <- H2. reflexivity.
Qed.

(* Exercise: 1 star, standard (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intro s. simpl. reflexivity. Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(* Exercise: 3 stars, advanced (remove_does_not_increase_count) *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intro s.
  induction s as [| n s' H].
  - simpl. reflexivity.
  - simpl. destruct n as [| n'].
    * simpl. rewrite leb_n_Sn. reflexivity.
    * simpl. rewrite H. reflexivity.
Qed.

(* Exercise: 3 stars, advanced (involution_injective) *)
Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H1 n1 n2 H2.
  rewrite H1.
  rewrite <- H2.
  rewrite <- H1.
  reflexivity.
Qed.

(* Exercise: 2 stars, advanced (rev_injective) *)
Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite rev_involutive.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* Exercise: 2 stars, standard (hd_error) *)
Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.
  
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard, optional (option_elim_hd) *)
Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l as [|n l'].
  - reflexivity.
  - simpl. reflexivity.
Qed.
End NatList.

Inductive id : Type :=
  | Id (n : nat).
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(* Exercise: 1 star, standard (eqb_id_refl) *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intro x.
  destruct x as [n].
  - simpl. induction n as [| n' H].
    * reflexivity.
    * simpl. rewrite H. reflexivity.
Qed.

Module PartialMap.
Export NatList. (* make the definitions from NatList available here *)
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* Exercise: 1 star, standard (update_eq) *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite eqb_id_refl. reflexivity.
Qed.

(* Exercise: 1 star, standard (update_neq) *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl. rewrite H. reflexivity.
Qed.

End PartialMap.