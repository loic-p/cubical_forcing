Require Import Arith.
Require Import Cubes.axioms
        Cubes.sprop_utils
        Cubes.arith_lemmas
        Cubes.hott_lemmas.

(** Definition of the cubes *)
(* we use the lawvere theory of 0, 1, ∨, ∧ with weakening, contraction and exchange
 n ~> m then corresponds to monotone functions 2^m -> 2^n *)

Definition finset (n : nat) : Set :=
  {m : nat | m < n}.

Theorem eq_finset {n : nat} (a b : finset n) : proj1_sig a = proj1_sig b -> a = b.
Proof.
  destruct a, b. simpl. intro H. etransitivity.
  apply (exist_transp (x := x) l H).
  rewrite (Peano_dec.le_unique (S x0) n (transport (fun m : nat => m < n) H l) l0). reflexivity.
Qed.


(* 2 ^ n *)
Definition cube (n : nat) : Set := finset n -> bool.

Definition degen_c {n : nat} (m : finset (S n)) : cube (S n) -> cube n.
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. now apply le_S.
  - apply x. exists (S i). now apply le_n_S.
  - apply x. exists (S i). now apply le_n_S.
Defined.

Definition face_c {n : nat} (m : finset (S n)) (d : bool) : cube n -> cube (S n).
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. eapply le_trans. exact H. now apply le_S_n.
  - exact d.
  - apply x. destruct i.
    + apply pos_ge_0 in H. destruct H.
    + exists i. apply le_S_n. exact q.
Defined.

Definition meet_c {n : nat} (m : finset n) : cube (S n) -> cube n.
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. now apply le_S.
  - apply andb.
    + apply x. exists i. now apply le_S.
    + apply x. exists (S i). now apply le_n_S.
  - apply x. exists (S i). now apply le_n_S.
Defined.

Definition join_c {n : nat} (m : finset n) : cube (S n) -> cube n.
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. now apply le_S.
  - apply orb.
    + apply x. exists i. now apply le_S.
    + apply x. exists (S i). now apply le_n_S.
  - apply x. exists (S i). now apply le_n_S.
Defined.

Definition exch_c {n : nat} (m : finset n) : cube (S n) -> cube (S n).
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_eq_lt_dec i m) as [[[H | H] | H] | H].
  - apply x. exists i. exact q.
  - apply x. exists (S m). now apply le_n_S.
  - apply x. exists m. now apply le_S.
  - apply x. exists i. exact q.
Defined.

Definition contr_c {n : nat} (m : finset n) : cube n -> cube (S n).
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_eq_lt_dec i m) as [[[H | H] | H] | H].
  - apply x. exists i. eapply le_trans. exact H. apply le_S_n. now apply le_S.
  - apply x. exists m. exact p.
  - apply x. exists m. exact p.
  - apply x. destruct i.
    + destruct (pos_ge_0 (S m) H).
    + exists i. now apply le_S_n.
Defined.

Inductive word : nat -> nat -> Type :=
| empty {a : nat} : word a a
| degen {a b : nat} : finset (S b) -> word a (S b) -> word a b
| face {a b : nat} : finset (S b) -> bool -> word a b -> word a (S b)
| meet {a b : nat} : finset b -> word a (S b) -> word a b
| join {a b : nat} : finset b -> word a (S b) -> word a b
| exch {a b : nat} : finset b -> word a (S b) -> word a (S b)
| contr {a b : nat} : finset b -> word a b -> word a (S b).

Fixpoint concat_word {a b c : nat} (w1 : word b c) (w2 : word a b) : word a c :=
  (match w1 in (word b c) return word a b -> word a c with
   | @empty x => (fun w : word a x => w)
   | @degen x y i w' => (fun w : word a x => degen i (concat_word w' w))
   | @face x y i d w' => (fun w : word a x => face i d (concat_word w' w))
   | @meet x y i w' => (fun w : word a x => meet i (concat_word w' w))
   | @join x y i w' => (fun w : word a x => join i (concat_word w' w))
   | @exch x y i w' => (fun w : word a x => exch i (concat_word w' w))
   | @contr x y i w' => (fun w : word a x => contr i (concat_word w' w))
   end) w2.

Fixpoint comp_word {a b : nat} (w : word a b) : cube a -> cube b :=
  match w with
  | empty => (fun x => x)
  | degen i w' => (degen_c i) o (comp_word w')
  | face i d w' => (face_c i d) o (comp_word w')
  | meet i w' => (meet_c i) o (comp_word w')
  | join i w' => (join_c i) o (comp_word w')
  | exch i w' => (exch_c i) o (comp_word w')
  | contr i w' => (contr_c i) o (comp_word w')
  end.




(** Lemmas about cubes *)

Theorem concat_id_left {a b : nat} (w : word a b) : concat_word empty w = w.
Proof.
  now compute.
Qed.

Theorem concat_id_right {a b : nat} (w : word a b) : concat_word w empty = w.
Proof.
  induction w ; simpl ; try rewrite IHw ; reflexivity.
Qed.

Theorem concat_assoc {a b c d : nat} (w1 : word c d) (w2 : word b c) (w3 : word a b) :
  concat_word w1 (concat_word w2 w3) = concat_word (concat_word w1 w2) w3.
Proof.
  induction w1 ; simpl ; try rewrite IHw1 ; reflexivity.
Qed.

Theorem comp_id {a : nat} : comp_word (@empty a) = fun x => x.
Proof.
  easy.
Qed.

Theorem concat_sound_s {a b c : nat} (w1 : word b c) (w2 : word a b) :
  comp_word w1 o comp_word w2 =s comp_word (concat_word w1 w2).
Proof.
  induction w1 ;
    simpl ;
    try (match goal with
         | |- ?XX o ?YY o ?ZZ =s ?RR => change (XX o (YY o ZZ) =s RR)
         end) ;
    try (specialize IHw1 with (w2:=w2)) ;
    try (destruct IHw1) ;
    apply refl_s.
Qed.

Theorem concat_sound {a b c : nat} (w1 : word b c) (w2 : word a b) :
  comp_word w1 o comp_word w2 = comp_word (concat_word w1 w2).
Proof.
  apply eqs_eq. apply concat_sound_s.
Qed.

Definition admissible {a b : nat} (f : cube a -> cube b) : SProp :=
  sexists_s (word a b) (fun w => (f =s comp_word w)).

Definition admissible' {a b : nat} (f : cube a -> cube b) :=
  { w : word a b | f = comp_word w }.

Theorem adm_id {a : nat} : admissible (fun x : cube a => x).
Proof.
  apply spair_s with (a:=empty). simpl.
  apply refl_s.
Qed.

Theorem adm_comp {a b c : nat} (f : cube a -> cube b) (g : cube b -> cube c) :
  admissible f -> admissible g -> admissible (g o f).
Proof.
  intros [w p] [w' q]. apply ssym in q. apply ssym in p.
  assert (admissible ((comp_word w') o (comp_word w))).
  - apply spair_s with (a:=concat_word w' w). apply concat_sound_s.
  - assert (admissible (g o (comp_word w))).
    apply (srewrite (fun g => admissible (g o comp_word w)) H q).
    apply (srewrite (fun f => admissible (g o f)) H0 p).
Qed.

Definition arrow (a b : nat) : Type :=
  @sexists (cube b -> cube a) admissible.

Definition compose {A B C : nat} (f : arrow B C) (g : arrow A B) : arrow A C :=
  (
    g.1s o f.1s ;
    adm_comp f.1s g.1s f.2s g.2s
  )s.

Notation "A ~> B" := (arrow A B) (at level 90, left associativity).

Notation "f 'ô' g" := (compose f g) (at level 50, left associativity).

Definition id {A : nat} : A ~> A :=
  (
    fun x => x ;
    adm_id
  )s.
