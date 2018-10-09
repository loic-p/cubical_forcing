Require Import String.
Require Import List.
Require Import Omega.

Require Import Template.monad_utils
        Template.Ast
        Template.AstUtils
        Template.Template
        Template.LiftSubst
        Template.Checker
        Template.Typing
        Template.Induction.

Require Import Forcing.TemplateForcing
        Forcing.translation_utils
        Forcing.Inductives.

Require Import FunctionalExtensionality.

Set Primitive Projections.

Definition fcompose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun x : A => f (g x).

Notation "f 'o' g" := (fcompose f g) (at level 50, left associativity).

Definition funext {A B : Type} := @functional_extensionality A B.
Definition funext_dep {A : Type} {B : A -> Type} := @functional_extensionality_dep A B.
Definition proof_irr {A : Prop} {a b : A} : a = b. Admitted.
Definition admitok : False. Admitted.


(** SProp manipulation and notations *)

Inductive sBox (P : SProp) : Prop :=
| wrap : P -> sBox P.

Theorem unwrap (P : SProp) (b : sBox P) : P.
Proof.
  destruct b. exact H.
Qed.

Inductive eq_s {A : Type} : A -> A -> SProp :=
| refl_s : forall a : A, eq_s a a.

Notation "A '=s' B" := (eq_s A B) (at level 65, left associativity).

Theorem eqs_eq {A : Type} {a b : A} : a =s b -> a = b.
Proof.
  intro H. destruct H. reflexivity.
Qed.

Theorem eq_eqs {A : Type} {a b : A} : a = b -> a =s b.
Proof.
  intro H. apply unwrap. rewrite H. apply wrap. apply refl_s.
Qed.

Theorem ssym {A : Type} {a b : A} (p : eq_s a b) : eq_s b a.
Proof.
  destruct p. apply refl_s.
Qed.

Theorem srewrite {A : Type} {a b : A} (P : A -> SProp) (α : P a) (p : a =s b) : P b.
Proof.
  destruct p. exact α.
Qed.

Inductive sexists_s (A : Type) (B : A -> SProp) : SProp :=
| spair_s : forall a : A, B a -> sexists_s A B.

Record sexists {A : Type} (B : A -> SProp) : Type :=
  {
    spi1 : A ;
    spi2 : B spi1
  }.

Print sexists.

Inductive sFalse : SProp :=.

Notation "x .1s" := x.(spi1 _) (at level 3).
Notation "x .2s" := x.(spi2 _) (at level 3).

Notation "( a ; b )s" := {| spi1 := a ; spi2 := b |}.

Theorem eq_sexist {A : Type} {P : A -> SProp} (a b : sexists P) (e : a.1s = b.1s) :
  a = b.
  destruct a, b. simpl in e. destruct e. reflexivity.
Qed.





(** HoTT lemmas for equality manipulation *)

Definition transport {A : Type} (P : A -> Type) {a b : A} : a = b -> P a -> P b.
Proof.
  intro H. destruct H. intro H. exact H.
Defined.

Definition sym {A : Type} {a b : A} : a = b -> b = a.
Proof.
  intro H. destruct H. reflexivity.
Defined.

Definition trans {A : Type} {a b c : A} : a = b -> b = c -> a = c.
Proof.
  intro H. destruct H. intro H. exact H.
Defined.

Theorem trans_id {A : Type} {a b : A} {e : a = b} : trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Qed.

Theorem id_trans {A : Type} {a b : A} {e : a = b} : trans eq_refl e = e.
Proof.
  reflexivity.
Qed.

Theorem trans_sym {A : Type} {a b : A} {e : a = b} : trans e (sym e) = eq_refl.
Proof.
  destruct e. reflexivity.
Qed.

Theorem sym_trans {A : Type} {a b : A} (e : a = b) : trans (sym e) e = eq_refl.
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_id {A : Type} {P : A -> Type} {a : A} {x : P a}
  : transport P eq_refl x = x.
Proof.
  reflexivity.
Qed.

Theorem transport_trans {A : Type} (P : A -> Type) {a b c : A} (e : a = b) (e' : b = c) (x : P a)
  : transport P (trans e e') x = transport P e' (transport P e x).
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_sym_trans {A : Type} (P : A -> Type) {a b : A} (e : a = b) (x : P b)
  : transport P (trans (sym e) e) x = x.
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_trans_sym {A : Type} (P : A -> Type) {a b : A} (e : a = b) (x : P a)
  : transport P (trans e (sym e)) x = x.
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_ap {A P a b} (f : forall x : A, P x) (e : a = b) : transport P e (f a) = f b.
Proof.
  destruct e. reflexivity.
Qed.

Theorem apD10 {A B} (f g : forall x : A, B x) : f = g -> forall x : A, f x = g x.
Proof.
  intro e. destruct e. intro x. reflexivity.
Qed.

Theorem exist_transp {A} {P : A -> Prop} {x y} (a : P x) (e : x = y) : exist P x a = exist P y (transport P e a).
Proof.
  destruct e. reflexivity.
Qed.

Theorem ap_transport {A x y} (P Q : A -> Type) {a : P x} {e : x = y} (f : forall x : A, P x -> Q x)
  : f y (transport P e a) = transport Q e (f x a).
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_domain {A B a b} {P : A -> Type} {e : a = b} {y : P b} (f : P a -> B)
  : transport (fun x : A => P x -> B) e f y = f (transport P (sym e) y).
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_codomain {A B a b} {y : B} {P : A -> Type} {e : a = b} (f : B -> P a)
  : transport (fun x : A => B -> P x) e f y = transport P e (f y).
Proof.
  destruct e. reflexivity.
Qed.



(** Redefinition of simple arithmetic *)

(* The definitions already present in the standard library are very complicated and take ages to quote *)

Theorem le_0_n : forall n, 0 <= n.
Proof.
  intro n. induction n.
  - apply le_n.
  - apply le_S. exact IHn.
Qed.

Theorem lt_0_succ : forall n, 0 < S n.
Proof.
  intro n. induction n.
  - now apply le_n.
  - apply le_S. exact IHn.
Qed.

Theorem pos_ge_0 : forall n, S n <= 0 -> False.
Proof.
  intros n H. inversion H.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m. revert n. induction m.
  - intros n H. inversion H.
    + apply le_n.
    + apply pos_ge_0 in H1. destruct H1.
  - intros n H. inversion H.
    + apply le_n.
    + apply IHm in H1. apply le_S. exact H1.
Qed.

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  intros n m. revert n. induction m.
  - intros n H. inversion H. apply le_n.
  - intros n H. inversion H.
    + apply le_n.
    + apply le_S. now apply IHm.
Qed.

Theorem add_0_r : forall n, n + 0 = n.
Proof.
  intro n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_S : forall n m : nat, n + S m = S (n + m).
Proof.
  intro n. induction n.
  - intro m. reflexivity.
  - intro m. simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intro n. induction n.
  - intro m. rewrite (add_0_r m). reflexivity.
  - intro m. simpl. rewrite IHn. rewrite add_S. reflexivity.
Qed.

Theorem le_plus_n : forall n m p, p + n <= p + m -> n <= m.
Proof.
  intros n m. induction p.
  - intro H. exact H.
  - intro H. simpl in H. apply le_S_n in H. exact (IHp H).
Qed.

Definition le_imp_eq_lt : forall n m : nat, n <= m -> (n = m) + (n < m).
  intro n. induction n.
  - intros m H. destruct m.
    + left. reflexivity.
    + right. apply lt_0_succ.
  - intros m H. destruct m.
    + apply pos_ge_0 in H. destruct H.
    + destruct (IHn m).
      * now apply le_S_n.
      * rewrite e. left. reflexivity.
      * right. now apply le_n_S.
Defined.

Definition lt_eq_lt_dec :  forall n m : nat, {n < m} + {n = m} + {m < n}.
  intros n m. induction m.
  - assert (0 <= n). apply le_0_n. apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + now right.
  - destruct IHm as [[H | H] | H].
    + left. left. now apply le_S.
    + rewrite H. left. left. now apply le_n.
    + apply le_imp_eq_lt in H. destruct H.
      * left. right. now rewrite e.
      * right. exact l.
Defined.

Definition le_lt_dec : forall n m : nat, {n <= m} + {m < n}.
  intros n m. destruct (lt_eq_lt_dec n m) as [[H | H] | H].
  - left. apply le_S_n. apply le_S. exact H.
  - left. rewrite H. apply le_n.
  - right. exact H.
Defined.

Definition lt_eq_lt_dec' :  forall n m : nat, {n < m} + {n = m} + {m < n}.
  intros n m. induction n.
  - assert (0 <= m). apply le_0_n. apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + left. now left.
  - destruct IHn as [[H | H] | H].
    + apply le_imp_eq_lt in H. destruct H.
      * left. right. exact e.
      * left. left. exact l.
    + rewrite H. right. now apply le_n.
    + right. now apply le_S.
Defined.

Definition lt_eq_eq_lt_dec (m n : nat) : {m < n} + {m = n} + {m = S n} + {m > S n}.
Proof.
  destruct (lt_eq_lt_dec m n) as [[H | H] | H].
  - left. left. now left.
  - left. left. now right.
  - apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + right. exact l.
Defined.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p. revert n m. induction p.
  - destruct m.
    + trivial.
    + intros H H'. apply pos_ge_0 in H'. destruct H'.
  - intros n m H. destruct m, n.
    + intro H'. apply le_0_n.
    + apply pos_ge_0 in H. destruct H.
    + intro H'. apply le_0_n.
    + intro H'. apply le_S_n in H. apply le_S_n in H'. apply le_n_S.
      eapply IHp. apply H. exact H'.
Qed.

Theorem sub_add_S {a b c : nat} : S b <= a -> a - S b + S c = a - b + c.
Proof.
  revert c. induction b.
  - intros c H. destruct a.
    + inversion H.
    + simpl. rewrite <- Minus.minus_n_O. apply add_S.
  - intros c H. destruct a.
    + inversion H.
    + simpl. apply eq_add_S.
      change (S (a - S b + S c)) with (S (a - S b) + S c). erewrite Minus.minus_Sn_m.
      change (S (a - b + c)) with (S (a - b) + c). erewrite Minus.minus_Sn_m.
      apply IHb.
      * apply le_S_n. eapply le_trans. exact H. apply le_S. apply le_n.
      * apply le_S_n. apply le_S_n. eapply le_trans. exact H. apply le_S. apply le_n.
      * now apply le_S_n.
Qed.

Theorem sub_sub {a b c : nat} : b <= a -> c <= b -> a - (b - c) = a - b + c.
Proof.
  revert c. induction b.
  - intros c Hb Hc. inversion Hc. easy.
  - intros c Hb Hc. destruct c.
    + simpl. easy.
    + simpl. erewrite IHb.
      * symmetry. apply sub_add_S. exact Hb.
      * apply le_S_n. eapply le_trans. exact Hb. apply le_S. apply le_n.
      * apply le_S_n. exact Hc.
Qed.







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





(** Decidability of a function being cubic *)

(* uses the fact that for the full category of cubes, being admissible is the same as being monotone *)
(* WIP *)

Definition zero_finset (p : nat) : finset (S p).
  exists 0. easy.
Defined.

Definition unique : cube 0.
  unfold cube. unfold finset. intros [m H]. apply pos_ge_0 in H. inversion H.
Defined.

Definition cube_le {a : nat} (c d : cube a) : Prop :=
  forall x : finset a, (c x = true) -> (d x = true).

Definition monotone {a b : nat} (f : cube a -> cube b) :=
  forall c d : cube a, cube_le c d -> cube_le (f c) (f d).

Definition admissible' {a b : nat} (f : cube a -> cube b) :=
  { w : word a b | f = comp_word w }.

Definition extend_cube {a : nat} (c : cube a) (b : bool) : cube (S a).
  intros [i p]. destruct i.
  - exact b.
  - apply le_S_n in p. apply c. exists i. exact p.
Defined.

Definition restr_map {a : nat} (f : cube (S a) -> cube 1) (b : bool) : cube a -> cube 1 :=
  fun x : cube a => f (extend_cube x b).

Theorem monotone_restr {a : nat} (f : cube (S a) -> cube 1) (b : bool) (H : monotone f)
  : monotone (restr_map f b).
Proof.
  intros c d H1. apply H.
  intros [x p]. destruct x.
  - easy.
  - simpl. apply H1.
Qed.

Definition fuse_cube {a b : nat} : (cube a) * (cube b) -> cube (a + b).
  intros [c d] [p i]. destruct (Compare_dec.le_lt_dec a p).
  - assert (p - a < b). easy.
    apply d. exists (p - a). exact H.
  - apply c. exists p. exact l.
Defined.

Definition split_cube {a b : nat} : cube (a + b) -> (cube a) * (cube b).
  intro c. split.
  - intros [x p]. apply c. exists x. easy.
  - intros [x p]. apply c. exists (x + a). easy.
Defined.

Fixpoint dup_word_aux1 {a : nat} (b : nat) (c : nat) (Hb : b <= a) (Hc : c <= b) : word (S b + a) (S b + a).
  destruct c.
  - exact empty.
  - simpl. apply exch.
    + exists (a - b + c). destruct b.
      * inversion Hc.
      * rewrite <- sub_sub. apply le_trans with (m := S a).
        -- apply le_n_S. apply PeanoNat.Nat.le_sub_l.
        -- simpl. apply le_n_S. easy.
        -- exact Hb.
        -- apply le_S. apply le_S_n. exact Hc.
    + apply (dup_word_aux1 a b c Hb). easy.
Defined.

Definition dup_map_aux1 {a : nat} (b : nat) (c : nat) (Hb : b <= a) (Hc : c <= b) : cube (S b + a) -> cube (S b + a).
  intro d. intros [x Hx].
  destruct (lt_eq_lt_dec (a - b + c) x) as [[H | H] | H].
  - apply d. exists x. exact Hx.
  - apply d. exists (a - b). apply le_trans with (m := S (a - b + c)).
    + apply le_n_S. apply Plus.le_plus_l.
    + rewrite H. exact Hx.
  - destruct (le_lt_dec (a - b) x).
    + apply d. exists (S x). simpl. apply le_n_S. eapply le_trans.
      * exact H.
      * apply le_trans with (m := a + c). apply Plus.plus_le_compat_r. apply PeanoNat.Nat.le_sub_l.
        rewrite add_comm. apply Plus.plus_le_compat_r. exact Hc.
    + apply d. exists x. exact Hx.
Defined.

Theorem dup_adm_aux1 {a : nat} (b : nat) (c : nat) (Hb : b <= a) (Hc : c <= b)
  : comp_word (dup_word_aux1 b c Hb Hc) = dup_map_aux1 b c Hb Hc.
Proof.
  revert Hc. induction c.
  - intro Hc. apply funext. intro d. apply funext. intros [x Hx]. simpl.
    destruct (lt_eq_lt_dec (a - b + 0) x) as [[H | H] | H].
    + easy.
    + pose H as H'. clearbody H'. rewrite add_0_r in H'. apply f_equal.
      apply eq_finset. simpl. symmetry. exact H'.
    + destruct (le_lt_dec (a - b) x).
      * assert False. easy. inversion H0.
      * reflexivity.
  - intro Hc. apply funext. intro d. apply funext. intros [x Hx]. simpl. rewrite IHc.
    match goal with
    | |- (?FF o ?GG) ?XX ?YY = _ => change ((FF o GG) XX) with (FF (GG XX))
    end. unfold dup_map_aux1.
    destruct (lt_eq_lt_dec (a - b + S c) x) as [[H | H] | H].
    + destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[H1 | H1] | H1].
      * assert False. destruct H1 ; easy. inversion H0.
      * easy.
      * destruct (lt_eq_lt_dec (a - b + c) x) as [[H2 | H2] | H2].
        -- reflexivity.
        -- easy.
        -- easy.
    + destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[[H1 | H1] | H1] | H1].
      * easy.
      * easy.
      * destruct (lt_eq_lt_dec (a - b + c) (a - b + c)) as [[H2 | H2] | H2].
        -- easy.
        -- apply f_equal. apply eq_finset. simpl. reflexivity.
        -- easy.
      * easy.
    + destruct (le_lt_dec (a - b) x).
      * destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[[H1 | H1] | H1] | H1].
        -- destruct (lt_eq_lt_dec (a - b + c) x) as [[H2 | H2] | H2].
           ++ easy.
           ++ easy.
           ++ apply f_equal. apply eq_finset. simpl. reflexivity.
        -- destruct (lt_eq_lt_dec (a - b + c) (S (a - b + c))) as [[H2 | H2] | H2].
           ++ apply f_equal. apply eq_finset. simpl. easy.
           ++ easy.
           ++ easy.
        -- easy.
        -- easy.
      * destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[[H1 | H1] | H1] | H1].
        -- destruct (lt_eq_lt_dec (a - b + c) x) as [[H2 | H2] | H2].
           ++ easy.
           ++ easy.
           ++ reflexivity.
        -- easy.
        -- easy.
        -- easy.
Qed.

Fixpoint dup_word_aux2 {a : nat} (b : nat) (Hb : b <= a) : word a (b + a).
  destruct b.
  - exact empty.
  - eapply concat_word.
    + apply (dup_word_aux1 b b). easy. apply le_n.
    + simpl. apply contr.
      * exists (a - (S b)). eapply PeanoNat.Nat.le_trans.
        -- apply PeanoNat.Nat.sub_lt. exact Hb.
           easy.
        -- rewrite add_comm. exact (PeanoNat.Nat.le_add_r a b).
      * apply (dup_word_aux2 a b). easy.
Defined.

Definition dup_map_aux2 {a : nat} (b : nat) (Hb : b <= a) : cube a -> cube (b + a).
  intros d [x Hx].
  destruct (le_lt_dec a x).
  - apply d. exists (x - b). apply le_plus_n with (p := b). rewrite add_S. rewrite <- Minus.le_plus_minus.
    + exact Hx.
    + eapply le_trans. exact Hb. exact l.
  - apply d. exists x. exact l.
Defined.

Theorem dup_adm_aux2 {a : nat} (b : nat) (Hb : b <= a) : comp_word (dup_word_aux2 b Hb) = dup_map_aux2 b Hb.
Proof.
  revert Hb. induction b.
  - intro H. apply funext. intro d. apply funext. intros [x Hx].
    simpl. destruct (le_lt_dec a x).
    + easy.
    + apply f_equal. apply eq_finset. simpl. reflexivity.
  - intro Hb. apply funext. intro d. apply funext. intros [x Hx]. simpl.
    rewrite <- concat_sound.
    unfold fcompose. etransitivity. refine (apD10 _ _ _ _). refine (apD10 _ _ _ _).
    apply dup_adm_aux1. cbn. rewrite IHb. cbn. destruct (le_lt_dec a x).
    + destruct (lt_eq_lt_dec (a - b + b) x) as [[H | H] | H].
      * destruct (lt_eq_eq_lt_dec x (a - S b)) as [[[H1 | H1] | H1] | H1].
        -- easy.
        -- easy.
        -- easy.
        -- destruct x.
           ++ easy.
           ++ simpl. destruct (le_lt_dec a x).
              ** apply f_equal. apply eq_finset. simpl. reflexivity.
              ** easy.
      * destruct (lt_eq_eq_lt_dec (a - b) (a - S b)) as [[[H1 | H1] | H1] | H1].
        -- easy.
        -- easy.
        -- destruct (le_lt_dec a (a - S b)).
           ++ easy.
           ++ apply f_equal. apply eq_finset. simpl. easy.
        -- easy.
      * easy.
    + destruct (lt_eq_lt_dec (a - b + b) x) as [[H | H] | H].
      * easy.
      * easy.
      * destruct (le_lt_dec (a - b) x).
        -- destruct (lt_eq_eq_lt_dec (S x) (a - S b)) as [[[H1 | H1] | H1] | H1] ; try reflexivity ; easy.
        -- destruct (lt_eq_eq_lt_dec x (a - S b)) as [[[H1 | H1] | H1] | H1].
           ++ reflexivity.
           ++ destruct (le_lt_dec a (a - S b)).
              ** easy.
              ** apply f_equal. apply eq_finset. simpl. easy.
           ++ easy.
           ++ easy.
Qed.

Definition dup_word (a : nat) : word a (a + a).
  apply dup_word_aux2. easy.
Defined.

Definition dup_map (a : nat) : cube a -> cube (a + a).
  intros d [x Hx].
  destruct (le_lt_dec a x).
  - apply d. exists (x - a). apply le_plus_n with (p := a). rewrite add_S. rewrite <- Minus.le_plus_minus.
    + exact Hx.
    + exact l.
  - apply d. exists x. exact l.
Defined.

Theorem dup_adm (a : nat) : comp_word (dup_word a) = dup_map a.
Proof.
  unfold dup_word. rewrite dup_adm_aux2.
  apply funext. intro d. apply funext. intros [x Hx].
  simpl. destruct (le_lt_dec a x).
  - apply f_equal. apply eq_finset. simpl. reflexivity.
  - reflexivity.
Qed.

Fixpoint tensor_word_aux {a b} c d (w : word a b) : word (c + a + d) (c + b + d).
  destruct w.
  - exact empty.
  - apply degen.
    + destruct f as [x Hx]. exists (c + x). apply le_n_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. apply le_S_n. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - refine (transport (fun X => word _ (X + d)) (sym (add_S _ _)) _). simpl. apply face.
    + destruct f as [x Hx]. exists (c + x). apply le_n_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. apply le_S_n. assumption. apply Nat.le_add_r.
    + exact b0.
    + exact (tensor_word_aux a b c d w).
  - apply meet.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - apply join.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - refine (transport (fun X => word _ (X + d)) (sym (add_S _ _)) _). simpl. apply exch.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - refine (transport (fun X => word _ (X + d)) (sym (add_S _ _)) _). simpl. apply contr.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + exact (tensor_word_aux a b c d w).
Defined.

Definition tensor_map_aux {a b} c d (f : cube a -> cube b) : cube (c + a + d) -> cube (c + b + d).
  intros γ [x Hx].
  destruct (le_lt_dec c x).
  - destruct (le_lt_dec (c + b) x).
    + apply γ. exists (x - b + a). rewrite <- Nat.add_assoc. rewrite (add_comm a d). rewrite Nat.add_assoc.
      apply plus_lt_compat_r. apply le_plus_n with (p := b).
      rewrite add_comm. simpl. rewrite Nat.sub_add. rewrite add_comm. rewrite <- Nat.add_assoc.
      rewrite (add_comm d b). rewrite Nat.add_assoc. exact Hx. apply le_trans with (m := c + b).
      apply le_plus_r. exact l0.
    + apply f.
      * intros [y Hy]. apply γ. exists (c + y). apply le_trans with (m := c + a).
        apply Plus.plus_lt_compat_l. exact Hy. apply Nat.le_add_r.
      * exists (x - c). eapply le_plus_n with (p := c). apply le_trans with (m := S x). rewrite add_S. apply le_n_S.
      rewrite <- Minus.le_plus_minus. apply le_n. exact l. exact l0.
  - apply γ. exists x. apply PeanoNat.Nat.lt_lt_add_r. apply PeanoNat.Nat.lt_lt_add_r. exact l.
Defined.

Lemma transport_finset {a b x : nat} {e : a = b} (f : nat -> nat) {H : x < f a} :
  transport (fun X : nat => finset (f X)) e (exist (fun m => m < f a) x H) = exist _ x (transport (fun m => x < f m) e H).
Proof.
  destruct e. reflexivity.
Qed.

Theorem tensor_adm_aux {a b c d} (w : word a b) : comp_word (tensor_word_aux c d w) = tensor_map_aux c d (comp_word w).
Proof.
  revert c d. induction w ; intros c d ; apply funext ; intro γ ; apply funext ; intros [x Hx] ; simpl.
  { destruct (le_lt_dec c x). destruct (le_lt_dec (c + a) x).
    all: apply f_equal ; apply eq_finset ; simpl ; easy. }
  all: destruct f as [y Hy].
  - unfold fcompose. etransitivity.
    { refine (apD10 _ _ _ _). apply f_equal. refine (apD10 _ _ _ γ).
      refine (ap_transport _ _ (e := add_S c b) (fun X Y => comp_word (b := X + d) Y)). }
    cbn. rewrite IHw. rewrite transport_codomain.
    destruct (lt_eq_lt_dec x (c + y)) as [[H | H] | H].
    all: etransitivity ; [ refine (transport_domain _) | ].
    all: etransitivity ; [ refine (f_equal _ _) ; refine (transport_finset (fun X => X + d)) | ].
    all: unfold tensor_map_aux.
    all: repeat match goal with
    | |- context [ match ?d with _ => _ end ] =>
      destruct d
    end.
    all: try (f_equal ; apply eq_finset ; simpl ; try (destruct c) ; easy).
    all: try omega.
  (** * Now all other cases should be roughly the same *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Definition tensor_word {a b a' b'} (w : word a b) (w' : word a' b') : word (a + a') (b + b').
  eapply concat_word.
  - exact (tensor_word_aux 0 b' w).
  - simpl. refine (transport (fun X => word X (a + b')) (add_0_r (a + a')) _).
    refine (transport (fun X => word (a + a' + 0) X) (add_0_r (a + b')) _).
    exact (tensor_word_aux a 0 w').
Defined.

Definition tensor_map {a b a' b'} (w : cube a -> cube b) (w' : cube a' -> cube b') : cube (a + a') -> cube (b + b').
  intros d [x Hx].
  destruct (le_lt_dec b x).
  - apply w'.
    + intros [y Hy]. apply d. exists (a + y). apply plus_lt_compat_l. exact Hy.
    + exists (x - b). apply plus_lt_reg_l with (p := b). rewrite le_plus_minus_r ; assumption.
  - apply w.
    + intros [y Hy]. apply d. exists y. apply Nat.lt_lt_add_r. exact Hy.
    + exists x. exact l.
Defined.

Lemma transport_cube {a b : nat} {e : a = b} (c : cube a) (d : finset b)
  : transport cube e c d = c (transport finset (sym e) d).
Proof.
  destruct e. reflexivity.
Qed.

Lemma transport_cube' {a b x : nat} {e : a = b} (c : cube a) (H : x < b)
  : transport cube e c (exist (fun m => m < b) x H) = c (exist _ x (transport (fun m => x < m) (sym e) H)).
Proof.
  destruct e. reflexivity.
Qed.

Theorem tensor_adm {a b a' b'} (w : word a b) (w' : word a' b')
  : comp_word (tensor_word w w') = tensor_map (comp_word w) (comp_word w').
Proof.
  unfold tensor_word. rewrite <- concat_sound.
  unfold fcompose. apply funext. intro d. etransitivity.
  { match goal with
    | |- ?XX ?YY ?ZZ = _ => refine (apD10 _ _ _ ZZ)
    end. refine (tensor_adm_aux _). }
  etransitivity.
  { apply f_equal. refine (apD10 _ _ _ d). etransitivity.
    refine (ap_transport _ _ (fun X Y => comp_word (a := X) Y)). apply f_equal. etransitivity.
    refine (ap_transport _ _ (fun X Y => comp_word (b := X) Y)). apply f_equal. refine (tensor_adm_aux _). }
  etransitivity.
  { apply f_equal. etransitivity. apply transport_domain.
    set (y := (transport cube (sym (add_0_r (a + a'))) d)). apply transport_codomain. }
  apply funext. intros [x Hx]. simpl.
  destruct (le_lt_dec 0 x) ; try omega. unfold tensor_map_aux. destruct (le_lt_dec b x).
  - etransitivity. apply transport_cube'. destruct (le_lt_dec a (x - b + a)) ; try omega.
    destruct (le_lt_dec (a + b') (x - b + a)) ; try omega. f_equal.
    + apply funext. intros [y Hy]. etransitivity. apply transport_cube'. f_equal.
      apply eq_finset. simpl. reflexivity.
    + apply eq_finset. simpl. omega.
  - f_equal.
    + apply funext. intros [y Hy]. etransitivity. apply transport_cube'. destruct (le_lt_dec a y) ; try omega.
      etransitivity. apply transport_cube'. f_equal. apply eq_finset. simpl. reflexivity.
    + apply eq_finset. simpl. easy.
Qed.

Definition product_word {a b b'} (w : word a b) (w' : word a b') : word a (b + b').
  eapply concat_word.
  - exact (tensor_word w w').
  - exact (dup_word a).
Defined.

(* Definition product_map {a b b'} (f : cube a -> cube b) (g : cube ) *)

Definition binary_and_word : word 2 1.
  apply meet.
  - exact (zero_finset 0).
  - exact empty.
Defined.

Definition binary_and_map : cube 2 -> cube 1.
  intros d x. apply andb.
  - apply d. exact (zero_finset 1).
  - apply d. exists 1. easy.
Defined.

Theorem binary_and_adm : comp_word (binary_and_word) = binary_and_map.
Proof.
  apply funext. intro d. apply funext. intros [x Hx]. simpl. unfold fcompose.
  destruct x ; try omega.
  unfold binary_and_map. f_equal.
  - f_equal. apply eq_finset. simpl. reflexivity.
  - f_equal. apply eq_finset. simpl. reflexivity.
Qed.

Definition binary_or_word : word 2 1.
  apply join.
  - exact (zero_finset 0).
  - exact empty.
Defined.

Definition binary_or_map : cube 2 -> cube 1.
  intros d x. apply orb.
  - apply d. exact (zero_finset 1).
  - apply d. exists 1. easy.
Defined.

Theorem binary_or_adm : comp_word (binary_or_word) = binary_or_map.
Proof.
  apply funext. intro d. apply funext. intros [x Hx]. simpl. unfold fcompose.
  destruct x ; try omega.
  unfold binary_or_map. f_equal.
  - f_equal. apply eq_finset. simpl. reflexivity.
  - f_equal. apply eq_finset. simpl. reflexivity.
Qed.

Definition simpl_word_aux {a : nat} (w : word a 1) : word (S a) 1.
  eapply concat_word.
  - exact binary_and_word.
  - change (S a) with (1 + a). change 2 with (1 + 1).
    apply tensor_word.
    + exact empty.
    + exact w.
Defined.

Definition simpl_map_aux {a : nat} (f : cube a -> cube 1) : cube (S a) -> cube 1.
  intros d x. apply andb.
  - apply f. apply degen_c.
    + exact (zero_finset a).
    + exact d.
    + exact x.
  - apply d. exact (zero_finset a).
Defined.

Theorem restr_adm {a : nat} {b : bool} {w : word (S a) 1}
  : comp_word (concat_word w (face (zero_finset a) b empty)) = restr_map (comp_word w) b.
Proof.
  rewrite <- concat_sound. apply funext. intro d.
  unfold restr_map. unfold fcompose. f_equal.
  apply funext. intros [x Hx]. simpl. unfold fcompose. destruct x ; reflexivity.
Qed.

Theorem simpl_adm_aux {a : nat} (w : word a 1)
  : comp_word (simpl_word_aux w) = simpl_map_aux (comp_word w).
Proof.
  unfold simpl_word_aux. rewrite <- concat_sound. unfold fcompose. apply funext ; intro d.
  rewrite binary_and_adm. etransitivity.
  { apply f_equal. refine (apD10 _ _ _ d).
    change (S a) with (1 + a). change 2 with (1 + 1).
    exact (tensor_adm empty w). }
  apply funext. intros [x Hx]. destruct x ; try omega.
  unfold simpl_map_aux. unfold binary_and_map. rewrite Bool.andb_comm at 1.
  remember (d (zero_finset a)) as b. destruct b.
  - f_equal.
    + simpl. f_equal.
      * apply funext. intros [y Hy]. destruct y ; f_equal ; apply eq_finset ; reflexivity.
      * apply eq_finset. reflexivity.
    + simpl. rewrite Heqb. apply f_equal. apply eq_finset. reflexivity.
  - rewrite Bool.andb_false_r. apply Bool.andb_false_intro2.
    simpl. rewrite Heqb. f_equal. apply eq_finset. reflexivity.
Qed.

Definition simpl_word {a : nat} (w w' : word a 1) : word (S a) 1.
  eapply concat_word.
  - exact binary_or_word.
  - change 2 with (1 + 1). apply product_word.
    + exact (simpl_word_aux w).
    + eapply concat_word. exact w'. apply degen.
      * exact (zero_finset a).
      * exact empty.
Defined.

Definition simpl_map {a : nat} (f g : cube a -> cube 1) : cube (S a) -> cube 1.
  intros d x. apply orb.
  - apply andb.
    + apply f.
      * apply degen_c.
        -- exact (zero_finset a).
        -- exact d.
      * exact x.
    + apply d. exact (zero_finset a).
  - apply g.
    + apply degen_c.
      * exact (zero_finset a).
      * exact d.
    + exact x.
Defined.

Theorem simpl_adm {a : nat} (w w' : word a 1)
  : comp_word (simpl_word w w') = simpl_map (comp_word w) (comp_word w').
Proof.
  unfold simpl_word. rewrite <- concat_sound. unfold fcompose. apply funext. intro d.
  rewrite binary_or_adm. etransitivity.
  { apply f_equal. refine (apD10 _ _ _ d). unfold product_word. rewrite <- concat_sound.
    unfold fcompose. apply funext. intro e.
    rewrite dup_adm. etransitivity. refine (apD10 _ _ _ (dup_map (S a) e)).
    exact (tensor_adm (simpl_word_aux w) (concat_word w' (degen (zero_finset a) empty))).
    rewrite simpl_adm_aux. rewrite <- concat_sound. reflexivity. }
  unfold simpl_map. unfold binary_or_map. apply funext. intros [x Hx]. destruct x ; try omega.
  - f_equal.
    + unfold simpl_map_aux. simpl. f_equal. f_equal.
      * apply funext. intros [y Hy]. destruct y.
        -- destruct (le_lt_dec (S a) 1) ; try omega. f_equal. apply eq_finset. reflexivity.
        -- destruct (le_lt_dec (S a) (S (S y))) ; try omega. f_equal. apply eq_finset. reflexivity.
      * apply eq_finset. reflexivity.
      * f_equal. apply eq_finset. reflexivity.
    + unfold simpl_map_aux. unfold fcompose. simpl. unfold fcompose. f_equal.
      * apply funext. intros [y Hy]. destruct y.
        -- destruct (le_lt_dec (S a) (S (a + 1))) ; try omega. f_equal. apply eq_finset. simpl. omega.
        -- destruct (le_lt_dec (S a) (S (a + (S (S y))))) ; try omega. f_equal. apply eq_finset. simpl. omega.
      * apply eq_finset. reflexivity.
Qed.

Theorem simpl_monotone {a : nat} (f : cube (S a) -> cube 1) (Hf : monotone f)
  : simpl_map (restr_map f true) (restr_map f false) = f.
Proof.
  apply funext. intro d. apply funext. intros [x Hx].
  unfold simpl_map. remember (d (zero_finset a)) as e. destruct e.
  - rewrite Bool.andb_true_r. unfold restr_map.
    assert (cube_le (extend_cube (degen_c (zero_finset a) d) false) (extend_cube (degen_c (zero_finset a) d) true)).
    { intros [y Hy]. destruct y.
      - simpl. intro H. reflexivity.
      - simpl. destruct y.
        + easy.
        + easy. }
    unfold monotone in Hf.
    specialize (Hf (extend_cube (degen_c (zero_finset a) d) false) (extend_cube (degen_c (zero_finset a) d) true) H).
    specialize (Hf (exist (fun m : nat => m < 1) x Hx)).
    assert ((extend_cube (degen_c (zero_finset a) d) true) = d).
    { apply funext. intros [y Hy]. destruct y.
      - simpl. rewrite Heqe. f_equal. apply eq_finset. reflexivity.
      - simpl. destruct y ; f_equal ; apply eq_finset ; reflexivity. }
    rewrite <- H0 at 3.
    destruct (f (extend_cube (degen_c (zero_finset a) d) false) (exist (fun m : nat => m < 1) x Hx)).
    + rewrite Bool.orb_true_r. symmetry. apply Hf. reflexivity.
    + rewrite Bool.orb_false_r. reflexivity.
  - rewrite Bool.andb_false_r. rewrite Bool.orb_false_l. unfold restr_map. f_equal.
    apply funext. intros [y Hy]. simpl. destruct y.
    + rewrite Heqe. f_equal. apply eq_finset. reflexivity.
    + destruct y ;f_equal ; apply eq_finset ; reflexivity.
Qed.

Theorem recover_word_1 {a : nat} (f : cube a -> cube 1) (Hf : monotone f) : { w : word a 1 | f = comp_word w }.
Proof.
  revert f Hf. induction a ; intros f Hf.
  - remember (f unique (zero_finset 0)) as fu. destruct fu.
    + unshelve refine (exist _ _ _).
      * exact (face (zero_finset 0) true empty).
      * apply funext. intro d. apply funext. intros [x Hx]. destruct x ; try omega.
        simpl. unfold fcompose. rewrite Heqfu. f_equal.
        apply funext. intros [y Hy]. omega. apply eq_finset. reflexivity.
    + unshelve refine (exist _ _ _).
      * exact (face (zero_finset 0) false empty).
      * apply funext. intro d. apply funext. intros [x Hx]. destruct x ; try omega.
        simpl. unfold fcompose. rewrite Heqfu. f_equal.
        apply funext. intros [y Hy]. omega. apply eq_finset. reflexivity.
  - pose proof (IHa (restr_map f true) (monotone_restr f true Hf)) as [w Hw].
    pose proof (IHa (restr_map f false) (monotone_restr f false Hf)) as [w' Hw'].
    pose proof (simpl_monotone f Hf). rewrite <- H.
    rewrite Hw. rewrite Hw'. rewrite <- simpl_adm.
    refine (exist _ _ _). reflexivity.
Qed.

Theorem monotone_impl_adm_1 {a : nat} (f : cube a -> cube 1) : monotone f -> admissible' f.
Proof.
  induction a.
  - admit.
  - intro H. remember H as H1. clear HeqH1.
    apply monotone_restr with (b := true) in H. apply monotone_restr with (b := false) in H1.
    apply IHa in H. apply IHa in H1.
Admitted.

Theorem adm_if_monotone {a b : nat} (f : cube a -> cube b) : monotone f -> admissible' f.
Admitted.

Theorem monotone_if_adm {a b : nat} (f : cube a -> cube b) : admissible' f -> monotone f.
Admitted.

Theorem decide_adm {a b : nat} (f : cube a -> cube b) :
  admissible' f + (admissible' f -> False).
Admitted.

Theorem recover_word {a b : nat} (f : a ~> b)
  : { w : word b a | f.1s = comp_word w }.
Proof.
  destruct (decide_adm (f.1s)) as [H | H].
  - destruct H. easy.
  - assert sFalse. destruct f as [f H1]. destruct H1 as [w H1].
    assert False. apply H. exists w. simpl. apply eqs_eq. exact H1.
    destruct H0.
    destruct H0.
Qed.

Theorem arrow_monotone {a b : nat} (f : a ~> b)
  : monotone f.1s.
Proof.
  apply monotone_if_adm. apply recover_word.
Qed.





(** Cartesian structure *)

(* based on the decidability part. This actually only requires the category of cubes having contractions *)

Definition fuse_cube_maps {a b c : nat} : (cube a -> cube b) * (cube a -> cube c) -> (cube a -> cube (b + c)).
  intros [f g] d [x p].
  destruct (le_lt_dec b x).
  - assert (x - b < c). apply le_plus_n with (p := b). rewrite add_S.
    rewrite <- Minus.le_plus_minus. exact p. exact l.
    apply (g d). exists (x - b). exact H.
  - apply (f d). exists x. exact l.
Defined.

Theorem fused_monotone {a b c : nat} (f : cube a -> cube b) (g : cube a -> cube c) :
  monotone f -> monotone g -> monotone (fuse_cube_maps (f, g)).
Proof.
  intros Hf Hg d e Hde [x Hx]. simpl.
  destruct (le_lt_dec b x).
  - apply Hg. exact Hde.
  - apply Hf. exact Hde.
Qed.

Definition fuse_arrows {a b c : nat} : (a ~> c) * (b ~> c) -> (a + b ~> c).
  intros [f g].
  refine ( fuse_cube_maps (f.1s, g.1s) ; _ )s.
  pose proof (arrow_monotone f). pose proof (arrow_monotone g).
  assert (admissible' (fuse_cube_maps (f.1s, g.1s))).
  apply adm_if_monotone. now apply fused_monotone.
  destruct H1 as [w H1].
  eapply spair_s. apply eq_eqs. exact H1.
Defined.

Definition split_cube_map {a b c : nat} : (cube a -> cube (b + c)) -> (cube a -> cube b) * (cube a -> cube c).
  intro f. split.
  - intros d [x p]. apply (f d). exists x. easy.
  - intros d [x p]. apply (f d). exists (b + x). unfold lt. rewrite <- add_S.
    apply Plus.plus_le_compat_l. exact p.
Defined.

Theorem splitted_monotone {a b c : nat} (f : cube a -> cube (b + c)) :
  monotone f -> monotone (fst (split_cube_map f)) /\ monotone (snd (split_cube_map f)).
Proof.
  intro Hf. split ; intros d e Hde [x Hx] ; simpl ; apply Hf ; exact Hde.
Qed.

Definition split_arrow {a b c : nat} : (a + b ~> c) -> (a ~> c) * (b ~> c).
  intro f. split.
  - refine ( fst (split_cube_map f.1s) ; _ )s.
    pose proof (arrow_monotone f). destruct (splitted_monotone f.1s H) as [H1 _].
    assert (admissible' (fst (split_cube_map f.1s))). apply adm_if_monotone. exact H1.
    destruct H0 as [w H0]. eapply spair_s. apply eq_eqs. exact H0.
  - refine ( snd (split_cube_map f.1s) ; _ )s.
    pose proof (arrow_monotone f). destruct (splitted_monotone f.1s H) as [_ H1].
    assert (admissible' (snd (split_cube_map f.1s))). apply adm_if_monotone. exact H1.
    destruct H0 as [w H0]. eapply spair_s. apply eq_eqs. exact H0.
Defined.

Theorem cartesian_lemma1 {a b c : nat} : forall f : cube a -> cube (b + c), fuse_cube_maps (split_cube_map f) = f.
  intro f.
  apply funext. intro d.
  apply funext. intros [x p].
  simpl. destruct (le_lt_dec b x).
  - assert (forall p' : b + (x - b) < b + c, exist (fun m : nat => m < b + c) (b + (x - b)) p' = exist (fun m : nat => m < b + c) x p).
    rewrite <- Minus.le_plus_minus. intro p'. rewrite (Peano_dec.le_unique (S x) (b + c) p p'). reflexivity.
    exact l.
    rewrite H. reflexivity.
  - erewrite (Peano_dec.le_unique _ _ (Plus.lt_plus_trans x b c l) p). reflexivity.
Qed.

Theorem cartesian_lemma2 {a b c : nat}
  : forall (f : cube a -> cube b) (g : cube a -> cube c), split_cube_map (fuse_cube_maps (f, g)) = (f, g).
  intros f g. apply injective_projections.
  - apply funext. intro d.
    apply funext. intros [x p].
    simpl. destruct (le_lt_dec b x).
    + assert False. easy. inversion H.
    + erewrite (Peano_dec.le_unique _ _ l p). reflexivity.
  - apply funext. intro d.
    apply funext. intros [x p].
    simpl. destruct (le_lt_dec b (b + x)).
    + assert (forall p' : b + x - b < c, exist (fun m : nat => m < c) (b + x - b) p' = exist (fun m : nat => m < c) x p).
      replace (b + x - b) with x. intro p'. erewrite (Peano_dec.le_unique _ _ p p'). reflexivity.
      easy.
      rewrite H. reflexivity.
    + assert False. easy. inversion H.
Qed.

Theorem cartesian_iso1 {a b c : nat} : fuse_arrows o split_arrow = fun x : a + b ~> c => x.
Proof.
  apply funext. intro f. apply eq_sexist.
  Opaque fuse_cube_maps. Opaque split_cube_map. simpl.
  rewrite <- (surjective_pairing (split_cube_map f.1s)).
  apply cartesian_lemma1.
Qed.

Theorem cartesian_iso2 {a b c : nat} : split_arrow o fuse_arrows = fun x : (a ~> c) * (b ~> c) => x.
Proof.
  apply funext. intros [f g]. apply injective_projections.
  - apply eq_sexist. compute.
    pose proof (cartesian_lemma2 f.1s g.1s).
    apply (f_equal fst) in H. exact H.
  - apply eq_sexist. compute.
    pose proof (cartesian_lemma2 f.1s g.1s). apply (f_equal snd) in H. exact H.
Qed.





(** Check that category laws are definitional *)

Theorem compose_assoc {A B C D : nat}
           (f : A ~> B) (g : B ~> C) (h : C ~> D) :
  h ô (g ô f) = (h ô g) ô f.
Proof.
  reflexivity.
Qed.

Theorem compose_id_right {A B : nat} (f : A ~> B) :
  f ô id = f.
Proof.
  reflexivity.
Qed.

Theorem compose_id_left {A B : nat} (f : A ~> B) :
  id ô f = f.
Proof.
  reflexivity.
Qed.





(** Definition of the forcing machinery *)

Definition 𝐂_obj := nat.
Definition 𝐂_hom := arrow.
Definition 𝐂_id := @id.
Definition 𝐂_comp := @compose.

Quote Definition q_𝐂_obj := nat.
Quote Definition q_𝐂_hom := arrow.
Quote Definition q_𝐂_id := @id.
Quote Definition q_𝐂_comp := @compose.

Definition 𝐂 : category :=
  mkCat q_𝐂_obj q_𝐂_hom q_𝐂_id q_𝐂_comp.


Import MonadNotation.
Import ListNotations.

Definition ForcingTranslation (cat : category) : Translation :=
  {| tsl_id := tsl_ident;
     tsl_tm := f_translate cat;
     tsl_ty := f_translate_type cat;
     tsl_ind := f_translate_ind cat
     (* tsl_context -> kername -> kername -> mutual_inductive_body *)
     (*             -> tsl_result (tsl_table * list mutual_inductive_body) *)
  |}.

Definition add_translation (ctx : tsl_context) (e : global_reference * term): tsl_context :=
  let (Σ, E) := ctx in
  (Σ, e :: E).

Instance Cubical : Translation := ForcingTranslation 𝐂.

(* Define a type that, when recursively quoted, imports all we need *)
Definition pack := (arrow , @compose , @id).

Run TemplateProgram (prg <- tmQuoteRec pack ;;
                         tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context := (reconstruct_global_context g_ctx,[]).






(** Definition of the interval *)

Run TemplateProgram (tImplementTC ΣE "I_TC" "I" Type).
Next Obligation.
  exact (1 ~> p0).
Defined.


Definition initial_word_aux (p : nat) (q : nat) : word (p+q) p.
  revert p. induction q.
  - intro p. rewrite <- (plus_n_O p). exact empty.
  - intro p. apply degen.
    + exists 0. easy.
    + rewrite <- plus_n_Sm.
      change (word (S (p + q)) (S p)) with (word (S p + q) (S p)).
      apply IHq.
Defined.

Definition initial_word (p : nat) : word p 0.
  exact (initial_word_aux 0 p).
Defined.

Definition initial_map (p : nat) : cube p -> cube 0.
  intro c. intros [a H]. destruct (pos_ge_0 a H).
Defined.


(*
   this proof uses funext to show that any two arrows with initial codomain must be
   equal. If necessary, it is possible to define a version that doesn't use it.
 *)
Theorem initial_map_admissible (p : nat) :
  initial_map p =s comp_word (initial_word p).
Proof.
  apply eq_eqs.
  apply funext. intro a. apply funext. intros [b H]. destruct (pos_ge_0 b H).
Qed.

Definition initial_arrow (p : nat) : 0 ~> p.
  assert (admissible (initial_map p)).
  - eapply spair_s. exact (initial_map_admissible p).
  - exact (initial_map p ; H)s.
Defined.

Theorem initial_arrow_is_initial (p : nat) (α : 0 ~> p) :
  α = initial_arrow p.
Proof.
  apply eq_sexist. apply funext. intro x. apply funext.
  intros [n H]. assert False. eapply pos_ge_0. exact H. inversion H0.
Qed.

Definition I_end_map (p : nat) (e : bool) : cube p -> cube 1 :=
  (fun (_ : cube p) (_ : finset 1) => e).

Definition I_end_word (p : nat) (e : bool) : word p 1.
  apply face.
  - exists 0. easy.
  - exact e.
  - exact (initial_word p).
Defined.

Theorem I_end_admissible (p : nat) (e : bool) :
  I_end_map p e =s comp_word (I_end_word p e).
Proof.
  apply eq_eqs. simpl. rewrite <- (eqs_eq (initial_map_admissible p)).
  apply funext. intro c. apply funext. intros [x H]. destruct x.
  - compute. reflexivity.
  - pose proof (le_S_n (S x) 0 H) as H'. apply pos_ge_0 in H'. destruct H'.
Qed.

Definition I_end (p : nat) (e : bool) : 1 ~> p.
  assert (admissible (I_end_map p e)).
  - eapply spair_s. exact (I_end_admissible p e).
  - exact (I_end_map p e ; H)s.
Defined.

Run TemplateProgram (tImplementTC I_TC "I0_TC" "I0" I).
Next Obligation.
  exact (I_end p false).
Defined.

Run TemplateProgram (tImplementTC I0_TC "I1_TC" "I1" I).
Next Obligation.
  exact (I_end p true).
Defined.






(** Imported inductives *)

(* We copy translated definitions of [eq] generated by the OCaml
   forcing plugin, because inducives are not supported yet by the
   template-coq forcing translation *)
Inductive eqᵗ (p : 𝐂_obj) (A : forall p0 : 𝐂_obj, p ~> p0 -> forall p : 𝐂_obj, p0 ~> p -> Type)
(x : forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (α ô id) p0 id) :
  (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (id ô (α ô id)) p0 id) -> Type :=
  eq_reflᵗ : eqᵗ p A x x.

(* This definition will fail if we leave the type of [A] implicit. *)
Definition eq_is_eq :
  forall p (A : forall x : 𝐂_obj, (p ~> x) -> forall x1 : 𝐂_obj, (x ~> x1) -> Type)
         (x y: forall p0 (f:p ~> p0), A p0 f p0 id),
    eq x y -> eqᵗ p A x y. (* it even fails if i don't mention A as an explicit argument
                             here b/c of some mysterious reason *)
Proof.
  intros. rewrite H. apply eq_reflᵗ.
Qed.

Run TemplateProgram (TC <- tAddExistingInd I1_TC "Coq.Init.Logic.eq" "eqᵗ" ;;
                          tmDefinition "eq_TC" TC).

Inductive Falseᵗ (p : 𝐂_obj) := .

Run TemplateProgram (TC <- tAddExistingInd eq_TC "Coq.Init.Logic.False" "Falseᵗ" ;;
                        tmDefinition "False_TC" TC).

Inductive orᵗ (p : 𝐂_obj) (A B : forall p0 : 𝐂_obj, p ~> p0 -> forall p1 : 𝐂_obj, p0 ~> p1 -> Prop) : Prop :=
    or_introlᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 α p0 id) -> orᵗ p A B
  | or_introrᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), B p0 α p0 id) -> orᵗ p A B.

Run TemplateProgram (TC <- tAddExistingInd False_TC "Coq.Init.Logic.or" "orᵗ" ;;
                        tmDefinition "or_TC" TC).

Inductive andᵗ (p : 𝐂_obj) (A B : forall p0 : 𝐂_obj, p ~> p0 -> forall p1 : 𝐂_obj, p0 ~> p1 -> Prop) : Prop :=
    conjᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 α p0 id) ->
            (forall (p0 : 𝐂_obj) (α : p ~> p0), B p0 α p0 id) -> andᵗ p A B.

Run TemplateProgram (TC <- tAddExistingInd or_TC "Coq.Init.Logic.and" "andᵗ" ;;
                        tmDefinition "and_TC" TC).

Inductive sigTᵗ (p : 𝐂_obj)
          (A : forall p0, p ~> p0 -> forall p, p0 ~> p -> Type)
          (P : forall p0 (α : p ~> p0),
              (forall p (α0 : p0 ~> p), A p (α0 ô α) p id) ->
              forall p, p0 ~> p -> Type) : Type :=
  existTᵗ : forall x : forall p0 (α : p ~> p0), A p0 α p0 id,
    (forall p0 (α : p ~> p0), P p0 α (fun (q : 𝐂_obj) (α0 : p0 ~> q) => x q (α0 ô α)) p0 id) ->
    sigTᵗ p A P.

Run TemplateProgram (TC <- tAddExistingInd and_TC "Coq.Init.Specif.sigT" "sigTᵗ" ;;
                        tmDefinition "sigT_TC" TC).

Inductive unitᵗ (p : 𝐂_obj) :=
  ttᵗ : unitᵗ p.

Run TemplateProgram (TC <- tAddExistingInd sigT_TC "Coq.Init.Datatypes.unit" "unitᵗ" ;;
                        tmDefinition "unit_TC" TC).

Definition complete_TC := unit_TC.






(** Axiom 1 for I : connectedness *)

Definition zero_corner_map (p : nat) : cube 0 -> cube p.
  intros x d. exact false.
Defined.

Definition zero_corner_word (p : nat) : word 0 p.
  induction p.
  - exact empty.
  - apply face.
    + exact (zero_finset p).
    + exact false.
    + exact IHp.
Defined.

Theorem zero_corner_admissible (p : nat) : zero_corner_map p = comp_word (zero_corner_word p).
  induction p.
  - apply funext. intro c. apply funext. intros [x H]. destruct (pos_ge_0 x H).
  - simpl. rewrite <- IHp. apply funext. intro c. apply funext. intros [x H].
    destruct x.
    + now compute.
    + now compute.
Qed.

Definition zero_corner (p : nat) : p ~> 0.
  assert (admissible (zero_corner_map p)).
  eapply spair_s. apply eq_eqs. exact (zero_corner_admissible p).
  exact ( zero_corner_map p ; H )s.
Defined.

Definition face_map (p : nat) (b : bool) : S p ~> p.
  assert (face_c (zero_finset p) b =s comp_word (face (zero_finset p) b empty)).
  apply eq_eqs. reflexivity.
  assert (admissible (face_c (zero_finset p) b)).
  eapply spair_s. exact H.
  exact ( face_c (zero_finset p) b ; H0 )s.
Defined.

Definition degen_map (p : nat) : p ~> S p.
  assert (degen_c (zero_finset p) =s comp_word (degen (zero_finset p) empty)).
  apply eq_eqs. reflexivity.
  assert (admissible (degen_c (zero_finset p))).
  eapply spair_s. exact H.
  exact ( degen_c (zero_finset p) ; H0 )s.
Defined.

Theorem face_degen (p : nat) (b : bool) : face_map p b ô degen_map p = id.
Proof.
  apply eq_sexist. apply funext.
  intro c. apply funext. intros [[| x] H].
  - compute. assert ((le_S_n 1 p (le_n_S 1 p H)) = H).
    apply Peano_dec.le_unique. rewrite H0. reflexivity.
  - compute. assert ((le_S_n (S (S x)) p (le_n_S (S (S x)) p H)) = H).
    apply Peano_dec.le_unique. rewrite H0. reflexivity.
Qed.

Definition side (p : nat) : cube (S p) -> bool.
  intro c. exact (c (zero_finset p)).
Defined.

Theorem side_face (p q : nat) (b : bool) α (c : cube q) :
  side p ((α ô face_map p b).1s c) = b.
Proof.
  now compute.
Qed.

Definition homotopy_to_zero (p : nat) (i : forall q : nat, p ~> q -> Iᵗ q q id)
  : forall q : nat, S p ~> q -> Iᵗ q q id.
  intros q α.
  specialize (i q (α ô (degen_map p))).
  pose (side p ((α.1s) (fun x => false))). destruct b. (* this is a travesty, not natural at all *)
  - exact i.
  - exact (I0ᵗ q).
Defined.

Theorem homotopy_restriction1 (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Iᵗ q q id)
  : i q α = (homotopy_to_zero p i) q (α ô face_map p true).
Proof.
  unfold homotopy_to_zero.
  rewrite side_face. change (α ô face_map p true ô degen_map p) with (α ô (face_map p true ô degen_map p)).
  rewrite (face_degen p true). reflexivity.
Qed.

Theorem homotopy_restriction2 (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Iᵗ q q id)
  : I0ᵗ q = (homotopy_to_zero p i) q (α ô face_map p false).
Proof.
  unfold homotopy_to_zero.
  rewrite side_face. reflexivity.
Qed.

Theorem factorization (p : nat) : exists f, zero_corner (S p) = f ô face_map p false.
Proof.
  exists (zero_corner p). apply eq_sexist. apply funext. intro c.
  apply funext. intros [[|x] H].
  - now compute.
  - now compute.
Qed.

Run TemplateProgram (tImplementTC complete_TC "ax1_TC" "ax1"
  (forall (φ : I -> Prop), ((forall i : I, φ i \/ (φ i -> False)) -> (forall i : I, φ i) \/ (forall i : I, φ i -> False)))).
Next Obligation.
  (* STRATEGY OUTLINE *)
  (* we start by applying H0 to decide whether φ(I0) is True or False. then we commit to prove that it is the
   same for every generalized point i. indeed, if φ(i) is different, we are able to build a generalized point
   that extends both I0(0, corner) and i(0, corner) therefore reaching a contradiction. *)
  rename H into H0.
  remember H0 as H1. clear HeqH1.
  specialize (H0 p id (fun p α => I0ᵗ p)). destruct H0.
  - apply or_introlᵗ. intros q α i.
    (* then apply H1 to the homotopy *)
    pose (homotopy_to_zero q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + assert ((fun (p2 : nat) (α1 : q ~> p2) => i p2 (id ô α1)) = (fun (p2 : nat) (α1 : q ~> p2) => (homotopy_to_zero q i) p2 (α1 ô face_map q true))).
      apply funext_dep. intro r. apply funext_dep. intro γ.
      rewrite homotopy_restriction1. reflexivity.
      rewrite H1. clear H1.
      change (homotopy_to_zero q i) with h. change (id ô id ô (id ô α ô id) ô id ô id) with α.
      specialize (H0 q (face_map q true)).
      change (id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id ô id) with (face_map q true ô degen_map q ô α) in H0.
      assert (α = face_map q true ô degen_map q ô α).
      rewrite face_degen. reflexivity.
      rewrite H1. apply H0.
    + specialize (H0 0 (zero_corner (S q))). assert (Falseᵗ 0).
      apply H0. intros q' β.
      pose proof (factorization q) as [γ H1].
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô zero_corner (S q) ô id))) = (fun (p4 : nat) (α3 : q' ~> p4) => I0ᵗ p4)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      rewrite H1. change (id ô δ ô β ô id ô (id ô (γ ô face_map q false) ô id)) with (δ ô β ô γ ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2. reflexivity.
      rewrite H2. clear H2.
      change (id ô β ô id ô (id ô zero_corner (S q) ô id) ô id ô (degen_map q ô α) ô id) with (β ô zero_corner (S q) ô degen_map q ô α).
      specialize (H q' (β ô zero_corner (S q) ô degen_map q ô α)). apply H.
      inversion H1.
  - apply or_introrᵗ. intros q α i H2.
    pose (homotopy_to_zero q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + clear H2. eapply H. intros q' β.
      specialize (H0 q' (β ô face_map q false)).
      change (id ô (id ô (β ô face_map q false) ô id) ô id ô (degen_map q ô α) ô id) with (β ô (face_map q false ô degen_map q) ô α) in H0.
      rewrite face_degen in H0.
      assert ((fun (p2 : nat) (α1 : q' ~> p2) => h p2 (id ô α1 ô (id ô (β ô face_map q false) ô id))) = (fun (p2 : nat) (α1 : q' ~> p2) => I0ᵗ p2)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô (id ô (β ô face_map q false) ô id)) with (δ ô β ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2. reflexivity.
      rewrite H1 in H0. exact H0.
    + clear H. apply H0 with (α0 := face_map q true). intros q' β.
      specialize (H2 q' β).
      change (id ô β ô id ô id ô (id ô α ô id) ô id) with (β ô id ô α) in H2.
      assert (β ô id ô α = β ô face_map q true ô degen_map q ô α). erewrite <- face_degen. reflexivity.
      rewrite H in H2. clear H.
      change (id ô β ô id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id) with (β ô face_map q true ô degen_map q ô α).
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô face_map q true ô id))) = (fun (p3 : nat) (α2 : q' ~> p3) => i p3 (id ô α2 ô β ô id))).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô β ô id ô (id ô face_map q true ô id)) with (δ ô β ô face_map q true).
      unfold h. rewrite <- homotopy_restriction1. reflexivity. rewrite H.
      exact H2.
Defined.







(** Axiom 1 for J *)

(* This should actually be SProp, but we cannot translate SProp as of now.
 So we will need some propositional extensionality i guess *)

Run TemplateProgram (tImplementTC ax1_TC "natp_TC" "natp" (Prop -> Prop)).
Next Obligation.
  rename X into S. rename X0 into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1), S p0 α0 p1 α1 <-> S p1 (α1 ô α0) p1 id).
Defined.

Run TemplateProgram (tImplementTC ax1_TC "nati_TC" "nati" (I -> Prop)).
Next Obligation.
  rename X into i. rename X0 into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1), α1 ô (i p0 α0) = i p1 (α1 ô α0)).
Defined.

Arguments existT {_ _} _.

Notation "'Σ' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) .. ))
                            (at level 200, x binder, y binder, right associativity).
Notation "( x ; .. ; y ; z )" := (existT x (.. (existT y z) ..)).

Definition J := Σ (i : I), nati i.

Run TemplateProgram (TC1 <- tTranslate nati_TC "J" ;;
                        tmDefinition "J_TC" TC1).

Run TemplateProgram (tImplementTC J_TC "J0_TC" "J0" J).
Next Obligation.
  unshelve refine (existTᵗ _ _ _ _ _).
  - intros p0 α0. exact (I_end p0 false).
  - intros p0 α0 p1 α1. apply eq_sexist. reflexivity.
Defined.

Run TemplateProgram (tImplementTC J0_TC "J1_TC" "J1" J).
Next Obligation.
  unshelve refine (existTᵗ _ _ _ _ _).
  - intros p0 α0. exact (I_end p0 true).
  - intros p0 α0 p1 α1. apply eq_sexist. reflexivity.
Defined.

Definition homotopy_to_zero' (p : nat) (i : forall q : nat, p ~> q -> Jᵗ q q id)
  : forall q : nat, S p ~> q -> Jᵗ q q id.
  intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _).
  - intros q α1. pose (α1 ô α0) as α.
    unshelve refine (Build_sexists _ _ _ _).
    + specialize (i p0 (α0 ô (degen_map p))). destruct i as [i Hi].
      intro c. pose (α.1s c) as c'. pose (side p c') as s. destruct s.
      * exact ((i p0 id).1s (α1.1s c)).
      * exact (fun _ => false).
    + destruct (i p0 (α0 ô degen_map p)) as [i' Hi]. simpl.
      assert (admissible'
                (fun c : cube q =>
                   if side p (α.1s c)
                   then (i' p0 id).1s (α1.1s c)
                   else fun _ : finset 1 => false)).
      { apply adm_if_monotone. intros c d Hcd.
        pose proof (arrow_monotone α). specialize (H c d Hcd).
        assert (side p (α.1s c) = true -> side p (α.1s d) = true). easy.
        destruct (side p (α.1s c)).
        - specialize (H0 eq_refl). rewrite H0.
          pose proof (arrow_monotone (α1 ô (i' p0 id))). exact (H1 c d Hcd).
        - intros x Hf. inversion Hf. }
      destruct H as [w Hw].
      eapply spair_s. apply eq_eqs. exact Hw.
  - intros p1 α1 p2 α2. apply eq_sexist.
    destruct (i p0 (α0 ô degen_map p)) as [i' Hi]. reflexivity.
Defined.

Definition projT1' {p : nat} {A : forall p0 : nat, p ~> p0 -> forall p1 : nat, p0 ~> p1 -> Type}
           {B : forall (p0 : nat) (α : p ~> p0), (forall (p1 : nat) (α0 : p0 ~> p1), A p1 (α0 ô α) p1 id) -> forall p1 : nat, p0 ~> p1 -> Type}
  : sigTᵗ p A B -> forall (p0 : nat) (α : p ~> p0), A p0 α p0 id.
  intros [x y]. exact x.
Defined.

Theorem J_eq {p : nat} (a b : Jᵗ p p id)
  : projT1' a = projT1' b -> a = b.
Proof.
  destruct a. destruct b. simpl.
  intro H. destruct H.
  assert (n = n0). apply proof_irr. rewrite H. reflexivity.
Qed.

Theorem homotopy_restriction1' (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Jᵗ q q id)
  : i q α = (homotopy_to_zero' p i) q (α ô face_map p true).
Proof.
  assert (projT1' (i q α) = projT1' (homotopy_to_zero' p i q (α ô face_map p true))).
  { apply funext_dep. intro p0. apply funext. intro α0.
    apply eq_sexist. unfold homotopy_to_zero'.
    Opaque side. Opaque degen_c. Opaque face_map. simpl.
    change (α ô face_map p true ô degen_map p) with (α ô (face_map p true ô degen_map p)).
    rewrite face_degen. change (α ô id) with α.
    destruct (i q α) as [j Hj]. simpl.
    apply funext. intro c.
    change ((face_map p true).1s o α.1s o α0.1s) with ((α0 ô α ô (face_map p true)).1s).
    rewrite side_face.
    specialize (Hj q id). unfold natiᵗ in Hj. unfold natiᵗ_obligation_1 in Hj.
    change (j p0 α0) with (j p0 (id ô (α0 ô id) ô id)).
    rewrite <- (Hj p0 α0). reflexivity. }
  apply J_eq. exact H.
  (* Proof is correct but it doesnt typecheck without printing implicits. *)
Admitted.


Theorem homotopy_restriction2' (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Jᵗ q q id)
  : J0ᵗ q = (homotopy_to_zero' p i) q (α ô face_map p false).
Proof.
  assert (projT1' (J0ᵗ q) = projT1' (homotopy_to_zero' p i q (α ô face_map p false))).
  { apply funext_dep. intro p0. apply funext. intro α0.
    apply eq_sexist. unfold homotopy_to_zero'.
    Opaque side. Opaque degen_c. Opaque face_map. simpl.
    change (α ô face_map p false ô degen_map p) with (α ô (face_map p false ô degen_map p)).
    rewrite face_degen. change (α ô id) with α.
    destruct (i q α) as [j Hj].
    apply funext. intro c.
    change ((face_map p false).1s o α.1s o α0.1s) with ((α0 ô α ô (face_map p false)).1s).
    rewrite side_face. now compute. }
  apply J_eq. exact H.
  (* Proof is correct but it doesnt typecheck without printing implicits. *)
Admitted.

Run TemplateProgram (tImplementTC J1_TC "ax1'_TC" "ax1'"
  (forall (φ : J -> Prop), ((forall i : J, φ i \/ (φ i -> False)) -> (forall i : J, φ i) \/ (forall i : J, φ i -> False)))).
Next Obligation.
  (* STRATEGY OUTLINE *)
  (* we start by applying H0 to decide whether φ(I0) is True or False. then we commit to prove that it is the
   same for every generalized point i. indeed, if φ(i) is different, we are able to build a generalized point
   that extends both I0(0, corner) and i(0, corner) therefore reaching a contradiction. *)
  rename H into H0.
  remember H0 as H1. clear HeqH1.
  specialize (H0 p id (fun p α => J0ᵗ p)). destruct H0.
  - apply or_introlᵗ. intros q α i.
    (* then apply H1 to the homotopy *)
    pose (homotopy_to_zero' q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + assert ((fun (p2 : nat) (α1 : q ~> p2) => i p2 (id ô α1)) = (fun (p2 : nat) (α1 : q ~> p2) => (homotopy_to_zero' q i) p2 (α1 ô face_map q true))).
      apply funext_dep. intro r. apply funext_dep. intro γ.
      rewrite homotopy_restriction1'. reflexivity.
      rewrite H1. clear H1.
      change (homotopy_to_zero' q i) with h. change (id ô id ô (id ô α ô id) ô id ô id) with α.
      specialize (H0 q (face_map q true)).
      change (id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id ô id) with (face_map q true ô degen_map q ô α) in H0.
      assert (α = face_map q true ô degen_map q ô α).
      rewrite face_degen. reflexivity.
      rewrite H1. apply H0.
    + specialize (H0 0 (zero_corner (S q))). assert (Falseᵗ 0).
      apply H0. intros q' β.
      pose proof (factorization q) as [γ H1].
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô zero_corner (S q) ô id))) = (fun (p4 : nat) (α3 : q' ~> p4) => J0ᵗ p4)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      rewrite H1. change (id ô δ ô β ô id ô (id ô (γ ô face_map q false) ô id)) with (δ ô β ô γ ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2'. reflexivity.
      rewrite H2. clear H2.
      change (id ô β ô id ô (id ô zero_corner (S q) ô id) ô id ô (degen_map q ô α) ô id) with (β ô zero_corner (S q) ô degen_map q ô α).
      specialize (H q' (β ô zero_corner (S q) ô degen_map q ô α)). apply H.
      inversion H1.
  - apply or_introrᵗ. intros q α i H2.
    pose (homotopy_to_zero' q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + clear H2. eapply H. intros q' β.
      specialize (H0 q' (β ô face_map q false)).
      change (id ô (id ô (β ô face_map q false) ô id) ô id ô (degen_map q ô α) ô id) with (β ô (face_map q false ô degen_map q) ô α) in H0.
      rewrite face_degen in H0.
      assert ((fun (p2 : nat) (α1 : q' ~> p2) => h p2 (id ô α1 ô (id ô (β ô face_map q false) ô id))) = (fun (p2 : nat) (α1 : q' ~> p2) => J0ᵗ p2)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô (id ô (β ô face_map q false) ô id)) with (δ ô β ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2'. reflexivity.
      rewrite H1 in H0. exact H0.
    + clear H. apply H0 with (α0 := face_map q true). intros q' β.
      specialize (H2 q' β).
      change (id ô β ô id ô id ô (id ô α ô id) ô id) with (β ô id ô α) in H2.
      assert (β ô id ô α = β ô face_map q true ô degen_map q ô α). erewrite <- face_degen. reflexivity.
      rewrite H in H2. clear H.
      change (id ô β ô id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id) with (β ô face_map q true ô degen_map q ô α).
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô face_map q true ô id))) = (fun (p3 : nat) (α2 : q' ~> p3) => i p3 (id ô α2 ô β ô id))).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô β ô id ô (id ô face_map q true ô id)) with (δ ô β ô face_map q true).
      unfold h. rewrite <- homotopy_restriction1'. reflexivity. rewrite H.
      exact H2.
Defined.





(** Axiom 2 : distinct end points *)

Definition lowest_corner (p : nat) : cube p.
  intro. exact false.
Defined.

Run TemplateProgram (tImplementTC ax1'_TC "ax2_TC" "ax2" (I0 = I1 -> False)).
Next Obligation.
  specialize (H p id). inversion H.
  assert (I0ᵗ p = I1ᵗ p).
  change (I0ᵗ p) with ((fun (p1 : nat) (_ : p ~> p1) => I0ᵗ p1) p id). rewrite H1. reflexivity.
  assert (I_end_map p false = I_end_map p true).
  change (I_end_map p false) with ((I0ᵗ p).1s). rewrite H0. reflexivity.
  assert (false = true).
  change false with (I_end_map p false (lowest_corner p) (zero_finset 0)). rewrite H2. reflexivity.
  inversion H3.
Defined.




(** Connection algebra structure *)

Definition join_arrow {p : nat} (f : 1 + 1 ~> p) : 1 ~> p.
  destruct (recover_word f) as [w H].
  pose (join_c (zero_finset 0)) as g.
  refine ( g o f.1s ; _ )s. apply spair_s with (a := join (zero_finset 0) w).
  apply eq_eqs. apply (f_equal (fun x => g o x)) in H. exact H.
Defined.

Definition meet_arrow {p : nat} (f : 1 + 1 ~> p) : 1 ~> p.
  destruct (recover_word f) as [w H].
  pose (meet_c (zero_finset 0)) as g.
  refine ( g o f.1s ; _ )s. apply spair_s with (a := meet (zero_finset 0) w).
  apply eq_eqs. apply (f_equal (fun x => g o x)) in H. exact H.
Defined.

Run TemplateProgram (tImplementTC ax2_TC "join_TC" "join_i" (I -> I -> I)).
Next Obligation.
  rename X into i1. rename X0 into i2.
  specialize (i1 p id). specialize (i2 p id).
  pose (fuse_arrows (i1, i2)). exact (join_arrow a).
Defined.

Run TemplateProgram (tImplementTC join_TC "meet_TC" "meet_i" (I -> I -> I)).
Next Obligation.
  rename X into i1. rename X0 into i2.
  specialize (i1 p id). specialize (i2 p id).
  pose (fuse_arrows (i1, i2)). exact (meet_arrow a).
Defined.

Notation "a ⊓ b" := (meet_i a b) (at level 65, left associativity).
Notation "a ⊔ b" := (join_i a b) (at level 65, left associativity).





(** Axiom 3 : computational behaviour of ⊓ *)

Theorem ax3 : forall i : I, I0 ⊓ i = I0 /\ i ⊓ I0 = I0 /\ I1 ⊓ i = i /\ i ⊓ I1 = i.
Admitted.

Definition ax3_TC := meet_TC.





(** Axiom 4 : computational behaviour of ⊔ *)

Run TemplateProgram (tImplementTC ax3_TC "ax4_1_TC" "ax4_1" (forall i : I, I0 ⊔ i = i)).
Next Obligation.
  assert ((fun (p0 : nat) (α : p ~> p0) => join_iᵗ p0 (fun (p1 : nat) (_ : p0 ~> p1) => I0ᵗ p1) (fun (p1 : nat) (α0 : p0 ~> p1) => i p1 (id ô α0 ô (id ô α ô id)))) = (fun (p0 : nat) (α : p ~> p0) => i p0 (id ô (id ô α ô id)))).
  apply funext_dep. intro q. apply funext_dep. intro α.
  unfold join_iᵗ. unfold join_iᵗ_obligation_1.
  apply eq_sexist.
  apply funext. intro c.
  apply funext. intros [x px].
  destruct x.
  - replace (join_arrow (fuse_arrows (I0ᵗ q, i q (id ô id ô (id ô α ô id))))).1s with (join_c (zero_finset 0) o (fuse_arrows (I0ᵗ q, i q α)).1s).
    + Transparent fuse_cube_maps.
      compute.
      match goal with
      | [ |- _ _ (exist _ 0 ?XX) = _ _ (exist _ 0 px) ] => erewrite (Peano_dec.le_unique _ _ XX px)
      end. reflexivity.
    + unfold join_arrow.
      destruct (recover_word (fuse_arrows (I0ᵗ q, i q (id ô id ô (id ô α ô id))))). reflexivity.
  - assert False. easy. inversion H.
  - rewrite H. apply eq_reflᵗ.
Defined.


Theorem ax4 : forall i : I, I0 ⊔ i = i /\ i ⊔ I0 = i /\ I1 ⊔ i = I1 /\ i ⊔ I1 = I1.
  intro i. split.
  exact (ax4_1 i).
  admit.
Admitted.

Definition ax4_TC := ax4_1_TC.




(** Face lattice *)

Definition constraint (n : nat) := (finset n) -> (option bool).

Definition face_lattice (n : nat) := list (constraint n).

Definition join_faces {n : nat} : face_lattice n -> face_lattice n -> face_lattice n.
  intro f. induction f.
  - intro f. exact f.
  - intro f'. exact (a::(IHf f')).
Defined.

Definition empty_constraint {n : nat} : constraint n -> Prop.
  intro c. exact (forall m : finset n, c m = None).
Defined.

Fixpoint covering {n : nat} (f : face_lattice n) : Prop :=
  match f with
  | nil => False
  | c::tl => (empty_constraint c) \/ (covering tl)
  end.

Theorem covering_join {n : nat} (f g : face_lattice n) :
  covering (join_faces f g) <-> covering f \/ covering g.
Proof.
  revert g. induction f.
  - intro g. simpl. split.
    + intro H ; now right.
    + intros [H | H] ; easy.
  - intro g. simpl. split.
    + intros [H | H]. left ; now left. apply (IHf g) in H. destruct H. left ; now right. now right.
    + intros [[H | H] | H]. now left. right. apply (IHf g). now left. right. apply (IHf g). now right.
Qed.

Definition last_finset (n : nat) : finset (S n).
  exists n. easy.
Defined.

Definition finset_inj (n : nat) : finset n -> finset (S n).
  intros [m p]. exists m. apply le_S. exact p.
Defined.

Theorem constraint_dec {n : nat} (c : constraint n) : {empty_constraint c} + {~ empty_constraint c}.
  revert c. induction n.
  - intro c. left. intros [m p]. inversion p.
  - intro c. pose (c (last_finset n)) as l. remember l as l'. destruct l'.
    + right. intro H. specialize (H (last_finset n)). change l with (c (last_finset n)) in Heql'.
      rewrite H in Heql'. inversion Heql'.
    + specialize (IHn (c o (finset_inj n))). destruct IHn.
      * left. intros [m p]. destruct (Compare_dec.le_lt_eq_dec (S m) (S n) p) as [H1 | H1].
        -- apply le_S_n in H1. specialize (e (exist (fun m : nat => m < n) m H1)).
           compute in e. rewrite <- e. erewrite (Peano_dec.le_unique _ _ p (le_S (S m) n H1)). reflexivity.
        -- inversion H1. destruct H0. rewrite Heql'. unfold l. compute.
           erewrite (Peano_dec.le_unique _ _ p (PeanoNat.Nat.lt_succ_diag_r m)). reflexivity.
      * right. intro H1. apply n0. intro m. specialize (H1 (finset_inj n m)). rewrite <- H1. reflexivity.
Qed.

Theorem covering_dec {n : nat} (f : face_lattice n) : {covering f} + {~ covering f}.
  induction f.
  - right. intro H. inversion H.
  - destruct IHf.
    + left. simpl. now right.
    + destruct (constraint_dec a).
      * left. simpl. now left.
      * right. intros [H1 | H1] ; easy.
Qed.


(* Should I setoid ? Should I SProp *)

Run TemplateProgram (tImplementTC ax4_TC "F_TC" "F" Type).
Next Obligation.
  exact (face_lattice p0).
Defined.

Definition restricts {p q : nat} (f1 : face_lattice p) (α : p ~> q) (f2 : face_lattice q) : Prop.
Admitted.

Run TemplateProgram (tImplementTC F_TC "natf_TC" "natf" (F -> Prop)).
Next Obligation.
  rename X into f. rename X0 into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1), restricts (f p0 α0) α1 (f p1 (α1 ô α0))).
Defined.

Run TemplateProgram (tImplementTC natf_TC "covers_TC" "covers" (F -> Prop)).
Next Obligation.
  rename X0 into α0. rename X into f.
  exact (covering (f p0 α0)).
Defined.

Run TemplateProgram (tImplementTC covers_TC "realize_TC" "realize" (F -> Prop)).
Next Obligation.
  rename X0 into α. rename X into f.
  specialize (f p0 α). exact (covering f). (* the problem is probably with this one, should give more constraint *)
Defined.

Definition sieve_equiv {p : nat} (S1 S2 : forall q : nat, p ~> q -> Prop) :=
  forall (q : nat) (α : p ~> q), S1 q α <-> S2 q α.

Notation "S ≈ T" := (sieve_equiv S T) (at level 65, left associativity).

(** Cofibrant propositions *)

Run TemplateProgram (tImplementTC realize_TC "cof_TC" "cof" (Prop -> Prop)).
Next Obligation.
  rename X0 into α. rename X into S.
  specialize (S p id).
  exact (exists f : (forall p0 : nat, p ~> p0 -> Fᵗ p0 p0 id),
            (fun (p0 : nat) (α : p ~> p0) => covering (f p0 α)) ≈ S).
Defined.

(* this one seems a better definition. However, i need to put it in the translation database, and i dont
 know how to do this without dirty hacks. Also, I need sigma-types translation. *)
Definition cof' : Prop -> Prop := fun s => exists f : F, s = realize f.





(** axioms on cof *)

Definition extremity {p : nat} (b : bool) (i : cube p -> cube 1) : face_lattice p.
Admitted.

Theorem extremity_correct {p : nat} (b : bool) (i : cube p -> cube 1) :
  covering (extremity b i) <-> i = I_end_map p b.
Admitted.

Run TemplateProgram (tImplementTC cof_TC "ax5_1_TC" "ax5_1" (forall (i : I) (Hi : nati i), cof (i = I0))).
Next Obligation.
  specialize (H p id).
  unshelve refine (ex_intro _ _ _).
  - intros p0 α0. exact (extremity false (i p0 α0).1s).
  - intros p0 α0. split.
    + intro H1. apply eq_is_eq. apply (extremity_correct false (i p0 α0).1s) in H1.
      apply funext_dep. intro p1. apply funext. intro α1. apply eq_sexist. simpl.
      change (id ô (id ô α1 ô α0) ô id ô id) with (id ô (α1 ô α0 ô id) ô id ô id).
      rewrite <- H.
      change (α1 ô α0 ô i p (id ô id ô id ô id)) with (α1 ô (α0 ô i p (id ô id ô id ô id))).
      rewrite H.
      change (id ô (α0 ô id) ô id ô id) with α0. simpl. rewrite H1.
      now compute.
    + destruct admitok.
Defined.

(* This thing cannot work, for in our vision of presheaves a disjunction isnt sheaf-like *)
(* Run TemplateProgram (tImplementTC ax5_1_TC "ax6_TC" "ax6" (forall (φ ψ : Prop) (Hφ : cof φ) (Hψ : cof ψ), cof (φ \/ ψ))). *)







Definition isEquiv (A B : Type) : Type :=
  Σ (f : A -> B) (g : B -> A), (f o g = fun x => x) /\ (g o f = fun x => x).

Notation "A ≅ B" := (isEquiv A B) (at level 65, left associativity).

Run TemplateProgram (TC1 <- tTranslate cof_TC "fcompose" ;;
                         TC2 <- tTranslate TC1 "isEquiv" ;;
                         tmDefinition "isEq_TC" TC2).

Definition projEq1' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
  : isEquivᵗ p A B p id -> (forall (p0 : nat) (α : p ~> p0),
                              (forall (p1 : nat) (α0 : p0 ~> p1), A p1 (α0 ô α) p1 id) ->
                              B p0 α p0 id).
  intros [x _]. exact x.
Defined.

Definition projEq2' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
  : isEquivᵗ p A B p id -> (forall (p0 : nat) (α : p ~> p0),
                              (forall (p1 : nat) (α0 : p0 ~> p1), B p1 (α0 ô α) p1 id) ->
                              A p0 α p0 id).
  intros [x y]. destruct (y p id) as [z _]. exact z.
Defined.

Definition projEq3' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           (ie : isEquivᵗ p A B p id)
           : (forall (p0 : 𝐂_obj) (α : p ~> p0),
                 eqᵗ p0
                     (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) =>
                        (forall (p3 : nat) (α2 : p2 ~> p3),
                            B p3 (α2 ô α1 ô α0 ô α) p3 id) ->
                        B p2 (α1 ô α0 ô α) p2 id)
                     (fun (p1 : nat) (α0 : p0 ~> p1) =>
                        fcomposeᵗ p1
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α)))
                     (fun (p1 : nat) (α0 : p0 ~> p1)
                        (x : forall (p2 : nat) (α1 : p1 ~> p2),
                            B p2 (α1 ô α0 ô α) p2 id) =>
                        x p1 id)).
  destruct ie as [x y]. simpl.
  destruct (y p id) as [z t]. destruct (t p id) as [a b].
  exact a.
Defined.

Definition projEq4' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           (ie : isEquivᵗ p A B p id)
           : (forall (p0 : 𝐂_obj) (α : p ~> p0),
                 eqᵗ p0
                     (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) =>
                        (forall (p3 : nat) (α2 : p2 ~> p3),
                            A p3 (α2 ô α1 ô α0 ô α) p3 id) ->
                        A p2 (α1 ô α0 ô α) p2 id)
                     (fun (p1 : nat) (α0 : p0 ~> p1) =>
                        fcomposeᵗ p1
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α)))
                     (fun (p1 : nat) (α0 : p0 ~> p1)
                        (x : forall (p2 : nat) (α1 : p1 ~> p2),
                            A p2 (α1 ô α0 ô α) p2 id) =>
                        x p1 id)).
  destruct ie as [x y]. simpl. destruct (y p id) as [z t]. destruct (t p id) as [a b]. exact b.
Defined.

Theorem covering_assumption {p : nat} {f : face_lattice p} (c : covering f) : covering_dec f = left c.
Proof.
  destruct (covering_dec f).
  - apply f_equal. apply proof_irr.
  - absurd (covering f). exact n. exact c.
Qed.

Theorem noncovering_assumption {p : nat} {f : face_lattice p} (c : ~ covering f) : covering_dec f = right c.
Proof.
  destruct (covering_dec f).
  - absurd (covering f). exact c. exact c0.
  - apply f_equal. apply proof_irr.
Qed.



Theorem restrict_covering {p q : nat} {α : p ~> q} {f1 : face_lattice p} {f2 : face_lattice q}
        (H : restricts f1 α f2)
  : covering f1 -> covering f2.
Proof.
Admitted.

Run TemplateProgram (tImplementTC isEq_TC "ax9_TC" "ax9"
                                  (forall (f : F) (Hf : natf f)
                                     (A : covers f -> Type) (B : Type) (s : forall u : (covers f), A u ≅ B),
                                      Σ (B' : Type) (s' : B' ≅ B), (forall u : (covers f), A u = B'))).
Next Obligation.
  revert p f H A B X. Abort.

Definition test : forall (p : nat) (f : forall p0 : nat, p ~> p0 -> Fᵗ p0 p0 id),
  (forall (p0 : nat) (α : p ~> p0), natfᵗ p0 (fun (p1 : nat) (α0 : p0 ~> p1) => f p1 (id ô α0 ô α ô id)) p0 id) ->
  forall
    (A : forall (p0 : nat) (α : p ~> p0),
         (forall (p1 : nat) (α0 : p0 ~> p1),
          coversᵗ p1 (fun (p2 : nat) (α1 : p1 ~> p2) => f p2 (id ô α1 ô α0 ô id ô α ô id ô id)) p1 id) ->
         forall p1 : nat, p0 ~> p1 -> Type) (B : forall p0 : nat, p ~> p0 -> forall p1 : nat, p0 ~> p1 -> Type),
  (forall (p0 : nat) (α : p ~> p0)
     (u : forall (p1 : nat) (α0 : p0 ~> p1),
          coversᵗ p1 (fun (p2 : nat) (α1 : p1 ~> p2) => f p2 (id ô α1 ô α0 ô id ô α ô id ô id ô id ô id)) p1 id),
   isEquivᵗ p0
     (fun (p1 : nat) (α0 : p0 ~> p1) =>
      A p1 (id ô α0 ô id ô α ô id ô id) (fun (p2 : nat) (α1 : p1 ~> p2) => u p2 (id ô α1 ô α0)))
     (fun (p1 : nat) (α0 : p0 ~> p1) => B p1 (id ô α0 ô id ô α ô id)) p0 id) ->
  sigTᵗ p (fun (p0 : nat) (_ : p ~> p0) (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type)
    (fun (p0 : nat) (α : p ~> p0) (B' : forall p1 : nat, p0 ~> p1 -> forall p2 : nat, p1 ~> p2 -> Type)
       (p1 : nat) (α0 : p0 ~> p1) =>
     sigTᵗ p1
       (fun (p2 : nat) (α1 : p1 ~> p2) =>
        isEquivᵗ p2 (fun (p3 : nat) (α2 : p2 ~> p3) => B' p3 (id ô α2 ô (id ô α1 ô α0)))
          (fun (p3 : nat) (α2 : p2 ~> p3) => B p3 (id ô α2 ô (id ô α1 ô α0) ô (id ô α ô id) ô id)))
       (fun (p2 : nat) (α1 : p1 ~> p2)
          (_ : forall (p3 : nat) (α2 : p2 ~> p3),
               isEquivᵗ p3 (fun (p4 : nat) (α3 : p3 ~> p4) => B' p4 (id ô α3 ô α2 ô (id ô α1 ô α0)))
                 (fun (p4 : nat) (α3 : p3 ~> p4) => B p4 (id ô α3 ô α2 ô (id ô α1 ô α0) ô (id ô α ô id) ô id)) p3 id)
          (p3 : nat) (α2 : p2 ~> p3) =>
        forall
          u : forall (p4 : nat) (α3 : p3 ~> p4),
              coversᵗ p4
                (fun (p5 : nat) (α4 : p4 ~> p5) =>
                 f p5 (id ô α4 ô α3 ô α2 ô (id ô α1 ô α0) ô (id ô α ô id) ô id ô id ô id ô id)) p4 id,
        eqᵗ p3 (fun (p4 : nat) (_ : p3 ~> p4) (p5 : nat) (_ : p4 ~> p5) => forall p6 : nat, p5 ~> p6 -> Type)
          (fun (p4 : nat) (α3 : p3 ~> p4) =>
           A p4 (id ô (id ô α3 ô id) ô α2 ô (id ô α1 ô α0) ô (id ô α ô id) ô id ô id)
             (fun (p5 : nat) (α4 : p4 ~> p5) => u p5 (id ô α4 ô (id ô α3 ô id))))
          (fun (p4 : nat) (α3 : p3 ~> p4) => B' p4 (id ô (id ô α3 ô id) ô α2 ô (id ô α1 ô α0))))).
  intros p f H A B X.
  rename X into s. rename H into Hf.
  unfold Fᵗ in f. unfold Fᵗ_obligation_1 in f.
  unshelve refine (existTᵗ _ _ _ _ _).
  (* Define B' *)
  - intros p0 α0 p1 α1.
    refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p0 α0))) ; intro c.
    + eapply (A p0 α0).
      * intros p2 α2. unfold coversᵗ. unfold coversᵗ_obligation_1.
        change (id ô id ô α2 ô id ô α0 ô id ô id) with (α2 ô α0).
        eapply restrict_covering.
        -- specialize (Hf p0 α0 p2 α2). exact Hf.
        -- exact c.
      * exact α1.
    + exact (B p0 α0 p1 α1).
  - intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _).
    (* Prove B ≅ B' *)
    + intros p1 α1. unfold isEquivᵗ. unshelve refine (existTᵗ _ _ _ _ _).
      (* First direction of equivalence *)
      * intros p2 α2 HB'.
        refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p2 (α2 ô α1 ô α0)))) ; intro c.
        -- specialize (s p2 (α2 ô α1 ô α0)).
           assert (forall (p3 : nat) (α3 : p2 ~> p3),
                      coversᵗ p3 (fun (p4 : nat) (α4 : p3 ~> p4) => f p4 (α4 ô α3 ô α2 ô α1 ô α0)) p3 id) as Hc'.
           { intros p3 α3. eapply restrict_covering.
             - exact (Hf p2 (α2 ô α1 ô α0) p3 α3).
             - exact c. }
           pose (projEq1' (s Hc')) as g. specialize (g p2 id). apply g.
           intros p3 α3. specialize (HB' p3 α3).
           apply (restrict_covering (Hf p2 (α2 ô α1 ô α0) p3 α3)) in c.
           assert ((fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c) =
                   (fun (p4 : nat) (α4 : p3 ~> p4) => Hc' p4 (id ô α4 ô (α3 ô id)))) as Hpi.
           { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
           apply (transport _ (covering_assumption c)) in HB'. simpl in HB'.
           apply (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x p3 id) Hpi) in HB'.
           exact HB'.
        -- specialize (HB' p2 id).
           apply (transport _ (noncovering_assumption c)) in HB'. simpl in HB'.
           exact HB'.
      * intros p2 α2. unshelve refine (existTᵗ _ _ _ _ _).
        (* Second direction of equivalence *)
        -- intros p3 α3 HB.
           match goal with
           | |- ?GG => refine (sumbool_rect (fun X => GG) _ _ (covering_dec (f p3 (α3 ô α2 ô α1 ô α0)))) ; intro c
           end.
           ++ apply (transport _ (sym (covering_assumption c))). simpl.
              assert (forall (p4 : nat) (α4 : p3 ~> p4),
                         coversᵗ p4 (fun (p5 : nat) (α5 : p4 ~> p5) => f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)) p4 id) as Hc'.
              { intros p4 α4. eapply restrict_covering.
                - exact (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4).
                - exact c. }
              pose (projEq2' (s p3 (α3 ô α2 ô α1 ô α0) Hc')) as g. specialize (g p3 id). simpl in g.
              assert ((fun (p2 : nat) (α1 : p3 ~> p2) => Hc' p2 (id ô α1 ô id)) =
                      (fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c)) as Hpi.
              { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
              refine (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x _ _) Hpi _). apply g.
              intros p4 α4.
              exact (HB p4 α4).
           ++ apply (transport _ (sym (noncovering_assumption c))). simpl.
              exact (HB p3 id).
        -- intros p3 α3. apply conjᵗ.
           (* First identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- transport ?X2 ?X3 (transport ?X4 ?X5 (sumbool_rect ?X6 ?X7 ?X8 _)) = ?X1 =>
                   apply (transport (fun x => transport X2 X3 (transport X4 X5 (sumbool_rect X6 X7 X8 x)) = X1) H)
                 end. simpl. etransitivity.
                 refine (f_equal _ _). eapply (sym (transport_trans _ _ _ _)).
                 etransitivity. refine (f_equal _ _). apply transport_sym_trans. etransitivity.
                 refine (sym (transport_trans _ _ _ _)).
                 refine (transport_ap (fun x => (projEq2'
                                                (s p6 (id ô (id ô α6) ô (id ô α5 ô id) ô (id ô α4 ô id) ô α3 ô α2 ô α1 ô α0) x) p6 id
                                                (fun (p7 : nat) (α7 : p6 ~> p7) => b p7 (id ô α7 ô α6)))) _).
                 simpl.

                 pose ((s p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)
                          (fun (p6 : nat) (α6 : p5 ~> p6) =>
                             restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))) as ss.
                 pose proof (projEq3' ss p5 id) as Hs. inversion Hs. clear Hs.
                 unfold fcomposeᵗ in H0. unfold ss in H0.
                 apply apD10 with (x := p5) in H0. apply apD10 with (x := id) in H0.
                 apply apD10 with (x := b) in H0.
                 (** * I think we need some kind of naturality for s, unless we somehow manage to call it with a higher forcing condition *)
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_sym_trans _ _ _). reflexivity.
           (* Second identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b'.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _). refine (f_equal _ _). refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) H)
                 end. simpl. reflexivity. etransitivity. refine (f_equal _ _). refine (f_equal _ _).
                 reflexivity.
                 (** * Same here *)
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_trans_sym _ _ _).
                 reflexivity.
    (* Prove A u = B' *)
    + intros p1 α1. intro Hφ. apply eq_is_eq.
      apply funext_dep. intro p2. apply funext_dep. intro α2.
      apply funext_dep. intro p3. apply funext. intro α3. simpl.
      change (id ô (id ô α2 ô id) ô id ô (id ô α1 ô id) ô α0) with (α2 ô α1 ô α0).
      destruct (covering_dec (f p2 (α2 ô α1 ô α0))).
      * assert ((fun (p5 : nat) (α4 : p2 ~> p5) => Hφ p5 (id ô α4 ô (id ô α2 ô id))) =
                (fun (p4 : nat) (α4 : p2 ~> p4) => restrict_covering (Hf p2 (α2 ô α1 ô α0) p4 α4) c)) as Hpi.
        { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
        refine (f_equal (fun x => A p2 _ x _ _) _). exact Hpi.
      * destruct (n (Hφ p2 α2)).
Defined.

Set Printing Universes.
Print test.