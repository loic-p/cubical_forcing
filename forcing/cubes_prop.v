Require Import String.
Require Import List.

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

Notation "f 'o' g" := (Basics.compose f g) (at level 50, left associativity).

Definition funext {A B : Type} := @functional_extensionality A B.



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

Inductive sFalse : SProp :=.

Notation "x .1s" := x.(spi1 _) (at level 3).
Notation "x .2s" := x.(spi2 _) (at level 3).

Notation "( a ; b )s" := {| spi1 := a ; spi2 := b |}.

Theorem eq_sexist {A : Type} {P : A -> SProp} (a b : sexists P) (e : a.1s = b.1s) :
  a = b.
  destruct a, b. simpl in e. destruct e. reflexivity.
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

Definition le_imp_eq_lt : forall n m : nat, n <= m -> {n = m} + {n < m}.
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







(** Definition of the cubes *)
(* we use the lawvere theory of 0, 1, ∨, ∧ with weakening, contraction and exchange
 n ~> m then corresponds to monotone functions 2^m -> 2^n *)

Definition finset (n : nat) : Set :=
  {m : nat | m < n}.

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

Theorem concat_sound {a b c : nat} (w1 : word b c) (w2 : word a b) :
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
  - apply spair_s with (a:=concat_word w' w). apply concat_sound.
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

Definition cube_le {a : nat} (c d : cube a) : Prop :=
  forall x : finset a, (c x = true) -> (d x = true).

Definition monotone {a b : nat} (f : cube a -> cube b) : Prop :=
  forall c d : cube a, cube_le c d -> cube_le (f c) (f d).

Definition admissible' {a b : nat} (f : cube a -> cube b) : Prop :=
  exists w : word a b, f = comp_word w.

Definition extend_cube {a : nat} (c : cube a) (b : bool) : cube (S a).
  intros [i p]. destruct i.
  - exact b.
  - apply le_S_n in p. apply c. exists i. exact p.
Defined.

Definition restr {a : nat} (f : cube (S a) -> cube 1) (b : bool) : cube a -> cube 1 :=
  fun x : cube a => f (extend_cube x b).

Theorem monotone_restr {a : nat} (f : cube (S a) -> cube 1) (b : bool) (H : monotone f)
  : monotone (restr f b).
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

Definition cube_arrow_and {a b : nat} (f : cube a -> cube 1) (g : cube b -> cube 1)
  : cube (a + b) -> cube 1.
  intro c. destruct (split_cube c). apply f in c0. apply g in c1.
  intro x. exact (andb (c0 x) (c1 x)).
Defined.

Theorem cube_arrow_and_amd {a b : nat} (f : cube a -> cube 1) (g : cube b -> cube 1)
        (p : admissible f) (q : admissible g)
  : admissible (cube_arrow_and f g).
Admitted.

Definition cube_arrow_or {a b : nat} (f : cube a -> cube 1) (g : cube b -> cube 1)
  : cube (a + b) -> cube 1.
  intro c. destruct (split_cube c). apply f in c0. apply g in c1.
  intro x. exact (orb (c0 x) (c1 x)).
Defined.

Theorem cube_arrow_or_amd {a b : nat} (f : cube a -> cube 1) (g : cube b -> cube 1)
        (p : admissible f) (q : admissible g)
  : admissible (cube_arrow_or f g).
Admitted.

(* Theorem monotone_fact {a : nat} (f : cube (S a) -> cube 1) (H : monotone f) : *)
(*   f = (cube_arrow_or (cube_arrow_and (fun x : cube 1 => x) (restr f true)) (restr f false)). *)

Theorem monotone_impl_adm_1 {a : nat} (f : cube a -> cube 1) : monotone f -> admissible' f.
Proof.
  induction a.
  - admit.
  - intro H. remember H as H1. clear HeqH1.
    apply monotone_restr with (b := true) in H. apply monotone_restr with (b := false) in H1.
    apply IHa in H. apply IHa in H1.
Admitted.

Theorem monotone_iff_adm {a b : nat} (f : cube a -> cube b) : monotone f <-> admissible' f.
Admitted.

Theorem decide_adm {a b : nat} (f : cube a -> cube b) :
  admissible' f \/ (admissible' f -> False).
Admitted.

Theorem recover_word {a b : nat} (f : a ~> b)
  : | w : word b a | f.1s = comp_word w }.
Proof.
  destruct (decide_adm (f.1s)).
  - destruct H. easy.
  - assert sFalse. destruct f as [f H1]. destruct H1 as [w H1].
    assert False. apply H. exists w. simpl. apply eqs_eq. exact H1.
    destruct H0.
    destruct H0.
Qed.

Theorem recover_word' {a b : nat} (f : a ~> b)
  : exists w : word b a, f.1s = comp_word w.
Proof.
  destruct (decide_adm (f.1s)).
  - destruct H. easy.
  - assert sFalse. destruct f as [f H1]. destruct H1 as [w H1].
    assert False. apply H. exists w. simpl. apply eqs_eq. exact H1.
    destruct H0.
    destruct H0.
Qed.

Theorem arrow_monotone {a b : nat} (f : a ~> b)
  : monotone f.1s.
Proof.
  apply monotone_iff_adm. apply recover_word.
Qed.





(** Cartesian structure *)

(* based on the decidability part. This actually only requires the category of cubes having contractions *)

Definition fuse_cube_maps {a b c : nat} : (cube a -> cube b) * (cube a -> cube c) -> (cube a -> cube (b + c)).
Admitted.

Theorem fused_monotone {a b c : nat} (f : cube a -> cube b) (g : cube a -> cube c) :
  monotone f -> monotone g -> monotone (fuse_cube_maps (f, g)).
Admitted.

Definition fuse_arrows {a b c : nat} : (a ~> c) * (b ~> c) -> (a + b ~> c).
  intros [f g].
  refine ( fuse_cube_maps (f.1s, g.1s) ; _ )s.
  pose proof (arrow_monotone f). pose proof (arrow_monotone g).
  assert (admissible' (fuse_cube_maps (f.1s, g.1s))).
  apply monotone_iff_adm. now apply fused_monotone.
  destruct H1 as [w H1].
  eapply spair_s. apply eq_eqs. exact H1.
Defined.

Definition split_cube_map {a b c : nat} : (cube a -> cube (b + c)) -> (cube a -> cube b) * (cube a -> cube c).
Admitted.

Theorem splitted_monotone {a b c : nat} (f : cube a -> cube (b + c)) :
  monotone f -> monotone (fst (split_cube_map f)) /\ monotone (snd (split_cube_map f)).
Admitted.

Definition split_arrow {a b c : nat} : (a + b ~> c) -> (a ~> c) * (b ~> c).
  intro f. split.
  - refine ( fst (split_cube_map f.1s) ; _ )s.
    pose proof (arrow_monotone f). destruct (splitted_monotone f.1s H) as [H1 _].
    assert (admissible' (fst (split_cube_map f.1s))). apply monotone_iff_adm. exact H1.
    destruct H0 as [w H0]. eapply spair_s. apply eq_eqs. exact H0.
  - refine ( snd (split_cube_map f.1s) ; _ )s.
    pose proof (arrow_monotone f). destruct (splitted_monotone f.1s H) as [_ H1].
    assert (admissible' (snd (split_cube_map f.1s))). apply monotone_iff_adm. Show Proof. exact H1.
    destruct H0 as [w H0]. eapply spair_s. apply eq_eqs. exact H0.
Defined.

Theorem cartesian_lemma1 {a b c : nat} : forall f : cube a -> cube (b + c), fuse_cube_maps (split_cube_map f) = f.
Admitted.

Theorem cartesian_lemma2 {a b c : nat}
  : forall (f : cube a -> cube b) (g : cube a -> cube c), split_cube_map (fuse_cube_maps (f, g)) = (f, g).
Admitted.

Theorem cartesian_iso1 {a b c : nat} : fuse_arrows o split_arrow = fun x : a + b ~> c => x.
Proof.
  apply funext. intro f. apply eq_sexist.
  simpl. rewrite <- (surjective_pairing (split_cube_map f.1s)).
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



(** Definition of the ○ modality *)

Run TemplateProgram (tImplementTC I1_TC "circle_TC" "circle" (Type -> Type)).
Next Obligation.
  exact (X p0 X0 p0 id).
Defined.

Notation O := circle.


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

Run TemplateProgram (TC <- tAddExistingInd circle_TC "Coq.Init.Logic.eq" "eqᵗ" ;;
                          tmDefinition "eq_TC" TC).

Inductive Falseᵗ (p : 𝐂_obj) := .

Run TemplateProgram (TC <- tAddExistingInd eq_TC "Coq.Init.Logic.False" "Falseᵗ" ;;
                        tmDefinition "False_TC" TC).

Inductive orᵗ (p : 𝐂_obj) (A B : forall p0 : 𝐂_obj, p ~> p0 -> forall p1 : 𝐂_obj, p0 ~> p1 -> Prop) : Prop :=
    or_introlᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 α p0 id) -> orᵗ p A B
  | or_introrᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), B p0 α p0 id) -> orᵗ p A B.

Run TemplateProgram (TC <- tAddExistingInd False_TC "Coq.Init.Logic.or" "orᵗ" ;;
                        tmDefinition "or_TC" TC).

Definition complete_TC := or_TC.




(** Axiom 1 : connectedness *)

Definition unique : cube 0.
  unfold cube. unfold finset. intros [m H]. apply pos_ge_0 in H. inversion H.
Defined.

Definition zero_finset (p : nat) : finset (S p).
  exists 0. easy.
Defined.

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

Run TemplateProgram (tImplementTC complete_TC "nat_pred_TC" "nat_pred" (forall (A : Type) (P : A -> Prop), Prop)).
Next Obligation.
  exact (forall q (β : p0 ~> q) (a : forall p1 (α1 : p0 ~> p1), A p1 (α1 ô X0) p1 id),
            X q (β ô X0) (fun p1 (α : q ~> p1) => a p1 (α ô β)) q id =
            X p0 X0 (fun p1 (α : p0 ~> p1) => a p1 α) q β).
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

Theorem side_face (p q : nat) (b : bool) α :
  side p ((α ô face_map p b).1s (fun _ : finset q => false)) = b.
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

Run TemplateProgram (tImplementTC nat_pred_TC "ax1_TC" "ax1"
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
      apply functional_extensionality_dep. intro r.
      apply functional_extensionality_dep. intro γ.
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
      apply functional_extensionality_dep. intro r.
      apply functional_extensionality_dep. intro δ.
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
      apply functional_extensionality_dep. intro r.
      apply functional_extensionality_dep. intro δ.
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
      apply functional_extensionality_dep. intro r.
      apply functional_extensionality_dep. intro δ.
      change (id ô δ ô β ô id ô (id ô face_map q true ô id)) with (δ ô β ô face_map q true).
      unfold h. rewrite <- homotopy_restriction1. reflexivity. rewrite H.
      exact H2.
Defined.





(** Axiom 2 : distinct end points *)

Definition lowest_corner (p : nat) : cube p.
  intro. exact false.
Defined.

Run TemplateProgram (tImplementTC ax1_TC "ax2_TC" "ax2" (I0 = I1 -> False)).
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
  apply recover_word in f.
Admitted.

Definition meet_arrow {p : nat} (f : 1 + 1 ~> p) : 1 ~> p.
Admitted.

Run TemplateProgram (tImplementTC ax2_TC "join_i_TC" "join_i" (I -> I -> I)).
Next Obligation.
  rename X into i1. rename X0 into i2.
  specialize (i1 p id). specialize (i2 p id).
  pose (fuse_arrows (i1, i2)). exact (join_arrow a).
Defined.

Run TemplateProgram (tImplementTC join_i_TC "meet_i_TC" "meet_i" (I -> I -> I)).
Next Obligation.
  rename X into i1. rename X0 into i2.
  specialize (i1 p id). specialize (i2 p id).
  pose (fuse_arrows (i1, i2)). exact (meet_arrow a).
Defined.

Notation "a ⊓ b" := (join_i a b) (at level 65, left associativity).
Notation "a ⊔ b" := (meet_i a b) (at level 65, left associativity).

(** Axiom 3 : *)
