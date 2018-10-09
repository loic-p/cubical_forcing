Require Import List.
Require Import String.
Require Import Omega.
Require Import Cubes.axioms
        Cubes.sprop_utils
        Cubes.arith_lemmas
        Cubes.hott_lemmas
        Cubes.cubes
        Cubes.cartesian
        Cubes.forcing_setup.

Import MonadNotation.


(** Definition of the interval *)

Run TemplateProgram (tImplementTC complete_TC "I_TC" "I" Type).
Next Obligation.
  exact (1 ~> p0).
Defined.


Definition initial_word_aux (p : nat) (q : nat) : word (p+q) p.
  revert p. induction q.
  - intro p. rewrite <- (plus_n_O p). exact cubes.empty.
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



(** J is another interval with naturality conditions as an experiment **)


Run TemplateProgram (tImplementTC I1_TC "natp_TC" "natp" (Prop -> Prop)).
Next Obligation.
  rename X into S. rename X0 into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1), S p0 α0 p1 α1 <-> S p1 (α1 ô α0) p1 id).
Defined.

Run TemplateProgram (tImplementTC natp_TC "nati_TC" "nati" (I -> Prop)).
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