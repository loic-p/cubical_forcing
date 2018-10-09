Require Import Template.monad_utils Template.Ast Template.AstUtils
        Template.Template Template.LiftSubst.
Require Import String PeanoNat.
Require Import Template.Checker.
Require Import Template.Typing.

Require Import Forcing.TemplateForcing.
Require Import Forcing.translation_utils.
Require Import TFUtils.
Require Import List.

Import ListNotations.
Import MonadNotation.
Open Scope string_scope.


(* To be able to work with values in SProp we define boxing/unboxing *)
Inductive sBox (A : SProp) : Prop := sbox : A -> sBox A.

Definition ubox {A : SProp} (bA : sBox A) : A :=
  match bA with
    sbox _ X => X
  end.

Definition fn_out_sbox (P : SProp) (A : Type) (f : P -> A) : sBox P -> A
  := fun x => f (ubox x).

Definition fn_out_sbox_dep (P : SProp) (A : P -> Type) (f : forall (p : P), A p)
  : forall (q : sBox P), A (ubox q) := fun x => f (ubox x).

(* Some axioms *)

Axiom functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.

Arguments functional_extensionality_dep {_ _} _ _ _.

(* Now we can prove the version of funext with the first type being SProp - thanks, Gaëtan! *)
Lemma functional_extensionality_dep_s :
  forall (A : SProp) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g.
Proof.
  intros A B f g H.
  pose (fn_out_sbox_dep _ _ f) as f'.
  pose (fn_out_sbox_dep _ _ g) as g'.
  assert (H' : f' = g').
  { apply functional_extensionality_dep. intros [x]. apply (H x). }
  (* we precompose each side with [sbox] and use the fact that composition [ubox ∘ sbox] is [id]  *)
  pose (fun (f : forall q : sBox A, B (ubox q)) (x : A) => (f (sbox _ x))) as d.
  apply f_equal with (f:=d) in H'. subst d. apply H'.
Qed.

(* All attempts use [rewrite] or [subst] fail, because [eq_sind_r] is not defined.
   We define it, but for some reason the tactics still complain about [eq_sind_r] *)
Definition eq_sind_r : forall (A : Type) (x : A) (P : A -> SProp),
    P x -> forall y : A, y = x -> P y.
Proof.
  intros A x P H y Heq. apply ubox. subst. apply sbox. exact H.
Defined.

Inductive sFalse : SProp :=.

Inductive sTrue : SProp := I.

Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

(* TODO: try this definition instead *)
Fixpoint sle_fun (n m : nat) : SProp :=
  match n,m with
  | 0,_ => sTrue
  | S n, S m => sle_fun n m
  | S m, 0 => sFalse
  end.

Definition sle_refl (n : nat) : sle n n.
Proof.
  induction n;constructor;auto.
Qed.

Definition sle_Sn_Sm {n m} : sle (S n) (S m) -> sle n m.
Proof.
  intros H.
  inversion H. apply ubox. subst. apply sbox. exact H2.
Qed.

Definition sle_n_m_S {n m} : sle n m -> sle (S n) (S m).
Proof.
  intros H. constructor;exact H.
Qed.

Lemma sle_Sn_0 : forall n, sle (S n) 0 -> sFalse.
Proof.
  unfold Hom; intros n H.
  inversion H.
Qed.

Definition sle_trans n m p (H : sle n m) (H': sle m  p) : sle n p.
Proof.
  revert H'. revert p. induction H.
  - intros p H'. apply sle_0.
  - intros p H'. inversion H'. apply ubox. subst. apply sbox. apply sle_S. apply IHsle;auto.
Qed.

(* This does not work, fails with the error:
   Fixpoints on proof irrelevant inductive types should produce proof irrelevant
   values.*)
Fixpoint sle_trans' n m p (H : sle n m) (H': sle m  p) {struct H} : sle n p.
Proof.
  destruct H. apply sle_0.
  inversion H'. apply ubox. subst. apply sbox. apply sle_S. exact (sle_trans _ _ _ H H1).
Abort.

Definition sle_Sn (n : nat) : sle n (S n).
Proof.
  induction n; constructor; auto.
Qed.

Definition nat_obj : Type := nat.
Definition nat_hom (P Q : nat_obj): SProp := sle Q P.
Notation "P ≥ Q" := (nat_hom P Q) (at level 70).

Definition id_nat_hom (P : nat_obj) : P ≥ P := sle_refl P.
Notation "# R" := (id_nat_hom R) (at level 70).

Definition nat_comp (A B C : nat_obj) (g : B ≥ C) (f : A ≥ B) : nat_hom A C
  := sle_trans _ _ _ g f.

Notation "g ∘ f" := (nat_comp _ _ _ g f) (at level 40).


Arguments sbox {_}.

(* Now, laws hold definitionally, thanks to SProp *)
(* We use sbox'ed version to prove this *)
Lemma nat_cat_left_id P R (g : R ≥ P)  : sbox (g ∘ (# _)) = sbox g.
Proof. reflexivity. Qed.

Lemma nat_cat_right_id P R (f : P ≥ R)  : sbox (f ∘ (# _)) = sbox f.
Proof. reflexivity. Qed.

Lemma nat_cat_assoc P Q R S (f : S ≥ Q) (g : R ≥ S) (h : P ≥ R):
  sbox (f ∘ (g ∘ h)) = sbox ((f ∘ g) ∘ h).
Proof. reflexivity. Qed.

Quote Definition q_nat_obj := nat_obj.
Quote Definition q_nat_hom := nat_hom.
Quote Definition q_id_nat_hom := id_nat_hom.
Quote Definition q_nat_comp := nat_comp.


(** A category of nat with the ordering *)
Definition nat_cat : category :=
  mkCat q_nat_obj q_nat_hom q_id_nat_hom q_nat_comp.

Instance GuardRec : Translation := ForcingTranslation nat_cat.

(* Building required context to pass to the translation *)

Run TemplateProgram (prg <- tmQuoteRec nat_hom ;;
                     tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context:= (reconstruct_global_context g_ctx,[]).


(* We use modules for namespacing, because Template Coq doesn't work well with sections *)


(** ** The definition of [later] operator *)
Module Later.
  Run TemplateProgram (tImplementTC ΣE "later_TC" "later" (Type->Type)).
  Next Obligation.
    destruct p0.
    - exact unit.
    - exact (X p0 (sle_Sn p0 ∘ H) p0 (# _)).
  Defined.

  Notation "⊳ A" := (later A) (at level 40).

  (* Iterated version of later *)
  Fixpoint nlater (n : nat) (A : Type) : Type :=
    match n with
    | O => A
    | S m => ⊳ (nlater m A)
    end.

  Notation "'⊳[' n ']' A" := (nlater n A) (at level 40).

  Run TemplateProgram
      (tImplementTC later_TC "later_app_TC" "later_app"
                   (forall A B (t : ⊳ (A -> B)) (u : ⊳ A), ⊳ B)).
  Next Obligation.
    destruct p.
    - cbv. exact tt.
    - refine (X (S p) (# _) _). intros q β.
      refine (X0 (S q) (sle_n_m_S β)).
  Defined.
  Notation "t ⊙ u" := (later_app _ _ t u) (at level 40).

  Run TemplateProgram
      (tImplementTC later_app_TC "later_unapp_TC" "later_unapp"
                   (forall A B (t : ⊳ A -> ⊳ B), ⊳ (A -> B))).
  Next Obligation.
    destruct p.
    - exact tt.
    - simpl. intros A'.
      pose (X (S p) (# _)) as f. apply f.
      intros. destruct p1.
      * exact tt.
      * simpl. apply (A' p1 (sle_Sn_Sm α0)).
  Defined.

  Run TemplateProgram
      (tImplementTC later_unapp_TC "nextp_TC" "nextp" (forall {T:Type}, T -> ⊳ T)).
  Next Obligation.
    destruct p.
    - exact tt.
    - simpl. refine (X p _).
  Defined.

  (** An action of the [later] endofunctor on arrows *)
  Definition later_funct_arrow : forall A B, (A -> B) -> (⊳A -> ⊳B)
    := fun _ _ x => later_app _ _ (nextp _ x).

  Notation "⊳_f f" := (later_funct_arrow _ _ f) (at level 40).

  (** We copy translated definitions of [eq] generated by the OCaml
     forcing plugin, because inducives are not supported yet by the
     template-coq forcing translation *)
  Inductive eqᵗ (p : nat_obj) (A : forall p0 : nat_obj, p ≥ p0 -> forall p : nat_obj, p0 ≥ p -> Type)
  (a : forall (p0 : nat_obj) (α : p ≥ p0), A p0 α p0 (# _))
    : (forall (p0 : nat_obj) (α : p ≥ p0), A p0 α p0 (# _)) -> Type :=
    eq_reflᵗ : eqᵗ p A a a.

  (* This definition will fail if we leave the type of [A] implicit. *)
  Definition eq_is_eq :
    forall p (A : forall x : nat_obj, p ≥ x -> forall x1 : nat_obj, x ≥ x1 -> Type)
           (x y: forall p0 (f:p ≥ p0), A p0 f p0 (# _)),
      x = y -> eqᵗ p _ x y.
  Proof.
    intros. rewrite H. apply eq_reflᵗ.
  Qed.

  Run TemplateProgram (TC <- tAddExistingInd nextp_TC "Coq.Init.Logic.eq" "eqᵗ" ;;
                          tmDefinition "ctx_with_eq" TC).

  Definition fun_comp {A B C} (g : B -> C) (f : A -> B)  : A -> C := fun x => g (f x).
  (* Importing Basics leads to the notation conflict with the function composition *)
  (* TODO : think about notation *)
  Notation "g ∘f f" := (fun_comp g f) (at level 40).

  (** Later is an endofunctor and respects composition *)
  Run TemplateProgram
      ( TC <- tTranslate ctx_with_eq "fun_comp" ;;
        TC' <- tTranslate TC "later_funct_arrow" ;;
        tImplementTC TC' "lrc_TC" "later_resp_comp"
        (forall {A B C} (f : A -> B) (g : B -> C),  ⊳_f (g ∘f f) = (⊳_f g) ∘f (⊳_f f))).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q; reflexivity.
  Qed.

  Run TemplateProgram
      (tImplement lrc_TC "next_id"
                  (forall (A : Type) (u : ⊳ A),
                      (nextp _ (fun (x : A) => x) ⊙ u) = u)).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q. destruct q.
    + simpl. destruct (u 0 (sle_0 p)). reflexivity.
    + reflexivity.
  Defined.

  (** Later is an endofunctor and respects composition *)
  Lemma later_resp_id {A : Type} : ⊳_f (id (A:=A)) = id.
  Proof.
    unfold later_funct_arrow.
    apply functional_extensionality_dep.
    intros. rewrite next_id. reflexivity.
  Qed.

  (* NOTE: this lemma was marked as "the proof should be eq_refl" in development of 2012 *)
  Run TemplateProgram
      (tImplementTC lrc_TC "lau_TC" "later_app_unapp"
                    (forall A B (f: ⊳A -> ⊳B), later_app _ _ (later_unapp _ _ f) = f)).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    apply functional_extensionality_dep. intros x.
    destruct q.
    - (* NOTE: we have to destruct  [f 0 α] of type [unit] here to be able to prove by
         reflexivity. *)
      destruct (f 0 α). reflexivity.
    - simpl. apply f_equal.
      apply functional_extensionality_dep.
      intros q1.
      apply functional_extensionality_dep_s.
      intros α1.
      destruct q1.
      * destruct (x 0 α1). reflexivity.
      * reflexivity.
  Qed.

  (* NOTE: this lemma was marked as "the proof should be eq_refl" in development of 2012 *)
  Run TemplateProgram
      (tImplementTC lau_TC "lua_TC" "later_unapp_app"
                    (forall A B (f: ⊳ (A->B)), later_unapp _ _ (later_app _ _ f) = f)).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q.
    - simpl. destruct (f 0 α). reflexivity.
    - reflexivity.
  Qed.

  (* NOTE: this lemma was marked as "the proof should be eq_refl" in development of 2012 *)
  Run TemplateProgram (
          tImplementTC lua_TC "nextp_natural_TC" "nextp_natural"
        (forall {A B : Type} (a : A) (f : A -> B), (nextp _ (f a)) = ((⊳_f f) (nextp _ a)))).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q; reflexivity.
  Qed.


  (** [later_app] computes on constant function *)
  Run TemplateProgram
      (tImplementTC nextp_natural_TC "lapp_next_const_TC" "later_app_const_β"
                  (forall A (t : A) (t' : ⊳ A),
                      (nextp _ (fun x => t) ⊙ t' = (nextp _ t)))).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q;reflexivity.
  Qed.

  (** [later_app] computes if both arfuments are applications of [nextp] *)
  Run TemplateProgram
      (tImplementTC lapp_next_const_TC "lapp_next_TC" "later_app_next_β"
                  (forall A B (f : A -> B) (t : A),
                      (nextp _ f ⊙ nextp _ t) = (nextp _ (f t)))).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q;reflexivity.
  Qed.

  Run TemplateProgram
      (tImplementTC lapp_next_const_TC "lunapp_const_TC" "later_unapp_const_β"
                    (forall A B (t : B),
                        (later_unapp A B (fun _ => nextp _ t) = (nextp _ (fun _ => t))))).
    Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q;reflexivity.
    Qed.

  Run TemplateProgram
    (tImplementTC lapp_next_const_TC "lapp_next_app_1_TC" "later_app_next_app_1_β"
                  (forall A B (g : ⊳ A -> B) (t : ⊳A ),
                      nextp _ (fun t0 => g (nextp _ t0)) ⊙ t = nextp _ (g t))).
  Next Obligation.
  apply eq_is_eq.
  apply functional_extensionality_dep.
  intros q.
  apply functional_extensionality_dep_s.
  intros α.
  destruct q.
  - reflexivity.
  - simpl. apply f_equal.
    apply functional_extensionality_dep.
    intros q1.
    apply functional_extensionality_dep_s.
    intros α1.
    destruct q1.
    * simpl. destruct (t 0 (α1 ∘ (sle_Sn q ) ∘ α)). reflexivity.
    * reflexivity.
  Qed.

  (* NOTE: Former "next_arrow_wird". It seems to me that this lemma is not provable without knowing what M is.
     In fact, it looks more like a property of M rather then a general lemma. *)
  (* TODO: remove, this lemma is not used in the development *)
  Lemma next_arr_later_arr :
    forall T U V (M : forall {n}, nlater n T -> nlater n U -> nlater n V) n g,
      later_app _ _ ((⊳_f M) (nextp _ g)) = M (n := S n) (nextp _ g).
  Proof.
  Admitted.

End Later.

Import Later.

Run TemplateProgram (tImplementTC lapp_next_TC "box_TC" "Box" (Type->Type)).
Next Obligation.
  exact (forall p1 (α0 : p0 ≥ p1), X p1 (α0 ∘ H) p1 (# _)).
Defined.

Notation "□ A" := (Box A) (at level 40).

Arguments sle_trans {_ _ _}.

Lemma sle_Sn_m {n m} : sle n m -> sle n (S m).
Proof.
  intros H. destruct n.
  - constructor.
  - constructor;auto. assert (H1 : sle n (S n)) by apply sle_Sn.
    exact (sle_trans H1 H ).
Defined.

Definition s_ex_falso (f : sFalse) : forall x, x := sFalse_rect _ f.

Module Fix.

  (* First, we construct a fixpoint going to □ T, this allows us to get
     a more general induction hypothesis *)
  Run TemplateProgram
      (tImplementTC box_TC "fix_TC" "fixp_"
                  (forall (T:Type), ((⊳ T) ->  T) -> □ T)).
  Next Obligation.
    revert X. revert T.
    induction p; intros T f q α; apply f; intros q0 α0.
    - destruct q0.
      + simpl. exact tt.
      + simpl.
        (* [destruct] doen't work here and [inversion] leads to "Bad relevance at the end." *)
        apply (s_ex_falso (sle_Sn_0 q0 (α0 ∘ α))).
    - simpl. destruct q0.
      + simpl. exact tt.
      + simpl.
        simple refine (let T' := _ :
          forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type in _).
        { intros p0 α0' p1 α1. exact (T p0 (sle_Sn_m α0') p1 α1). }
        unfold Boxᵗ,Boxᵗ_obligation_1 in IHp.
        refine (IHp T' _ q0 (sle_Sn_Sm (α0 ∘ α))).
        intros q1 α1 x. subst T'. simpl.
        apply (f q1 (sle_Sn_m α1)).
        intros p1 α2.
        exact (x p1 α2).
  Defined.

  Run TemplateProgram
      (tImplementTC fix_TC "counit_TC" "Box_counit" (forall (A:Type) , □ A -> A)).
  Next Obligation.
    exact (X p (# _) p (# _)).
  Defined.

  Definition fixp : forall {T:Type}, ((⊳ T) ->  T) -> T  :=
    fun T f => Box_counit _ (fixp_ T f).

  Run TemplateProgram (TC <- tTranslate counit_TC "fixp" ;;
                       tmDefinition "fixp_TC" TC).

  Definition happly {A B : Type} (f g : A -> B) : f = g -> forall x, f x = g x.
  Proof.
    intros p x. destruct p. reflexivity.
  Defined.

  Definition happly_dep {A : Type} {P : A -> Type} {f g : forall (a : A), P a}
    : f = g -> forall x, f x = g x.
  Proof.
    intros p x. destruct p. reflexivity.
  Defined.


  Lemma sle_Sn_m' {n m : nat} : sle (S n) m -> sle n m.
  Proof.
    intros. inversion H. apply ubox. subst. apply sbox.
    apply sle_Sn_m. exact H1.
  Qed.

  Run TemplateProgram
      (tImplementTC fixp_TC "unfold_TC" "unfold_fix"
                    (forall A (f: ⊳ A -> A), (fixp f) = (f (nextp _ (fixp f))))).
  Next Obligation.
    unfold fixpᵗ,Box_counitᵗ,Box_counitᵗ_obligation_1.
    (* First, we generalise the statement to make it work with arbitrary p' *)
    assert ( forall p0 (α0 : p ≥ p0) p' (α' : p0 ≥ p'),
     fixp_ᵗ p0
       (fun (p1 : nat_obj) (α : p0 ≥ p1) =>
        A p1 ( α ∘ α0))
       (fun (p1 : nat_obj) (α : p0 ≥ p1) =>
        f p1 (α ∘ α0)) p'  (α': p0 ≥ p') =

     f p' (α' ∘ α0)
       (fun (p1 : nat_obj) (α1 : p' ≥ p1) =>
        nextpᵗ p1
          (fun (p2 : nat_obj) (α2 : p1 ≥ p2) =>
           A p2 (α2 ∘ α1 ∘ α' ∘ α0))
          (fun (p2 : nat_obj) (α2 : p1 ≥ p2) =>
           fixp_ᵗ p2
             (fun (p3 : nat_obj) (α : p2 ≥ p3) =>
              A p3
                (α ∘ α2 ∘ α1 ∘ α' ∘ α0))
             (fun (p3 : nat_obj) (α : p2 ≥ p3) =>
              f p3
                (α ∘ α2 ∘ α1 ∘ α' ∘ α0))
             p2 (# p2)))).
    { induction p.
      - intros p0 α p' α'.
        destruct p0.
        * simpl. apply f_equal.
          apply functional_extensionality_dep.
          intros q.
          destruct q.
          ** reflexivity.
          ** intros. apply functional_extensionality_dep_s. intros α1.
             apply (s_ex_falso (sle_Sn_0 _ (α1 ∘ α'))).
        * apply (s_ex_falso (sle_Sn_0 _ α)).
      - simpl. intros.
        destruct p0.
        * simpl. apply f_equal.
          apply functional_extensionality_dep.
          intros q.
          destruct q.
          ** reflexivity.
          ** intros. apply functional_extensionality_dep_s. intros α1.
             apply (s_ex_falso (sle_Sn_0 _ (α1 ∘ α'))).
        * simpl. apply f_equal.
          apply functional_extensionality_dep.
          intros q.
          destruct q.
          ** reflexivity.
          ** apply functional_extensionality_dep_s. intros α1. simpl.
             simple refine
                    (let A' : forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type := _
                     in _).
             { intros p3 α3 p4 α4. apply (A p3 (sle_Sn_m α3) p4 α4). }
             simple refine (let f' : forall (p0 : nat_obj) (α : p ≥ p0),
                                (forall (p1 : nat_obj) (α0 : p0 ≥ p1),
                                    laterᵗ p1
                                     (fun (p2 : nat_obj) (α1 : p1 ≥ p2) =>
                                     A' p2 (α1 ∘ α0 ∘ α)) p1 (# p1)) ->
                                A' p0  α p0 (# p0) := _ in _).
             { intros p4 α4 X. exact (f p4 (sle_Sn_m α4) X). }
             assert (HH := IHp A' f' p0 (sle_Sn_Sm α0) q (sle_Sn_Sm (α1 ∘ α'))).
             change (  fixp_ᵗ p0
                        (fun (p1 : nat_obj) (α : p0 ≥ p1) => A' p1 (α ∘ sle_Sn_Sm α0))
                        (fun (p1 : nat_obj) (α : p0 ≥ p1) => f' p1 (α ∘ sle_Sn_Sm α0)) q
                                                                 (sle_Sn_Sm (α1 ∘ α'))
                     = fixp_ᵗ q
                        (fun (p3 : nat_obj) (α : q ≥ p3) =>
                          A p3 ((((α ∘ (sle_Sn q)) ∘ α1) ∘ α') ∘ α0))
                        (fun (p3 : nat_obj) (α : q ≥ p3) =>
                           f p3 ((((α ∘ (sle_Sn q)) ∘ α1) ∘ α') ∘ α0)) q (# q)).
             rewrite HH. clear HH.
             symmetry.
             assert (HH' := IHp A' f' q (sle_Sn_Sm (α1 ∘ α' ∘ α0)) q (# _)).
             apply HH'.
    }
    intros.
    apply eq_is_eq.
    refine (functional_extensionality_dep _ _ (fun (p0 : nat_obj) => _)).
    exact (@functional_extensionality_dep_s (p ≥ p0) _ _ _  (fun (a : p ≥ p0) => H p0 a p0 (# p0))).
  Qed.

  Run TemplateProgram (tImplementTC unfold_TC "switchp_TC" "switchp" ((⊳ Type) -> Type)).
  Next Obligation.
    destruct p0.
    - exact unit.
    - exact (X (S p0) H p0 (# _)).
  Defined.

  Run TemplateProgram (tImplementTC switchp_TC "switch_next_TC" "switch_next"
                                    (forall (T:Type), (switchp (nextp Type T)) = (⊳ T))).
  Next Obligation. reflexivity. Defined.

  Definition mu : (Type -> Type) -> Type.
    intros f.
    apply fixp.
    apply (fun x => f (switchp x)).
  Defined.

  Definition mu' : (⊳Type -> Type) -> Type
    := fun f => fixp f.

  Run TemplateProgram (TC <- tTranslate switchp_TC "mu" ;;
                       tmDefinition "mu_TC" TC).

  Lemma unfold_mu : forall (f: Type -> Type), (mu f) = (f (⊳ (mu f))).
  Proof.
    intros.
    unfold mu.
    rewrite unfold_fix at 1.
    rewrite switch_next.
    f_equal.
  Defined.
End Fix.

Import Fix.

Module FoldUnfold.

  
  Definition unfoldp (f : Type -> Type) : mu f -> f (⊳ (mu f))
    := @transport _ (fun x => x) _ _ (unfold_mu f).

  Definition foldp (f : Type -> Type) : f (⊳ (mu f)) -> mu f
    := @transport _ (fun x => x) _ _ (eq_sym (unfold_mu f)).


  (** *** Iterated versions of fold/unfold. *** *)

  (** The [nunfold] function takes an additional parameter [later_f]
   allowing to "push" later application from outside to the argument,
   which is crucial for the recursive case. This is not always available
   for arbitrary [f], so this definition will work only for [f] for
   which it is possible to define such a function *)
  Fixpoint nunfoldp {n} (f : Type -> Type) (later_f : forall A, ⊳ f A -> f (⊳ A))
    : ⊳[n] (mu f) -> f (⊳[1+n] mu f) :=
      match n with
      | O => fun (x : mu f) => unfoldp f x
      | S m => fun (x : ⊳[1+m] (mu f)) => later_f _ ((⊳_f (nunfoldp f later_f)) x)
      end.

  (** Dually to the definition of [unfold] in the definition of [fold] we need
     some function with the type [f (⊳ A) -> ⊳ f A] *)
  Fixpoint nfoldp {n : nat} (f : Type -> Type) (later_f : forall A, f (⊳ A) -> ⊳ f A)
    : f (⊳[1+n] mu f) -> ⊳[n] (mu f) :=
    match n as m return (f (⊳[1+m] mu f) -> ⊳[m] (mu f)) with
    | O => fun (x : f (⊳ mu f)) => foldp f x
    | S m => fun (x : f (⊳[2+m] mu f)) => (⊳_f (nfoldp f later_f)) (later_f _ x)
    end.

  Lemma fold_unfold_id f a : foldp f (unfoldp f a) = a.
  Proof.
    unfold foldp,unfoldp.
    rewrite transp_concat.
    rewrite concat_inv_r.
    reflexivity.
  Qed.

  Arguments nextp {_}.

  Lemma nfold_nunfold_id {n} f h h' {ψ : forall A, retract (h A) (h' A)}
        (a : ⊳[n] (mu f)) : nfoldp f h (nunfoldp f h' a) = a.
  Proof.
    induction n.
    - apply fold_unfold_id.
    - simpl. rewrite ψ.
      change (((⊳_f nfoldp f h) ∘f (⊳_f nunfoldp f h')) a = a).
      rewrite <- later_resp_comp.
      assert (H : (nfoldp (n:=n) f h) ∘f (nunfoldp f h') = id).
      { apply functional_extensionality_dep; exact IHn. }
      rewrite H.
      rewrite later_resp_id.
      reflexivity.
  Qed.

  
  Lemma unfold_fold_id (f : Type -> Type) (a : f (⊳ mu f)) : unfoldp f (foldp f a) = a.
  Proof.
    unfold foldp,unfoldp.
    rewrite transp_concat.
    rewrite concat_inv_l.
    reflexivity.
  Qed.

  Arguments later_resp_comp {_ _ _ _ _}.

  Lemma nunfold_nfold_id {n} f h' h (a : f (⊳[1+n] (mu f))) {ψ : forall A, sect (h A) (h' A)}
    : nunfoldp f h' (nfoldp f h a) = a.
  Proof.
    induction n.
    - (* NOTE: without this call of [simpl], definitions for untyped lambda fail because of universe constraints *)
      simpl.
      apply unfold_fold_id.
    - simpl.
      pose (happly_dep (later_resp_comp (f:=nfoldp f h) (g:= nunfoldp (n:=n) f h'))) as H.
      unfold fun_comp in H. rewrite <- H.
      assert (IHn' : (nunfoldp (n:=n) f h') ∘f (nfoldp f h) = id).
      { apply functional_extensionality_dep; exact IHn. }
      change (fun x : f (⊳[ 1 + n] mu f) => nunfoldp f h' (nfoldp f h x))
        with ((nunfoldp (n:=n) f h') ∘f (nfoldp f h)).
      rewrite IHn'.
      rewrite later_resp_id. unfold id.
      rewrite ψ. reflexivity.
  Qed.

  Lemma nfold_next {n} F
        (h : forall A, ⊳ F A -> F (⊳ A))
        (h' : forall A, F (⊳ A) -> ⊳ F A) f
        (ψ : forall A, sect (h A) (h' A))
    : nfoldp (n:=1+n) F h' (h _ (nextp f)) = nextp (nfoldp F h' f).
  Proof.
    simpl; rewrite ψ; rewrite <- nextp_natural; reflexivity.
  Qed.
  
  Lemma nunfold_next {n} F f
        (h : forall A, ⊳ F A -> F (⊳ A))
   : nunfoldp (n:=S n) F h (nextp f) = h _ (nextp (nunfoldp F h f)).
  Proof.
    simpl; rewrite <- nextp_natural; reflexivity.
  Qed.
    

End FoldUnfold.
