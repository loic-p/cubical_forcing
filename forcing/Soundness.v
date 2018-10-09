Require Import Omega.
Require Import Forcing.TemplateForcing.
Require Import Template.Typing Template.Ast Template.WeakSubst Template.LiftSubst.
From Template Require Export univ uGraph.

Require Import String.
Local Open Scope string_scope.

Require Import List.
Import ListNotations.
Open Scope list.

Import Environ.

Definition cat : category :=
  makeCatS "Obj" "Hom" "Id_hom" "Comp".

Definition ft_type c Σ σ :=
  (snd (otranslate_type otranslate (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt c)).

Definition ft_term c Σ σ :=
  (snd (otranslate (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt c)).

Definition ft_ctx Γ Σ σ  :=
  (snd (otranslate_context (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt Γ)).

Definition leq_refl sigma t : leq_term sigma t t = true.
  induction t.
Admitted.

(** We assume the following sorts for the objects and morphisms of the base category *)
Axiom obj_sort : forall Σ Γ, Σ ;;; Γ |- tConst "Obj" [] : tSort [Universe.Expr.set].
Axiom hom_sort : forall Σ Γ t1 t2,
    Σ ;;; Γ |- t1 : tConst "Obj" [] ->
    Σ ;;; Γ |- t2 : tConst "Obj" [] ->
                    Σ ;;; Γ |- tApp (Ast.tConst "Hom" []) [t1; t2] : tSort [Universe.Expr.set].
Axiom id_hom_type : forall Σ Γ t,
    Σ ;;; Γ |- t : tConst "Obj" [] ->
    Σ ;;; Γ |- tApp (Ast.tConst "Id_hom" []) [t] : tApp (Ast.tConst "Hom" []) [t; t].


Lemma wf_init_graph : wf_graph init_graph.
Proof.
  constructor.
  - constructor.
    + apply SetoidList.InA_cons_tl. auto.
    + intuition. apply SetoidList.InA_cons_hd; auto.
      simpl. apply SetoidList.InA_cons_hd; eauto.
      (* NOTE: something is not right, either [wf_graph] or [init_graph] *)
Admitted.


Ltac setctx na :=
  match goal with
    |- ?Σ ;;; ?Γ |- _ : _ => set(na := Γ)
  end.

Ltac solve_rel :=
  let Γ' := fresh "Γ" in
  let H' := fresh in
  match goal with
    |- ?Σ ;;; ?Γ |- tRel ?n : _ =>
    setctx Γ';
    assert (H' : n < #|Γ'|) by (subst;simpl; omega);
    subst; apply type_Rel with (isdecl:=H')
  end.

Reserved Notation "E ## Γ |= σ" (at level 40).

(* TODO: think about the empty context case *)
Inductive fctx_valid E : context -> list forcing_condition -> Type :=
| fctx_valid_nil : E ## vass (nNamed "p") Relevant (tConst "Obj" nil) :: nil |= nil
| fctx_valid_cons_var Γ σ T t : E ## Γ |= σ -> (to_global_context E) ;;; Γ |- t : T ->
                            E ## (Γ ,, vass (nNamed "t") Relevant T) |= (σ ,, fcVar)
| fctx_valid_cons_lift Γ σ : E ## Γ |= σ ->
                        E ## (Γ ,,, get_ctx_lift cat E (last_condition σ)) |= (σ ,, fcLift)
where "E ## Γ |= σ" := (fctx_valid E Γ σ).


Lemma last_condition_sound σ Γ (Σ := ([], init_graph)) :
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ ;;; Γ |- tRel (last_condition σ) : tConst "Obj" [].
Proof.
  intros TyCtx FCvalid.
  induction FCvalid.
  - simpl. setctx Γ'.
         assert (H1 : 0 < #|Γ'|) by (subst;simpl; omega).
         subst. apply type_Rel with (n:=0) (isdecl:=H1).
  - simpl.
    pose [vass (nNamed "t") Relevant T] as Γ'.
    change (Σ;;; Γ ,,, Γ' |- lift0 #|Γ'| (tRel (last_condition σ)) : lift0 #|Γ'| (tConst "Obj" [])).
    assert (TyCtxΓ : type_local_env Σ Γ).
    { inversion TyCtx;subst;auto. }
    apply weakening.
    + simpl. constructor. apply wf_init_graph.
    + simpl.
      (* NOTE: here we do inversion again, because of some issues with [typing] being in [Type] *)
      inversion TyCtx;subst;auto.
    + apply IHFCvalid; eauto.
  - solve_rel.
Qed.


Lemma lam_q_f_sound (Σ := (nil,init_graph)) Γ σ t T :
  let E := (of_global_context Σ) in
  let fctx := (mkFCtxt σ cat []) in
  let ext := get_ctx_lift cat E (last_condition σ) in
  type_local_env Σ Γ ->
  Σ ;;; Γ ,,, ext |- t : T ->
  Σ ;;; Γ |- snd (λ_q_f E fctx) t : snd (Π_q_f E fctx) T.
Proof.
  simpl. intros TyCtx Ty.
  econstructor.
  + eapply obj_sort.
  + econstructor.
    * eapply hom_sort.
      ** pose (vass pos_name Relevant (tConst "Obj" []) :: nil) as Γ'.
         change
           (Σ;;; Γ ,,, Γ' |- lift0 #|Γ'| (tRel (last_condition σ)) : lift0 #|Γ'| (tConst "Obj" [])).
         apply weakening with (Γ' := Γ').
         *** simpl. constructor. apply wf_init_graph.
         *** simpl. constructor. apply TyCtx. econstructor. simpl. apply obj_sort.
         *** apply last_condition_sound.
             (* TODO : add Γ typed assumption *)
             admit.
             (* TODO : add forcing context validity assumption *)
             admit.
      ** solve_rel.
  Admitted.

Lemma Π_q_f_lift_sound (Σ := (nil,init_graph)) Γ σ T l :
  let σ_ext := σ ,, fcLift in
  let fctx_ext := (mkFCtxt σ_ext cat []) in
  let E := (of_global_context Σ) in
  let ext1 := get_ctx_lift cat E (last_condition σ) in
  let ext2 := get_ctx_lift cat E (last_condition σ_ext) in
  Σ ;;; Γ ,,, ext1 ,,, ext2  |- T : tSort l ->
  Σ ;;; Γ ,,, ext1 |- snd (Π_q_f E fctx_ext) T :
  tSort (Universe.sup [Universe.Expr.set]  (Universe.sup [Universe.Expr.set] l)).
Proof.
  simpl.
  intros H.
  apply type_Prod.
  ** apply obj_sort.
  ** apply type_Prod.
     *** apply hom_sort; solve_rel.
     *** eauto.
Qed.


Notation "'[' c ']ᵗ' " := (ft_term c) (at level 40).
Notation "⟦ Γ ⟧" := (ft_ctx Γ)  (at level 40).
Notation "'⟦' c '⟧ᵀ'" := (ft_type c) (at level 40).

Lemma context_traslation_valid E Γ σ :
  let Σ := to_global_context E in
  type_local_env Σ Γ ->
  E ## (⟦Γ⟧ Σ σ) |= σ.
Proof.
  intros ? TyCtx.
  Admitted.

Lemma forcing_context_soundness Σ Γ σ :
  type_local_env Σ Γ -> type_local_env Σ (⟦Γ⟧ Σ σ).
Admitted.

Lemma forcing_typing_soundness (Σ := (nil,init_graph)) Γ t T σ  :
  type_local_env Σ Γ ->
  Σ ;;; Γ |- t : T ->
  let Σ' := Σ in Σ' ;;; (⟦Γ⟧ Σ σ) |- ([t]ᵗ Σ σ) : (⟦T⟧ᵀ Σ σ).
Proof.
  intros TyCtx Ty.
  induction Ty; simpl.
  - simpl. unfold translate_var.
    unshelve econstructor; simpl.
    Focus 2. constructor.  admit.
  - destruct l;simpl.
    + (* Simplifying the applications in the type first*)
      eapply type_Conv.
      * unfold ft_term,otranslate,lambda_prefix,extend. simpl.
        apply lam_q_f_sound;simpl.
        ** apply forcing_context_soundness;assumption.
        ** eapply Π_q_f_lift_sound; apply type_Sort.
      * unfold ft_type. simpl. unfold mkOptApp.
        eapply type_App.
        ** eapply lam_q_f_sound;simpl.
           *** apply forcing_context_soundness;assumption.
           *** apply Π_q_f_lift_sound. unfold Universe.super. simpl.
               unfold Universe.type1,Universe.Expr.type1.
           (* TODO: show that [tSort [(Level.set, true)]] has type [tSort l] for some level l *)
           (* constructor [type_Sort] does not apply here. *)
               admit.
        ** (* typing_spine *)
           simpl. econstructor.
           *** eapply cumul_refl. apply leq_refl.
           *** apply last_condition_sound.
               **** apply forcing_context_soundness;assumption.
               **** apply context_traslation_valid. apply TyCtx.
           *** econstructor.
               **** eapply cumul_refl. apply leq_refl.
               **** simpl. apply id_hom_type. apply last_condition_sound.
                    ***** apply forcing_context_soundness;assumption.
                    ***** apply context_traslation_valid. apply TyCtx.
               **** simpl. econstructor.
      * simpl. unfold ft_type. simpl. unfold mkOptApp.

        (* constructor. simpl. *)
        (* apply Π_q_f_lift_sound. unfold Universe.super. simpl. *)
        (* unfold Universe.type1,Universe.Expr.type1. *)
       (* econstructor;simpl. Focus 4. *)
       (* eapply cumul_red_r. *)
       (* Focus 2. eapply red_beta. simpl. *)
       (* eapply cumul_red_r. *)
       (* Focus 2. eapply red_beta. simpl. *)
       (* eapply cumul_refl. apply leq_refl. *)
       (* econstructor. *)
       (* apply obj_sort. *)
       (* econstructor. econstructor.  *)

               (* econstructor. econstructor. *)
Admitted.