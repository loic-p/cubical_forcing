(* Formalisation of Guarded Recursive Types using the cbn forcing translation in Template Coq
   with the ordered set of natural numbers as forcing conditions *)

Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst.
Require Import String PeanoNat.
Require Import Forcing.TemplateForcing.

(* Some axioms *)
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Open Scope string.

Definition Obj : Type := nat.
Definition Hom : Obj -> Obj -> Prop := fun n m => m <= n.

(** Yoneda embedding  *)
Definition Ynat_obj := nat.
Definition Ynat_hom := (fun (P Q : Ynat_obj) => forall R, Hom Q R -> Hom P R).
Definition Yid_nat_hom (P : Ynat_obj) := (fun (R : Ynat_obj) (k : Hom P R) => k).
Definition Ynat_comp (P Q R : Ynat_obj) (g : Ynat_hom Q R) (f : Ynat_hom P Q)
  := (fun (S : Ynat_obj) (k : Hom R S) => f S (g S k)).

Notation "P ≤ Q" := (Ynat_hom P Q) (at level 70).
Notation "#" := Yid_nat_hom.
Notation "f ∘ g" := (fun (R : Ynat_obj) (k : Hom _ R) => f R (g R k)) (at level 40).

(* Now, laws hold definitionally *)
Lemma nat_cat_left_id P R (g : R ≤ P)  : (# R) ∘ g = g.
Proof. reflexivity. Qed.

Lemma nat_cat_right_id P R (f : P ≤ R)  : f ∘ (# R) = f.
Proof. reflexivity. Qed.

Lemma nat_cat_assoc P Q R S (f : P ≤ Q) (g : Q ≤ R) (h : R ≤ S):
  f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof. reflexivity. Qed.

Definition Ynat_cat : category :=
  makeCatS "Ynat_obj" "Ynat_hom" "Yid_nat_hom" "Ynat_comp".


(* Translating Type *)

Quote Definition qType := Type.

Definition tr_Type_syn := Eval vm_compute in translate_simple true Ynat_cat qType.


(* A translation of Type from the forcing plugin *)
Definition tpᶠ : forall p p0 : Ynat_obj, p ≤ p0 -> Type
  := fun (p p0 : Ynat_obj) (_ : p ≤ p0) => forall p1 : Ynat_obj, p0 ≤ p1 -> Type.


(* Unqouting the syntax for the translated Type *)
Make Definition unqType := Eval compute in tr_Type_syn.

Lemma unqType_forcing_plugin_eq : unqType = tpᶠ.
Proof. reflexivity. Qed.

(* Lemmas from the the implementation of guarded recursive types using
the forcing transalation plugin. *)

Lemma Yle_to_le : forall n m, n ≤ m -> m <= n.
Proof.
  intros n m H.
  unfold Hom in H.
  eapply H.
  eapply le_n.
Qed.



Lemma le_to_Yle : forall n m, n <= m -> m ≤ n.
Proof.
unfold Hom.
intros n m H R H'.
refine (Nat.le_trans _ n _ _ _); tauto.
Qed.


Lemma Yle_Sn_0 : forall n, 0 ≤ S n -> False.
Proof.
  unfold Hom;
  intros n H.
  specialize (H (S n) (le_n (S n))).
  inversion H.
Qed.

Definition Yle_S' m : S m ≤ m.
Proof.
  eapply le_to_Yle.
  eapply le_S.
  eapply le_n.
Defined.

Definition Ynat_irr p q (α α' : p ≤ q): α = α'.
Proof.
  unfold Hom in α,α'.
  apply (functional_extensionality_dep α α').
  intro r.
  apply (functional_extensionality_dep (α r) (α' r)).
  intro α''.
  apply ProofIrrelevance.proof_irrelevance.
Defined.


(* The definition of [later] operator *)

Quote Definition qTypeConstr := (Type -> Type).

Definition tr_TypeConstr_syn := Eval vm_compute in translate_type_simple true Ynat_cat qTypeConstr.

Make Definition gArrowTypeType := Eval vm_compute in tr_TypeConstr_syn.

Definition later : gArrowTypeType.
Proof.
  unfold gArrowTypeType.
  intros p T q f.
  destruct q.
  exact unit.
  exact (T q (f ∘ (Yle_S' q)) q (# _)).
Defined.

Notation "⊳ A" := (later A) (at level 40).