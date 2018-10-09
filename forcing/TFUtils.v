Require Import Template.All.
Require Import List.
Require Import Template.Ast.
Require Import String.

Open Scope string_scope.


(* Taken from the template-coq parametricity translation *)

Definition tsl_table := list (global_reference * term).

Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.

Definition default_term := tVar "constant_not_found".

Definition lookup_default (E : tsl_table) (gr : global_reference)
  : term :=
  match (lookup_tsl_table E gr) with
  | None => match gr with
            | ConstRef n => tVar ("Not_found_" ++ n)
            | _ => default_term
            end
  | Some t => t
  end.

Import ListNotations.

(* Partly taken from Template.Typing *)
Definition it_mkLambda_or_LetIn (t : term) (l : context) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tLambda d.(decl_name) d.(decl_relevance) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) d.(decl_relevance) b d.(decl_type) acc
       end) l t.

Definition it_mkProd_or_LetIn (t : term) (l : context) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tProd d.(decl_name) d.(decl_relevance) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) d.(decl_relevance) b d.(decl_type) acc
       end) l t.

Fixpoint fold_map_internal {A B C : Type} (f : A -> B -> A * C) (a : A)
         (cs : list C) (bs : list B) : A * (list C)
  := match bs with
     | [] => (a, rev cs)
     | hd :: tl => let (a_, c_) := f a hd in fold_map_internal f a_ (c_ :: cs) tl
     end.

Definition fold_map {A B C : Type} (f : A -> B -> A * C) (a : A)
           (bs : list B) : A * (list C) := fold_map_internal f a [] bs.

Fixpoint fold_map' {A B C : Type} (f : A -> B -> A * C) (a : A)
         (bs : list B) : A * (list C)
  := match bs with
     | [] => (a, [])
     | hd :: tl => let (a_, c_) := f a hd in
                   let (a__, cs) := fold_map' f a_ tl in
                   (a__, c_ :: cs)
     end.

Example ex_fold_map : fold_map (fun x y => (x+y, y+1)) 0 [1;2;3] = (6,[2;3;4]).
reflexivity.
Qed.

Example ex_fold_map_fold_map' :
  fold_map (fun x y => (x+y, y+1)) 0 [1;2;3] = fold_map' (fun x y => (x+y, y+1)) 0 [1;2;3].
reflexivity.
Qed.

Definition sect {A B} (s : A -> B) (r : B -> A) := forall (x : A), r (s x) = x.

Definition retract {A B} (s : A -> B) (r : B -> A) := sect r s.

(* Auxiliary definitions related to equality *)
Definition transport {A : Type} {F : A -> Type} {a b : A} (p : a = b) : F a -> F b.
Proof.
  destruct p. apply id.
Defined.

(** Concatenation of paths *)
Definition path_concat {A : Type} {x y z : A} : x = y -> y = z -> x = z.
  intros p q. destruct p. apply q. Defined.

(** Lemma 2.3.9 in the HoTT book *)
Definition transp_concat {A : Type} {B : A -> Type} {x y z : A} {u : B x}
           (p : x = y) (q : y = z) :
  transport q (transport p u) = transport (path_concat p q) u.
  destruct p. reflexivity. Defined.


Definition ap {A B} (f : A -> B) {x y} : x = y -> f x = f y.
    destruct 1. reflexivity.
Defined.

(* Lemma 2.3.10 in the HoTT book *)
Definition transp_naturality {A B : Type} {C : B -> Type} {x y : A} {f : A -> B}
           {u : C (f x)} (p : x = y) :
  transport (ap f p) u =  @transport _ (fun x => C (f x)) _ _ p u.
  destruct p. reflexivity. Defined.

(* Lemma 2.3.11 in the HoTT book *)
Definition move_transport {A : Type}{F G : A -> Type}(f : forall {a : A}, F a -> G a)
           {a a' : A} (u : F a) (p : a = a') : f (transport p u) = transport p (f u).
  destruct p. reflexivity. Defined.

Definition concat_inv_r {A : Type} {x y : A} (p : x = y) :
  path_concat p (eq_sym p) = eq_refl.
  destruct p. reflexivity. Defined.

Definition concat_inv_l {A : Type} {x y : A} (p : x = y) :
  path_concat (eq_sym p) p = eq_refl.
  destruct p. reflexivity. Defined.
