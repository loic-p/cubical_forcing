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

Set Primitive Projections.


Notation "f 'o' g" := (Basics.compose f g) (at level 50, left associativity).

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

Notation "x .1s" := x.(spi1 _) (at level 3).
Notation "x .2s" := x.(spi2 _) (at level 3).

Notation "( a ; b )s" := {| spi1 := a ; spi2 := b |}.






(* now we redefine some basic arithmetic, because it takes ages to quote these
   recursively from the standard library *)

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






(*
   funext is just here to make some proofs more convenient as of now
 *)
Require Import FunctionalExtensionality.
Definition funext {A B : Type} := @functional_extensionality A B.

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

Definition rev_c {n : nat} (m : finset n) : cube (S n) -> cube (S n).
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_eq_lt_dec i m) as [[[H | H] | H] | H].
  - apply x. exists i. exact q.
  - apply x. exists (S m). now apply le_n_S.
  - apply x. exists m. now apply le_S.
  - apply x. exists i. exact q.
Defined.

Inductive word : nat -> nat -> Type :=
| empty {a : nat} : word a a
| degen {a b : nat} : finset (S b) -> word a (S b) -> word a b
| face {a b : nat} : finset (S b) -> bool -> word a b -> word a (S b)
| meet {a b : nat} : finset b -> word a (S b) -> word a b
| join {a b : nat} : finset b -> word a (S b) -> word a b
| rev {a b : nat} : finset b -> word a (S b) -> word a (S b).

Fixpoint concat_word {a b c : nat} (w1 : word b c) (w2 : word a b) : word a c :=
  (match w1 in (word b c) return word a b -> word a c with
   | @empty x => (fun w : word a x => w)
   | @degen x y i w' => (fun w : word a x => degen i (concat_word w' w))
   | @face x y i d w' => (fun w : word a x => face i d (concat_word w' w))
   | @meet x y i w' => (fun w : word a x => meet i (concat_word w' w))
   | @join x y i w' => (fun w : word a x => join i (concat_word w' w))
   | @rev x y i w' => (fun w : word a x => rev i (concat_word w' w))
   end) w2.

Fixpoint comp_word {a b : nat} (w : word a b) : cube a -> cube b :=
  match w with
  | empty => (fun x => x)
  | degen i w' => (degen_c i) o (comp_word w')
  | face i d w' => (face_c i d) o (comp_word w')
  | meet i w' => (meet_c i) o (comp_word w')
  | join i w' => (join_c i) o (comp_word w')
  | rev i w' => (rev_c i) o (comp_word w')
  end.

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
  @sexists (cube a -> cube b) admissible.

Definition compose {A B C : nat} (g : arrow B C) (f : arrow A B) : arrow A C :=
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




(* Categorical laws hold *definitionally* :
   to check this, we prove them using only reflexivity *)

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





(* Okay so now that we have constructed our site, let us use it to do forcing *)

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


(*
   Shouldnt all this stuff be part of the templatecoq plugin instead ?!
   Here translate *actually* performs the translation, like explained in the
   pape. This is not some TemplateCoq complicated stuff.
 *)

Import MonadNotation.
Import ListNotations.


Definition f_translate (cat : category) (tsl_ctx : tsl_context) (trm : term)
  : tsl_result term :=
  Success (snd (translate true None
                          (snd tsl_ctx)
                          cat
                          ({| Environ.env_globals := (fst (fst tsl_ctx)) |})
                          tt
                          trm)).

Definition f_translate_type (cat : category) (tsl_ctx : tsl_context) (trm : term)
  : tsl_result term :=
  Success (snd (translate_type true None
                               (snd tsl_ctx)
                               cat
                               ({| Environ.env_globals := (fst (fst tsl_ctx)) |})
                               tt
                               trm)).


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


(* now comes the actual forcing *)

(* Here we recursively get all the definitions needed to define arrow, which is enough
   for basically everything defined previously. Warning : can take a few seconds… *)
(* The point of this is when we want TemplateCoq to do reduction or typechecking, it
   will need a context of definitions. *)
Definition pack := (arrow , @compose , @id).

Run TemplateProgram (prg <- tmQuoteRec pack ;;
                         tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context := (reconstruct_global_context g_ctx,[]).

(** Tests of the translation for inductives *)

Definition empty_env := Environ.empty_env.
Definition empty_σ := from_env empty_env.

Quote Definition term1 := (Prop -> Type).
Inductive ind1 : Set :=
| lc1 : ind1
| lc2 : ind1 -> ind1.
Definition ind1_body :=
  {|
    ind_npars := 0;
    ind_bodies := [{|
                     ind_name := "ind1";
                     ind_type := tSort [(Level.lSet, false)];
                     ind_kelim := [InSProp; InProp; InSet; InType];
                     ind_ctors := [("lc1", tRel 0, 0);
                                    ("lc2", tProd nAnon Relevant (tRel 0) (tRel 1), 1)];
                     ind_projs := [] |}];
    ind_universes := Monomorphic_ctx (UContext.make [] Constraint.empty) |}.

Run TemplateProgram (α <- tmQuoteInductive "ind1" ;;
                       tmPrint α).

Definition f_translate_oib_type' (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ  : evar_map) (id : kername) (arityctxt : list (name * relevance * term))
  : evar_map * term :=
  (* we translate I as λp params indices q α . (var I) p params indices *)
  (* first, the body of the lambda abstraction *)
  let narityctxt := length arityctxt in
  let args := map tRel (List.rev (seq 2 (S narityctxt))) in (** TODO Check de Bruijn indices *)
  let fnbody := mkApps (tVar id) args in
  (* then, translate all the params and indices types *)
  let fold := fun (acc : evar_map * context) (decl : name * relevance * term) =>
               let (σ, ctxt) := acc in
               let '(n, rel, t) := decl in
               let (σ, tr_t) := translate_type true None (snd tsl_ctx) cat env σ t in
               (σ, {| decl_name := n ;
                      decl_relevance := rel ;
                      decl_body := None ;
                      decl_type := tr_t |}::ctxt)
  in
  let (σ, tr_arity) := fold_left fold arityctxt (σ, nil) in
  (* build the arguments of the lambda abstraction *)
  let hom := tApp cat.(cat_hom) [tRel (1 + narityctxt) ; tRel 0] in (** TODO Check de Bruijn indices *)
  let argctxt := (vass (nNamed "α") Relevant hom)
                  ::(vass (nNamed "p") Relevant cat.(cat_obj))
                  ::(tr_arity ++ [vass (nNamed "q") Relevant cat.(cat_obj)])%list in
  (* put everything together *)
  (* memo : it_mkLambda_or_LetIn is defined both in Template.Typing and Forcing.TFUtils with reversed arguments *)
  (σ, it_mkLambda_or_LetIn argctxt fnbody).

(* arity *)

(* type *)
Eval lazy in (snd (f_translate_oib_type' ΣE 𝐂 empty_env empty_σ "kername"
                                         [(nNamed "bjr", Relevant, tSort [(Level.lProp, false)]) ;
                                            (nNamed "arv", Relevant, tSort [(Level.lSet, false)])])).

Parameter A : nat -> (forall p : nat,
      (fun (p0 : nat) (_ : p ~> p0) => forall p1 : nat, p0 ~> p1 -> Prop) p
        id) -> (forall p p0 : nat, p ~> p0 -> Set) -> Type.

Make Definition test2 := (tLambda (nNamed "q") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
         (tLambda (nNamed "bjr") Relevant
            (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
               (tApp
                  (tLambda (nNamed "p") Relevant
                     (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                     (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
                        (tProd (nNamed "p") Relevant
                           (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                           (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                              (tSort [(Level.lProp, false)]))))) [tRel 0; tApp (tConst "Top.id" []) [tRel 0]]))
            (tLambda (nNamed "arv") Relevant
               (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                  (tApp
                     (tLambda (nNamed "p") Relevant
                        (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                        (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
                           (tProd (nNamed "p") Relevant
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                              (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                 (tSort [(Level.lSet, false)]))))) [tRel 0; tApp (tConst "Top.id" []) [tRel 0]]))
               (tLambda (nNamed "p") Relevant
                  (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                  (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 3; tRel 0])
                           (tApp (tConst "A" []) [tRel 4; tRel 3; tRel 2])))))).

Eval simpl in test2.

Definition f_translate_oib_types' (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (mib : mutual_inductive_body)
  : evar_map * list (ident * term) :=
  let fold := fun (acc : evar_map * list (ident * term)) oib =>
               let (σ, tail) := acc in
               let (arityctxt, _) := decompose_prod oib.(ind_type) in
               let (σ, tr) := f_translate_oib_type' tsl_ctx cat env σ oib.(ind_name) arityctxt in
               (σ, (oib.(ind_name), tr)::tail)
  in
  fold_left fold mib.(ind_bodies) (σ, nil).




(* We can do eq !! Im sure we can, come on *)

Inductive eq' {A : Type} (x : A) : A -> Prop :=  eq_refl' : eq' x x.

Run TemplateProgram (α <- tmQuoteInductive "eq'" ;; tmPrint α).

Definition eq'_q : mutual_inductive_body :=
  {| ind_npars := 2;
     ind_bodies :=
       [{| ind_name := "eq'";
           ind_type := tProd (nNamed "A") Relevant (tSort [(Level.Level "Top.110", false)])
                            (tProd (nNamed "x") Relevant (tRel 0)
                                   (tProd nAnon Relevant (tRel 1) (tSort [(Level.lProp, false)])));
           ind_kelim := [InSProp; InProp; InSet; InType];
           ind_ctors := [("eq_refl'",
                         tProd (nNamed "A") Relevant (tSort [(Level.Level "Top.110", false)])
                               (tProd (nNamed "x") Relevant (tRel 0) (tApp (tRel 2) [tRel 1; tRel 0; tRel 0])), 0)];
           ind_projs := [] |}];
     ind_universes := Monomorphic_ctx (UContext.make [Level.Level "Top.110"] Constraint.empty) |}.

(* mind_body_to_entry *)

Definition eq'_e : mutual_inductive_entry :=
  {| mind_entry_record := None;
     mind_entry_finite := Finite;
     mind_entry_params := [("A", LocalAssum (tSort [(Level.Level "Top.110", false)]));
                            ("x", LocalAssum (tRel 0))];
     mind_entry_inds := [{|
                           mind_entry_typename := "eq'";
                           mind_entry_arity := tProd nAnon Relevant (tRel 1) (tSort [(Level.lProp, false)]);
                           mind_entry_template := false;
                           mind_entry_consnames := ["eq_refl'"];
                           mind_entry_lc := [tApp (tRel 2) [tRel 1; tRel 0; tRel 0]] |}];
     mind_entry_universes := Monomorphic_ctx
                              ([Level.Level "Top.110"],
                               {| Constraint.this := []; Constraint.is_ok := Constraint.Raw.empty_ok |});
     mind_entry_private := None |}.

Eval lazy in (snd (f_translate_oib_types ΣE 𝐂 empty_env empty_σ eq'_q)).

Definition substfn : list (ident * term) :=
  [("eq'",
        tLambda (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
          (tLambda nAnon Relevant
             (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                (tApp (tApp (tRel 1) [tRel 0; tApp (tConst "Top.id" []) [tRel 0]])
                   [tRel 0; tApp (tConst "Top.id" []) [tRel 0]]))
             (tLambda (nNamed "x") Relevant
                (tProd (nNamed "p") Relevant
                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                   (tApp (tApp (tRel 0) [tRel 0; tApp (tConst "Top.id" []) [tRel 0]])
                      [tRel 0; tApp (tConst "Top.id" []) [tRel 0]]))
                (tLambda (nNamed "A") Relevant
                   (tProd (nNamed "p") Relevant
                      (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                      (tApp
                         (tLambda (nNamed "p") Relevant
                            (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                            (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
                               (tProd (nNamed "p") Relevant
                                  (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                  (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                     (tSort [(Level.Level "Top.110", false)])))))
                         [tRel 0; tApp (tConst "Top.id" []) [tRel 0]]))
                   (tLambda (nNamed "q") Relevant
                      (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                      (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 4; tRel 0])
                         (tApp (tConst "eq'" []) [tRel 5; tRel 4; tRel 3; tRel 2])))))))].

Definition invsubst : list ident := ["eq'"].

Definition lc : list term := [tApp (tRel 2) [tRel 1; tRel 0; tRel 0]].

Eval lazy in (f_translate_lc_list ΣE 𝐂 empty_env empty_σ 2 lc substfn invsubst).
Eval lazy in (f_translate_mib ΣE 𝐂 eq'_q).

Run TemplateProgram (tmMkInductive {|
         mind_entry_record := None;
         mind_entry_finite := Finite;
         mind_entry_params := [("p",
                               LocalAssum (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []));
                              ("A",
                              LocalAssum
                                (tProd (nNamed "p") Relevant
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
                                      (tApp
                                         (tLambda (nNamed "p") Relevant
                                            (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                            (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                               (tProd (nNamed "p") Relevant
                                                  (tInd
                                                     {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}
                                                     [])
                                                  (tProd (nNamed "α") Relevant
                                                     (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                                     (tSort [(Level.Level "Top.110", false)])))))
                                         [tRel 1; tApp (tConst "Top.id" []) [tRel 1]]))));
                              ("x",
                              LocalAssum
                                (tProd (nNamed "p") Relevant
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                      (tApp (tApp (tRel 2) [tRel 1; tRel 0]) [tRel 1; tApp (tConst "Top.id" []) [tRel 1]]))))];
         mind_entry_inds := [{|
                             mind_entry_typename := "eq'ᵗ";
                             mind_entry_arity := tProd nAnon Relevant
                                                   (tProd (nNamed "p") Relevant
                                                      (tInd
                                                         {|
                                                         inductive_mind := "Coq.Init.Datatypes.nat";
                                                         inductive_ind := 0 |} [])
                                                      (tProd (nNamed "α") Relevant
                                                         (tApp (tConst "Top.arrow" []) [tRel 3; tRel 0])
                                                         (tApp (tRel 3)
                                                            [tRel 1;
                                                            tApp (tConst "Top.compose" [])
                                                              [tRel 4; tRel 4; tRel 1; tRel 0;
                                                              tApp (tConst "Top.id" []) [tRel 4]];
                                                            tRel 1; tApp (tConst "Top.id" []) [tRel 1]])))
                                                   (tSort [(Level.lProp, false)]);
                             mind_entry_template := false;
                             mind_entry_consnames := ["eq_refl'ᵗ"];
                             mind_entry_lc := [tApp (tRel 3) [tRel 2; tRel 1; tRel 0; tRel 0]] |}];
         mind_entry_universes := Monomorphic_ctx
                                   ([Level.Level "Top.110"],
                                   {| Constraint.this := []; Constraint.is_ok := Constraint.Raw.empty_ok |});
         mind_entry_private := None |}).

Run TemplateProgram (α <- tmQuoteInductive "Coq.Init.Logic.False" ;;
                    tmPrint α).

Eval lazy in (f_translate_mib ΣE 𝐂 {|
ind_npars := 0;
ind_bodies := [{|
               ind_name := "False";
               ind_type := tSort [(Level.lProp, false)];
               ind_kelim := [InSProp; InProp; InSet; InType];
               ind_ctors := [];
               ind_projs := [] |}];
ind_universes := Monomorphic_ctx (UContext.make [] Constraint.empty) |}).



Definition f_translate_arity' (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (n_params : nat) (name : kername) (arity : term)
  : tsl_result (evar_map * term) :=
  (* put parameters in context with dummy types *)
  let reduction_context := dummy_context (S n_params) in
  (* translation the arity *)
  let (l, s) := decompose_prod arity  in
  let n_indices := length l in
  let (σ, arity') := translate_type false None (snd tsl_ctx) cat env σ arity in
  (* now reduce compositions with id, β-redexes, η-redexes *)
  arity' <- match reduce [] reduction_context arity' with
           | Checked a => ret a
           | TypeError e => Error (TypingError e)
           end ;;
  (* and then replace the translated sort with the base one *)
  (* the ocaml plugin does something pretty weird here, probably because of universe stuff *)
  a <- match decompose_prod_n n_indices arity' with
      | Some (a, _) => ret a
      | None => Error (UnexpectedError
                        ("Something went really wrong during the translation of the arity of " ++ name))
      end ;;
  ret (σ, compose_prod a s).


Eval lazy in (reduce [] (dummy_context 5) (reduce_compositions (snd (fst ΣE)) 𝐂  (snd (translate_type false None (snd ΣE) 𝐂 empty_env empty_σ (tProd nAnon Relevant (tRel 1) (tSort [(Level.lProp, false)])))))).

Eval lazy in (reduce_compositions (snd (fst ΣE)) 𝐂 (tProd nAnon Relevant
            (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
               (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
                  (tApp (tRel 3)
                     [tRel 1;
                     tApp (tConst "Top.compose" [])
                       [tRel 2; tRel 2; tRel 1;
                       tApp (tConst "Top.compose" []) [tRel 2; tRel 1; tRel 1; tApp (tConst "Top.id" []) [tRel 1]; tRel 0];
                       tApp (tConst "Top.id" []) [tRel 2]]; tRel 1; tApp (tConst "Top.id" []) [tRel 1]])))
            (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
               (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0]) (tSort [(Level.lProp, false)]))))).

Eval lazy in (decompose_prod_n 1 (tProd nAnon Relevant
         (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
            (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
               (tApp (tRel 3) [tRel 1; tRel 0; tRel 1; tApp (tConst "Top.id" []) [tRel 1]])))
         (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
            (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0]) (tSort [(Level.lProp, false)]))))).
Eval lazy in (compose_prod [(nAnon, Relevant,
           tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
             (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
                (tApp (tRel 3)
                   [tRel 1;
                   tApp (tConst "Top.compose" [])
                     [tRel 2; tRel 2; tRel 1;
                     tApp (tConst "Top.compose" []) [tRel 2; tRel 1; tRel 1; tApp (tConst "Top.id" []) [tRel 1]; tRel 0];
                     tApp (tConst "Top.id" []) [tRel 2]]; tRel 1; tApp (tConst "Top.id" []) [tRel 1]])))] (tSort [(Level.lProp, false)])).

Eval lazy in (f_translate_arity' ΣE 𝐂 empty_env empty_σ 2 "kername" (tProd nAnon Relevant (tRel 1) (tSort [(Level.lProp, false)]))).

Inductive eqᵗ (p : 𝐂_obj) (A : forall p0 : 𝐂_obj, p ~> p0 -> forall p : 𝐂_obj, p0 ~> p -> Type)
(x : forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (α ô id) p0 id) :
  (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (id ô (α ô id)) p0 id) -> Type :=
  eq_reflᵗ : eqᵗ p A x x.

Run TemplateProgram (α <- tmQuoteInductive "eqᵗ" ;;
                       β <- tmEval lazy (mind_body_to_entry α) ;;
                       tmPrint β).

Run TemplateProgram (tmMkInductive ({|
         mind_entry_record := None;
         mind_entry_finite := Finite;
         mind_entry_params := [("p",
                               LocalAssum (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []));
                              ("A",
                              LocalAssum
                                (tProd (nNamed "p") Relevant
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])

                                               (tProd (nNamed "p") Relevant
                                                  (tInd
                                                     {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}
                                                     [])
                                                  (tProd (nNamed "α") Relevant
                                                     (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                                     (tSort [(Level.Level "Top.110", false)])))
                              )));
                              ("x",
                              LocalAssum
                                (tProd (nNamed "p") Relevant
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                      (tApp (tApp (tRel 2) [tRel 1; tRel 0]) [tRel 1; tApp (tConst "Top.id" []) [tRel 1]]))))];
         mind_entry_inds := [{|
                             mind_entry_typename := "eq'ᵗ";
                             mind_entry_arity := tProd nAnon Relevant ((tProd (nNamed "p0") Relevant (tConst "Top.𝐂_obj" [])
                                             (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 3; tRel 0])
                                                (tApp (tRel 3)
                                                   [tRel 1;
                                                   tApp (tConst "Top.compose" [])
                                                     [tRel 4; tRel 1; tRel 1; tApp (tConst "Top.id" []) [tRel 1];
                                                     tApp (tConst "Top.compose" [])
                                                       [tRel 4; tRel 4; tRel 1; tRel 0;
                                                       tApp (tConst "Top.id" []) [tRel 4]]]; tRel 1;
                                                   tApp (tConst "Top.id" []) [tRel 1]])))) (tSort [(Level.lProp, false)]);
                             mind_entry_template := false;
                             mind_entry_consnames := ["eq_refl'ᵗ"];
                             mind_entry_lc := [tApp (tRel 3) [tRel 2; tRel 1; tRel 0; tRel 0]] |}];
         mind_entry_universes := Monomorphic_ctx
                                   ([Level.Level "Top.110"],
                                   {| Constraint.this := []; Constraint.is_ok := Constraint.Raw.empty_ok |});
         mind_entry_private := None |})).

Run TemplateProgram (tmMkInductive ({|
         mind_entry_record := None;
         mind_entry_finite := Finite;
         mind_entry_params := [("p",
                               LocalAssum (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []));
                              ("A",
                              LocalAssum
                                (tProd (nNamed "p") Relevant
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])

                                               (tProd (nNamed "p") Relevant
                                                  (tInd
                                                     {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}
                                                     [])
                                                  (tProd (nNamed "α") Relevant
                                                     (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                                     (tSort [(Level.Level "Top.110", false)])))
                              )));
                              ("x",
                              LocalAssum
                                (tProd (nNamed "p") Relevant
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                      (tApp (tApp (tRel 2) [tRel 1; tRel 0]) [tRel 1; tApp (tConst "Top.id" []) [tRel 1]]))))];
         mind_entry_inds := [{|
                             mind_entry_typename := "eq'ᵗ";
                             mind_entry_arity := tProd nAnon Relevant (tRel 1) (tSort [(Level.lProp, false)]);
                             mind_entry_template := false;
                             mind_entry_consnames := ["eq_refl'ᵗ"];
                             mind_entry_lc := [tApp (tRel 3) [tRel 2; tRel 1; tRel 0; tRel 0]] |}];
         mind_entry_universes := Monomorphic_ctx
                                   ([Level.Level "Top.110"],
                                   {| Constraint.this := []; Constraint.is_ok := Constraint.Raw.empty_ok |});
         mind_entry_private := None |})).

(*
tsl_context = global_context * tsl_table
global_context = (list global_decl) * uGraph.t
tsl_table = list (global_reference * term)
 *)

Eval lazy in (f_translate_lc_list ΣE 𝐂 empty_env empty_σ _ lc substfn invsubst).


(** End of tests *)

Run TemplateProgram (tImplementTC ΣE "𝕀_TC" "𝕀" Type).
Next Obligation.
  exact (p0 ~> 1).
Defined.


(* Now defining some useful maps *)

Definition terminal_word_aux (p : nat) (q : nat) : word (p+q) p.
  revert p. induction q.
  - intro p. rewrite <- (plus_n_O p). exact empty.
  - intro p. apply degen.
    + exists 0. easy.
    + rewrite <- plus_n_Sm.
      change (word (S (p + q)) (S p)) with (word (S p + q) (S p)).
      apply IHq.
Defined.

Definition terminal_word (p : nat) : word p 0.
  exact (terminal_word_aux 0 p).
Defined.

Definition terminal_map (p : nat) : cube p -> cube 0.
  intro c. intros [a H]. destruct (pos_ge_0 a H).
Defined.


(*
   this proof uses funext to show that any two arrows with terminal codomain must be
   equal. If necessary, it is possible to define a version that doesn't use it.
 *)
Theorem terminal_map_admissible (p : nat) :
  terminal_map p =s comp_word (terminal_word p).
Proof.
  apply eq_eqs.
  apply funext. intro a. apply funext. intros [b H]. destruct (pos_ge_0 b H).
Qed.

Definition terminal_arrow (p : nat) : p ~> 0.
  assert (admissible (terminal_map p)).
  - eapply spair_s. exact (terminal_map_admissible p).
  - exact (terminal_map p ; H)s.
Defined.

Definition 𝕀_end_map (p : nat) (e : bool) : cube p -> cube 1 :=
  (fun (_ : cube p) (_ : finset 1) => e).

Definition 𝕀_end_word (p : nat) (e : bool) : word p 1.
  apply face.
  - exists 0. easy.
  - exact e.
  - exact (terminal_word p).
Defined.

Theorem 𝕀_end_admissible (p : nat) (e : bool) :
  𝕀_end_map p e =s comp_word (𝕀_end_word p e).
Proof.
  apply eq_eqs. simpl. rewrite <- (eqs_eq (terminal_map_admissible p)).
  apply funext. intro c. apply funext. intros [x H]. destruct x.
  - compute. reflexivity.
  - pose proof (le_S_n (S x) 0 H) as H'. apply pos_ge_0 in H'. destruct H'.
Qed.

Definition 𝕀_end (p : nat) (e : bool) : p ~> 1.
  assert (admissible (𝕀_end_map p e)).
  - eapply spair_s. exact (𝕀_end_admissible p e).
  - exact (𝕀_end_map p e ; H)s.
Defined.

Run TemplateProgram (tImplementTC 𝕀_TC "𝕀₀_TC" "𝕀₀" 𝕀).
Next Obligation.
  exact (𝕀_end p false).
Defined.

Run TemplateProgram (tImplementTC 𝕀₀_TC "𝕀₁_TC" "𝕀₁" 𝕀).
Next Obligation.
  exact (𝕀_end p true).
Defined.

Definition test6 := ltac:(let t := eval lazy in (snd (translate_type true None (snd ΣE) 𝐂 {| Environ.env_globals := (fst (fst ΣE)) |} tt test3)) in exact t).

Eval lazy in (hnf_stack
                []
                []
                (snd (translate_type true None (snd ΣE) 𝐂 {| Environ.env_globals := (fst (fst ΣE)) |} tt test3))).

Make Definition test7 := (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
  (tApp
     (tLambda (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
        (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 1; tRel 0])
           (tProd nAnon Relevant
              (tProd (nNamed "p") Relevant (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                 (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                    (tApp
                       (tLambda (nNamed "p") Relevant
                          (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                          (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                             (tProd (nNamed "p") Relevant
                                (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                   (tSort [(Level.lProp, false)]))))) [tRel 1; tApp (tConst "Top.id" []) [tRel 1]])))
              (tApp
                 (tLambda (nNamed "p") Relevant
                    (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                    (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 3; tRel 0])
                       (tProd nAnon Relevant
                          (tProd (nNamed "p") Relevant
                             (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                             (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                (tApp
                                   (tLambda (nNamed "p") Relevant
                                      (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                      (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                         (tProd (nNamed "p") Relevant
                                            (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                            (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                               (tSort [(Level.lSet, false)])))))
                                   [tRel 1; tApp (tConst "Top.id" []) [tRel 1]])))
                          (tApp
                             (tLambda (nNamed "p") Relevant
                                (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                (tLambda (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 3; tRel 0])
                                   (tProd (nNamed "p") Relevant
                                      (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                      (tProd (nNamed "α") Relevant (tApp (tConst "Top.arrow" []) [tRel 2; tRel 0])
                                         (tSort [(Level.Level "Top.64", false)])))))
                             [tRel 2; tApp (tConst "Top.id" []) [tRel 2]])))) [tRel 2; tApp (tConst "Top.id" []) [tRel 2]]))))
     [tRel 0; tApp (tConst "Top.id" []) [tRel 0]])).

Eval vm_compute in (hnf_stack
                      []
                      []
                      (snd (translate_type false None (snd ΣE) 𝐂 {| Environ.env_globals := (fst (fst ΣE)) |} tt test3))).

Run TemplateProgram (α <- tmEval lazy (translate_type false None (snd ΣE) 𝐂 {| Environ.env_globals := (fst (fst ΣE)) |} tt test3) ;;
                       tmPrint α).

Inductive test := const_test : test.
Fixpoint test' (n : nat) := 3.
Definition bonjour := fun (A : Type) (x : A) => x.
Run TemplateProgram (α <- tmEval all (tsl_id "test") ;;
                       tmPrint α).

Inductive test1 : Type :=
| c1 : test2 -> test1
with test2 : Type :=
| c2 : test1 -> test2.

Run TemplateProgram (α <- tmAbout "test1" ;;
                       tmPrint α).

(* tmAbout "test" -> "Top.test" *)
(* tsl_id "test" -> "testᵗ" *)
(* kn' will, however, be Top.testᵗ *)

Run TemplateProgram (α <- tmQuoteInductive "test1" ;;
                    tmPrint α).

Run TemplateProgram (γ <- tTranslate 𝕀₁_TC "test" ;;
                       tmDefinition "testTC" γ ;;
                       ret γ).
Run TemplateProgram (tTranslate bonjourTC "bonjour'").
Print bonjour'ᵗ.



(* We copy translated definitions of [eq] generated by the OCaml
   forcing plugin, because inducives are not supported yet by the
   template-coq forcing translation *)
Inductive eqᵗ (p : 𝐂_obj) (A : forall p0 : 𝐂_obj, p ~> p0 -> forall p : 𝐂_obj, p0 ~> p -> Type)
(x : forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (α ô id) p0 id) :
  (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (id ô (α ô id)) p0 id) -> Type :=
  eq_reflᵗ : eqᵗ p A x x.

(* We use this trick with η-expanded version of application of [eq] to
   be able to use existing translations.  If we just lest plain [eq],
   the application would be of a special kind (of inductive type) and
   it is translated differently, not as an ordinary application of a
   global constant *)
Definition eq_f {A: Type} (a b : A) := a = b.

Definition eq_fᵗ := fun (p : 𝐂_obj) (A : forall p0 : 𝐂_obj, p ~> p0 -> forall p1 : 𝐂_obj, p0 ~> p1 -> Type)
  (a b : forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (α ô id) p0 id) (p0 : 𝐂_obj)
  (α : p ~> p0) =>
eqᵗ p0
  (fun (p1 : 𝐂_obj) (α0 : p0 ~> p1) =>
   (fun (p2 : 𝐂_obj) (α1 : p ~> p2) => A p2 (α1 ô id)) p1 (id ô (α0 ô α)))
  (fun (p1 : 𝐂_obj) (α0 : p0 ~> p1) =>
   (fun (p2 : 𝐂_obj) (α1 : p ~> p2) => a p2 (α1 ô id)) p1 (id ô (α0 ô α)))
  (fun (p1 : 𝐂_obj) (α0 : p0 ~> p1) =>
     (fun (p2 : 𝐂_obj) (α1 : p ~> p2) => b p2 (α1 ô id)) p1 (id ô (α0 ô α))).


(* This definition will fail if we leave the type of [A] implicit. *)
Definition eq_is_eq :
  forall p (A : forall x : 𝐂_obj, (p ~> x) -> forall x1 : 𝐂_obj, (x ~> x1) -> Type)
         (x y: forall p0 (f:p ~> p0), A p0 f p0 id),
    eq x y -> eqᵗ p A x y. (* it even fails if i don't mention A as an explicit argument
                             here b/c of some mysterious reason *)
Proof.
  intros. rewrite H. apply eq_reflᵗ.
Qed.

Definition ctx_with_eq := add_translation 𝕀₁_TC (ConstRef "Top.eq_f", tConst "eq_fᵗ" []).



(* I need false, too *)
Run TemplateProgram (tImplement 𝕀₁_TC "ax2" (eq_f 𝕀₀ 𝕀₁ -> False)).
