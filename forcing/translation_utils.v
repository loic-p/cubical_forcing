(* Taken from Template Coq *)
Require Import Template.All.
Require Import List.
Import ListNotations MonadNotation String.
Open Scope string_scope.

Axiom todo : forall {A}, A.


Definition tsl_table := list (global_reference * term).

Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.


Definition tsl_context := (global_context * tsl_table)%type.

Definition emptyTC : tsl_context := (([], uGraph.init_graph), []).

Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandeled
| TypingError (t : type_error)
| UnexpectedError (s : string).

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.



Class Translation := { tsl_id : ident -> ident ;
                       tsl_tm : tsl_context -> term -> tsl_result term ;
                       tsl_ty : tsl_context -> term -> tsl_result term ;
                       tsl_ind : tsl_context -> kername -> kername -> mutual_inductive_body
                            -> tsl_result (tsl_table * mutual_inductive_entry)
                     }.


Definition tsl_ident (id : ident) : ident := (id ++ "ᵗ")%string.

Definition tsl_name tsl_ident n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.


Fixpoint in_listb (x : string) (l : list string) : bool :=
  match l with
    | [] => false
    | h :: t => if (string_dec h x) then true else in_listb x t
  end.

(** Remove duplicates from the list of strings *)
Fixpoint undup_string_list (l : list string) : list string :=
  match l with
    | [] => []
    | h :: t => if (in_listb h t) then undup_string_list t else h :: undup_string_list t
   end.

Arguments List.app  {_}.

(** Get all the global definitions in the term.  *)
Fixpoint get_global_consts (tm : term) : list ident :=
  match tm with
  | tRel _ => []
  | tVar _ => []
  | tMeta _ => []
  | tEvar _ _ => []
  | tSort _ => []
  | tCast t1 _ t2 => get_global_consts t1 ++ get_global_consts t2
  | tProd _ _ t1 t2 => get_global_consts t1 ++ get_global_consts t2
  | tLambda _ _ t1 t2 => get_global_consts t1 ++ get_global_consts t2
  | tLetIn _ _ t1 t2 t3 => get_global_consts t1 ++ get_global_consts t2 ++  get_global_consts t3
  | tApp t ts => get_global_consts t ++ (List.fold_left List.app (List.map get_global_consts ts) [])
  | tConst kn _ => [kn]
  | tInd  _ _ => []
  | tConstruct _ _ _ => []
  | tCase _ _ _ _ _ => []
  | tProj _ t => get_global_consts t
  | tFix _ _ => []
  | tCoFix _ _ => []
  end.


Definition add_translations (ctx : tsl_context) (ts : list (global_reference * term)): tsl_context :=
  let (Σ, E) := ctx in
  (Σ,  ts ++ E)%list.

Definition to_ctx `{Translation} (xs : list ident) : list (global_reference * term) :=
  List.map (fun x => (ConstRef x, tConst (tsl_id x) [])) xs.

(** Add global definitions to the translation table *)
Definition scan_globals `{Translation} (tm : term) (init : tsl_context) : TemplateMonad (tsl_context) :=
  ( mp <- tmCurrentModPath tt ;;
    ret (add_translations init (to_ctx (undup_string_list (get_global_consts tm))))).

(** Translates a given term and adds corresponding definitions *)
Definition tTranslateTm {A : Type} {tsl : Translation} (ΣE : tsl_context) (id : ident) (tm : A)
  : TemplateMonad tsl_context :=
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  kn' <- tmEval all (mp ++ "." ++ id') ;;
  t <- tmQuote tm ;;
  ty <- tmQuote A ;;
  t' <- tmEval lazy (tsl_tm ΣE t) ;;
     match t' with
     | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the body of " ++ id)
     | Success t' =>
        tmMkDefinition id t ;;
        tmMkDefinition id' t' ;;
        let decl := {| cst_universes := Monomorphic_ctx UContext.empty;
                       cst_type := ty; cst_body := Some t |} in
        let Σ' := add_global_decl (ConstantDecl id decl) (fst ΣE) in
        let E' := (ConstRef id, tConst kn' []) :: (snd ΣE) in
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
     end.

Definition tTranslateTmG {A : Type} {tsl : Translation} (ΣE : tsl_context) (id : ident) (tm : A)
  : TemplateMonad tsl_context :=
  t <- tmQuote tm ;;
  ΣE' <- scan_globals t ΣE ;;
  tTranslateTm ΣE' id tm.

Definition tTranslate {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmAbout id ;; (* whether id is a constant, an inductive, or a constructor *)
  id' <- tmEval all (tsl_id id) ;; (* that would be the translated name
                                   not a great idea when it comes to mutual inductives,
                                   because it is only the name of the first one *)
  mp <- tmCurrentModPath tt ;; (* the current location *)
  kn' <- tmEval all (mp ++ "." ++ id') ;; (* the path to the translated variable *)
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstructRef (mkInd kn n) _) (* this case really isnt handled at all *)
  | Some (IndRef (mkInd kn n)) =>
      d <- tmQuoteInductive id ;; (* get the body of the inductive *)
      d' <- tmEval lazy (tsl_ind ΣE kn kn' d) ;; (* translate the inductive *)
      match d' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the inductive " ++ id)
      | Success (E, decl) =>
        tmMkInductive decl ;;
        print_nf  (id ++ " has been translated as " ++ id') ;; (** TODO : list translated inductive types *)
        ret (add_global_decl (InductiveDecl kn d) (fst ΣE), E ++ snd ΣE)%list
      end

  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ => fail_nf (id ++ "is an axiom, not a definition")
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_universes := univs;
                         definition_entry_body := t |} =>
      (* ΣE' <- scan_globals t ΣE ;; *)
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      match t' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the body of " ++ id)
      | Success t' =>
        tmMkDefinition id' t' ;;
        let decl := {| cst_universes := univs;
                       cst_type := A; cst_body := Some t |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst kn' (UContext.instance (repr univs))) :: (snd ΣE) in
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  end.

Definition tAddExistingConst {tsl : Translation} (ΣE : tsl_context) (id : ident) (idᵗ : ident)
  : TemplateMonad tsl_context :=
  mp <- tmCurrentModPath tt ;;
  kn <- tmEval all (mp ++ "." ++ id) ;;
  knᵗ <- tmEval all (mp ++ "." ++ idᵗ) ;;
  e <- tmQuoteConstant idᵗ true ;;
  match e with
  | ParameterEntry _ => fail_nf (id ++ "is an axiom, not a definition")
  | DefinitionEntry {| definition_entry_type := A;
                       definition_entry_universes := univs;
                       definition_entry_body := t |} =>
    let decl := {| cst_universes := univs;
                   cst_type := A; cst_body := Some t |} in
    let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
    let E' := (ConstRef kn, tConst knᵗ (UContext.instance (repr univs))) :: (snd ΣE) in
    ret (Σ', E')
  end.

Definition tAddExistingInd {tsl : Translation} (ΣE : tsl_context) (id : ident) (idᵗ : ident)
  : TemplateMonad tsl_context :=
  mp <- tmCurrentModPath tt ;;
  (* kn <- tmEval all (mp ++ "." ++ id) ;; *)
  (* knᵗ <- tmEval all (mp ++ "." ++ idᵗ) ;; *)
  e <- tmQuoteInductive id ;;
  eᵗ <- tmQuoteInductive idᵗ ;;
  let Σ' := add_global_decl (InductiveDecl id e) (fst ΣE) in
  let Σ'' := add_global_decl (InductiveDecl idᵗ eᵗ) (fst ΣE) in
  let ind := mkInd id 0 in
  let indᵗ := mkInd idᵗ 0 in
  let E' := (IndRef ind,
             tInd indᵗ (UContext.instance (repr e.(ind_universes)))) :: (snd ΣE) in
  ret (Σ'', E').


Definition get_ucontext (id : kername) : TemplateMonad universe_context
  := qid <- tmQuoteConstant id false ;;
      ret (match qid with
           | ParameterEntry pe => pe.(parameter_entry_universes)
           | DefinitionEntry de => de.(definition_entry_universes)
           end).

Definition tImplement {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA <- tmQuote A ;;
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  match tA' with
  | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the type of " ++ id)
  | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      A' <- tmUnquoteTyped Type tA' ;;
      tmLemma id' A' ;;
      (* A'' <- tmUnquoteTyped Type tA ;; *)
      tmAxiom id A ;;
      gr <- tmAbout id ;;
      match gr with
      | Some (ConstRef kn) =>
        uc <- get_ucontext kn ;;
        let decl := {| cst_universes := uc;
                       cst_type := tA; cst_body := None |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' (UContext.instance (repr uc))) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      | _ => fail_nf (id ++ " was not found or is not a constant, this is a bug")
      end
  end.

(* A version of tImplement that defines a new context [newTC],
   extended with the implemented definition *)
Definition tImplementTC {tsl : Translation} (ΣE : tsl_context) (newTC : ident)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  TC <- tImplement ΣE id A ;;
  tmDefinition newTC TC ;;
  print_nf ("New translation context has been defined: " ++ newTC);;
  ret TC.


(* A version of tImplement that scans given type for global constants
   and builds a translation table. Works only if translated terms are difined using them
   naming shceme generated by [tsl_id]*)
Definition tImplementG {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA <- tmQuote A ;;
  ΣE' <- scan_globals tA ΣE ;;
  tImplement ΣE' id A.

(* Definition tImplementExisting (tsl_id : ident -> ident) *)
(*            (tsl_tm tsl_ty : global_context -> tsl_table -> term *)
(*                             -> tsl_result term) *)
(*            (Σ : tsl_context) (id : ident) *)
(*   : TemplateMonad (option tsl_context) := *)
(*   e <- tmQuoteConstant id true ;; *)
(*   match e with *)
(*   | ParameterEntry _ => tmPrint "Not a definition" ;; *)
(*                        tmReturn None *)
(*   | DefinitionEntry {| definition_entry_type := A; *)
(*                        definition_entry_body := t |} => *)
(*     match tsl_ty (fst Σ) (snd Σ) A with *)
(*     | Error _ => tmPrint "tsl error in type" ;; *)
(*                   tmReturn None *)
(*     | Success tA' => *)
(*       id' <- tmEval all (tsl_id id) ;; *)
(*       A' <- tmUnquoteTyped Type tA' ;; *)
(*       tmLemma id' A' ;; *)
(*       let decl := {| cst_universes := []; *)
(*                      cst_type := A; cst_body := Some t |} in *)
(*       let Σ' := ConstantDecl id decl :: (fst Σ) in *)
(*       let E' := (ConstRef id, tConst id' []) :: (snd Σ) in *)
(*       msg <- tmEval all (id ++ " has been translated as " ++ id') ;; *)
(*       tmPrint msg ;; *)
(*       tmReturn (Some (Σ', E')) *)
(*     end *)
(*   end. *)
