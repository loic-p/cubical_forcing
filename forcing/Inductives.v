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
        Forcing.TFUtils.

Import MonadNotation.
Import ListNotations.

(* When possible, decomposes a product Π(x₁:τ₁)…(xₙ:τₙ).t into a tuple ([x₁:τ₁ ; … ; xₙ:τₙ] , t)
   If not possible, returns None. *)
Definition decompose_prod_n (n : nat) (tm : term) :=
  let fix aux param n tm :=
      match n with
      | 0 => Some (param, tm)
      | S n' => match tm with
               | tProd na r t u => aux ((na, r, t)::param) n' u
               | tCast c _ _ => aux param n c
               | _ => None
               end
      end
  in
  aux [] n tm.

(* Decomposes completely a product type into (typed arguments) * body *)
Definition decompose_prod (tm : term) :=
  let fix aux param tm :=
      match tm with
      | tProd na r t u => aux ((na, r, t)::param) u
      | tCast c _ _ => aux param c
      | _ => (param, tm)
      end
  in
  aux [] tm.

(* Rebuilds a previously decomposed product type *)
Fixpoint compose_prod param tm :=
  match param with
  | nil => tm
  | (na, r, t)::tail => compose_prod tail (tProd na r t tm)
  end.

(* Generates a context for reduction with n assumtions of a random type. *)
(* This is used to close terms before sending them to reduce *)
Fixpoint dummy_context (n : nat) :=
  match n with
  | 0 => []
  | S n' => (dummy_context n') ,, (vass nAnon Relevant (tConst "dummy var" []))
  end.

Definition dummy_fctx translator cat n :=
  let ctx := [] : list forcing_condition in
  let empty := {| f_context := []; f_category := cat; f_translator := translator; |} in
  let fix aux n acc :=
      match n with
      | 0 => acc
      | S n' => aux n' (add_variable acc)
      end
  in
  aux n empty.

(* applies f to all the subterms of t, without any recursion *)
Definition map_constr (f : term -> term) (t : term) : term :=
    match t with
    | tRel i => t
    | tEvar ev args => tEvar ev (List.map f args)
    | tLambda na r T M => tLambda na r (f T) (f M)
    | tApp u v => tApp (f u) (List.map f v)
    | tProd na r A B => tProd na r (f A) (f B)
    | tCast c kind t => tCast (f c) kind (f t)
    | tLetIn na r b t b' => tLetIn na r (f b) (f t) (f b')
    | tCase ind r p c brs =>
      let brs' := List.map (on_snd f) brs in
      tCase ind r (f p) (f c) brs'
    | tProj p c => tProj p (f c)
    | tFix mfix idx =>
      let mfix' := List.map (map_def f) mfix in
      tFix mfix' idx
    | tCoFix mfix k =>
      let mfix' := List.map (map_def f) mfix in
      tCoFix mfix' k
    | x => x
    end.

(* reduces all [shallow] redexes of the form (id ∘ f) or (f ∘ id) to f *)
Fixpoint reduce_compositions (ug : uGraph.t) (cat : category) (t : term) : term :=
  match t with
  | tApp u (_::_::_::α1::α2::nil) =>
    if eq_term ug cat.(cat_comp) u then
      let is_id := fun x => match x with
                        | tApp v _ => if eq_term ug cat.(cat_id) v then true else false
                        | _ => false
                        end
      in
      if is_id α1 then
        reduce_compositions ug cat α2
      else if is_id α2 then
        reduce_compositions ug cat α1
      else
        map_constr (reduce_compositions ug cat) t
    else
      map_constr (reduce_compositions ug cat) t
  | _ => map_constr (reduce_compositions ug cat) t
  end.

Definition andb_list l := fold_left (fun acc b => andb acc b) l true.

(* returns true if the variable with de Bruijn index n does not occur in t *)
Fixpoint noccurn (n : nat) (t : term) : bool :=
  match t with
  | tRel m => negb (eq_nat n m)
  | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tMeta _ => true
  | tEvar _ tl => andb_list (List.map (noccurn n) tl)
  | tCast t1 _ t2 => (noccurn n t1) && (noccurn n t2)
  | tProd _ _ t1 t2 => (noccurn n t1) && (noccurn (S n) t2)
  | tLambda _ _ t1 t2 => (noccurn n t1) && (noccurn (S n) t2)
  | tLetIn _ _ t1 t2 t3 => (noccurn n t1) && (noccurn n t2) && (noccurn (S n) t3)
  | tApp t tl => (noccurn n t) && (andb_list (List.map (noccurn n) tl))
  | tCase _ _ t1 t2 tl => (noccurn n t1) && (noccurn n t2) && (andb_list (List.map (fun t => noccurn n (snd t)) tl))
  | tProj _ t => noccurn n t
  | tFix mfix _ => andb_list (List.map (fun x => noccurn n (x.(dbody))) mfix)
  | tCoFix mfix _ => andb_list (List.map (fun x => noccurn n (x.(dbody))) mfix)
  end.

(* η-reduces all redexes in t *)
Fixpoint eta_reduce (t : term) : term :=
  match t with
  | tLambda na r a b =>
    match eta_reduce b with
    | tApp f args =>
      match List.rev args with
      | (tRel 0)::tl =>
        let args' := List.rev tl in
        if andb_list (List.map (noccurn 0) (f::args')) then
          (mkApps f args') {0 := (tConst "dummy var" [])}
	else
          map_constr eta_reduce t
      | _ => map_constr eta_reduce t
      end
    | _ => map_constr eta_reduce t
    end
  | _ => map_constr eta_reduce t
  end.

(* translates the arity of a one_inductive_body. env should contain the parameters of
 the mutual_inductive_body *)
Definition f_translate_arity (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (n_params : nat) (name : kername) (arity : term)
  : tsl_result (evar_map * term) :=
  (* put parameters in context with dummy types *)
  let reduction_context := dummy_context (S n_params) in
  let forcing_ctxt := dummy_fctx (snd tsl_ctx) cat n_params in
  (* translation the arity *)
  let (l, s) := decompose_prod arity  in
  let n_indices := length l in
  let (σ, arity') := otranslate_type otranslate env forcing_ctxt σ arity in
  (* now reduce compositions with id, β-redexes, η-redexes *)
  let arity' := reduce_compositions (snd (fst tsl_ctx)) cat arity' in
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

(* see coq Vars.substnl *)
Definition substnl l n t :=
  List.fold_left (fun t u => subst u n t) l t.

(* this builds a substitution that will come in handy later *)
(* contexts from the ocaml plugin have been converted to list of name * relevance * term *)
(* the head of the arityctxt list shall be the first argument, and so on *)
Definition f_translate_oib_type (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ  : evar_map) (id : kername) (arityctxt : list (name * relevance * term))
  : evar_map * term :=
  (* we translate I as λp params indices q α . (var I) p params indices *)
  (* first, the body of the lambda abstraction *)
  let narityctxt := length arityctxt in
  let args := map tRel (List.rev (seq 2 (S narityctxt))) in
  let fnbody := mkApps (tConst id []) args in
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
  let hom := tApp cat.(cat_hom) [tRel (1 + narityctxt) ; tRel 0] in (** TODO : should that morphism be reversed ? *)
  let argctxt := (vass (nNamed "α") Relevant hom)
                  ::(vass (nNamed "q") Relevant cat.(cat_obj))
                  ::(tr_arity ++ [vass (nNamed "p") Relevant cat.(cat_obj)])%list in
  (* put everything together *)
  (* memo : it_mkLambda_or_LetIn is defined both in Template.Typing and Forcing.TFUtils with reversed arguments *)
  (σ, it_mkLambda_or_LetIn fnbody argctxt).

(* applies f_translate_oib_names to all the inductives of a mutual inductive body,
 in order to build a substitution : list of name * translated type *)
Definition f_translate_oib_types (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (mib : mutual_inductive_body)
  : evar_map * list (ident * term) :=
  let fold := fun (acc : evar_map * list (ident * term)) oib =>
               let (σ, tail) := acc in
               let (arityctxt, _) := decompose_prod oib.(ind_type) in
               let (σ, tr) := f_translate_oib_type tsl_ctx cat env σ oib.(ind_name) arityctxt in
               (σ, (oib.(ind_name), tr)::tail)
  in
  fold_left fold mib.(ind_bodies) (σ, nil).

(* this is supposed to mimic Vars.replace_vars from Coq, except that the translation
   does not handle vars. So we use consts instead. *)
Fixpoint replace_const t k u :=
  match u with
  | tConst x _ => match eq_string x (fst t) with
                 | true => lift0 k (snd t)
                 | false => u
                 end
  | tEvar ev args => tEvar ev (List.map (replace_const t k) args)
  | tLambda na r T M => tLambda na r (replace_const t k T) (replace_const t (S k) M)
  | tApp u v => tApp (replace_const t k u) (List.map (replace_const t k) v)
  | tProd na r A B => tProd na r (replace_const t k A) (replace_const t (S k) B)
  | tCast c kind ty => tCast (replace_const t k c) kind (replace_const t k ty)
  | tLetIn na r b ty b' => tLetIn na r (replace_const t k b) (replace_const t k ty) (replace_const t (S k) b')
  | tCase ind r p c brs =>
    let brs' := List.map (on_snd (replace_const t k)) brs in
    tCase ind r (replace_const t k p) (replace_const t k c) brs'
  | tProj p c => tProj p (replace_const t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (replace_const t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (replace_const t k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Fixpoint replace_consts s t :=
  match s with
  | nil => t
  | head::tail => replace_consts tail (replace_const head 0 t)
  end.

(* this is supposed to mimic Vars.substn_vars in Coq.
   since the plugin doesnt handle vars, we use consts instead. *)
Definition substn_consts (p : nat) (vars : list ident) (c : term)
  : term :=
  let fold := fun acc var =>
               let (n, l) := acc : nat * list (ident * term) in
               ((S n), (var, tRel n)::l)
  in
  let (_, subst) := fold_left fold vars (p,[]) in
  replace_consts (List.rev subst) c.

(* given a list of constant names, adds bindings to their translated version *)
Fixpoint extend_tsl_table (names : list ident) (tbl : tsl_table) :=
  match names with
  | [] => tbl
  | hd::tl => extend_tsl_table tl ((ConstRef hd, tConst hd [])::tbl)
  end.

(* translation of the constructors list *)
(* the context for constructors is : 0 ~ n parameters, n+1 ~ n+k inductives *)
(* if this stack overflows, look for open terms passed to reduce *)
Definition f_translate_lc_list (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (n_params : nat) (lc : list term)
           (substfn : list (ident * term)) (invsubst : list ident)
  : tsl_result (evar_map * list term) :=
  (* put names of inductives inside tsl_tbl, so that the translation function will
     be able to recognize them *)
  let tsl_tbl := extend_tsl_table invsubst (snd tsl_ctx) in
  (* put arguments in the context (with dummy type because they are not necessary) *)
  let reduction_ctxt := dummy_context (S n_params) in
  (* put them in the forcing context too, somewhat *)
  let forcing_ctxt := dummy_fctx tsl_tbl cat n_params in
  let f_translate_lc :=
      fun (m : tsl_result (evar_map * list term)) typ =>
        acc <- m ;;
        let (σ, tail) := acc : evar_map * list term in
        (* lift all free variables in the type to account for insertion of a new parameter
         i think this corresponds to the trick with envtr in the ocaml plugin ? *)
                (* replace the indices for oib's with their names *)
        let typ := substnl (map (fun x => tConst x []) invsubst) n_params typ in
        let (σ, typ) := otranslate_type otranslate env forcing_ctxt σ typ in
        (* replace the names of oib's with their translation *)
        let typ := replace_consts substfn typ in
        let typ := reduce_compositions (snd (fst tsl_ctx)) cat typ in
        typ' <- match reduce [] reduction_ctxt typ with
               | Checked typ => ret typ
               | TypeError e => Error (TypingError e)
               end ;;
        (* put indices back *)
        let typ' := substn_consts (S n_params) invsubst typ' in
        let typ' := eta_reduce typ' in (* we need clean parameters for the constructor to be well formed *)
        (** ocaml code for universe handling (?) *)
        (* let envtyp_ = Environ.push_rel_context [Name (Nameops.add_suffix body.mind_typename "_f"),None, *)
        (*       				  it_mkProd_or_LetIn arity params] env in *)
        (* let envtyp_ = Environ.push_rel_context params envtyp_ in *)
        (* let sigma, ty = Typing.type_of envtyp_ sigma typ_ in                              *)
        (* let sigma, b = Reductionops.infer_conv ~pb:Reduction.CUMUL envtyp_ sigma ty s in *)
        (** end *)
        ret (σ, typ'::tail)
  in
  fold_left f_translate_lc lc (ret (σ, nil)).

(* Vernacular names of the translated inductive and constructors *)
(* Here the ocaml plugin tries to use provided ids before calling the name translation function.
 This might be important, but i dont think so *)
Definition f_translate_names (typename : ident) (consnames : list ident)
  : ident * list ident :=
  (tsl_ident typename, map tsl_ident consnames).


(* Apply the translation to one oib *)
Definition f_translate_oib (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map)
           (entry : one_inductive_entry)
           (n_params : nat) (substfn : list (ident * term)) (invsubst : list ident)
  : tsl_result (evar_map * one_inductive_entry) :=
  let (typename, consnames) := f_translate_names entry.(mind_entry_typename) entry.(mind_entry_consnames) in
  let template := entry.(mind_entry_template) in   (* translation should preserve template polymorphism *)
  x <- f_translate_arity tsl_ctx cat env σ n_params entry.(mind_entry_typename) entry.(mind_entry_arity) ;;
  let (σ, arity) := x : evar_map * term in
  x <- f_translate_lc_list tsl_ctx cat env σ n_params entry.(mind_entry_lc) substfn invsubst ;;
  let (σ, lc) := x : evar_map * list term in
  ret (σ, {| mind_entry_typename := typename ;
             mind_entry_arity := arity ;
             mind_entry_template := template ;
             mind_entry_consnames := consnames ;
             mind_entry_lc := List.rev lc |}).

(** TODO : Universes *)
Definition from_env (env : Environ.env)
  : evar_map :=
  tt.

Definition f_translate_params (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map)
           (params : list (ident * local_entry))
  : evar_map * list (ident * local_entry) :=
  let fold := fun param acc =>
               let (id, e) := param : ident * local_entry in
               let t := match e with
                       | LocalDef x => x
                       | LocalAssum x => x
                       end in
               let '(σ, fctx, tail) := acc : evar_map * forcing_context * list (ident * local_entry)  in
               let (ext, tfctx) := extend env fctx in
               let (σ, t') := otranslate_type otranslate env tfctx σ t in
               let t' := it_mkProd_or_LetIn t' ext in
               let t' := reduce_compositions (snd (fst tsl_ctx)) cat t' in
               let fctx := add_variable fctx in
               (σ, fctx, (id, LocalAssum t')::tail)
  in
  let init := [("p", LocalAssum (cat.(cat_obj)))] in
  let empty := {| f_context := []; f_category := cat; f_translator := (snd tsl_ctx) ; |} in
  let '(σ, _, params) := fold_right fold (σ, empty, init) (List.rev params) in
  (σ, List.rev params).

(* main translation function for inductives *)
Definition f_translate_mib (tsl_ctx : tsl_context) (cat : category) (mib : mutual_inductive_body)
  : tsl_result mutual_inductive_entry :=
  (* entries are more pleasant to work with than bodies *)
  let entry := mind_body_to_entry mib in
  (** TODO : universes *)
  (* env and σ should be used to keep track of universe variables *)
  let env := Environ.empty_env in
  let σ := from_env env in
  let invsubst := List.rev (map (fun x => x.(mind_entry_typename)) entry.(mind_entry_inds)) in
  let (σ, substfn) := f_translate_oib_types tsl_ctx cat env σ mib in
  let (σ, params) := f_translate_params tsl_ctx cat env σ entry.(mind_entry_params) in
  let fold := fun oib acc =>
               α <- acc ;;
               let (σ, tail) := α : evar_map * (list one_inductive_entry) in
               α <- f_translate_oib tsl_ctx cat env σ oib mib.(ind_npars) substfn invsubst ;;
               let (σ, oib) := α : evar_map * one_inductive_entry in
               ret (σ, oib::tail)
  in
  α <- fold_right fold (ret (σ, nil)) entry.(mind_entry_inds) ;;
  let (σ, bodies) := α : evar_map * list one_inductive_entry in
  (* let params := List.map make_param params in *)
  (* let (_, uctx) := Evd.universe_context sigma in *)
  let entry := {| mind_entry_record := None ; (* quoting inductives seems to ignore records *)
               mind_entry_finite := Finite ; (* not dealing with coinductives *)
               mind_entry_params := params ;
               mind_entry_inds := bodies ;
               (* Okay so the ocaml plugin somehow gets the universe graph from the evar_map.
                I guess this is because translation could introduce new universe constraints. *)
               mind_entry_universes := entry.(mind_entry_universes) ; (** TODO : universes *)
               mind_entry_private := None |} (* this is also lost during quoting *)
  in
  ret entry.

(* finalizes the translation by adding everything to the translation context *)
Definition f_translate_ind (cat : category) (tsl_ctx : tsl_context)
           (id : kername) (id' : kername) (mib : mutual_inductive_body) :
  tsl_result (tsl_table * mutual_inductive_entry) :=
  mib <- f_translate_mib tsl_ctx cat mib ;;
  let translator := snd tsl_ctx in (** TODO *) (* not really sure what should be added to translator *)
  ret (translator, mib).
