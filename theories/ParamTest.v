From MetaCoq Require Import Template.All Template.Universes.
Import Universes.Level.
Require Import Arith.Compare_dec.
Require Import TranslationUtils.
From MetaCoq.Translations Require Import translation_utils.
Import String List Lists.List.ListNotations MonadNotation.
Open Scope list_scope.
Open Scope string_scope.

Infix "<=" := Nat.leb.

Definition default_term   := tVar "constant_not_found".
Definition debug_term msg := tVar ("debug: " ++ msg).

Fixpoint tsl_rec0 (n : nat) (o : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if n <= k then (* global variable *) tRel (3 * (k - n) + n + o)
                        else (* local  variable *) t
  | tEvar k ts   => tEvar k (map (tsl_rec0 n o) ts)
  | tCast t c a  => tCast (tsl_rec0 n o t) c (tsl_rec0 n o a)
  | tProd na A B => tProd na (tsl_rec0 n o A) (tsl_rec0 (n+1) o B)
  | tLambda na A t  => tLambda na (tsl_rec0 n o A) (tsl_rec0 (n+1) o t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n o t) (tsl_rec0 n o A) (tsl_rec0 (n+1) o u)
  | tApp t lu       => tApp (tsl_rec0 n o t) (map (tsl_rec0 n o) lu)
  | tCase ik t u br => tCase ik (tsl_rec0 n o t) (tsl_rec0 n o u)
                            (map (fun x => (fst x, tsl_rec0 n o (snd x))) br)
  | tProj p t => tProj p (tsl_rec0 n o t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ _ t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _  => tApp t us
  end.


Definition suffix (n : name) s : name :=
  match n with
  | nAnon     => nAnon
  | nNamed id => nNamed (id ++ s)
  end.

Fixpoint apply (app : list term) (t : term) :=
  match app with
  | t' :: app =>  apply app (mkApp t (t' {4 := tRel 2} {3 := tRel 1} {2 := tRel 0}))
  | [] => t
  end.

Fixpoint tsl_rec1_app (app : list term) (E : tsl_table) (t : term) : term :=
  let tsl_rec1 := tsl_rec1_app [] in
  let debug case symbol :=
      debug_term ("tsl_rec1: " ++ case ++ " " ++ symbol ++ " not found") in
  match t with
  | tLambda na A t =>
      let A0 := tsl_rec0 0 2 A in
      let A1 := tsl_rec1 E A in

      tLambda (suffix na "₁") A0
        (tLambda (suffix na "₂") A0
          (tLambda (tsl_name tsl_ident na)
            (subst_app (lift0 2 A1) [tRel 1; tRel 0])
            (tsl_rec1_app (map (lift 2 3) app) E t)))
  | _ => let t1 :=
  match t with
  | tSort s =>
      tLambda (nNamed "x₁") (tSort s)
        (tLambda (nNamed "x₂") (tSort s)
          (tProd nAnon (tRel 1) (tProd nAnon (tRel 1) (tSort s))))

  | tRel k => tRel (3 * k)

  | tProd na A B =>
      let A0 := tsl_rec0 0 2 A in
      let B0 := tsl_rec0 1 2 B in
      let A1 := tsl_rec1 E A in
      let B1 := tsl_rec1 E B in
      let ΠAB0 := tProd na A0 B0 in
      
      tLambda (nNamed "f₁") ΠAB0
        (tLambda (nNamed "f₂") ΠAB0
          (tProd (suffix na "₁") (lift0 2 A0)
            (tProd (suffix na "₂") (lift0 2 A0)
              (tProd (tsl_name tsl_ident na)
                (subst_app (lift0 4 A1) [tRel 1; tRel 0])
                (subst_app (lift 2 3 B1) [tApp (tRel 4) [tRel 2]; tApp (tRel 3) [tRel 1]])))))

  | tApp t us =>
      let us' := concat (map (fun v => [tsl_rec0 0 2 v; tsl_rec0 0 1 v; tsl_rec1 E v]) us) in
      mkApps (tsl_rec1 E t) us'

  | tCast t c A =>
      let t0 := tsl_rec0 0 2 t in
      let t1 := tsl_rec1 E t in
      let A0 := tsl_rec0 0 2 A in
      let A1 := tsl_rec1 E A in
      tCast t1 c (mkApps A1 [tCast t0 c A0])

  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => set_univs t univs
    | None => debug "tConst" s
    end

  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => set_univs t univs
    | None => debug "tInd" (match i with mkInd s _ => s end)
    end

  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => set_univs t univs
    | None => debug "tConstruct" (match i with mkInd s _ => s end)
    end

  (* TODO *)
  | tCase ik t u brs as case =>
    let brs' := List.map (on_snd (lift0 1)) brs in
    let case1 := tCase ik (lift0 3 t) (tRel 2) brs' in
    let case2 := tCase ik (lift0 3 t) (tRel 1) brs' in
    match lookup_tsl_table E (IndRef (fst ik)) with
    | Some (tInd i _univ) =>
      tCase (i, (snd ik) * 3)
            (tsl_rec1_app [tsl_rec0 0 2 case1; tsl_rec0 0 1 case2] E t)
            (tsl_rec1 E u)
            (map (on_snd (tsl_rec1 E)) brs)
    | _ => debug "tCase" (match (fst ik) with mkInd s _ => s end)
    end

  | tLetIn na t A u => todo
  | tProj _ _ => todo
  | tFix _ _ | tCoFix _ _ => todo
  | tVar _ | tEvar _ _ => todo
  | tLambda _ _ _ => tVar "impossible"
  end
  in apply app t1
  end.

Definition tsl_rec1 := tsl_rec1_app [].

Fixpoint mapi_ {A B} n (f : nat -> A -> B) (t : list A) :=
  match t with
  | x :: t => f n x :: mapi_ (S 1) f t
  | [] => []
  end.
  
Definition mapi {A B} := @mapi_ A B 0. 

Definition universes_to_vars (U : universes_decl) : list Level.t :=
  match U with 
  | Polymorphic_ctx ctx => mapi (fun i _ => Var i) (fst ctx)
  | _ => []
  end.

Definition tsl_mind_body (E : tsl_table) (mp : string) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  pose (vars := universes_to_vars mind.(ind_universes)).
  refine (_, [{| ind_npars := 3 * mind.(ind_npars);
                 ind_params := []; (* params are inferred when converting to mutual_inductive_entry *)
                 ind_bodies := _;
                 ind_universes := mind.(ind_universes)|}]).  (* FIXME always ok? *)
  - refine (let kn' := tsl_kn tsl_ident kn mp in
            fold_left_i (fun E i ind => _ :: _ ++ E)%list mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - exact mind.(ind_finite).
  - refine (mapi _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}. (* UGLY HACK!!! todo *)
    + (* arity  *)
      refine (let ar := subst_app (tsl_rec1 E ind.(ind_type))
                                  [tInd (mkInd kn i) vars; tInd (mkInd kn i) vars] in
              ar).
    + (* constructors *)
      refine (mapi _ ind.(ind_ctors)).
      intros k ((name, typ), nargs).
      refine (tsl_ident name, _, 3 * nargs).
      refine (subst_app _ [tConstruct (mkInd kn i) k vars; tConstruct (mkInd kn i) k vars]).
      refine (fold_left_i (fun t0 i u => t0 {S i := u} {S i := u}) _ (tsl_rec1 E typ)).
      (* [I_0; ... I_(n-1)] *)
      
      refine (rev (mapi (fun i _ => tInd (mkInd kn i) vars)
                              mind.(ind_bodies))).
Defined.

Instance param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun ΣE t => ret (tsl_rec1 (snd ΣE) t) ;
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ty  := None ;
     tsl_ind := fun ΣE mp kn mind => ret (tsl_mind_body (snd ΣE) mp kn mind) |}.