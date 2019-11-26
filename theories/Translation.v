From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Require Import UR TranslationUtils HoTT.
Import String MonadNotation List Lists.List.
Require Import String.
Import Template.Universes.Level.
Import Lists.List.ListNotations.

Open Scope list_scope.
Open Scope nat_scope.
Open Scope type_scope.

Set Universe Polymorphism.
Local Existing Instance default_fuel.
Open Scope list_scope.

(* Given e : A ⋈ B, a : A, b : B, returns a ≈ b with the given UR *)
Definition rel_of (e a b: term) :=
  tApp (tProj ({| inductive_mind := "ParametricityALaCarte.theories.UR.Rel"
                ; inductive_ind  := 0 |}, 2, 0)%core
         (tProj ({| inductive_mind := "ParametricityALaCarte.theories.UR.FR_Type"
                  ; inductive_ind  := 0 |}, 2, 1)%core 
           (e))) [a; b].

(* Given a term e :  A ⋈ B, returns the projection onto _REquiv *)
Definition proj_equiv (e : term) :=
  tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.FR_Type"
          ; inductive_ind  := 0 |}, 2, 0)%core e.

Definition univ_transport := <% @univalent_transport %>.

Definition ur_refl@{i} {A B : Type@{i}} {UR : A ⋈ B} (x : A) :
  @rel A B UR x (@univalent_transport _ _ UR x).
  eapply center.
Defined.

Definition ur_refl' := <% @ur_refl %>.

(* This is wrong *)
Definition mk_transport (A B UR t : term) := tApp <% univ_transport %> [A; B; tApp <% @FR_TypetoEquiv %> [A; B; UR]; t].

Definition mkForallUR (A A' eA B B' eB: term) := tApp <% FP_forall %> [A; A'; eA; B; B'; eB].


Fixpoint tsl_rec0 (n : nat) (o : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if Nat.leb n k then (* global variable *) tRel (3 * (k - n) + n + o)
                        else (* local  variable *) t
  | tEvar k ts      => tEvar k (List.map (tsl_rec0 n o) ts)
  | tCast t c a     => tCast (tsl_rec0 n o t) c (tsl_rec0 n o a)
  | tProd na A B    => tProd na (tsl_rec0 n o A) (tsl_rec0 (n+1) o B)
  | tLambda na A t  => tLambda na (tsl_rec0 n o A) (tsl_rec0 (n+1) o t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n o t) (tsl_rec0 n o A) (tsl_rec0 (n+1) o u)
  | tApp t lu       => tApp (tsl_rec0 n o t) (List.map (tsl_rec0 n o) lu)
  | tProj p t       => tProj p (tsl_rec0 n o t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Open Scope pair_scope.

Fixpoint tsl_rec (fuel : nat) (E : tsl_table) (Σ : global_env_ext) (Γ₁ : context) (Γ₂ : context) (t : term)
  : tsl_result TslRes :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
	match t with
  | tSort s => ret (mkRes t todo) (*(tApp <% UR_id %> [t])*)

  | tProd n A B =>
    rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
    let B' := tLambda n A B in
    rB <- tsl_rec fuel E Σ Γ₁ Γ₂ B' ;;

    (* this is undesirable, but for now we cannot do better *)
    ret {| trad := tProd n (trad rA) (tApp (lift 1 0 (trad rB)) [tRel 0])
              (* {A A'} {HA : UR A A'} {P : A -> Type} {Q : A' -> Type} (eB : forall x y (H:x ≈ y), P x ⋈ Q y) *)
        ;  w := mkForallUR A (trad rA) (w rA) B' (trad rB) (mkForallUR A (trad rA) (w rA) B' (trad rB) (w rB))
        |}
    
  | tInd ind u =>
      match lookup_table E (IndRef ind) with
      | Some tsl => ret tsl
      | None => ret (mkRes t todo)
      (* | None     => ret (mkRes t (tApp <% UR_id %> [t])) *)
      end

  | tConstruct i n univs =>
      match lookup_table E (ConstructRef i n) with
      | Some tsl => ret tsl
      | None =>
          match infer' Σ Γ₁ t with
          | Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp univ_transport [ typ; trad typ'; proj_equiv (w typ') ; t ])
                (tApp ur_refl' [ typ; trad typ'; w typ'; t ]))
          | TypeError e => Error (TypingError e)
          end
      end

  | tConst n univs =>
      match lookup_table E (ConstRef n) with
      | Some tsl => ret tsl
      | None =>
          match infer' Σ Γ₁ t with
          | Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp univ_transport [ typ; trad typ'; proj_equiv (w typ') ; t ])
                (tApp ur_refl' [ typ; trad typ'; w typ'; t ]))
          | TypeError e => Error (TypingError e)
          end
      end

  | tRel x => ret (mkRes t (tRel (x * 3)))

  | tLambda n A B =>
      rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
      rB <- tsl_rec fuel E Σ (vass n A :: Γ₁) (vass n (trad rA) :: Γ₂) B ;;
      ret {| trad := tLambda n (trad rA) (trad rB)
          ;  w := tLambda (suffix n "₁") A (
                    tLambda (suffix n "₂") (trad rA) (
                      tLambda (suffix n "ᵣ") (rel_of (w rA) (tRel 1) (tRel 0)) (
                        w rB
                      )
                    )
                  )
          |}
  
  | tApp f args =>
      rf    <- tsl_rec fuel E Σ Γ₁ Γ₂ f ;;
      args' <- monad_map (tsl_rec fuel E Σ Γ₁ Γ₂) args ;;
      
      ret (mkRes (tApp (trad rf) (List.map trad args'))
                 (tApp (w rf) (List.flat_map (fun (p : term × TslRes) =>
                              [tsl_rec0 0 2 (p .1); tsl_rec0 0 1 (trad (p .2)); w (p .2)]) (zip args args'))))

	| _ => ret (mkRes t todo)
  end
  end.

  
Open Scope string_scope.
Inductive ResultType := Term | Witness.

Definition convert {A} (ΣE : (global_env * tsl_table)%type) (t : ResultType) (x : A) :=
  p <- tmQuoteRec x ;;

  let term := p.2 in
  let env := empty_ext (app (fst ΣE) p.1) in
  let E := snd ΣE in

  result <- tmEval lazy (tsl_rec fuel E env [] [] term) ;;
  
  match result with
  | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
      
  | Success rt =>
      tmPrint "obtained translation: " ;;
      t <- tmEval all (match t with Term => trad rt | Witness => (w rt) end);;
      (* tmPrint t ;; *)
      tmUnquote t >>= tmPrint
  end.

Definition translate {A} (ΣE : (global_env * tsl_table)%type) (name : ident) (x : A) :=
  p <- tmQuoteRec x ;;

  let term := p.2 in 
  let env  := empty_ext (app (fst ΣE) p.1) in
  let E    := snd ΣE in

  result  <- tmEval lazy (tsl_rec fuel E env [] [] term) ;;

  match result with
  | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
    
  | Success res =>
      (* let t := (pair (trad res') (tLambda nAnon (trad res') (UR_apply (w res') (term) (trad res))) (trad res) (w res)) in
      tmUnquote t >>= tmDefinition name *)
      (* let t := (pair (tSort fresh_universe) (tLambda nAnon (tSort fresh_universe) (tProd nAnon (tRel 0) (tSort fresh_universe)))
                (trad res) (w res)) in
      tmUnquote t >>= tmDefinition name *)
      (* tmPrint (w res) ;; *)
      tmMkDefinition name (trad res) ;;
      tmMkDefinition (name ++ "_ur") (w res)
  end.