Require Import MetaCoq.Template.All.
From MetaCoq.Translations Require Import translation_utils.
Import Template.Universes.Level.
Import String MonadNotation List Lists.List.
Import Init.Datatypes Lists.List.ListNotations.
Require Import UR.

Set Universe Polymorphism.
Open Scope string_scope.


(* TODO: only use global references *)
Record TslRes := mkRes
  { trad : term (* the translated term *)
  ; w  : term   (* witness of relation between the source and translated terms *)
                (* if t : Type, then w : t ⋈ t'
                   otherwise, with t : A,  w : t ≈ t' : A ⋈ A'*)
  }.

Definition tsl_table := list (Datatypes.prod global_reference TslRes).
Definition tsl_context := (tsl_table * global_env_ext)%type.

Fixpoint lookup_table (E : tsl_table) (gr : global_reference) : option TslRes :=
	match E with
	| hd :: tl =>
		if gref_eq_dec gr (fst hd) then Some (snd hd)
		else lookup_table tl gr
	| [] => None
	end.

Definition suffix (n : name) s : name :=
  match n with
  | nAnon     => nAnon
  | nNamed id => nNamed (id ++ s)
  end.

Definition with_default {A} (d : A) (x : option A) : A :=
  match x with
  | Some x => x
  | None => d
  end.


Definition fmap {M} `{Monad M} {A B} (f : A -> B) (m : M A) : M B :=
  m >>= fun x => ret (f x).

Definition set_univs (t : term) (levels : list Level.t) :=
  match t with
  | tConst c u => tConst c levels
  | tInd i u => tInd i levels
  | _ => t
  end.

Fixpoint is_closed (n : nat) (t : term): bool :=
  match t with
  | tRel k => negb (Nat.leb n k)
  | tConst _ _ => true
  | tConstruct _ _ _ => true
  | tApp f args => is_closed n f && forallb (is_closed n) args
  | _ => false
  end.

Definition liftA2 {M} `{Monad M} {A B C} (f : A -> B -> C) (ma : M A) (mb : M B) : M C :=
  a <- ma ;;
  b <- mb ;;
  ret (f a b).

Infix "$>"  := fmap (at level 10, left associativity).
Infix "<*>" := (liftA2 id) (at level 10, left associativity).

Fixpoint sequence {M} {A : Type}  `{Monad M} (t : Datatypes.list (M A)) : M (Datatypes.list A) :=
  match t with
  | List.nil => ret List.nil
  | List.cons x t => List.cons $> x <*> (sequence t)
  end.

Instance list_monad : Monad List.list :=
  {| ret A a := List.cons a List.nil
  ;  bind A B m f := List.flat_map f m
  |}.

Fixpoint zip {A B : Type} (ta : List.list A) (tb : List.list B) : Datatypes.list (A × B) :=
  match ta, tb with
  | List.cons a ta, List.cons b tb => List.cons (a, b) (zip ta tb)
  | _, _ => List.nil
  end.

(* Utilities to provide correct by construction translation rules *)
Arguments existT {_ _} _ _.
Definition type_subst@{i} := { A : Type@{i} & { B : Type@{i} & A ⋈ B }}.
Definition term_subst@{i} := { A : Type@{i} & { B : Type@{i} & { w : Rel A B & { a : A & {b : B & a ≈ b }}}}}.

Definition subst_type@{i} {A B : Type@{i}} (ur : A ⋈ B) : type_subst := existT A (existT B ur).
Definition subst_term@{i} {A B : Type@{i}} {w : Rel A B} {a : A} {b : B} (e : @rel A B w a b) : term_subst :=
  existT A (existT B (existT w (existT a (existT b e)))).

Definition to_global_ref (t : term) : option global_reference :=
  match t with
  | tInd ind _ => ret (IndRef ind)
  | tConstruct ind i _ => ret (ConstructRef ind i)
  | tConst n _ => ret (ConstRef n)
  | _ => None
  end.

Close Scope string_scope.

Fixpoint extract_type_rules (t : list type_subst) : TemplateMonad tsl_table :=
  match t with
  | nil => ret List.nil
  | cons (existT A (existT B ur)) t =>
      A  <- tmQuote A ;;
      B  <- tmQuote B ;;
      ur <- tmQuote ur ;;
      rest <- extract_type_rules t ;;
      tmEval lazy (with_default rest (option_map (fun gr => List.cons (gr, mkRes B ur) rest) (to_global_ref A)))
  end.

Open Scope pair_scope.

Fixpoint extract_term_rules (t : list term_subst) : TemplateMonad tsl_table :=
  match t with
  | nil => ret List.nil
  | cons (existT _ (existT _ (existT _ (existT a (existT b e))))) t =>
      a    <- tmQuote a ;;
      b    <- tmQuote b ;;
      e    <- tmQuote e ;;
      rest <- extract_term_rules t ;;
      tmEval lazy (with_default rest (option_map (fun gr => List.cons (gr, mkRes b e) rest) (to_global_ref a)))
  end.

Definition define_translation (n : ident)
                              (type_rules : list type_subst)
                              (term_rules : list term_subst) :=
  one <- extract_type_rules type_rules ;;
  two <- extract_term_rules term_rules ;;
  t <- tmQuoteRec term_rules ;;
  t' <- tmQuoteRec type_rules ;;
  tmDefinition n ((List.nil : global_env), one ++ two).

Set Printing Universes.
Check define_translation.