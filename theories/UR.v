Require Import HoTT HoTT_axioms.
From Coq Require Import ssreflect.

Open Scope list_scope.
Set Universe Polymorphism.
Set Printing Universes.

Class IsFun@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) :=
  isFun : (forall x, IsContr (sigT (fun y => R x y))).
Hint Mode IsFun - - ! : typeclass_instances.

Definition sym {A B} (R : A -> B -> Type) := fun b a => R a b.
Typeclasses Opaque sym.

Class IsBiFun@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) :=
  { isBFun :> IsFun R
  ; isBFunSym :> IsFun (sym R)
  }.

Arguments isFun {_ _ _} _.
Arguments isBFun {_ _ _} _.
Arguments isBFunSym {_ _ _} _.

Definition funR@{i} {A B : Type@{i}} {R} : IsFun R -> A -> B
  := fun H x => (H.(isFun) x).1.1.


Definition center@{i} {A B : Type@{i}} {R : A -> B -> Type@{i}} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.


Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
Proof.
  by apply: IsTrunc_Forall => [|?]; [apply: funext|apply: IsHPropIsContr].
Defined.

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Instance IsBiFun_sym A B (R : A -> B -> Type) :
  forall (f : IsBiFun R), IsBiFun (sym R).
Proof.
  by move=> Rwe; split; [apply: isBFunSym|apply isBFun].
Defined.

Definition IsBiFun_IsEquiv {A B} {R : A -> B -> Type} :
  forall (F : IsBiFun R), IsEquiv (funR (isBFun F)).
Proof.
  move=> [f g]; apply: (isequiv_adjointify _ (funR g)) => [x|y] /=.
    exact: (((g (funR f x)).2 (x;(center f) x))..1).
  exact: (((f (funR g y)).2 (y;(center g) y))..1).
Defined.
Arguments IsBiFun_IsEquiv {_ _ _} _.

Definition BiFunToEquiv {A B} {R : A -> B -> Type} (f : IsBiFun R) : Equiv A B.
  econstructor.
  eapply IsBiFun_IsEquiv.
Defined.
Coercion BiFunToEquiv : IsBiFun >-> Equiv.

Definition IsFunRf A B (f : A -> B) : IsFun (fun a b => f a = b).
Proof.
  move=> a; exists (f a;eq_refl) => - [b b_fa].
  apply: path_sigma_uncurried. exists b_fa. apply: transport_paths_r.
Defined.

Definition IsFunRfsymIsBiFun A B (f : A -> B) :
  IsFun (sym (fun a b => f a = b)) -> IsBiFun (fun a b => f a = b).
Proof.
  by move=> ?; split=> //; apply: IsFunRf.
Defined.

Definition IsFun_sym A A' (R R': A -> A' -> Type) :
  (forall a a', R a a' ≃ R' a a') -> IsFun R -> IsFun R'.
Proof.
  move=> ReR' FR x; set R'xFx := ReR' _ _ (center FR x).
  exists (funR FR x;R'xFx) => - [y R'xy].
  apply: path_sigma_uncurried; have Fxy := ((FR x).2 (y; e_inv' (ReR' _ _) R'xy)).
  exists (Fxy..1); have /= := (Fxy..2); move: (Fxy..1) => /= {Fxy} Fxy.
  by case: _ / Fxy R'xy => /= ??; apply: Move_equiv_equiv.
Defined.

Definition IsFun_id@{i} (A : Type@{i}) : IsFun (fun a a' : A => a = a') := IsFunRf A A id.

Class Rel@{i} (A B : Type@{i}) := rel : A -> B -> Type@{i}.
Coercion rel : Rel >-> Funclass.
Hint Mode Rel ! ! : typeclass_instances.
Typeclasses Transparent Rel.

Arguments rel {_ _ _} _ _.
Notation "x ≈ y" := (rel x y) (at level 20).

Class UR@{i} (A B : Type@{i}) :=
  { _Rel :> Rel A B
  ; _REquiv :> IsBiFun rel
  }.

Coercion _Rel    : UR >-> Rel.
Coercion _REquiv : UR >-> IsBiFun.
Arguments _Rel {_ _} _.
Arguments _REquiv {_ _} _.
Typeclasses Transparent _Rel.

Infix "⋈" := UR (at level 25).

Definition URToEquiv@{i} {A B : Type@{i}} (UR : A ⋈ B) : Equiv A B
  := BiFunToEquiv UR.



(*! Universe !*)

(* Relation for Type *)
Instance R_Type@{i j} : Rel@{j} Type@{i} Type@{i} := UR@{i}.

(* Relation for dependent product *)
Definition R_Forall@{i j k} {A A' : Type@{i}} 
                        {B : A -> Type@{j}} {B' : A' -> Type@{j}} 
                        (RA : Rel A A')
                        (RB: forall x y (H: RA x y), Rel (B x) (B' y)) :
  Rel@{k} (forall x, B x) (forall y, B' y)
  := fun f g => forall x y (H : RA x y), RB x y H (f x) (g y).


(* we have a canonical Univalent Relation between A and itself *)
Definition UR_id@{i} (A : Type@{i}) : A ⋈ A.
  suff : IsBiFun (fun a b : A => a = b) by apply: Build_UR.
  split; first exact: IsFun_id.
  move=> a. exists (a;eq_refl : sym _ a a) => - [b b_a].
  by apply: path_sigma_uncurried; exists b_a^; case: b_a.
Defined.

(* every type A is in relation with itself (in R_Type) *)
Definition R_Type_id@{i j} (A : Type@{i}): R_Type@{i j} A A := UR_id A.

Hint Extern 0 (?x ≈ ?y)    => eassumption : typeclass_instances.
Hint Extern 0 (_Rel _ _ _) => eassumption : typeclass_instances.

(* Univalent Relation between Typeᵢ and Typeᵢ *)
Instance UR_Type@{i j} : UR@{j} Type@{i} Type@{i}.
Proof.
  econstructor. unfold rel. unshelve econstructor.
  intro A. unshelve econstructor.
  exists A. apply R_Type_id.
  intros [B e]. apply path_sigma_uncurried. unshelve eexists.
  cbn. apply univalence.
  unshelve econstructor.
  exact (funR (e.(_REquiv).(isBFun))). apply IsBiFun_IsEquiv.
  cbn. cheat.
  intro A. unshelve econstructor.
  exists A. apply R_Type_id.
  intros [B e]. apply path_sigma_uncurried. unshelve eexists.
  cbn. apply univalence.
  unshelve econstructor.
  exact (funR (e.(_REquiv).(isBFunSym))).
  unfold sym in e.
  apply (@IsBiFun_IsEquiv _ _ _ (IsBiFun_sym _ _ _ (_REquiv e))).
  cbn.
  cheat.
Defined.


Definition IsFun_forall@{i j k} (A A' : Type@{i})
           (B : A -> Type@{j}) (B' : A' -> Type@{j})
           (RA : Rel@{i} A A')
           (RB: forall x y (H: RA x y), Rel@{j} (B x) (B' y))
           (eAsym : IsFun (sym RA))
           (eB : forall a a' e, IsFun (RB a a' e)):
  IsFun (R_Forall@{i j k} RA RB).
Proof.
  intro f.
  unshelve econstructor.
  - unshelve eexists.
    + intros x. apply ((eB ((funR eAsym) x) x (eAsym.(center) x)).(funR) (f (eAsym.(funR) x))).
    + intros a a' ea. cbn.
      pose (e := (eAsym a').2 (a ; ea)).
      apply (transport_eq (fun X => (RB a a' ea) (f a)
                                                  (((eB X .1 a' X .2) (f X .1)).1) .1) e^).
        exact ((eB a a' ea).(center) (f a)).
  - intros [g efg]. cbn in *. eapply path_sigma_uncurried.
    unshelve eexists. cbn. apply funext.
    + intros a'.
        exact ((((eB (funR eAsym a') a' (center eAsym a')) (f (funR eAsym a'))).2 (g a'; efg _ a' _))..1).
    + cbn. unfold R_Forall.
      rewrite transport_forall_cst.
      apply funext; intro a; apply funext; intro a'; apply funext ; intro e. unfold rel in eB.
      rewrite (transport_funext_aux (fun y0 y  =>
                                       forall (e0 : RA a y0), (RB a y0 e0) (f a) y)).
        rewrite transport_forall_cst.
        set (T := (RB a a' e) (f a)).
        rewrite <- (transport_ap T ((fun X : {y : A & sym RA a' y} =>
                                       (((eB X .1 a' X .2)(f X .1)) .1) .1))).
        rewrite <- transport_pp.
        unfold center, funR, isFun.
        set (isContrT := (eB a a' e) (f a)).
        destruct ((eAsym a') .2 (a; e))^. cbn.
        change (transport_eq T (isContrT .2 (g a'; efg a a' e) ..1)
                             (isContrT .1) .2 = efg a a' e).
        apply transport_pr1_path.
Admitted.

Hint Extern 1 (Rel (forall x:?A, _) (forall x:?A', _)) =>
  refine (@R_Forall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

Definition Forall_sym_sym
           {A A' : Type} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
           (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) :
  forall f g, R_Forall RA RB f g ≃ sym (R_Forall (sym RA) (fun x y e => sym (RB y x e))) f g.
Proof.
  intros. unshelve econstructor; cbn. 
  compute; intros; auto. 
  unshelve econstructor.
  - compute; intros; auto. 
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.   

Instance UR_Prop : Prop ⋈ Prop. Admitted.
Instance R_Prop : Rel Prop Prop := UR_Prop.

(* Univalent Relation for dependent product *)
Definition UR_Forall@{i j k l} (A A' : Type@{i}) (eA : A ⋈ A')
                           (B : A -> Type@{j}) (B' : A' -> Type@{j}) (RB: forall x y (H: eA x y), R_Type@{k l} (B x) (B' y)) :
  UR@{l} (forall x : A, B x) (forall x : A', B' x).
Proof.
  unshelve econstructor.
  unshelve eapply R_Forall.
  intros. eapply RB. apply H.
  unshelve econstructor.
  apply IsFun_forall. typeclasses eauto.
  intros a a' e. typeclasses eauto.
  eapply IsFun_sym@{l l l l}. eapply Forall_sym_sym.
  apply IsFun_forall. destruct eA. destruct _REquiv0. assumption.
  intros. destruct (RB a' a e). destruct _REquiv0. assumption.
Defined.

Definition UR_Forall_Prop@{i k} (A A' : Type@{i}) (eA : A ⋈ A')
                           (B : A -> Prop) (B' : A' -> Prop) (RB: forall x y (H: eA x y), R_Prop@{k} (B x) (B' y)) :
  R_Prop (forall x : A, B x) (forall x : A', B' x).
Proof.
Admitted.