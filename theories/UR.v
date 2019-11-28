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

Class IsWeakEquiv@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) :=
  { isWFun :> IsFun R
  ; isWFunSym :> IsFun (sym R)
  }.

Arguments isFun {_ _ _} _.
Arguments isWFun {_ _ _} _.
Arguments isWFunSym {_ _ _} _.

Definition funR@{i} {A B : Type@{i}} {R} : IsFun R -> A -> B := fun H x => (H.(isFun) x).1.1.

Definition center@{i} {A B : Type@{i}} {R : A -> B -> Type@{i}} (F : IsFun R) :
  forall x, R x (funR F x) := fun x => (F x).1.2.

Definition IsFunIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun R).
Proof.
  by apply: IsTrunc_Forall => [|?]; [apply: funext|apply: IsHPropIsContr].
Defined.

Definition IsFunSymIsHProp A B (R : A -> B -> Type) : IsHProp (IsFun (sym R)) :=
  IsFunIsHProp B A (sym R).

Instance IsWeakEquiv_sym A B (R : A -> B -> Type) :
  forall (f : IsWeakEquiv R), IsWeakEquiv (sym R).
Proof.
  by move=> Rwe; split; [apply: isWFunSym|apply isWFun].
Defined.

Definition IsWeakEquiv_IsEquiv {A B} {R : A -> B -> Type} :
  forall (f : IsWeakEquiv R), IsEquiv (funR (isWFun f)).
Proof.
  move=> [f g]; apply: (isequiv_adjointify _ (funR g)) => [x|y] /=.
    exact: (((g (funR f x)).2 (x;(center f) x))..1).
  exact: (((f (funR g y)).2 (y;(center g) y))..1).
Defined.

Definition WeakEquivToEquiv {A B} {R : A -> B -> Type} (f : IsWeakEquiv R) : Equiv A B.
  econstructor.
  eapply IsWeakEquiv_IsEquiv.
Defined.

Coercion WeakEquivToEquiv : IsWeakEquiv >-> Equiv.

Definition IsFunRf A B (f : A -> B) : IsFun (fun a b => f a = b).
Proof.
  move=> a; exists (f a;eq_refl) => - [b b_fa].
  by apply: path_sigma_uncurried; exists b_fa; apply: transport_paths_r.
Defined.

Arguments IsWeakEquiv_IsEquiv {_ _ _} _.

Definition IsFunRfsymIsWeakEquiv A B (f : A -> B) :
  IsFun (sym (fun a b => f a = b)) -> IsWeakEquiv (fun a b => f a = b).
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

Class Rel@{i} (A B : Type@{i}) := rel : A -> B -> Type@{i}.
Coercion rel : Rel >-> Funclass.

Hint Mode Rel ! ! : typeclass_instances.
Typeclasses Transparent Rel.

Arguments rel {_ _ _} _ _.

Notation "x ≈ y" := (rel x y) (at level 20).

Class FR_Type@{i} (A B : Type@{i}) :=
  { _Rel :> Rel A B
  ; _REquiv:> IsWeakEquiv rel
  }.

Coercion _Rel    : FR_Type >-> Rel.
Coercion _REquiv : FR_Type >-> IsWeakEquiv.

Infix "⋈" := FR_Type (at level 25).

Arguments _Rel {_ _} _.
Arguments _REquiv {_ _} _.
Typeclasses Transparent _Rel.


Definition FR_TypetoEquiv@{i} {A B : Type@{i}} (UR : A ⋈ B) : Equiv A B.
Proof.
  eapply WeakEquivToEquiv.
  eapply UR.
Defined.


(*! Universe !*)

Instance FR_Type_def@{i j} : Rel@{j} Type@{i} Type@{i} := FR_Type@{i}.

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.
Hint Extern 0 (_Rel _ _ _) => eassumption : typeclass_instances.

Definition FRForall@{i j k} {A A' : Type@{i}} 
                        {B : A -> Type@{j}} {B' : A' -> Type@{j}} 
                        (RA : Rel A A')
                        (RB: forall x y (H: RA x y), Rel (B x) (B' y)) :
  Rel@{k} (forall x, B x) (forall y, B' y)
  := fun f g => forall x y (H : RA x y), RB x y H (f x) (g y).

Definition IsFun_id@{i} (A : Type@{i}) : IsFun (fun a a' : A => a = a').
Proof.
  exact: IsFun_sym (fun _ _ => Equiv_id _) (IsFunRf _ _ id).
Defined.

Definition FR_Type_id@{i j} (A : Type@{i}): FR_Type_def@{i j} A A.
Proof.
  suff : IsWeakEquiv (fun a b : A => a = b) by apply: Build_FR_Type.
  split; first exact: IsFun_id.
  move=> a. exists (a;eq_refl : sym _ a a) => - [b b_a].
  by apply: path_sigma_uncurried; exists b_a^; case: b_a.
Defined.

Instance FP_Type@{i j} : FR_Type@{j} Type@{i} Type@{i}.
Proof.
  econstructor. unfold rel. unshelve econstructor.
  intro A. unshelve econstructor.
  exists A. apply FR_Type_id.
  intros [B e]. apply path_sigma_uncurried. unshelve eexists.
  cbn. apply univalence.
  unshelve econstructor.
  exact (funR (e.(_REquiv).(isWFun))). apply IsWeakEquiv_IsEquiv.
  cbn. cheat.
  intro A. unshelve econstructor.
  exists A. apply FR_Type_id.
  intros [B e]. apply path_sigma_uncurried. unshelve eexists.
  cbn. apply univalence.
  unshelve econstructor.
  exact (funR (e.(_REquiv).(isWFunSym))).
  unfold sym in e.
  apply (@IsWeakEquiv_IsEquiv _ _ _ (IsWeakEquiv_sym _ _ _ (_REquiv e))).
  cbn.
  cheat.
Defined.

Definition IsFun_forall (A A' : Type)
           (B : A -> Type) (B' : A' -> Type)
           (RA : Rel A A')
           (RB: forall x y (H: x ≈ y), Rel (B x) (B' y))
           (eAsym : IsFun (sym RA))
           (eB : forall a a' e, IsFun (RB a a' e)):
  IsFun (FRForall RA RB).
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
    + cbn. unfold FRForall.
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
Defined.

Hint Extern 1 (Rel (forall x:?A, _) (forall x:?A', _)) =>
  refine (@FRForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

Definition Forall_sym_sym
           {A A' : Type} {B : A -> Type} {B' : A' -> Type} (RA : Rel A A')
           (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) :
  forall f g, FRForall RA RB f g ≃ sym (FRForall (sym RA) (fun x y e => sym (RB y x e))) f g.
Proof.
  intros. unshelve econstructor; cbn. 
  compute; intros; auto. 
  unshelve econstructor.
  - compute; intros; auto. 
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.   

(* FRForall@{i j} {A A' : Type@{i}} 
                        {B : A -> Type@{j}} {B' : A' -> Type@{j}} 
                        (RA : Rel A A')
                        (RB: forall x y (H: x ≈ y), Rel (B x) (B' y)) : *)
Definition FP_forall@{i j k} (A A' : Type@{i}) (eA : A ⋈ A')
                           (B : A -> Type@{j}) (B' : A' -> Type@{j}) (RB: forall x y (H: eA x y), FR_Type@{j} (B x) (B' y)) :
  FR_Type@{k} (forall x : A, B x) (forall x : A', B' x).
Proof.
  unshelve econstructor.
  unshelve econstructor.
  apply IsFun_forall. typeclasses eauto.
  intros a a' e. typeclasses eauto.
  eapply IsFun_sym. eapply Forall_sym_sym.
  apply IsFun_forall. destruct eA. destruct _REquiv0. assumption.
  intros. destruct (RB a' a e). destruct _REquiv0. assumption.
Admitted.

(*
  unshelve econstructor.
  unshelve eapply FRForall.
  intros. eapply eB. typeclasses eauto.
  split.
  apply IsFun_forall.  typeclasses eauto.
  intros a a' e. eapply IsFun_sym. eapply Forall_sym_sym.
  apply IsFun_forall. destruct eA. destruct _REquiv0. assumption.
  intros. destruct (eB a' a e). destruct _REquiv0. assumption.
Defined. *)

Print FP_forall.

Module URList.

  Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

  Arguments nil {_}.
  Arguments cons {_} _ _.
  Arguments list_rec {_} _ _.
  Notation "[ ]" := nil (format "[ ]") : ur_list_scope.
  Notation "[ x ]" := (cons x nil)     : ur_list_scope.
  Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : ur_list_scope.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) : ur_list_scope.
  Infix "::" := cons (at level 60, right associativity) : ur_list_scope.

  Open Scope ur_list_scope.

  Inductive listR@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) : list A -> list B -> Type :=
  | listR_nil : listR R nil nil
  | listR_cons : forall {a b l l'},
      (R a b) -> (listR R l l') -> listR R (a::l) (b::l').

  Hint Extern 0 (Rel (list ?A) (list ?B)) => unshelve notypeclasses refine (@listR _ _ _): typeclass_instances.
  Hint Extern 0 (@listR ?R [] []) => exact (listR_nil R)  : typeclass_instances.
  Hint Extern 0 (@listR ?R (_::_) (_::_)) => unshelve refine (listR_cons R _ _) : typeclass_instances.

  Definition transport_listR_cons A B (RA : A -> B -> Type)
            (a :A) b b' (l: list A ) (lb lb':list B) (h:b=b') (e:lb=lb')
    (E: RA a b) (E': listR RA l lb):
    transport_eq
      (fun Y => listR RA (a::l) Y)
      (ap2 cons h e) (listR_cons _ E E')  =
    listR_cons RA (transport_eq (fun X => RA _ X) h E)
                  (transport_eq (fun X : list B => listR RA l X) e E').
    destruct h, e. reflexivity.
  Defined.

  Definition IsFun_list (A A' : Type) (RA : A -> A' -> Type)
            (FA : IsFun RA) : IsFun (listR RA).
  Proof.
    intro l. unshelve econstructor.
    - unshelve eexists.
      + exact (list_rec (fun _ => list A') []
                        (fun a _ l' => cons (funR FA a) l') l).
      + induction l.
        * exact (listR_nil _).
        * eapply listR_cons; try assumption. apply center.
    - intros [l' ell'].
      induction ell'; cbn.
      + reflexivity.
      + apply path_sigma_uncurried. unshelve eexists; cbn in *.
        * apply ap2. exact (((FA a).2 (b ;r))..1). exact (IHell'..1).
        * rewrite transport_listR_cons. apply ap2.
          exact (((FA a).2 (b ;r))..2).
          exact (IHell'..2).
  Defined.

  Definition listR_sym_sym A A' (R : A -> A' -> Type) :
    forall l l', listR R l l' ≃ sym (listR (sym R)) l l'.
  Proof.
    intros l l'. unshelve econstructor.
    induction 1; constructor; assumption.
    unshelve eapply isequiv_adjointify.
    - induction 1; constructor; assumption.
    - intro e; induction e; cbn. reflexivity.
      apply ap2; try reflexivity; assumption.
    - intro e; induction e; cbn. reflexivity.
      apply ap2; try reflexivity; assumption.
  Defined.

  Definition FP_list (A A' : Type) (eA : A ⋈ A'):
    FR_Type (list A) (list A').
  Proof.
    unshelve econstructor.
    exact (listR (_Rel eA)).
    split.
    apply IsFun_list; typeclasses eauto.
    eapply IsFun_sym. eapply listR_sym_sym.
    apply IsFun_list. destruct eA. destruct _REquiv0.
    exact isWFunSym0.
  Defined.

End URList.


(* 
Parameter A B : Type.
Parameter eAB : A ⋈ B.

Inductive ZA :=
  | posA : A -> ZA
  | negA : A -> ZA.
Check [ _ ].


Inductive ZB :=
  | posB : B -> ZB
  | negB : B -> ZB.

Inductive ZR (R : A -> B -> Type) : ZA -> ZB -> Type :=
  | posR : forall {x y}, R x y -> ZR R (posA x) (posB y)
  | negR : forall {x y}, R x y -> ZR R (negA x) (negB y).

Definition transport_ZR_posR A B (RA : A -> B -> Type)
  (a :A) b b' (h:b=b') (e: RA a b):
transport_eq
 (fun Y => ZR RA (posR a) Y) (ap posB h) (posR)  =
  posR RA (transport_eq (fun X => RA _ X) h _)
          (transport_eq (fun X : list B => ZR RA _ X) e _).
destruct h, e. reflexivity.
Defined.


Definition IsFun_Z (R : A -> B -> Type) (F : IsFun R) : IsFun (ZR R).
Proof.
  intro za. unshelve econstructor.
- unshelve eexists.
  + exact ((ZA_rec (fun _ => ZB) (fun a => posB (funR F a)) (fun a => negB (funR F a))) za).
  + induction za.
    * eapply posR, center.
    * eapply negR, center.
- intros [za' zr].
  induction zr; cbn.
  apply path_sigma_uncurried. unshelve eexists. cbn in *.
  eapply ap. exact (((F x).2 (y ;r))..1).

  shelve.
  apply path_sigma_uncurried. unshelve eexists. cbn in *.
  eapply ap. exact (((F x).2 (y ;r))..1).
  

  
  (* * exact (listR_nil _).
  * eapply listR_cons; try assumption. apply center.
- intros [l' ell'].
induction ell'; cbn.
+ reflexivity.
+ apply path_sigma_uncurried. unshelve eexists; cbn in *.
* apply ap2. exact (((FA a).2 (b ;r))..1). exact (IHell'..1).
* rewrite transport_listR_cons. apply ap2.
exact (((FA a).2 (b ;r))..2).
exact (IHell'..2). *)
Admitted.

Definition ZR_sym_sym (R : A -> B -> Type) :
forall za zb, ZR R za zb ≃ sym (ZR (sym R)) za zb.
Proof.
intros l l'. unshelve econstructor.
induction 1; constructor; assumption.
unshelve eapply isequiv_adjointify.
- induction 1; constructor; assumption.
- intro e; induction e; cbn. reflexivity.
apply ap2; try reflexivity; assumption.
- intro e; induction e; cbn. reflexivity.
apply ap2; try reflexivity; assumption.
Defined.

Definition FP_list (A A' : Type) (eA : A ⋈ A'):
list A ⋈ list A'.
Proof.
unshelve econstructor.
exact (listR (_Rel eA)).
split.
apply IsFun_list; typeclasses eauto.
eapply IsFun_sym. eapply listR_sym_sym.
apply IsFun_list. destruct eA. destruct _REquiv0.
exact isWFunSym0.
Defined. *)
