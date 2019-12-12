From MetaCoq Require Import Template.All.
From MetaCoq.Translations Require Import translation_utils.
Require Import UR Translation TranslationUtils ParamTest.
Require Import List Lists.List.
Require Import Nat BinNat String.
Import Lists.List.ListNotations.

Open Scope string_scope.

Instance compat_nat_N : nat ⋈ N. Admitted.
Instance compat_Prop_Prop : Prop ⋈ Prop. Admitted.

Definition compat_zero : 0 ≈ 0%N. Admitted.
Definition compat_add : add ≈ N.add. Admitted.
Definition compat_sub : sub ≈ N.sub. Admitted.
Definition compat_mul : mult ≈ N.mul. Admitted.
Definition compat_le : Peano.le ≈ N.le. Admitted.
Definition compat_succ : S ≈ N.succ. Admitted.

Set Printing Universes.
Unset Strict Unquote Universe Mode.

Definition qnat := {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}.
Definition qle :=  {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |}.

Definition tsl_nat_N : tsl_context := (
  [ (IndRef qnat, mkRes <% N %> <% compat_nat_N %>)
  ; (ConstRef "Coq.Init.Nat.add", mkRes <% N.add %> <% compat_add %>)
  ; (ConstRef "Coq.Init.Nat.sub", mkRes <% N.sub %> <% compat_sub %>)
  ; (ConstructRef qnat 0, mkRes <% 0%N %> <% compat_zero %>)
  ; (ConstructRef qnat 1, mkRes <% N.succ %> <% compat_succ %>)
  ; (IndRef qle, mkRes <% N.le %> <% compat_le %>)
  ]
  , empty_ext []
  ).

Infix "<=" := Peano.le.
Close Scope type_scope.

Test Quote (forall (x : nat), (nat -> nat)%type).
Run TemplateProgram (convert (fst tsl_nat_N) Witness (nat -> nat)%type).
Run TemplateProgram (convert (fst tsl_nat_N) Witness (nat -> nat -> nat)%type).
Run TemplateProgram (convert (fst tsl_nat_N) Witness (forall (x: nat), (nat -> nat)%type)).

Definition t := UR_Forall nat N compat_nat_N (fun _ : nat => (nat -> nat)%type)
(fun _ : N => forall H : N, (fun _ : N => N) H)
(fun (x₁ : nat) (x₂ : N) (_ : compat_nat_N x₁ x₂) =>
 UR_Forall nat N compat_nat_N (fun _ : nat => nat)
   (fun _ : N => N)
   (fun (H : nat) (H0 : N) (_ : compat_nat_N H H0) =>
    compat_nat_N)).

Check t.