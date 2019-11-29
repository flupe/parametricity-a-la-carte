From MetaCoq Require Import Template.All .
From MetaCoq.Translations Require Import translation_utils.
Require Import UR Translation TranslationUtils.
Require Import List Lists.List.
Require Import Nat BinNat String.
Import Lists.List.ListNotations.

Set Universe Polymorphism.

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

Definition tsl_nat_N : global_env * tsl_table := (
  [],
  [ (IndRef qnat, mkRes <% N %> <% compat_nat_N %>)
  ; (ConstRef "Coq.Init.Nat.add", mkRes <% N.add %> <% compat_add %>)
  ; (ConstRef "Coq.Init.Nat.sub", mkRes <% N.sub %> <% compat_sub %>)
  ; (ConstRef "Coq.Init.Nat.sub", mkRes <% N.sub %> <% compat_sub %>)
  ; (ConstructRef qnat 0, mkRes <% 0%N %> <% compat_zero %>)
  ; (ConstructRef qnat 1, mkRes <% N.succ %> <% compat_succ %>)
  ; (IndRef qle, mkRes <% N.le %> <% compat_le %>)
  ]
).

Infix "<=" := Peano.le.
Close Scope type_scope.

Run TemplateProgram (convert tsl_nat_N Witness (10)).
Run TemplateProgram (convert tsl_nat_N Witness (fun x : nat => x + 5)).
Run TemplateProgram (convert tsl_nat_N Witness (fun x : nat => S (S x))).
Run TemplateProgram (convert tsl_nat_N Witness (fun x : nat => 3)).
Run TemplateProgram (convert tsl_nat_N Witness (nat -> nat)%type).

Unset Strict Universe Declaration.

Definition s := FP_forall_Prop nat N compat_nat_N (fun x : nat => Peano.le 0 x) (fun x : N => N.le 0%N x)
                            (fun (x1 : nat) (x2 : N) (xr : x1 ≈ x2) => compat_le 0 0%N compat_zero x1 x2 xr).

Run TemplateProgram (convert tsl_nat_N  Witness (forall x : nat, 0 <= x)).