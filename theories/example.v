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
Instance UR_nat_N : Rel nat N := compat_nat_N.
Instance UR_Prop : Rel Prop Prop := compat_Prop_Prop.

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
Run TemplateProgram (convert tsl_nat_N Term (fun x : nat => x + 5)).
Run TemplateProgram (convert tsl_nat_N Term (fun x : nat => S (S x))).
Run TemplateProgram (convert tsl_nat_N Term (fun x : nat => 3)).
Run TemplateProgram (convert tsl_nat_N Term (forall x : nat, 0 <= x)).