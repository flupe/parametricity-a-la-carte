From MetaCoq Require Import Template.All.
Require Import UR Translation TranslationUtils.
Require Import Nat BinNat String List Lists.List.
Import Lists.List.ListNotations.

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
Print compat_le.

Run TemplateProgram (
  define_translation "tsl_nat_N"%string
    [ subst_type compat_nat_N ]
    [ subst_term compat_add
    ; subst_term compat_succ
    ; subst_term compat_zero
    ; subst_term compat_mul
    ; subst_term compat_sub
    ; subst_term compat_le
    ]).