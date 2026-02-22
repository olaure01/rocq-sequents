(** Commutative Residuated Lattices = IMALL **)
(** Girard's presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import Lia Wf_nat CMorphisms.
From OLlibs Require Import List_more PermutationT_more.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Formulas *)

Definition Atom := nat : Type.

Implicit Type X : Atom.

Inductive formula :=
| var (_ : Atom) | wedge (_ _ : formula) | top | vee (_ _ : formula) | bot
| tens (_ _ : formula) | one | imp (_ _ : formula).
Infix "∧" := wedge (at level 35).
Notation "⊤" := top.
Infix "∨" := vee (at level 35).
Notation "⊥" := bot.
Infix "⊗" := tens (at level 33).
Notation "1" := one.
Infix "⊸" := imp (at level 36).

Coercion var : Atom >-> formula.

Fixpoint fsize A := S
match A with
| var _ | ⊤ | ⊥ | 1 => 0
| B ∧ C | B ∨ C | B ⊗ C | B ⊸ C => fsize B + fsize C
end.


(** * Proofs *)

Reserved Notation "l ⊢ A" (at level 65).
Inductive imall : list formula -> formula -> Type :=
| ax X : [var X] ⊢ X
| ex l1 l2 C : PermutationT l1 l2 -> l1 ⊢ C -> l2 ⊢ C
| wr l A B : l ⊢ A -> l ⊢ B -> l ⊢ A ∧ B
| wl1 l1 B l2 A C : l1 ++ A :: l2 ⊢ C -> l1 ++ A ∧ B :: l2 ⊢ C
| wl2 l1 B l2 A C : l1 ++ A :: l2 ⊢ C -> l1 ++ B ∧ A :: l2 ⊢ C
| tr l : l ⊢ ⊤
| vr1 B l A : l ⊢ A -> l ⊢ A ∨ B
| vr2 B l A : l ⊢ A -> l ⊢ B ∨ A
| vl l1 l2 A B C : l1 ++ A :: l2 ⊢ C -> l1 ++ B :: l2 ⊢ C -> l1 ++ A ∨ B :: l2 ⊢ C
| bl l1 l2 C : l1 ++ ⊥ :: l2 ⊢ C
| pr l1 l2 A B : l1 ⊢ A -> l2 ⊢ B -> l1 ++ l2 ⊢ A ⊗ B
| pl l1 l2 A B C : l1 ++ A :: B :: l2 ⊢ C -> l1 ++ A ⊗ B :: l2 ⊢ C
| ur : [] ⊢ 1
| ul l1 l2 C : l1 ++ l2 ⊢ C -> l1 ++ 1 :: l2 ⊢ C
| ir l A B : A :: l ⊢ B -> l ⊢ A ⊸ B
| il l2 l1 l3 A B C : l1 ⊢ A -> l2 ++ B :: l3 ⊢ C -> l2 ++ l1 ++ A ⊸ B :: l3 ⊢ C
where "l ⊢ A" := (imall l A).
Arguments ax {_}, _.
Arguments ex [_ _ _ _] _, [_ _ _] _ _.
Arguments wl1 [_ _ _ _ _] _, _ [_ _ _] _, _ _ [_ _] _.
Arguments wl2 [_ _ _ _ _] _, _ [_ _ _] _, _ _ [_ _] _.
Arguments tr {_}, _.
Arguments vr1 [_ _ _] _, _ [_ _] _.
Arguments vr2 [_ _ _] _, _ [_ _] _.
Arguments vl [_ _ _ _ _] _ _,  _ [_ _ _ _] _ _.
Arguments bl {_ _ _}, _ {_ _}.
Arguments pr [_ _ _ _] _ _, _ [_ _ _] _ _.
Arguments pl [_ _ _ _ _] _, _ [_ _ _] _.
Arguments ul [_ _ _] _, _ [_ _] _.
Arguments ir [_ _ _] _.
Arguments il [_ _ _ _ _ _] _ _, _ [_ _ _ _ _] _ _.

Instance imall_PermutationT : Proper (@PermutationT _ ==> eq ==> iffT) imall.
Proof. intros l1 l2 HP B A ->. split; intro pi; [ | symmetry in HP ]; apply (ex HP pi). Qed.


(** * Axiom expansion *)

Lemma ax_gen A : [A] ⊢ A.
Proof.
induction A; try now rewrite <- (app_nil_l _); repeat constructor.
- apply (@pl []).
  apply (@pr [_]); assumption.
- constructor. apply (@il [] [_]); assumption.
Qed.


(** * Cut *)

Fixpoint pweight l A (pi : l ⊢ A) := S
match pi with
| ax | tr | bl | ur => 0
| wr pi1 pi2 | vl pi1 pi2 => max (pweight pi1) (pweight pi2)
| ex pi1 | wl1 pi1 | wl2 pi1 | vr1 pi1 | vr2 pi1 | pl pi1 | ul pi1 | ir pi1 => pweight pi1
| pr pi1 pi2 | il pi1 pi2  => (pweight pi1) + (pweight pi2)
end.

Lemma cut A l1 l l2 B : l ⊢ A -> l1 ++ A :: l2 ⊢ B -> l1 ++ l ++ l2 ⊢ B.
Proof.
remember (fsize A) as d eqn:Hd.
induction d as [d IHd] in A, B, l, l1 , l2, Hd |- * using (well_founded_induction_type lt_wf). subst d.
assert (forall l1' l' l2' A' B', l' ⊢ A' -> l1' ++ A' :: l2' ⊢ B' -> fsize A' < fsize A -> l1' ++ l' ++ l2' ⊢ B')
  as IHf; [ | clear IHd ].
{ intros l1' l' l2' A' B' pi1' pi2' Hs. exact (IHd _ Hs A' _ _ _ _ eq_refl pi1' pi2'). }
intros pi1 pi2.
remember (pweight pi1 + pweight pi2) as n eqn:Hn.
induction n as [n IHn] in A, B, l, l1, l2, pi1, pi2, IHf, Hn |- * using (well_founded_induction_type lt_wf).
subst n.
assert (forall l' l1' l2' B' (pi1' : l' ⊢ A) (pi2' : l1' ++ A :: l2' ⊢ B'),
        pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> l1' ++ l' ++ l2' ⊢ B') as IH; [ | clear IHn ].
{ intros l' l1' l2' B' pi1' pi2' Hn. exact (IHn _ Hn _ _ _ _ _ IHf pi1' pi2' eq_refl). }
remember (l1 ++ A :: l2) as l0 eqn:Hl0.
destruct pi2 as [ | ? ? ? HP2 pi2 | ? ? ? pi2_1 pi2_2 | ? B' ? A' ? pi2 | ? A' ? B' ? pi2 |
                | ? ? ? pi2 | ? ? ? pi2 | ? ? A' B' ? pi2_1 pi2_2 |
                | ? ? A' B' pi2_1 pi2_2 | ? ? A' B' ? pi2 | |
                | ? A' B' pi2 | ? ? ? A' B' ? pi2_1 pi2_2 ];
  try subst l0; cbn in IH.
- decomp_list_eq Hl0. list_simpl. assumption.
- subst.
  (* PAUSE *)
  apply PermutationT_vs_elt_inv_perm in HP2 as [(l1', l2') HP2 ->].
  refine (ex _ (IH _ _ _ _ pi1 pi2 ltac:(lia))).
  apply PermutationT_app_middle. assumption.
- apply wr.
  + apply (IH _ _ _ _ pi1 pi2_1). cbn. lia.
  + apply (IH _ _ _ _ pi1 pi2_2). cbn. lia.
- decomp_list_eq Hl0; subst.
  + list_apply wl1.
    revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
  + remember (A' ∧ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ pi1 (wl1 pi2)). cbn. lia.
    * apply (IHf _ _ _ _ _ pi1_1 pi2). cbn. lia.
    * list_apply (@wl1 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl1 pi2)). cbn. lia.
    * list_apply (@wl2 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl1 pi2)). cbn. lia.
    * list_apply (@vl (l1 ++ l0)).
      -- list_apply (IH _ _ _ _ pi1_1 (wl1 pi2)). cbn. lia.
      -- list_apply (IH _ _ _ _ pi1_2 (wl1 pi2)). cbn. lia.
    * list_apply (@bl (l1 ++ l0)).
    * list_apply (@pl (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl1 pi2)). cbn. lia.
    * list_apply (@ul (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl1 pi2)). cbn. lia.
    * list_apply (@il (l1 ++ l0)); [ assumption | ].
      list_apply (IH _ _ _ _ pi1_2 (wl1 pi2)). cbn. lia.
  + list_apply (@wl1 (l1 ++ l ++ l4)).
    revert pi2 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
- decomp_list_eq Hl0; subst.
  + list_apply wl2.
    revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
  + remember (A' ∧ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ pi1 (wl2 pi2)). cbn. lia.
    * apply (IHf _ _ _ _ _ pi1_2 pi2). cbn. lia.
    * list_apply (@wl1 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl2 pi2)). cbn. lia.
    * list_apply (@wl2 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl2 pi2)). cbn. lia.
    * list_apply (@vl (l1 ++ l0)).
      -- list_apply (IH _ _ _ _ pi1_1 (wl2 pi2)). cbn. lia.
      -- list_apply (IH _ _ _ _ pi1_2 (wl2 pi2)). cbn. lia.
    * list_apply (@bl (l1 ++ l0)).
    * list_apply (@pl (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl2 pi2)). cbn. lia.
    * list_apply (@ul (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (wl2 pi2)). cbn. lia.
    * list_apply (@il (l1 ++ l0)); [ assumption | ].
      list_apply (IH _ _ _ _ pi1_2 (wl2 pi2)). cbn. lia.
  + list_apply (@wl2 (l1 ++ l ++ l4)).
    revert pi2 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
- apply tr.
- apply vr1. apply (IH _ _ _ _ pi1 pi2). cbn. lia.
- apply vr2. apply (IH _ _ _ _ pi1 pi2). cbn. lia.
- decomp_list_eq Hl0; subst.
  + list_apply vl.
    * revert pi2_1 IH. rewrite app_comm_cons, app_assoc. intros pi2_1 IH.
      list_apply (IH _ _ _ _ pi1 pi2_1). lia.
    * revert pi2_2 IH. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      list_apply (IH _ _ _ _ pi1 pi2_2). lia.
  + remember (A' ∨ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ pi1 (vl pi2_1 pi2_2)). cbn. lia.
    * list_apply (@wl1 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (vl pi2_1 pi2_2)). cbn. lia.
    * list_apply (@wl2 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (vl pi2_1 pi2_2)). cbn. lia.
    * apply (IHf _ _ _ _ _ pi1 pi2_1). cbn. lia.
    * apply (IHf _ _ _ _ _ pi1 pi2_2). cbn. lia.
    * list_apply (@vl (l1 ++ l0)).
      -- list_apply (IH _ _ _ _ pi1_1 (vl pi2_1 pi2_2)). cbn. lia.
      -- list_apply (IH _ _ _ _ pi1_2 (vl pi2_1 pi2_2)). cbn. lia.
    * list_apply (@bl (l1 ++ l0)).
    * list_apply (@pl (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (vl pi2_1 pi2_2)). cbn. lia.
    * list_apply (@ul (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (vl pi2_1 pi2_2)). cbn. lia.
    * list_apply (@il (l1 ++ l0)); [ assumption | ].
      list_apply (IH _ _ _ _ pi1_2 (vl pi2_1 pi2_2)). cbn. lia.
  + list_apply (@vl (l1 ++ l ++ l4)).
    * revert pi2_1 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2_1 IH.
      list_apply (IH _ _ _ _ pi1 pi2_1). lia.
    * revert pi2_2 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2_2 IH.
      list_apply (IH _ _ _ _ pi1 pi2_2). lia.
- decomp_list_eq Hl0; subst.
  + list_apply bl.
  + remember ⊥ as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ pi1 bl). cbn. lia.
    * list_apply (@wl1 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 bl). cbn. lia.
    * list_apply (@wl2 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 bl). cbn. lia.
    * list_apply (@vl (l1 ++ l0)).
      -- list_apply (IH _ _ _ _ pi1_1 bl). cbn. lia.
      -- list_apply (IH _ _ _ _ pi1_2 bl). cbn. lia.
    * list_apply (@bl (l1 ++ l0)).
    * list_apply (@pl (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 bl). cbn. lia.
    * list_apply (@ul (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 bl). cbn. lia.
    * list_apply (@il (l1 ++ l0)); [ assumption | ].
      list_apply (IH _ _ _ _ pi1_2 bl). cbn. lia.
  + list_apply (bl (l1 ++ l ++ l4)).
- decomp_list_eq Hl0; subst.
  + list_apply (@pr (l1 ++ l ++ l4)); [ | assumption ].
    apply (IH _ _ _ _ pi1 pi2_1). lia.
  + list_apply (@pr l0); [ assumption | ].
    apply (IH _ _ _ _ pi1 pi2_2). lia.
- decomp_list_eq Hl0; subst.
  + list_apply pl.
    revert pi2 IH. rewrite 2 app_comm_cons, app_assoc. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
  + remember (A' ⊗ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ pi1 (pl pi2)). cbn. lia.
    * list_apply (@wl1 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (pl pi2)). cbn. lia.
    * list_apply (@wl2 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (pl pi2)). cbn. lia.
    * list_apply (@vl (l1 ++ l0)).
      -- list_apply (IH _ _ _ _ pi1_1 (pl pi2)). cbn. lia.
      -- list_apply (IH _ _ _ _ pi1_2 (pl pi2)). cbn. lia.
    * list_apply (@bl (l1 ++ l0)).
    * list_apply (IHf (l1 ++ l0) _ _ _ _ pi1_2); [ | cbn; lia ].
      list_apply (IHf _ _ _ _ _ pi1_1 pi2). cbn. lia.
    * list_apply (@pl (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (pl pi2)). cbn. lia.
    * list_apply (@ul (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (pl pi2)). cbn. lia.
    * list_apply (@il (l1 ++ l0)); [ assumption | ].
      list_apply (IH _ _ _ _ pi1_2 (pl pi2)). cbn. lia.
  + list_apply (@pl (l1 ++ l ++ l4)).
    revert pi2 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
- decomp_list_eq Hl0.
- decomp_list_eq Hl0; subst.
  + list_apply ul.
    revert pi2 IH. rewrite app_assoc. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
  + remember 1 as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ pi1 (ul pi2)). cbn. lia.
    * list_apply (@wl1 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (ul pi2)). cbn. lia.
    * list_apply (@wl2 (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (ul pi2)). cbn. lia.
    * list_apply (@vl (l1 ++ l0)).
      -- list_apply (IH _ _ _ _ pi1_1 (ul pi2)). cbn. lia.
      -- list_apply (IH _ _ _ _ pi1_2 (ul pi2)). cbn. lia.
    * list_apply (@bl (l1 ++ l0)).
    * list_apply (@pl (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (ul pi2)). cbn. lia.
    * assumption.
    * list_apply (@ul (l1 ++ l0)). list_apply (IH _ _ _ _ pi1 (ul pi2)). cbn. lia.
    * list_apply (@il (l1 ++ l0)); [ assumption | ].
      list_apply (IH _ _ _ _ pi1_2 (ul pi2)). cbn. lia.
  + list_apply (@ul (l1 ++ l ++ l4)).
    revert pi2 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2 IH.
    list_apply (IH _ _ _ _ pi1 pi2). lia.
- apply ir.
  revert pi2 IH. rewrite app_comm_cons. intros pi2 IH.
  list_apply (IH _ _ _ _ pi1 pi2). lia.
- decomp_list_eq Hl0; [ | | decomp_list_eq Hl0 ]; subst.
  + list_apply (@il (l1 ++ l ++ l5)); [ assumption | ].
    revert pi2_2 IH. rewrite <- app_assoc, <- app_comm_cons. intros pi2_2 IH.
    list_apply (IH _ _ _ _ pi1 pi2_2). lia.
  + list_apply (@il l0 (l5 ++ l ++ l6)); [ | assumption ].
    apply (IH _ _ _ _ pi1 pi2_1). lia.
  + list_apply il; [ assumption | ].
    revert pi2_2 IH. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
    list_apply (IH _ _ _ _ pi1 pi2_2). lia.
  + remember (A' ⊸ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 |
                    | | | | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      list_simpl. rewrite app_assoc. unshelve refine (IH _ _ _ _ pi1 _ _).
      -- list_apply (il pi2_1 pi2_2).
      -- list_simpl. lia.
    * list_apply (@wl1 (l0 ++ l3 ++ l1)).
      list_simpl. rewrite app_comm_cons, (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1 _ _).
      -- list_apply (il pi2_1 pi2_2).
      -- list_simpl. lia.
    * list_apply (@wl2 (l0 ++ l3 ++ l1)).
      list_simpl. rewrite app_comm_cons, (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1 _ _).
      -- list_apply (il pi2_1 pi2_2).
      -- list_simpl. lia.
    * list_apply (@vl (l0 ++ l3 ++ l1)).
      -- list_simpl. rewrite app_comm_cons, (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1_1 _ _).
         ++ list_apply (il pi2_1 pi2_2).
         ++ list_simpl. lia.
      -- list_simpl. rewrite app_comm_cons, (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1_2 _ _).
         ++ list_apply (il pi2_1 pi2_2).
         ++ list_simpl. lia.
    * list_apply (@bl (l0 ++ l3 ++ l1)).
    * list_apply (@pl (l0 ++ l3 ++ l1)).
      list_simpl. rewrite 2 app_comm_cons, (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1 _ _).
      -- list_apply (il pi2_1 pi2_2).
      -- list_simpl. lia.
    * list_apply (@ul (l0 ++ l3 ++ l1)).
      list_simpl. rewrite (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1 _ _).
      -- list_apply (il pi2_1 pi2_2).
      -- list_simpl. lia.
    * list_apply (IHf _ _ _ _ _ pi2_1); [ | cbn; lia ].
      list_apply (IHf _ _ _ _ _ pi1 pi2_2). cbn. lia.
    * list_apply (@il (l0 ++ l3 ++ l1)); [ assumption | ].
      list_simpl. rewrite app_comm_cons, (app_assoc l1), app_assoc. unshelve refine (IH _ _ _ _ pi1_2 _ _).
      -- list_apply (il pi2_1 pi2_2).
      -- list_simpl. lia.
Qed.
