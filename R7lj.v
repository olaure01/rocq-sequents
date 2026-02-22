(** Heyting Algebras = LJ **)
(** multiplicative presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import PeanoNat Lia Wf_nat CMorphisms.
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
| var (_ : Atom) | wedge (_ _ : formula) | top | vee (_ _ : formula) | bot | imp (_ _ : formula).
Infix "∧" := wedge (at level 35).
Notation "⊤" := top.
Infix "∨" := vee (at level 35).
Notation "⊥" := bot.
Infix "→" := imp (at level 36).

Coercion var : Atom >-> formula.

Fixpoint fsize A := S
match A with
| var _ | ⊤ | ⊥ => 0
| B ∧ C | B ∨ C | B → C => fsize B + fsize C
end.


(** * Proofs *)

Reserved Notation "l ⊢ A" (at level 65).
Inductive lj : list formula -> formula -> Type :=
| ax X : [var X] ⊢ X
| ex l1 l2 C : PermutationT l1 l2 -> l1 ⊢ C -> l2 ⊢ C
| co l1 A l2 C : l1 ++ A :: A :: l2 ⊢ C -> l1 ++ A :: l2 ⊢ C
| wk l1 A l2 C : l1 ++ l2 ⊢ C -> l1 ++ A :: l2 ⊢ C
| wr l A B : l ⊢ A -> l ⊢ B -> l ⊢ A ∧ B
| wl1 l1 B l2 A C : l1 ++ A :: l2 ⊢ C -> l1 ++ A ∧ B :: l2 ⊢ C
| wl2 l1 B l2 A C : l1 ++ A :: l2 ⊢ C -> l1 ++ B ∧ A :: l2 ⊢ C
| tr l : l ⊢ ⊤
| vr1 B l A : l ⊢ A -> l ⊢ A ∨ B
| vr2 B l A : l ⊢ A -> l ⊢ B ∨ A
| vl l1 l2 A B C : l1 ++ A :: l2 ⊢ C -> l1 ++ B :: l2 ⊢ C -> l1 ++ A ∨ B :: l2 ⊢ C
| bl l1 l2 C : l1 ++ ⊥ :: l2 ⊢ C
| ir l A B : A :: l ⊢ B -> l ⊢ A → B
| il l2 l1 l3 A B C : l1 ⊢ A -> l2 ++ B :: l3 ⊢ C -> l2 ++ l1 ++ A → B :: l3 ⊢ C
where "l ⊢ A" := (lj l A).
Arguments ax {_}, _.
Arguments ex [_ _ _ _] _, [_ _ _] _ _.
Arguments co [_ _ _ _] _, _ [_ _ _] _.
Arguments wk [_ _ _ _] _, _ [_ _ _] _, _ _ [_ _] _.
Arguments wl1 [_ _ _ _ _] _, _ [_ _ _] _, _ _ [_ _] _.
Arguments wl2 [_ _ _ _ _] _, _ [_ _ _] _, _ _ [_ _] _.
Arguments tr {_}, _.
Arguments vr1 [_ _ _] _, _ [_ _] _.
Arguments vr2 [_ _ _] _, _ [_ _] _.
Arguments vl [_ _ _ _ _] _ _,  _ [_ _ _ _] _ _.
Arguments bl {_ _ _}, _ {_ _}.
Arguments ir [_ _ _] _.
Arguments il [_ _ _ _ _ _] _ _, _ [_ _ _ _ _] _ _.

Instance imall_PermutationT : Proper (@PermutationT _ ==> eq ==> iffT) lj.
Proof. intros l1 l2 HP B A ->. split; intro pi; [ | symmetry in HP ]; apply (ex HP pi). Qed.

Lemma cw_gen r l l0 C : l ++ concat (repeat l0 r) ⊢ C -> l ++ l0 ⊢ C.
Proof.
intro pi. rewrite PermutationT_app_comm in pi. rewrite PermutationT_app_comm.
induction r as [ | r IHr ] in l, pi |- *; list_simpl in pi.
- induction l0 as [ | A l0 IHl ]; [ assumption | ].
  list_simpl. apply (@wk []). assumption.
- rewrite PermutationT_app_swap_app in pi. apply IHr in pi. clear IHr.
  induction l0 as [ | A l0 IH ] in l, pi |- *; [ assumption | list_simpl in * ].
  apply (@co []). cbn. rewrite 2 PermutationT_middle. apply IH.
  rewrite app_assoc, <- 2 PermutationT_middle. list_simpl. rewrite app_comm_cons, PermutationT_middle.
  list_assumption.
Qed.


(** * Axiom expansion *)

Lemma ax_gen A : [A] ⊢ A.
Proof.
induction A; try now rewrite <- (app_nil_l _); do 2 constructor.
constructor. apply (@il [] [_]); assumption.
Qed.


(** * Cut *)

Fixpoint pweight l A (pi : l ⊢ A) := S
match pi with
| ax | tr | bl => 0
| wr pi1 pi2 | vl pi1 pi2 => Nat.max (pweight pi1) (pweight pi2)
| ex pi1 | co pi1 | wk pi1 | wl1 pi1 | wl2 pi1 | vr1 pi1 | vr2 pi1 | ir pi1 => pweight pi1
| il pi1 pi2 => (pweight pi1) + (pweight pi2)
end.

Lemma cut A l1 l l2 B : l ⊢ A -> l1 ++ A :: l2 ⊢ B -> l1 ++ l ++ l2 ⊢ B.
Proof.
(* PAUSE *)
enough (forall r A' l0' l1' l' B', l' ⊢ A' -> l0' ⊢ B' -> PermutationT l0' (repeat A' r ++ l1') ->
          l1' ++ l' ⊢ B') as mcut.
{ intros pi1 pi2.
  assert (PermutationT (l1 ++ A :: l2) (repeat A 1 ++ l1 ++ l2)) as HP
    by (symmetry; cbn; apply PermutationT_middle).
  apply (mcut _ _ _ _ _ _ pi1 pi2) in HP.
  refine (ex _ HP).
  list_simpl. apply PermutationT_app_head, PermutationT_app_comm. }
clear A l1 l l2 B. intros r A.
remember (fsize A) as d eqn:Hd.
induction d as [d IHd] in A, r, Hd |- * using (well_founded_induction_type lt_wf). subst d.
assert (forall A' l1' l2' l' B', l' ⊢ A' -> l1' ++ A' :: l2' ⊢ B' -> fsize A' < fsize A -> l1' ++ l' ++ l2' ⊢ B')
  as IHf; [ | clear IHd ].
{ intros A' l1' l2' l' B' pi1' pi2' Hs.
  rewrite <- PermutationT_app_rot, app_assoc. apply (IHd _ Hs 1 _ eq_refl _ _ _ _ pi1' pi2').
  rewrite <- PermutationT_middle. apply PermutationT_cons, PermutationT_app_comm. reflexivity. }
intros l0 l1 l B pi1 pi2.
remember (pweight pi1 + pweight pi2) as n eqn:Hn.
induction n as [n IHn] in r, A, B, l0, l, l1, pi1, pi2, IHf, Hn |- * using (well_founded_induction_type lt_wf).
subst n.
assert (forall r' l0' l1' l' B' (pi1' : l' ⊢ A) (pi2' : l0' ⊢ B'), PermutationT l0' (repeat A r' ++ l1') ->
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 ->
          l1' ++ l' ⊢ B') as IH; [ | clear IHn ].
{ intros r' l0' l1' l' B' pi1' pi2' HP Hn. exact (IHn _ Hn _ _ IHf _ _ _ _ pi1' pi2' eq_refl HP). }
destruct pi2 as [ | ? ? ? HP2 pi2 | | | ? A' B' pi2_1 pi2_2 | ? B' ? A' ? pi2 | ? A' ? B' ? pi2 |
                | ? ? ? pi2 | ? ? ? pi2 | ? ? A' B' ? pi2_1 pi2_2 |
                | ? A' B' pi2 | ? ? ? A' B' ? pi2_1 pi2_2 ]; cbn in IH; intro HP.
- apply PermutationT_length_1_inv in HP. decomp_list_eq HP.
  + destruct r; inversion HP0. subst.
    apply (cw_gen 0), ax.
  + destruct r as [ | [] ]; inversion HP. subst.
    list_assumption.
- rewrite <- HP2 in HP.
  apply (IH _ _ _ _ _ pi1 pi2 HP). cbn. lia.
- symmetry in HP. apply PermutationT_vs_elt_inv_perm in HP as [(l0', l2') HP Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq). rewrite repeat_length, length_app in Hl. cbn in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [<- [Heq1 Heq2]].
    rewrite <- Heq1, <- Heq2 in HP. clear Heq1 Heq2.
    apply (IH (S r) _ _ _ _ pi1 pi2); [ | cbn; lia ].
    rewrite <- PermutationT_middle, app_comm_cons, <- PermutationT_middle. list_simpl.
    apply PermutationT_cons; [ reflexivity | ]. rewrite <- HP.
    rewrite app_assoc, app_comm_cons. apply PermutationT_app_tail. rewrite <- Hl.
    rewrite repeat_app. cbn. apply PermutationT_middle.
  + list_apply (@co l3).
    list_apply (IH r _ (l3 ++ A0 :: A0 :: l2') _ _ pi1 pi2); [ | cbn; lia ].
    rewrite app_assoc. do 2 apply PermutationT_elt. symmetry. assumption.
- symmetry in HP. apply PermutationT_vs_elt_inv_perm in HP as [(l0', l2') HP Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq).
    rewrite repeat_length, length_app in Hl. cbn in Hl. rewrite Nat.add_succ_r in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [<- [Heq1 Heq2]].
    rewrite <- Heq1, <- Heq2 in HP. clear Heq1 Heq2.
    apply (IH (pred r) _ _ _ _ pi1 pi2); [ | cbn; lia ].
    rewrite <- HP, <- Hl. cbn. rewrite repeat_app. list_reflexivity.
  + list_apply (@wk l3).
    list_apply (IH r _ (l3 ++ l2') _ _ pi1 pi2); [ | cbn; lia ].
    symmetry. list_assumption.
- apply wr.
  + apply (IH r _ _ _ _ pi1 pi2_1 HP). cbn. lia.
  + apply (IH r _ _ _ _ pi1 pi2_2 HP). cbn. lia.
- assert (HP' := HP). symmetry in HP'. apply PermutationT_vs_elt_inv in HP' as [(l0', l2') Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq).
    rewrite repeat_length, length_app in Hl. cbn in Hl. rewrite Nat.add_succ_r in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [-> _].
    remember (A' ∧ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | | | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ _ pi1 (wl1 pi2) HP). cbn. lia.
    * list_apply (@co (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl1 pi2) HP). cbn. lia.
    * list_apply (@wk (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl1 pi2) HP). cbn. lia.
    * apply (cw_gen 2). list_simpl. apply (IHf _ _ _ _ _ pi1_1); [ | cbn; lia ].
      cons2app. rewrite app_assoc.
      apply (IH (length l0' + length l3) _ _ _ _ (wr pi1_1 pi1_2) pi2); [ | cbn; lia ].
      cbn in HP. symmetry in HP. apply PermutationT_cons_app_inv in HP.
      rewrite <- PermutationT_middle, PermutationT_cons_append, <- HP. list_reflexivity.
    * list_apply (@wl1 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl1 pi2) HP). cbn. lia.
    * list_apply (@wl2 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl1 pi2) HP). cbn. lia.
    * list_apply (@vl (l1 ++ l4)).
      -- list_apply (IH _ _ _ _ _ pi1_1 (wl1 pi2) HP). cbn. lia.
      -- list_apply (IH _ _ _ _ _ pi1_2 (wl1 pi2) HP). cbn. lia.
    * list_apply (@bl (l1 ++ l4)).
    * list_apply (@il (l1 ++ l4)); [ assumption | ].
      list_apply (IH _ _ _ _ _ pi1_2 (wl1 pi2) HP). cbn. lia.
  + list_apply wl1.
    list_apply (IH _ _ (l3 ++ A' :: l2') _ _ pi1 pi2); [ | cbn; lia ].
    rewrite app_assoc in HP. apply PermutationT_app_inv in HP.
    rewrite app_assoc. apply PermutationT_elt. eassumption.
- assert (HP' := HP). symmetry in HP'. apply PermutationT_vs_elt_inv in HP' as [(l0', l2') Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq).
    rewrite repeat_length, length_app in Hl. cbn in Hl. rewrite Nat.add_succ_r in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [-> _].
    remember (A' ∧ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | | | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ _ pi1 (wl2 pi2) HP). cbn. lia.
    * list_apply (@co (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl2 pi2) HP). cbn. lia.
    * list_apply (@wk (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl2 pi2) HP). cbn. lia.
    * apply (cw_gen 2). list_simpl. apply (IHf _ _ _ _ _ pi1_2); [ | cbn; lia ].
      cons2app. rewrite app_assoc.
      apply (IH (length l0' + length l3) _ _ _ _ (wr pi1_1 pi1_2) pi2); [ | cbn; lia ].
      cbn in HP. symmetry in HP. apply PermutationT_cons_app_inv in HP.
      rewrite <- PermutationT_middle, PermutationT_cons_append, <- HP. list_reflexivity.
    * list_apply (@wl1 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl2 pi2) HP). cbn. lia.
    * list_apply (@wl2 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (wl2 pi2) HP). cbn. lia.
    * list_apply (@vl (l1 ++ l4)).
      -- list_apply (IH _ _ _ _ _ pi1_1 (wl2 pi2) HP). cbn. lia.
      -- list_apply (IH _ _ _ _ _ pi1_2 (wl2 pi2) HP). cbn. lia.
    * list_apply (@bl (l1 ++ l4)).
    * list_apply (@il (l1 ++ l4)); [ assumption | ].
      list_apply (IH _ _ _ _ _ pi1_2 (wl2 pi2) HP). cbn. lia.
  + list_apply wl2.
    list_apply (IH _ _ (l3 ++ B' :: l2') _ _ pi1 pi2); [ | cbn; lia ].
    rewrite app_assoc in HP. apply PermutationT_app_inv in HP.
    rewrite app_assoc. apply PermutationT_elt. eassumption.
- apply tr.
- apply vr1. apply (IH _ _ _ _ _ pi1 pi2 HP). cbn. lia.
- apply vr2. apply (IH _ _ _ _ _ pi1 pi2 HP). cbn. lia.
- assert (HP' := HP). symmetry in HP'. apply PermutationT_vs_elt_inv in HP' as [(l0', l2') Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq).
    rewrite repeat_length, length_app in Hl. cbn in Hl. rewrite Nat.add_succ_r in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [-> _].
    remember (A' ∨ B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | | | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ _ pi1 (vl pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@co (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (vl pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@wk (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (vl pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@wl1 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (vl pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@wl2 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 (vl pi2_1 pi2_2) HP). cbn. lia.
    * apply (cw_gen 2). list_simpl. apply (IHf _ _ _ _ _ pi1); [ | cbn; lia ].
      cons2app. rewrite app_assoc.
      apply (IH (length l0' + length l3) _ _ _ _ (vr1 pi1) pi2_1); [ | cbn; lia ].
      cbn in HP. symmetry in HP. apply PermutationT_cons_app_inv in HP.
      rewrite <- PermutationT_middle, PermutationT_cons_append, <- HP. list_reflexivity.
    * apply (cw_gen 2). list_simpl. apply (IHf _ _ _ _ _ pi1); [ | cbn; lia ].
      cons2app. rewrite app_assoc.
      apply (IH (length l0' + length l3) _ _ _ _ (vr2 pi1) pi2_2); [ | cbn; lia ].
      cbn in HP. symmetry in HP. apply PermutationT_cons_app_inv in HP.
      rewrite <- PermutationT_middle, PermutationT_cons_append, <- HP. list_reflexivity.
    * list_apply (@vl (l1 ++ l4)).
      -- list_apply (IH _ _ _ _ _ pi1_1 (vl pi2_1 pi2_2) HP). cbn. lia.
      -- list_apply (IH _ _ _ _ _ pi1_2 (vl pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@bl (l1 ++ l4)).
    * list_apply (@il (l1 ++ l4)); [ assumption | ].
      list_apply (IH _ _ _ _ _ pi1_2 (vl pi2_1 pi2_2) HP). cbn. lia.
  + rewrite app_assoc in HP. apply PermutationT_app_inv in HP.
    list_apply vl.
    * list_apply (IH _ _ (l3 ++ A' :: l2') _ _ pi1 pi2_1); [ | cbn; lia ].
      rewrite app_assoc. apply PermutationT_elt. eassumption.
    * list_apply (IH _ _ (l3 ++ B' :: l2') _ _ pi1 pi2_2); [ | cbn; lia ].
      rewrite app_assoc. apply PermutationT_elt. eassumption.
- assert (HP' := HP). symmetry in HP'. apply PermutationT_vs_elt_inv in HP' as [(l0', l2') Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq).
    rewrite repeat_length, length_app in Hl. cbn in Hl. rewrite Nat.add_succ_r in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [-> _].
    remember ⊥ as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | | | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ _ pi1 bl HP). cbn. lia.
    * list_apply (@co (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 bl HP). cbn. lia.
    * list_apply (@wk (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 bl HP). cbn. lia.
    * list_apply (@wl1 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 bl HP). cbn. lia.
    * list_apply (@wl2 (l1 ++ l4)). list_apply (IH _ _ _ _ _ pi1 bl HP). cbn. lia.
    * list_apply (@vl (l1 ++ l4)).
      -- list_apply (IH _ _ _ _ _ pi1_1 bl HP). cbn. lia.
      -- list_apply (IH _ _ _ _ _ pi1_2 bl HP). cbn. lia.
    * list_apply (@bl (l1 ++ l4)).
    * list_apply (@il (l1 ++ l4)); [ assumption | ].
      list_apply (IH _ _ _ _ _ pi1_2 bl HP). cbn. lia.
  + list_apply bl.
- apply ir. rewrite app_comm_cons. apply (IH r _ _ _ _ pi1 pi2); [ | cbn; lia ].
  apply PermutationT_cons_app. assumption.
- assert (HP' := HP).
  symmetry in HP'. rewrite app_assoc in HP'. apply PermutationT_vs_elt_inv in HP' as [(l0', l2') Heq].
  decomp_list_eq Heq; subst.
  + assert (Hl := f_equal (@length _) Heq).
    rewrite repeat_length, length_app in Hl. cbn in Hl. rewrite Nat.add_succ_r in Hl.
    symmetry in Heq. apply repeat_eq_elt in Heq as [-> _].
    remember (A' → B') as C' eqn:HC.
    destruct pi1 as [ | ? ? ? HP1 pi1 | | | ? ? ? pi1_1 pi1_2 | ? ? ? ? ? pi1 | ? ? ? ? ? pi1 |
                    | | | ? ? ? ? ? pi1_1 pi1_2 | | | ]; destr_eq HC; subst.
    * rewrite <- HP1.
      apply (IH _ _ _ _ _ pi1 (il pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@co (l1 ++ l5)). list_apply (IH _ _ _ _ _ pi1 (il pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@wk (l1 ++ l5)). list_apply (IH _ _ _ _ _ pi1 (il pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@wl1 (l1 ++ l5)). list_apply (IH _ _ _ _ _ pi1 (il pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@wl2 (l1 ++ l5)). list_apply (IH _ _ _ _ _ pi1 (il pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@vl (l1 ++ l5)).
      -- list_apply (IH _ _ _ _ _ pi1_1 (il pi2_1 pi2_2) HP). cbn. lia.
      -- list_apply (IH _ _ _ _ _ pi1_2 (il pi2_1 pi2_2) HP). cbn. lia.
    * list_apply (@bl (l1 ++ l5)).
    * cbn in HP. symmetry in HP. rewrite app_assoc in HP. apply PermutationT_cons_app_inv in HP.
      remember (length l0' + length l4) as r eqn:Hr. clear Hr.
      list_simpl in HP. rewrite PermutationT_app_swap_app in HP.
      apply PermutationT_app_app_inv in HP as [[[[l0r l1a] lr] l1b] [[HP1 HP2] [HP3 HP4]]].
      symmetry in HP1. apply PermutationT_repeat in HP1. symmetry in HP1. apply repeat_eq_app in HP1 as [Hr1 Hr2].
      rewrite <- Hr1 in HP3.
      assert (IH1 := IH (length l0r) _ l1a _ _ (ir pi1) pi2_1 HP3 ltac:(cbn; lia)).
      rewrite <- Hr2 in HP4. apply (PermutationT_elt B') in HP4.
      assert (IH2 := IH (length lr) _ (B' :: l1b) _ _ (ir pi1) pi2_2 HP4 ltac:(cbn; lia)).
      list_simpl in IH2.
      assert (pi := IHf _ [] _ _ _ IH1 pi1 ltac:(cbn; lia)). list_simpl in pi.
      assert (pi' := IHf _ [] _ _ _ pi IH2 ltac:(cbn; lia)). list_simpl in pi'.
      apply (cw_gen 3). list_simpl. rewrite HP2. list_simpl. refine (ex _ pi').
      apply PermutationT_app_head. rewrite 2 PermutationT_app_rot. list_reflexivity.
    * list_apply (@il (l1 ++ l5)); [ assumption | ].
      list_apply (IH _ _ _ _ _ pi1_2 (il pi2_1 pi2_2) HP). cbn. lia.
  + rewrite 2 app_assoc in HP. apply PermutationT_app_inv in HP. list_simpl in HP.
    list_simpl in HP. rewrite PermutationT_app_swap_app in HP.
    apply PermutationT_app_app_inv in HP as [[[[l0r l23r] l0b] l23b] [[HP1 HP2] [HP3 HP4]]].
    symmetry in HP3. apply PermutationT_repeat in HP3. symmetry in HP3. apply repeat_eq_app in HP3 as [Hr1 Hr2].
    rewrite <- Hr1 in HP1.
    assert (IH1 := IH (length l0r) _ _ _ _ pi1 pi2_1 HP1 ltac:(cbn; lia)).
    rewrite <- Hr2 in HP2. apply (PermutationT_elt B') in HP2.
    assert (IH2 := IH (length l23r) _ (B' :: l23b) _ _ pi1 pi2_2 HP2 ltac:(cbn; lia)).
    list_simpl in IH2.
    assert (pi := @il [] _ _ _ _ _ IH1 IH2). list_simpl in pi.
    apply (cw_gen 2). list_simpl. refine (ex _ pi).
    rewrite app_assoc. apply PermutationT_elt. rewrite ! app_assoc, HP4. list_simpl.
    apply PermutationT_app_head, PermutationT_app_swap_app.
Qed.
