(** Ortholattices = orthologic **)
(** OL presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import Bool Lia Wf_nat List.
From OLlibs Require Import PermutationT_more.
Import EqNotations ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Preliminaries *)

Lemma PermutationT_diag T (A B C : T) : PermutationT [A; A] [B; C] -> A = B /\ A = C.
Proof. intros [[= <- <-] | [= <- <-]]%PermutationT_length_2_inv; repeat split. Qed.


(** * Formulas *)

Definition Atom := nat : Type.

Implicit Type X : Atom.

Inductive formula := var (_ : bool) (_ : Atom) | bin (_ : bool) (_ _ : formula) | nul (_ : bool).
Coercion pvar := var true.
Infix "∧" := (bin true) (at level 35).
Infix "∨" := (bin false) (at level 35).
Notation "'𝖳'" := (nul true).
Notation "'⊥'" := (nul false).

Reserved Notation "¬ A" (format "¬ A", at level 25, right associativity).
Fixpoint neg A :=
match A with
| var b X => var (negb b) X
| bin b A B => bin (negb b) (¬ A) (¬ B)
| nul b => nul (negb b)
end
where "¬ A" := (neg A).

Lemma bineg A : ¬¬A = A.
Proof. induction A; cbn; rewrite negb_involutive; f_equal; assumption. Qed.
Arguments bineg {_}, _.

Fixpoint fsize A := S
match A with
| var _ _ | nul _ => 0
| bin _ B C => fsize B + fsize C
end.

Lemma fsize_neg A : fsize (¬A) = fsize A.
Proof. induction A as [ | ? ? IHA1 ? IHA2 | ]; cbn; rewrite ? IHA1, ? IHA2; reflexivity. Qed.


(** * Proofs *)

Reserved Notation "⊢ A , B" (at level 65).
Inductive ol : formula -> formula -> Type :=
| ax X : ⊢ ¬X, X
| ex A B : ⊢ A, B -> ⊢ B, A
| w A B C : ⊢ A, C -> ⊢ B, C -> ⊢ A ∧ B, C
| t C : ⊢ 𝖳, C
| v1 B A C : ⊢ A, C -> ⊢ A ∨ B, C
| v2 B A C : ⊢ A, C -> ⊢ B ∨ A, C
| cw B A : ⊢ A, A -> ⊢ A, B
where "⊢ A , B" := (ol A B).
Arguments ax {_}, _.
Arguments t {_}, _.
Arguments v1 [_ _ _] _, _ [_ _] _.
Arguments v2 [_ _ _] _, _ [_ _] _.
Arguments cw [_ _] _, _ [_] _.

Lemma axr X : ⊢ X, ¬X.
Proof. apply ex, ax. Qed.

Lemma wr A B C : ⊢ C, A -> ⊢ C, B -> ⊢ C, A ∧ B.
Proof. intros. apply ex, w; apply ex; assumption. Qed.

Lemma tr C : ⊢ C, 𝖳.
Proof. apply ex, t. Qed.

Lemma v1r B A C : ⊢ C, A -> ⊢ C, A ∨ B.
Proof. intro. apply ex, v1, ex. assumption. Qed.

Lemma v2r B A C : ⊢ C, A -> ⊢ C, B ∨ A.
Proof. intro. apply ex, v2, ex. assumption. Qed.

Lemma cwr B A : ⊢ A, A -> ⊢ B, A.
Proof. intro. apply ex, cw. assumption. Qed.


(** * Axiom expansion *)

Lemma ax_gen A : ⊢ ¬A, A.
Proof.
induction A as [ b X | b A IHA B IHB | ]; destruct b; try now constructor.
- apply axr.
- apply wr; [ apply v1 | apply v2 ]; assumption.
- apply w; [ apply v1r | apply v2r ]; assumption.
- apply tr.
Qed.


(** * Cut *)

Fixpoint pweight A B (pi : ⊢ A, B) := S
match pi with
| ax | t => 0
| w pi1 pi2 => max (pweight pi1) (pweight pi2)
| ex pi1 | v1 pi1 | v2 pi1 | cw pi1 => pweight pi1
end.

Fixpoint sweight A B (pi : ⊢ A, B) :=
match pi with
| ex pi1 | cw pi1 => S (sweight pi1)
| _ => 0
end.

Lemma cut A B C : ⊢ A, ¬B -> ⊢ B, C -> ⊢ A, C.
Proof.
intros pi1 pi2.
enough (forall A' B' C' D' E', ⊢ ¬B', A' -> ⊢ C', D' -> PermutationT [C'; D'] [B'; E'] ->
          (⊢ A', E') * (C' = D' -> ⊢ A', A')) as IH.
{ apply (IH _ _ _ _ _ (ex pi1) pi2). reflexivity. }
clear. intros A B.
remember (fsize B) as d eqn:Hd.
induction d as [d IHd] in A, B, Hd |- * using (well_founded_induction_type lt_wf). subst d.
intros C D E pi1.
remember (sweight pi1) as s eqn:Hs.
induction s as [s IHs] in A, B, C, D, E, IHd, pi1, Hs |- * using (well_founded_induction_type lt_wf). subst s.
intro pi2.
remember (pweight pi2) as n eqn:Hn.
induction n as [n IHn] in A, B, C, D, E, IHd, IHs, pi1, pi2, Hn |- * using (well_founded_induction_type lt_wf).
subst n.
assert (forall A' B' C' D' E' (pi1' : ⊢ ¬B', A') (pi2' : ⊢ C', D'),
          PermutationT [C'; D'] [B'; E'] ->
           ((fsize B' < fsize B) + ((fsize B' = fsize B) * (sweight pi1' < sweight pi1))
          + ((B' = B) * (sweight pi1' = sweight pi1) * (pweight pi2' < pweight pi2)))%type ->
          (⊢ A', E') * (C' = D' -> ⊢ A', A')) as IH; [ | clear IHd IHs IHn ].
{ intros A' B' C' D' E' pi1' pi2' HP [ [ Hf | [Hf Hs] ] | [[-> Hs] Hn] ].
  - apply (IHd _ Hf _ _ eq_refl _ _ _ pi1' pi2' HP).
  - refine (IHs _ Hs _ _ _ _ _ _ pi1' eq_refl pi2' HP).
    rewrite Hf. apply IHd.
  - refine (IHn _ Hn _ _ IHd _ _ _ pi1' _ pi2' eq_refl HP).
    rewrite Hs. apply IHs. }
intro HP.
split; [ | intros Heq ];
  destruct pi2 as [ | C D pi2 | C1 C2 D pi2_1 pi2_2 | | C2 C1 D pi2 | C1 C2 D pi2 | C D pi2 ]; cbn in *; subst.
- apply PermutationT_length_2_inv in HP as [ [= -> ->] | [= -> ->] ]; apply ex; assumption.
- apply (IH _ _ _ _ _ pi1 pi2); [ | intuition lia ].
  rewrite <- HP. apply PermutationT_swap.
- apply PermutationT_length_2_inv in HP as [ [= -> ->] | [= -> ->] ].
  + remember (¬(C1 ∧ C2)) as E eqn:HE.
    destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ];
      destr_eq HE; subst.
    * apply ex.
      apply (IH _ _ _ _ _ (rew <- [fun x => ⊢ x, D] bineg in (w pi2_1 pi2_2)) pi1).
      -- apply PermutationT_swap.
      -- rewrite ! fsize_neg, (bineg (C1 ∧ C2)). cbn. intuition lia.
    * apply (IH _ _ _ _ _ pi1 pi2_1); [ reflexivity | cbn; intuition lia ].
    * apply (IH _ _ _ _ _ pi1 pi2_2); [ reflexivity | cbn; intuition lia ].
    * apply ex, cw.
      apply (IH _ _ _ _ (¬(C1 ∧ C2)) (rew <- [fun x => ⊢ x, D] bineg in (w pi2_1 pi2_2)) pi1); try reflexivity.
      rewrite ! fsize_neg, (bineg (C1 ∧ C2)). cbn. intuition lia.
  + apply wr.
    * apply (IH _ _ _ _ _ pi1 pi2_1); [ | intuition lia ].
      apply PermutationT_swap.
    * apply (IH _ _ _ _ _ pi1 pi2_2); [ | intuition lia ].
      apply PermutationT_swap.
- apply PermutationT_length_2_inv in HP as [ [= -> ->] | [= -> ->] ].
  + remember (¬𝖳) as E eqn:HE.
    destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ];
      destr_eq HE; subst.
    * apply ex.
      apply (IH _ _ _ _ _ (rew <- [fun x => ⊢ x, C] bineg in t) pi1).
      -- apply PermutationT_swap.
      -- rewrite ! fsize_neg, (bineg 𝖳). cbn. intuition lia.
    * apply ex, cw.
      apply (IH _ _ _ _ (¬𝖳) (rew <- [fun x => ⊢ x, C] bineg in t) pi1); try reflexivity.
      rewrite ! fsize_neg, (bineg 𝖳). cbn. intuition lia.
  + apply tr.
- apply PermutationT_length_2_inv in HP as [ [= -> ->] | [= -> ->] ].
  + remember (¬(C1 ∨ C2)) as E eqn:HE.
    destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ];
      destr_eq HE; subst.
    * apply ex.
      apply (IH _ _ _ _ _ (rew <- [fun x => ⊢ x, D] bineg in (v1 C2 pi2)) pi1).
      -- apply PermutationT_swap.
      -- rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
    * apply (IH _ _ _ _ _ pi1_1 pi2); [ reflexivity | cbn; intuition lia ].
    * apply ex, cw.
      apply (IH _ _ _ _ (¬(C1 ∨ C2)) (rew <- [fun x => ⊢ x, D] bineg in (v1 C2 pi2)) pi1); try reflexivity.
      rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
  + apply v1r.
    apply (IH _ _ _ _ _ pi1 pi2); [ | intuition lia ].
    apply PermutationT_swap.
- apply PermutationT_length_2_inv in HP as [ [= -> ->] | [= -> ->] ].
  + remember (¬(C1 ∨ C2)) as E eqn:HE.
    destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ];
      destr_eq HE; subst.
    * apply ex.
      apply (IH _ _ _ _ _ (rew <- [fun x => ⊢ x, D] bineg in (v2 C1 pi2)) pi1).
      -- apply PermutationT_swap.
      -- rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
    * apply (IH _ _ _ _ _ pi1_2 pi2); [ reflexivity | cbn; intuition lia ].
    * apply ex, cw.
      apply (IH _ _ _ _ (¬(C1 ∨ C2)) (rew <- [fun x => ⊢ x, D] bineg in (v2 C1 pi2)) pi1); try reflexivity.
      rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
  + apply v2r.
    apply (IH _ _ _ _ _ pi1 pi2); [ | intuition lia ].
    apply PermutationT_swap.
- apply PermutationT_length_2_inv in HP as [ [= -> ->] | [= -> ->] ].
  + apply cw.
    apply (IH _ _ _ _ D pi1 pi2); [ | intuition lia | ]; reflexivity.
  + apply ex, cw. assumption.
- discriminate Heq.
- apply (IH _ _ _ _ _ pi1 pi2 HP); [ intuition lia | reflexivity ].
- apply PermutationT_diag in HP as [<- <-].
  remember (¬(C1 ∧ C2)) as E eqn:HE.
  destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ]; destr_eq HE; subst.
  + assert (pi'1 := fst (IH _ _ _ _ _ (ex pi1) pi2_1 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    assert (pi'2 := fst (IH A _ _ _ _ (ex pi1) pi2_2 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    apply ex in pi'1, pi'2.
    refine (fst (IH _ _ _ _ A (rew <- [fun x => ⊢ x, A] bineg in (w pi'1 pi'2)) pi1 _ _)).
    * apply PermutationT_swap.
    * rewrite ! fsize_neg, (bineg (C1 ∧ C2)). cbn. intuition lia.
  + unshelve refine (fst (IH _ _ B C1 _ pi1 _ _ _)).
    * apply (IH _ (C1 ∧ C2) _ _ _ (v1 pi1) pi2_1).
      -- apply PermutationT_swap.
      -- intuition lia.
    * apply PermutationT_swap.
    * cbn. intuition lia.
  + unshelve refine (fst (IH _ _ B C2 _ pi1 _ _ _)).
    * apply (IH _ (C1 ∧ C2) _ _ _ (v2 pi1) pi2_2).
      -- apply PermutationT_swap.
      -- intuition lia.
    * apply PermutationT_swap.
    * cbn. intuition lia.
  + assert (pi'1 := fst (IH A _ _ _ _ (cw pi1) pi2_1 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    assert (pi'2 := fst (IH A _ _ _ _ (cw pi1) pi2_2 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    apply ex in pi'1, pi'2.
    apply (IH _ _ _ _ (¬(C1 ∧ C2)) (rew <- [fun x => ⊢ x, A] bineg in (w pi'1 pi'2)) pi1).
    * apply PermutationT_swap.
    * rewrite ! fsize_neg, (bineg (C1 ∧ C2)). cbn. intuition lia.
    * reflexivity.
- apply PermutationT_diag in HP as [<- <-].
  remember (¬𝖳) as E eqn:HE.
  destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ]; destr_eq HE; subst.
  + refine (fst (IH A _ _ _ A (rew <- [fun x => ⊢ x, A] bineg in t) pi1 _ _)).
    -- apply PermutationT_swap.
    -- rewrite ! fsize_neg, (bineg 𝖳). cbn. intuition lia.
  + refine (snd (IH A _ _ _ (¬𝖳) (rew <- [fun x => ⊢ x, A] bineg in t) pi1 _ _) eq_refl).
    -- reflexivity.
    -- rewrite ! fsize_neg, (bineg 𝖳). cbn. intuition lia.
- apply PermutationT_diag in HP as [<- <-].
  remember (¬(C1 ∨ C2)) as E eqn:HE.
  destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ]; destr_eq HE; subst.
  + assert (pi' := fst (IH _ _ _ _ _ (ex pi1) pi2 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    apply ex in pi'.
    refine (fst (IH _ _ _ _ A (rew <- [fun x => ⊢ x, A] bineg in (v1 pi')) pi1 _ _)).
    * apply PermutationT_swap.
    * rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
  + unshelve refine (fst (IH _ _ B C1 _ pi1_1 _ _ _)).
    * apply (IH _ (C1 ∨ C2) _ _ _ (w pi1_1 pi1_2) pi2).
      -- apply PermutationT_swap.
      -- intuition lia.
    * apply PermutationT_swap.
    * cbn. intuition lia.
  + assert (pi' := fst (IH A _ _ _ _ (cw pi1) pi2 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    apply ex in pi'.
    apply (IH _ _ _ _ (¬(C1 ∨ C2)) (rew <- [fun x => ⊢ x, A] bineg in (v1 C2 pi')) pi1).
    * apply PermutationT_swap.
    * rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
    * reflexivity.
- apply PermutationT_diag in HP as [<- <-].
  remember (¬(C1 ∨ C2)) as E eqn:HE.
  destruct pi1 as [ | A B pi1 | A1 A2 B pi1_1 pi1_2 | | A2 A1 B pi1 | A1 A2 B pi1 | A B pi1 ]; destr_eq HE; subst.
  + assert (pi' := fst (IH _ _ _ _ _ (ex pi1) pi2 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    apply ex in pi'.
    refine (fst (IH _ _ _ _ A (rew <- [fun x => ⊢ x, A] bineg in (v2 pi')) pi1 _ _)).
    * apply PermutationT_swap.
    * rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
  + unshelve refine (fst (IH _ _ B C2 _ pi1_2 _ _ _)).
    * apply (IH _ (C1 ∨ C2) _ _ _ (w pi1_1 pi1_2) pi2).
      -- apply PermutationT_swap.
      -- intuition lia.
    * apply PermutationT_swap.
    * cbn. intuition lia.
  + assert (pi' := fst (IH A _ _ _ _ (cw pi1) pi2 ltac:(apply PermutationT_swap) ltac:(intuition lia))).
    apply ex in pi'.
    apply (IH _ _ _ _ (¬(C1 ∨ C2)) (rew <- [fun x => ⊢ x, A] bineg in (v2 C1 pi')) pi1).
    * apply PermutationT_swap.
    * rewrite ! fsize_neg, (bineg (C1 ∨ C2)). cbn. intuition lia.
    * reflexivity.
- apply PermutationT_diag in HP as [<- <-].
  apply (IH _ _ _ _ C pi1 pi2); [ | intuition lia | ]; reflexivity.
Qed.
