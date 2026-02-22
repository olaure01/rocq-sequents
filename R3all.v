(** Involutive Lattices = ALL **)
(** Tait's presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import Bool Lia Wf_nat.
Import EqNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Formulas *)

Definition Atom := nat : Type.

(* PAUSE *)
Inductive formula := var (_ : bool) (_ : Atom) | bin (_ : bool) (_ _ : formula) | nul (_ : bool).
Infix "∧" := (bin true) (at level 35).
Infix "∨" := (bin false) (at level 35).
Notation "⊤" := (nul true).
Notation "⊥" := (nul false).

Coercion pvar := var true.

Reserved Notation "¬ A" (format "¬ A", at level 25, right associativity).
Fixpoint neg A :=
match A with
| var b X => var (negb b) X
| bin b B C => bin (negb b) (¬ B) (¬ C)
| nul b => nul (negb b)
end
where "¬ A" := (neg A).

Lemma bineg A : ¬¬A = A.
Proof. induction A; cbn; rewrite negb_involutive; f_equal; assumption. Qed.
Arguments bineg {_}, _.


(** * Proofs *)

Reserved Notation "⊢ A , B" (at level 65).
Inductive all : formula -> formula -> Type :=
| ax (X : Atom) : ⊢ ¬X, X
| ex A B : ⊢ A, B -> ⊢ B, A
| w A B C : ⊢ A, C -> ⊢ B, C -> ⊢ A ∧ B, C
| t C : ⊢ ⊤, C
| v1 B A C : ⊢ A, C -> ⊢ A ∨ B, C
| v2 B A C : ⊢ A, C -> ⊢ B ∨ A, C
where "⊢ A , B" := (all A B).
Arguments ax {_}, _.
Arguments t {_}, _.
Arguments v1 [_ _ _] _, _ [_ _] _.
Arguments v2 [_ _ _] _, _ [_ _] _.

Lemma axr (X : Atom) : ⊢ X, ¬X.
Proof. apply ex, ax. Qed.

Lemma wr A B C : ⊢ C, A -> ⊢ C, B -> ⊢ C, A ∧ B.
Proof. intros. apply ex, w; apply ex; assumption. Qed.

Lemma tr C : ⊢ C, ⊤.
Proof. apply ex, t. Qed.

Lemma v1r B A C : ⊢ C, A -> ⊢ C, A ∨ B.
Proof. intro. apply ex, v1, ex. assumption. Qed.

Lemma v2r B A C : ⊢ C, A -> ⊢ C, B ∨ A.
Proof. intro. apply ex, v2, ex. assumption. Qed.


(** * Axiom expansion *)

Lemma ax_gen A : ⊢ ¬A, A.
Proof.
induction A as [ b X | b A IHA B IHB | b ]; destruct b; try now constructor.
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
| ex pi1 | v1 pi1 | v2 pi1 => pweight pi1
end.

Lemma cut A B C : ⊢ A, ¬B -> ⊢ B, C -> ⊢ A, C.
Proof.
intros pi1 pi2.
(* PAUSE *)
enough (forall D E, ⊢ D, E -> ((D = A) * (E = ¬B)) + ((D = ¬B) * (E = A)) -> ⊢ A, C) as H
  by (apply (H _ _ pi1); left; split; reflexivity).
clear pi1. intros D E pi1.

remember (pweight pi1 + pweight pi2) as n eqn:Hn.
induction n as [n IHn] in A, B, C, D, E, pi1, pi2, Hn |- * using (well_founded_induction_type lt_wf). subst n.
assert (forall A' B' C' (pi1' : ⊢ A', ¬B') (pi2' : ⊢ B', C'),
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> ⊢ A', C') as IH1.
{ intros A' B' C' pi1' pi2' Hn.
  apply (IHn _ Hn _ _ _ pi2' _ _ pi1' eq_refl). left. split; reflexivity. }
assert (forall A' B' C' (pi1' : ⊢ ¬B', A') (pi2' : ⊢ B', C'),
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> ⊢ A', C') as IH2; [ | clear IHn ].
{ intros A' B' C' pi1' pi2' Hn.
  apply (IHn _ Hn _ _ _ pi2' _ _ pi1' eq_refl). right. split; reflexivity. }

remember pi2 as pi2' eqn:Hpi2. apply (f_equal (@pweight _ _)) in Hpi2.
destruct pi2' as [ | B C pi2_1 | B1 B2 C pi2_1 pi2_2 | | B2 B1 C pi2_1 | B1 B2 C pi2_1 ]; cbn in *.
- intros [[-> ->] | [-> ->]]; [ | apply ex ]; assumption.
- intros [[-> ->] | [-> ->]].
  + match type of pi1 with ⊢ ?F, ?G => remember G as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2;
      try (constructor; ((let pil := fresh in eapply (IH1 _ _ _ ltac:(refine ?[pil]) pi2);
           instantiate (pil := ltac:(eassumption)); cbn; lia))).
    * rewrite HD, bineg. assumption.
    * apply (IH2 _ _ _ pi1 pi2). cbn. lia.
  + apply ex. (* PAUSE *)
    apply (IH1 _ _ _ (rew <- [fun x => ⊢ B, x] bineg in pi2_1) pi1).
    rewrite (bineg C). cbn. lia.
- intros [[-> ->] | [-> ->]].
  + match type of pi1 with ⊢ ?F, ?G => remember G as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2;
      try (constructor; ((let pil := fresh in eapply (IH1 _ (B1 ∧ B2) _ ltac:(refine ?[pil]) pi2);
           instantiate (pil := ltac:(eassumption)); cbn; lia))).
    apply (IH2 _ (B1 ∧ B2) _ pi1 pi2). cbn. lia.
  + match type of pi1 with ⊢ ?F, ?G => remember F as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2.
    * apply (IH1 _ (B1 ∧ B2) _ pi1 pi2). cbn. lia.
    * apply (IH2 _ _ _ pi1 pi2_1). cbn. lia.
    * apply (IH2 _ _ _ pi1 pi2_2). cbn. lia.
- intros [[-> ->] | [-> ->]].
  + match type of pi1 with ⊢ ?F, ?G => remember G as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intros Hpi2;
      try (constructor; ((let pil := fresh in eapply (IH1 _ ⊤ _ ltac:(refine ?[pil]) pi2);
           instantiate (pil := ltac:(eassumption)); cbn; lia))).
    apply (IH2 _ ⊤ _ pi1 pi2). cbn. lia.
  + match type of pi1 with ⊢ ?F, ?G => remember F as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2.
    apply (IH1 _ ⊤ _ pi1 pi2). cbn. lia.
- intros [[-> ->] | [-> ->]].
  + match type of pi1 with ⊢ ?F, ?G => remember G as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2;
      try (constructor; ((let pil := fresh in eapply (IH1 _ (B1 ∨ B2) _ ltac:(refine ?[pil]) pi2);
           instantiate (pil := ltac:(eassumption)); cbn; lia))).
    apply (IH2 _ (B1 ∨ B2) _ pi1 pi2). cbn. lia.
  + match type of pi1 with ⊢ ?F, ?G => remember F as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2.
    * apply (IH1 _ (B1 ∨ B2) _ pi1 pi2). cbn. lia.
    * apply (IH2 _ _ _ pi1_1 pi2_1). cbn. lia.
- intros [[-> ->] | [-> ->]].
  + match type of pi1 with ⊢ ?F, ?G => remember G as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2;
      try (constructor; ((let pil := fresh in eapply (IH1 _ (B1 ∨ B2) _ ltac:(refine ?[pil]) pi2);
           instantiate (pil := ltac:(eassumption)); cbn; lia))).
    apply (IH2 _ (B1 ∨ B2) _ pi1 pi2). cbn. lia.
  + match type of pi1 with ⊢ ?F, ?G => remember F as D eqn:HD end.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; destr_eq HD;
      revert Hpi2; subst; intro Hpi2.
    * apply (IH1 _ (B1 ∨ B2) _ pi1 pi2). cbn. lia.
    * apply (IH2 _ _ _ pi1_2 pi2_1). cbn. lia.
Qed.
