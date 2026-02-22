(** Involutive Lattices = ALL **)
(** Tait's presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import Bool Lia Wf_nat.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Formulas *)

Definition Atom := nat : Type.

Implicit Type X : Atom.

(* PAUSE *)
Inductive formula := var (_ : bool) (_ : Atom) | bin (_ : bool) (_ _ : formula) | nul (_ : bool).
Coercion pvar := var true.
Infix "∧" := (bin true) (at level 35).
Infix "∨" := (bin false) (at level 35).
Notation "⊤" := (nul true).
Notation "⊥" := (nul false).

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

Lemma coneg A B : ¬A = B <-> A = ¬B.
Proof. split; [ intros <-; symmetry | intros -> ]; apply bineg. Qed.


(** * Proofs *)

Reserved Notation "⊢ A , B" (at level 65).
Inductive all : formula -> formula -> Type :=
| ax X : ⊢ ¬X, X
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

Lemma axr X : ⊢ X, ¬X.
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
| ex pi1 | v1 pi1 | v2 pi1 => pweight pi1
end.

Lemma cut A B C : ⊢ A, ¬B -> ⊢ B, C -> ⊢ A, C.
Proof.
intros pi1 pi2.
enough (forall D E, ⊢ D, E -> (D = A -> E = ¬B -> ⊢ D, C) * (D = ¬B -> E = A -> ⊢ E, C)) as H
  by (apply (H _ _ pi1); reflexivity).
clear pi1. intros D E pi1.
remember (pweight pi1 + pweight pi2) as n eqn:Hn.
induction n as [n IHn] in A, B, C, D, E, pi1, pi2, Hn |- * using (well_founded_induction_type lt_wf). subst n.
assert (forall A' B' C' (pi1' : ⊢ A', ¬B') (pi2' : ⊢ B', C'),
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> ⊢ A', C') as IH1.
{ intros A' B' C' pi1' pi2' Hn. exact (fst (IHn _ Hn _ _ _ pi2' _ _ pi1' eq_refl) eq_refl eq_refl). }
assert (forall A' B' C' (pi1' : ⊢ ¬B', A') (pi2' : ⊢ B', C'),
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> ⊢ A', C') as IH2.
{ intros A' B' C' pi1' pi2' Hn. exact (snd (IHn _ Hn _ _ _ pi2' _ _ pi1' eq_refl) eq_refl eq_refl). }
clear IHn.
destruct pi2 as [ | B C pi2 | B1 B2 C pi2_1 pi2_2 | | B2 B1 C pi2 | B1 B2 C pi2 ]; cbn in *.
- split; intros -> ->; [ | apply ex ]; assumption.
- split; intros -> ->.
  + remember (¬C) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; subst.
    * destruct C as [ [] Y | | ]; inversion HD.
      apply ex. exact pi2.
    * apply ex.
      remember (pweight pi2) as n eqn:Hn.
      clear IH2. revert pi2 Hn. rewrite <- (bineg C). intros pi2 ->.
      apply (IH1 _ _ _ pi2 pi1). cbn. lia.
    * apply w; [ apply (IH1 _ _ _ pi1_1 (ex pi2)) | apply (IH1 _ _ _ pi1_2 (ex pi2)) ]; cbn; lia.
    * apply t.
    * apply v1. apply (IH1 _ _ _ pi1 (ex pi2)). cbn. lia.
    * apply v2. apply (IH1 _ _ _ pi1 (ex pi2)). cbn. lia.
  + apply ex.
    remember (pweight pi2) as n eqn:Hn.
    clear IH2. revert pi2 Hn. rewrite <- (bineg C). intros pi2 ->.
    apply (IH1 _ _ _ pi2 pi1). lia.
- split; intros -> ->.
  + remember (¬B1 ∨ ¬B2) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; subst.
    * discriminate HD.
    * apply (IH2 _ (B1 ∧ B2) _ pi1 (w pi2_1 pi2_2)). cbn. lia.
    * apply w; [ apply (IH1 _ (B1 ∧ B2) _ pi1_1 (w pi2_1 pi2_2))
               | apply (IH1 _ (B1 ∧ B2) _ pi1_2 (w pi2_1 pi2_2)) ]; cbn; lia.
    * apply t.
    * apply v1. apply (IH1 _ (B1 ∧ B2) _ pi1 (w pi2_1 pi2_2)). cbn. lia.
    * apply v2. apply (IH1 _ (B1 ∧ B2) _ pi1 (w pi2_1 pi2_2)). cbn. lia.
  + remember (¬B1 ∨ ¬B2) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; try destr_eq HD; subst.
    * apply (IH1 _ (B1 ∧ B2) _ pi1 (w pi2_1 pi2_2)). cbn. lia.
    * apply (IH2 _ _ _ pi1 pi2_1). cbn. lia.
    * apply (IH2 _ _ _ pi1 pi2_2). cbn. lia.
- split; intros -> ->.
  + remember ⊥ as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; subst.
    * discriminate HD.
    * apply (IH2 _ ⊤ _ pi1 t). cbn. lia.
    * apply w; [ apply (IH1 _ ⊤ _ pi1_1 t)
               | apply (IH1 _ ⊤ _ pi1_2 t) ]; cbn; lia.
    * apply t.
    * apply v1. apply (IH1 _ ⊤ _ pi1 t). cbn. lia.
    * apply v2. apply (IH1 _ ⊤ _ pi1 t). cbn. lia.
  + remember ⊥ as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; try destr_eq HD; subst.
    apply (IH1 _ ⊤ _ pi1 t). cbn. lia.
- split; intros -> ->.
  + remember (¬B1 ∧ ¬B2) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; subst.
    * discriminate HD.
    * apply (IH2 _ (B1 ∨ B2) _ pi1 (v1 pi2)). cbn. lia.
    * apply w; [ apply (IH1 _ (B1 ∨ B2) _ pi1_1 (v1 pi2))
               | apply (IH1 _ (B1 ∨ B2) _ pi1_2 (v1 pi2)) ]; cbn; lia.
    * apply t.
    * apply v1. apply (IH1 _ (B1 ∨ B2) _ pi1 (v1 pi2)). cbn. lia.
    * apply v2. apply (IH1 _ (B1 ∨ B2) _ pi1 (v1 pi2)). cbn. lia.
  + remember (¬B1 ∧ ¬B2) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; try destr_eq HD; subst.
    * apply (IH1 _ (B1 ∨ B2) _ pi1 (v1 pi2)). cbn. lia.
    * apply (IH2 _ _ _ pi1_1 pi2). cbn. lia.
- split; intros -> ->.
  + remember (¬B1 ∧ ¬B2) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; subst.
    * discriminate HD.
    * apply (IH2 _ (B1 ∨ B2) _ pi1 (v2 pi2)). cbn. lia.
    * apply w; [ apply (IH1 _ (B1 ∨ B2) _ pi1_1 (v2 pi2))
               | apply (IH1 _ (B1 ∨ B2) _ pi1_2 (v2 pi2)) ]; cbn; lia.
    * apply t.
    * apply v1. apply (IH1 _ (B1 ∨ B2) _ pi1 (v2 pi2)). cbn. lia.
    * apply v2. apply (IH1 _ (B1 ∨ B2) _ pi1 (v2 pi2)). cbn. lia.
  + remember (¬B1 ∧ ¬B2) as D eqn:HD.
    destruct pi1 as [ | ? ? pi1 | ? ? ? pi1_1 pi1_2 | | ? ? ? pi1 | ? ? ? pi1 ]; try destr_eq HD; subst.
    * apply (IH1 _ (B1 ∨ B2) _ pi1 (v2 pi2)). cbn. lia.
    * apply (IH2 _ _ _ pi1_2 pi2). cbn. lia.
Qed.
