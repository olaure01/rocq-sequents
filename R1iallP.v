(** Bounded Lattices = IALL **)
(** Whitman's presentation *)

(** proofs in [Prop] *)
(** 2nd inductive type with size parameter in [nat] *)


From Stdlib Require Import Lia Wf_nat Relations RelationClasses.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Formulas *)

Definition Atom := nat : Type.

Inductive formula := var (_ : Atom) | wedge (_ _ : formula) | top | vee (_ _ : formula) | bot.
Infix "∧" := wedge (at level 35).
Notation "⊤" := top.
Infix "∨" := vee (at level 35).
Notation "⊥" := bot.

Coercion var : Atom >-> formula.


(** * Proofs *)

Reserved Notation "A ⊢ B" (at level 65).
Inductive iall : relation formula (* formula -> formula -> Prop *) :=
| ax (X : Atom) : X ⊢ X
| wr A B C : C ⊢ A -> C ⊢ B -> C ⊢ A ∧ B
| wl1 B A C : A ⊢ C -> A ∧ B ⊢ C
| wl2 B A C : A ⊢ C -> B ∧ A ⊢ C
| tr C : C ⊢ ⊤
| vr1 B A C : C ⊢ A -> C ⊢ A ∨ B
| vr2 B A C : C ⊢ A -> C ⊢ B ∨ A
| vl A B C : A ⊢ C -> B ⊢ C -> A ∨ B ⊢ C
| bl C : ⊥ ⊢ C
where "A ⊢ B" := (iall A B).


(** * Axiom expansion *)

Lemma ax_gen A : A ⊢ A.
Proof. induction A; now repeat constructor. Qed.


(** * Proofs with size *)

Reserved Notation "n $ A ⊢ B" (at level 64, A at next level, B at next level).
Inductive iall_s : nat -> relation formula :=
| axs (X : Atom) : 1 $ X ⊢ X
| wrs n m A B C : n $ C ⊢ A -> m $ C ⊢ B -> S (max n m) $ C ⊢ A ∧ B
| wl1s n B A C : n $ A ⊢ C -> S n $ A ∧ B ⊢ C
| wl2s n B A C : n $ A ⊢ C -> S n $ B ∧ A ⊢ C
| trs C : 1 $ C ⊢ ⊤
| vr1s n B A C : n $ C ⊢ A -> S n $ C ⊢ A ∨ B
| vr2s n B A C : n $ C ⊢ A -> S n $ C ⊢ B ∨ A
| vls n m A B C : n $ A ⊢ C -> m $ B ⊢ C -> S (max n m) $ A ∨ B ⊢ C
| bls C : 1 $ ⊥ ⊢ C
where "n $ A ⊢ B" := (iall_s n A B).

Lemma iall_ialls A B : A ⊢ B <-> exists n, n $ A ⊢ B.
Proof.
split; intro pi.
- induction pi as [ | ? ? ? ? [] ? [] | ? ? ? ? [] | ? ? ? ? [] |
               | ? ? ? ? [] | ? ? ? ? [] | ? ? ? ? [] ? [] | ];
  eexists; constructor; eassumption.
- destruct pi as [? pi]. now induction pi; constructor.
Qed.


(** * Cut *)

Lemma cut A B C : A ⊢ B -> B ⊢ C -> A ⊢ C.
Proof.
intros [n1 pi1]%iall_ialls [n2 pi2]%iall_ialls.

remember (n1 + n2) as n eqn:Hn.
induction n as [n IHn] in n1, n2, Hn, A, B, C, pi1, pi2 |- * using (well_founded_induction lt_wf). subst n.
assert (forall m1 m2 A B C, m1 $ A ⊢ B -> m2 $ B ⊢ C -> m1 + m2 < n1 + n2 -> A ⊢ C) as IH; [ | clear IHn ].
{ intros m1 m2 A' B' C' pi1' pi2' Hmn. exact (IHn _ Hmn _ _ _ _ pi1' _ pi2' eq_refl). }

remember pi2 as pi2' eqn:Hpi2.
destruct pi2';
  try (constructor; (eapply IH; [ eassumption .. | lia ])); (* commutative cases on [pi2] *)
  inversion pi1; revert Hpi2; subst; intro Hpi2; try (constructor; (eapply IH; [ eassumption .. | lia ]));
     (* commutative cases on [pi1] *)
  try (eapply IH; [ eassumption .. | lia ]); (* matches left proof first *)
  try (eapply IH; [ | eassumption | ]; [ eassumption | lia ]). (* matches right proof first *)
Qed.


Instance iall_preorder : PreOrder iall.
Proof. split; [ exact ax_gen | exact cut ]. Qed.
