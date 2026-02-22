(** Bounded Lattices = IALL **)
(** Whitman's presentation *)

(** proofs in [Prop] *)
(** 2nd inductive type with size parameter in [nat] *)


From Stdlib Require Import Lia Wf_nat.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Formulas *)

Definition Atom := nat : Type.

Implicit Type X : Atom.

Inductive formula := var (_ : Atom) | wedge (_ _ : formula) | top | vee (_ _ : formula) | bot.
Infix "∧" := wedge (at level 35).
Notation "'𝖳'" := top.
Infix "∨" := vee (at level 35).
Notation "'⊥'" := bot.

Coercion var : Atom >-> formula.


(** * Proofs *)

Reserved Notation "A ⊢ B" (at level 65).
Inductive iall : formula -> formula -> Prop (* Relation_Definitions.relation formula *) :=
| ax X : X ⊢ X
| wr A B C : C ⊢ A -> C ⊢ B -> C ⊢ A ∧ B
| wl1 B A C : A ⊢ C -> A ∧ B ⊢ C
| wl2 B A C : A ⊢ C -> B ∧ A ⊢ C
| tr C : C ⊢ 𝖳
| vr1 B A C : C ⊢ A -> C ⊢ A ∨ B
| vr2 B A C : C ⊢ A -> C ⊢ B ∨ A
| vl A B C : A ⊢ C -> B ⊢ C -> A ∨ B ⊢ C
| bl C : ⊥ ⊢ C
where "A ⊢ B" := (iall A B).
Arguments ax {_}, _.
Arguments wl1 [_ _ _] _, _ [_ _] _.
Arguments wl2 [_ _ _] _, _ [_ _] _.
Arguments tr {_}, _.
Arguments vr1 [_ _ _] _, _ [_ _] _.
Arguments vr2 [_ _ _] _, _ [_ _] _.
Arguments bl {_}, _.


(** * Axiom expansion *)

Lemma ax_gen A : A ⊢ A.
Proof. induction A; now repeat constructor. Qed.


(** * Proofs with size *)

Reserved Notation "n $ A ⊢ B" (at level 64, A at next level, B at next level).
Inductive iall_s : nat -> formula -> formula -> Prop :=
| axs X : 1 $ X ⊢ X
| wrs n m A B C : n $ C ⊢ A -> m $ C ⊢ B -> S (max n m) $ C ⊢ A ∧ B
| wl1s n B A C : n $ A ⊢ C -> S n $ A ∧ B ⊢ C
| wl2s n B A C : n $ A ⊢ C -> S n $ B ∧ A ⊢ C
| trs C : 1 $ C ⊢ 𝖳
| vr1s n B A C : n $ C ⊢ A -> S n $ C ⊢ A ∨ B
| vr2s n B A C : n $ C ⊢ A -> S n $ C ⊢ B ∨ A
| vls n m A B C : n $ A ⊢ C -> m $ B ⊢ C -> S (max n m) $ A ∨ B ⊢ C
| bls C : 1 $ ⊥ ⊢ C
where "n $ A ⊢ B" := (iall_s n A B).
Arguments axs {_}, _.
Arguments wl1s [_ _ _ _] _, [_] _ [_ _] _.
Arguments wl2s [_ _ _ _] _, [_] _ [_ _] _.
Arguments trs {_}, _.
Arguments vr1s [_ _ _ _] _, [_] _ [_ _] _.
Arguments vr2s [_ _ _ _] _, [_] _ [_ _] _.
Arguments bls {_}, _.

Lemma ialls_iall n A B : n $ A ⊢ B -> A ⊢ B.
Proof. now induction 1; constructor. Qed.

Lemma iall_ialls A B : A ⊢ B -> exists n, n $ A ⊢ B.
Proof.
induction 1 as [ | ? ? ? ? IH1 ? IH2 | ? ? ? ? IH | ? ? ? ? IH |
               | ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? IH1 ? IH2 | ];
 try destruct IH; try destruct IH1; try destruct IH2;
 eexists; econstructor; eassumption.
Qed.


(** * Cut *)

Lemma cut A B C : A ⊢ B -> B ⊢ C -> A ⊢ C.
Proof.
intros [n1 pi1]%iall_ialls [n2 pi2]%iall_ialls.
remember (n1 + n2) as n eqn:Hn.
induction n as [n IHn] in n1, n2, Hn, A, B, C, pi1, pi2 |- * using (well_founded_induction lt_wf). subst n.
assert (forall m1 m2 A B C, m1 $ A ⊢ B -> m2 $ B ⊢ C -> m1 + m2 < n1 + n2 -> A ⊢ C) as IH; [ | clear IHn ].
{ intros m1 m2 A' B' C' pi1' pi2' Hmn. exact (IHn _ Hmn _ _ _ _ pi1' _ pi2' eq_refl). }
destruct pi2 as [ X | ? ? C1 C2 B pi2_1 pi2_2 | ? B2 B1 C pi2 | ? B1 B2 C pi2 |
                | ? C2 C1 B pi2 | ? C1 C2 B pi2 | ? ? B1 B2 C pi2_1 pi2_2 | ].
- apply (ialls_iall pi1).
- apply wr; (eapply IH; [ eassumption .. | lia ]).
- inversion pi1; subst.
  + refine (IH _ _ _ _ _ _ pi2 _); [ eassumption | lia ].
  + apply wl1. eapply IH; [ eassumption | apply (wl1s pi2) | lia ].
  + apply wl2. eapply IH; [ eassumption | apply (wl1s pi2) | lia ].
  + apply vl; (eapply IH; [ eassumption | apply (wl1s pi2) | lia ]).
  + apply bl.
- inversion pi1; subst.
  + refine (IH _ _ _ _ _ _ pi2 _); [ eassumption | lia ].
  + apply wl1. eapply IH; [ eassumption | apply (wl2s pi2) | lia ].
  + apply wl2. eapply IH; [ eassumption | apply (wl2s pi2) | lia ].
  + apply vl; (eapply IH; [ eassumption | apply (wl2s pi2) | lia ]).
  + apply bl.
- apply tr.
- apply vr1. eapply IH; [ eassumption .. | lia ].
- apply vr2. eapply IH; [ eassumption .. | lia ].
- inversion pi1; subst.
  + apply wl1. eapply IH; [ eassumption | apply (vls pi2_1 pi2_2) | lia ].
  + apply wl2. eapply IH; [ eassumption | apply (vls pi2_1 pi2_2) | lia ].
  + eapply IH; [ eassumption .. | lia ].
  + eapply IH; [ eassumption .. | lia ].
  + apply vl; (eapply IH; [ eassumption | apply (vls pi2_1 pi2_2) | lia ]).
  + apply bl.
- inversion pi1; subst.
  + apply wl1. eapply IH; [ eassumption | apply bls | lia ].
  + apply wl2. eapply IH; [ eassumption | apply bls | lia ].
  + apply vl; (eapply IH; [ eassumption | apply bls | lia ]).
  + apply bl.
Qed.
