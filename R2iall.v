(** Bounded Lattices = IALL **)
(** Whitman's presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import Lia Wf_nat CMorphisms.

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
Inductive iall : crelation formula (* formula -> formula -> Type *) :=
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


(** * Cut *)

Fixpoint pweight A B (pi : A ⊢ B) := S
match pi with
| ax | tr | bl => 0
| wr pi1 pi2 | vl pi1 pi2 => max (pweight pi1) (pweight pi2)
| wl1 pi1 | wl2 pi1 | vr1 pi1 | vr2 pi1 => pweight pi1
end.

Lemma cut A B C : A ⊢ B -> B ⊢ C -> A ⊢ C.
Proof.
intros pi1 pi2.

remember (pweight pi1 + pweight pi2) as n eqn:Hn.
induction n as [n IHn] in A, B, C, pi1, pi2, Hn |- * using (well_founded_induction_type lt_wf). subst n.
assert (forall A' B' C' (pi1' : A' ⊢ B') (pi2' : B' ⊢ C'),
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> A' ⊢ C') as IH; [ | clear IHn ].
{ intros A' B' C' pi1' pi2' Hn. exact (IHn _ Hn _ _ _ pi1' pi2' eq_refl). }

remember pi2 as pi2' eqn:Hpi2. apply (f_equal (@pweight _ _)) in Hpi2.
destruct pi2';
  try (constructor; (let pir := fresh in eapply (IH _ _ _ pi1 ltac:(refine ?[pir]));
       instantiate (pir := ltac:(eassumption)); cbn; lia)); (* commutative cases on [pi2] *)
  try (cbn in *; match type of pi1 with ?F ⊢ ?G => remember G as C' eqn:HC end;
       destruct pi1; destr_eq HC; subst;
       try (constructor; (let pil := fresh in eapply (IH _ _ _ ltac:(refine ?[pil]) pi2);
            instantiate (pil := ltac:(eassumption)); cbn; lia))); (* commutative cases on [pi1] *)
  (let pil := fresh in let pir := fresh in eapply (IH _ _ _ ltac:(refine ?[pil]) ltac:(refine ?[pir]));
       (instantiate (pil := ltac:(eassumption)); instantiate (pir := ltac:(eassumption)); cbn; lia)
           (* matches left proof first *)
     + (instantiate (pir := ltac:(eassumption)); instantiate (pil := ltac:(eassumption)); cbn; lia)).
           (* matches right proof first *)
Qed.

Instance iall_preorder : PreOrder iall.
Proof. split; [ exact ax_gen | exact cut ]. Qed.
