(** Definably-Complete Meet-Semi-Lattices = I&LL₂ **)
(** anti-locally-nameless presentation *)

(** proofs in [Type] *)
(** size given by [pweight] *)


From Stdlib Require Import PeanoNat Lia Wf_nat List CMorphisms.
From OLlibs Require Import Logic_Datatypes_more.
Import ListNotations LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Formulas *)

Definition Atom := nat : Type.

Implicit Type X Y : Atom.
Implicit Type x : Atom + nat.

Inductive formula := var (_ : Atom + nat) | wedge (_ _ : formula) | top | frl (_ : Atom) (_ : formula).
Infix "∧" := wedge (at level 35).
Notation "'𝖳'" := top.
Notation "∀" := frl.
Notation "'dvar' n" := (var (inr n)) (at level 31).

Coercion avar := fun X => var (inl X).

Fixpoint fsize A := S
match A with
| B ∧ C => fsize B + fsize C
| ∀ X B => fsize B
| _ => 0
end.

(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| var (inl Y) => if Nat.eq_dec Y X then F else var (inl Y)
| B ∧ C => (subs X F B) ∧ (subs X F C)
| ∀ Y B => ∀ Y (if Nat.eq_dec Y X then B else subs X F B)
| _ => A
end.

Lemma fsize_subs_var X x A : fsize (subs X (var x) A) = fsize A.
Proof.
induction A as [ [ Y | n ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn; try reflexivity.
- destruct (Nat.eq_dec Y X); reflexivity.
- cbn. rewrite IHA1, IHA2. reflexivity.
- destruct (Nat.eq_dec Y X); [ | rewrite IHA ]; reflexivity.
Qed.

(** free variables *)
Fixpoint freevars A :=
match A with
| var (inl X) => [X]
| B ∧ C => (freevars B) ++ (freevars C)
| ∀ X B => remove Nat.eq_dec X (freevars B)
| _ => []
end.
Notation closed A := (freevars A = []).

Lemma nfree_subs X F A : ~ In X (freevars A) -> subs X F A = A.
Proof.
induction A as [ [ Y | n ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn; intro Hnf; try reflexivity.
- destruct (Nat.eq_dec Y X); [ | reflexivity ].
  contradiction Hnf. left. assumption.
- rewrite IHA1, IHA2; [ reflexivity | | ].
  + intro Hf. apply Hnf, in_or_app. right. assumption.
  + intro Hf. apply Hnf, in_or_app. left. assumption.
- destruct (Nat.eq_dec Y X); [ reflexivity | ].
  rewrite IHA; [ reflexivity | ].
  intro Hf. apply Hnf. apply in_in_remove; [ symmetry | ]; assumption.
Qed.

(** substitutes [formula] [F] for index [n] in [formula] [A] and decreases indexes above [n] *)
Fixpoint nsubs n F A :=
match A with
| dvar k => match n ?= k with
            | Eq => F
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| B ∧ C => (nsubs n F B) ∧ (nsubs n F C)
| ∀ X B => ∀ X (nsubs n F B)
| _ => A
end.

Lemma nsubs_subs_com X F n G (Hin : ~ In X (freevars G)) A :
  nsubs n G (subs X F A) = subs X (nsubs n G F) (nsubs n G A).
Proof.
induction A as [ [ Y | m ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn; try reflexivity.
- destruct (Nat.eq_dec Y X); reflexivity.
- destruct (n ?= m); [ | reflexivity .. ].
  now rewrite nfree_subs.
- rewrite IHA1, IHA2. reflexivity.
- destruct (Nat.eq_dec Y X); [ | rewrite IHA ]; reflexivity.
Qed.

Lemma freevars_nsubs n F (Hc : closed F) A : freevars (nsubs n F A) = freevars A.
Proof.
induction A as [ [ Y | m ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn; try reflexivity.
- now destruct (n ?= m).
- rewrite IHA1, IHA2. reflexivity.
- rewrite IHA. reflexivity.
Qed.

(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| dvar n => if n <? k then dvar n else dvar (S n)
| B ∧ C => (fup k B) ∧ (fup k C)
| ∀ X B => ∀ X (fup k B)
| _ => A
end.
Notation fupz := (fup 0).

Lemma fsize_fup k A : fsize (fup k A) = fsize A.
Proof.
induction A as [ [ X | n ] | A1 IHA1 A2 IHA2 | | X A IHA ]; cbn; try reflexivity.
- destruct k; [ | destruct (n <=? k)]; reflexivity.
- rewrite IHA1, IHA2. reflexivity.
- rewrite IHA. reflexivity.
Qed.

Lemma freevars_fup k A : freevars (fup k A) = freevars A.
Proof.
induction A as [ [ X | n ] | A1 IHA1 A2 IHA2 | | X A IHA ]; cbn; try reflexivity.
- destruct k; [ | destruct (n <=? k) ]; reflexivity.
- rewrite IHA1, IHA2. reflexivity.
- rewrite IHA. reflexivity.
Qed.

Lemma fup_fupz_com k A : fup (S k) (fupz A) = fupz (fup k A).
Proof.
induction A as [ [ X | n ] | A1 IHA1 A2 IHA2 | | X A IHA ]; cbn; try reflexivity.
- destruct k; [ | destruct (n <=? k) ]; reflexivity.
- rewrite IHA1, IHA2. reflexivity.
- rewrite IHA. reflexivity.
Qed.

Lemma fup_subs_com k X F A : fup k (subs X F A) = subs X (fup k F) (fup k A).
Proof.
induction A as [ [ Y | n ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn.
- destruct (Nat.eq_dec Y X); reflexivity.
- destruct k; [ | destruct (n <=? k) ]; reflexivity.
- rewrite IHA1, IHA2. reflexivity.
- reflexivity.
- destruct (Nat.eq_dec Y X); [ | rewrite IHA ]; reflexivity.
Qed.

Lemma nsubs_fupz_com k F A : nsubs (S k) (fupz F) (fupz A) = fupz (nsubs k F A).
Proof.
induction A as [ [ Y | n ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn; try reflexivity.
- cbn. case_eq (k ?= n); try reflexivity.
  intros Hkn%Compare_dec.nat_compare_Lt_lt.
  cbn. do 2 f_equal. lia.
- rewrite IHA1, IHA2. reflexivity.
- rewrite IHA. reflexivity.
Qed.

Lemma nsubs_z_fup F A : nsubs 0 F (fupz A) = A.
Proof.
induction A as [ [ Y | n ] | A1 IHA1 A2 IHA2 | | Y A IHA ]; cbn; try reflexivity.
- rewrite IHA1, IHA2. reflexivity.
- rewrite IHA. reflexivity.
Qed.


(** * Proofs *)

Reserved Notation "A ⊢ B" (at level 65).
Inductive iwll2 : crelation formula :=
| ax A : A ⊢ A (* PAUSE *)
| wr A B C : C ⊢ A -> C ⊢ B -> C ⊢ A ∧ B
| wl1 B A C : A ⊢ C -> A ∧ B ⊢ C
| wl2 B A C : A ⊢ C -> B ∧ A ⊢ C
| tr C : C ⊢ 𝖳
| fr X A C : fupz C ⊢ subs X (dvar 0) (fupz A) -> C ⊢ frl X A
| fl B X A C : closed B -> subs X B A ⊢ C -> frl X A ⊢ C
where "A ⊢ B" := (iwll2 A B).
Arguments ax {_}, _.
Arguments wl1 [_ _ _] _, _ [_ _] _.
Arguments wl2 [_ _ _] _, _ [_ _] _.
Arguments tr {_}, _.
Arguments fr [_ _ _] _, _ [_ _] _.
Arguments fl [_ _ _ _] _ _.

Fixpoint pweight A B (pi : A ⊢ B) := S
match pi with
| ax | tr => 0
| wr pi1 pi2 => max (pweight pi1) (pweight pi2)
| wl1 pi1 | wl2 pi1 | fr pi1 | fl _ pi1 => pweight pi1
end.

(** lift indexes above [k] in proof [pi] *)
Lemma pup k A B (pi : A ⊢ B) : { pi' : fup k A ⊢ fup k B | pweight pi' = pweight pi }.
Proof.
induction pi in k |- *;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- exists ax. reflexivity.
- exists (wr pi1' pi2'). cbn. lia.
- exists (wl1 pi'). cbn. lia.
- exists (wl2 pi'). cbn. lia.
- exists tr. cbn. lia.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rewrite fup_subs_com, ! fup_fupz_com. cbn. intro pi'.
  exists (fr pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. rewrite fup_subs_com. intro pi'.
  exists (fl e pi'). cbn. lia.
Qed.

(** substitutes [formula] [F] for index [k] in proof [pi] and decreases indexes above [k] *)
Lemma psubs k F (Hc : closed F) A B (pi : A ⊢ B) :
  { pi' : nsubs k F A  ⊢ nsubs k F B | pweight pi' = pweight pi }.
Proof.
induction pi in k, F, Hc |- *;
  try (destruct (IHpi k F Hc) as [pi' Hs]);
  try (destruct (IHpi1 k F Hc) as [pi1' Hs1]);
  try (destruct (IHpi2 k F Hc) as [pi2' Hs2]).
- exists ax. reflexivity.
- exists (wr pi1' pi2'). cbn. lia.
- exists (wl1 pi'). cbn. lia.
- exists (wl2 pi'). cbn. lia.
- exists tr. cbn. lia.
- clear pi' Hs.
  rewrite <- (freevars_fup 0) in Hc.
  destruct (IHpi (S k) _ Hc) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'. rewrite nsubs_subs_com, ! nsubs_fupz_com by (rewrite Hc; intros []). intro pi'.
  exists (fr pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  revert pi'. rewrite nsubs_subs_com by (rewrite Hc; intros []). intro pi'.
  assert (closed (nsubs k F B)) as Hc' by (rewrite freevars_nsubs; assumption).
    exists (fl Hc' pi'). cbn. lia.
Qed.


(** * Cut *)

Lemma cut A B C : A ⊢ B -> B ⊢ C -> A ⊢ C.
Proof.
intros pi1 pi2.
remember (pweight pi1 + pweight pi2) as n eqn:Hn.
induction n as [n IHn] in A, B, C, pi1, pi2, Hn |- * using (well_founded_induction_type lt_wf). subst n.
assert (forall A' B' C' (pi1' : A' ⊢ B') (pi2' : B' ⊢ C'),
          pweight pi1' + pweight pi2' < pweight pi1 + pweight pi2 -> A' ⊢ C') as IH; [ | clear IHn ].
{ intros A' B' C' pi1' pi2' Hn. exact (IHn _ Hn _ _ _ pi1' pi2' eq_refl). }
destruct pi2 as [ | ? A' B' pi2_1 pi2_2 | B' A' ? pi2 | B' A' ? pi2 | | ? A' ? pi2 | ? X A' ? Hc2 pi2 ].
- assumption.
- apply wr.
  + apply (IH _ _ _ pi1 pi2_1). cbn. lia.
  + apply (IH _ _ _ pi1 pi2_2). cbn. lia.
- cbn in IH. remember (A' ∧ B') as C' eqn:HC.
  destruct pi1 as [ | ? ? ? pi1_1 pi1_2 | ? ? ? pi1 | ? ? ? pi1 | | ? ? ? pi1 | ? ? ? ? Hc1 pi1 ];
    destr_eq HC; subst.
  + apply wl1. assumption.
  + apply (IH _ _ _ pi1_1 pi2). cbn. lia.
  + apply wl1. apply (IH _ _ _ pi1 (wl1 pi2)). cbn. lia.
  + apply wl2. apply (IH _ _ _ pi1 (wl1 pi2)). cbn. lia.
  + apply (fl Hc1). apply (IH _ _ _ pi1 (wl1 pi2)). cbn. lia.
- cbn in IH. remember (B' ∧ A') as C' eqn:HC.
  destruct pi1 as [ | ? ? ? pi1_1 pi1_2 | ? ? ? pi1 | ? ? ? pi1 | | ? ? ? pi1 | ? ? ? ? Hc1 pi1 ];
    destr_eq HC; subst.
  + apply wl2. assumption.
  + apply (IH _ _ _ pi1_2 pi2). cbn. lia.
  + apply wl1. apply (IH _ _ _ pi1 (wl2 pi2)). cbn. lia.
  + apply wl2. apply (IH _ _ _ pi1 (wl2 pi2)). cbn. lia.
  + apply (fl Hc1). apply (IH _ _ _ pi1 (wl2 pi2)). cbn. lia.
- apply tr.
- apply fr.
  destruct (pup 0 pi1) as [pi1' Hs].
  apply (IH _ _ _ pi1' pi2). cbn. lia.
- cbn in IH. remember (∀ X A') as C' eqn:HC.
  destruct pi1 as [ | ? ? ? pi1_1 pi1_2 | ? ? ? pi1 | ? ? ? pi1 | | ? ? ? pi1 | ? ? ? ? Hc1 pi1 ];
    destr_eq HC; subst.
  + apply (fl Hc2). assumption.
  + apply wl1. apply (IH _ _ _ pi1 (fl Hc2 pi2)). cbn. lia.
  + apply wl2. apply (IH _ _ _ pi1 (fl Hc2 pi2)). cbn. lia.
  + destruct (psubs 0 _ Hc2 pi1) as [pi1' Hs].
    revert pi1' Hs. rewrite nsubs_subs_com by (rewrite Hc2; intros []). cbn. rewrite !nsubs_z_fup. intros pi1' Hs.
    apply (IH _ _ _ pi1' pi2). cbn. lia.
  + apply (fl Hc1). apply (IH _ _ _ pi1 (fl Hc2 pi2)). cbn. lia.
Qed.


(** * Axiom expansion *)

Reserved Notation "A ⊩ B" (at level 65).
Inductive iwll2at : crelation formula :=
| ax_at x : var x ⊩ var x
| wr_at A B C : C ⊩ A -> C ⊩ B -> C ⊩ A ∧ B
| wl1_at B A C : A ⊩ C -> A ∧ B ⊩ C
| wl2_at B A C : A ⊩ C -> B ∧ A ⊩ C
| tr_at C : C ⊩ 𝖳
| fr_at X A C : fupz C ⊩ subs X (dvar 0) (fupz A) -> C ⊩ frl X A
| fl_at B X A C : closed B -> subs X B A ⊩ C -> frl X A ⊩ C
where "A ⊩ B" := (iwll2at A B).

Lemma ax_gen A : A ⊩ A.
Proof.
remember (fsize A) as n eqn:Hn.
induction n as [ n IH ] in A, Hn |- * using (well_founded_induction_type lt_wf). subst n.
destruct A as [ x | A1 A2 | | X A ].
- apply ax_at.
- apply wr_at; [ apply wl1_at | apply wl2_at ]; (eapply IH; [ | reflexivity ]); cbn; lia.
- apply tr_at.
- apply fr_at. cbn. apply (@fl_at (dvar 0)); [ reflexivity | ].
  apply (IH (fsize A)); [ cbn; lia | ]. rewrite fsize_subs_var, fsize_fup. reflexivity.
Qed.

Lemma axiom_expansion A B : A ⊢ B <=> A ⊩ B.
Proof.
split; intro pi; induction pi; try now constructor.
- apply ax_gen.
- apply (fl_at _ _ _ e). assumption.
- apply (fl e). assumption.
Qed.

Lemma cut_at A B C : A ⊩ B -> B ⊩ C -> A ⊩ C.
Proof. intros pi1%axiom_expansion pi2%axiom_expansion. apply axiom_expansion. apply (cut pi1 pi2). Qed.


Instance iwll2at_preorder : PreOrder iwll2at.
Proof. split; [ exact ax_gen | exact cut_at ]. Qed.
