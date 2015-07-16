(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of definitions and theorems that are
    used throughout the development.  It complements the Coq standard
    library. *)

Require Export ZArith.
Require Import Znumtheory.
Require Export List.
Require Export Bool.
Require Import Wf_nat.
Require Import Psatz.
Require Import CoqListFacts.

(***

(** * Logical axioms *)

(** We use two logical axioms that are not provable in Coq but consistent
  with the logic: function extensionality and proof irrelevance.
  These are used in the memory model to show that two memory states
  that have identical contents are equal. *)

Axiom extensionality:
  forall (A B: Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Axiom proof_irrelevance:
  forall (P: Prop) (p1 p2: P), p1 = p2.
***)

(** * Useful tactics *)

Ltac inv H := inversion H; clear H; subst.

Ltac predSpec pred predspec x y :=
  generalize (predspec x y); case (pred x y); intro.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Ltac destructEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; destruct name; intro.

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac byContradiction :=
  cut False; [contradiction|idtac].

Ltac omegaContradiction :=
  cut False; [contradiction|omega].

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

Ltac destruct_if :=
match goal with
| H: context [(if ?lk then _ else _)] |- _ =>
   remember lk as R; destruct R; try inv H
| H: context [if ?lk then _ else _] |- _ =>
   remember lk as R; destruct R; try inv H
| |- context [(if ?lk then _ else _)] =>
   remember lk as R; destruct R; subst; auto
| |- context [if ?lk then _ else _] => remember lk as R; destruct R; subst; auto
end.

(** * Definitions and theorems over the type [positive] *)

Definition peq (x y: positive): {x = y} + {x <> y}.
Proof.
  intros. caseEq (Pcompare x y Eq).
  intro. left. apply Pcompare_Eq_eq; auto.
  intro. right. red. intro. subst y. rewrite (Pcompare_refl x) in H. discriminate.
  intro. right. red. intro. subst y. rewrite (Pcompare_refl x) in H. discriminate.
Qed.

Lemma peq_true:
  forall (A: Type) (x: positive) (a b: A), (if peq x x then a else b) = a.
Proof.
  intros. case (peq x x); intros.
  auto.
  elim n; auto.
Qed.

Lemma peq_false:
  forall (A: Type) (x y: positive) (a b: A), x <> y -> (if peq x y then a else b) = b.
Proof.
  intros. case (peq x y); intros.
  elim H; auto.
  auto.
Qed.

Definition Plt (x y: positive): Prop := Zlt (Zpos x) (Zpos y).

Lemma Plt_ne:
  forall (x y: positive), Plt x y -> x <> y.
Proof.
  unfold Plt; intros. red; intro. subst y. omega.
Qed.
Hint Resolve Plt_ne: coqlib.

Lemma Plt_trans:
  forall (x y z: positive), Plt x y -> Plt y z -> Plt x z.
Proof.
  unfold Plt; intros; omega.
Qed.

Remark Psucc_Zsucc:
  forall (x: positive), Zpos (Psucc x) = Zsucc (Zpos x).
Proof.
  intros. rewrite Pplus_one_succ_r.
  reflexivity.
Qed.

Lemma Plt_succ:
  forall (x: positive), Plt x (Psucc x).
Proof.
  intro. unfold Plt. rewrite Psucc_Zsucc. omega.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_trans_succ:
  forall (x y: positive), Plt x y -> Plt x (Psucc y).
Proof.
  intros. apply Plt_trans with y. assumption. apply Plt_succ.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_succ_inv:
  forall (x y: positive), Plt x (Psucc y) -> Plt x y \/ x = y.
Proof.
  intros x y. unfold Plt. rewrite Psucc_Zsucc.
  intro. assert (A: (Zpos x < Zpos y)%Z \/ Zpos x = Zpos y). omega.
  elim A; intro. left; auto. right; injection H0; auto.
Qed.

Definition plt (x y: positive) : {Plt x y} + {~ Plt x y}.
Proof.
 intros. unfold Plt. apply Z_lt_dec.
Qed.

Definition Ple (p q: positive) := Zle (Zpos p) (Zpos q).

Lemma Ple_refl: forall (p: positive), Ple p p.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Ple_trans: forall (p q r: positive), Ple p q -> Ple q r -> Ple p r.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Plt_Ple: forall (p q: positive), Plt p q -> Ple p q.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Lemma Ple_succ: forall (p: positive), Ple p (Psucc p).
Proof.
  intros. apply Plt_Ple. apply Plt_succ.
Qed.

Lemma Plt_Ple_trans:
  forall (p q r: positive), Plt p q -> Ple q r -> Plt p r.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Lemma Plt_strict: forall p, ~ Plt p p.
Proof.
  unfold Plt; intros. omega.
Qed.

Hint Resolve Ple_refl Plt_Ple Ple_succ Plt_strict: coqlib.

(** Peano recursion over positive numbers. *)

Section POSITIVE_ITERATION.

Lemma Plt_wf: well_founded Plt.
Proof.
  apply well_founded_lt_compat with nat_of_P.
  intros. apply nat_of_P_lt_Lt_compare_morphism. exact H.
Qed.

Variable A: Type.
Variable v1: A.
Variable f: positive -> A -> A.

Lemma Ppred_Plt:
  forall x, x <> xH -> Plt (Ppred x) x.
Proof.
  intros. elim (Psucc_pred x); intro. contradiction.
  set (y := Ppred x) in *. rewrite <- H0. apply Plt_succ.
Qed.

Let iter (x: positive) (P: forall y, Plt y x -> A) : A :=
  match peq x xH with
  | left EQ => v1
  | right NOTEQ => f (Ppred x) (P (Ppred x) (Ppred_Plt x NOTEQ))
  end.

Definition positive_rec : positive -> A :=
  Fix Plt_wf (fun _ => A) iter.

Lemma unroll_positive_rec:
  forall x,
  positive_rec x = iter x (fun y _ => positive_rec y).
Proof.
  unfold positive_rec. apply (Fix_eq Plt_wf (fun _ => A) iter).
  intros. unfold iter. case (peq x 1); intro. auto. decEq. apply H.
Qed.

Lemma positive_rec_base:
  positive_rec 1%positive = v1.
Proof.
  rewrite unroll_positive_rec. unfold iter. case (peq 1 1); intro.
  auto. elim n; auto.
Qed.

Lemma positive_rec_succ:
  forall x, positive_rec (Psucc x) = f x (positive_rec x).
Proof.
  intro. rewrite unroll_positive_rec. unfold iter.
  case (peq (Psucc x) 1); intro.
  destruct x; simpl in e; discriminate.
  rewrite Ppred_succ. auto.
Qed.

Lemma positive_Peano_ind:
  forall (P: positive -> Prop),
  P xH ->
  (forall x, P x -> P (Psucc x)) ->
  forall x, P x.
Proof.
  intros.
  apply (well_founded_ind Plt_wf P).
  intros.
  case (peq x0 xH); intro.
  subst x0; auto.
  elim (Psucc_pred x0); intro. contradiction. rewrite <- H2.
  apply H0. apply H1. apply Ppred_Plt. auto.
Qed.

End POSITIVE_ITERATION.

(** * Definitions and theorems over the type [Z] *)

Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z_eq_dec.

Lemma zeq_true:
  forall (A: Type) (x: Z) (a b: A), (if zeq x x then a else b) = a.
Proof.
  intros. case (zeq x x); intros.
  auto.
  elim n; auto.
Qed.

Lemma zeq_false:
  forall (A: Type) (x y: Z) (a b: A), x <> y -> (if zeq x y then a else b) = b.
Proof.
  intros. case (zeq x y); intros.
  elim H; auto.
  auto.
Qed.

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_ge_dec.

Lemma zlt_true:
  forall (A: Type) (x y: Z) (a b: A),
  x < y -> (if zlt x y then a else b) = a.
Proof.
  intros. case (zlt x y); intros.
  auto.
  omegaContradiction.
Qed.

Lemma zlt_false:
  forall (A: Type) (x y: Z) (a b: A),
  x >= y -> (if zlt x y then a else b) = b.
Proof.
  intros. case (zlt x y); intros.
  omegaContradiction.
  auto.
Qed.

Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.

Lemma zle_true:
  forall (A: Type) (x y: Z) (a b: A),
  x <= y -> (if zle x y then a else b) = a.
Proof.
  intros. case (zle x y); intros.
  auto.
  omegaContradiction.
Qed.

Lemma zle_false:
  forall (A: Type) (x y: Z) (a b: A),
  x > y -> (if zle x y then a else b) = b.
Proof.
  intros. case (zle x y); intros.
  omegaContradiction.
  auto.
Qed.

(** Properties of powers of two. *)

Lemma two_power_nat_O : two_power_nat O = 1.
Proof. reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n. rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. omega.
Qed.

Lemma two_power_nat_two_p:
  forall x, two_power_nat x = two_p (Z_of_nat x).
Proof.
  induction x. auto.
  rewrite two_power_nat_S. rewrite inj_S. rewrite two_p_S. omega. omega.
Qed.

Lemma two_p_monotone:
  forall x y, 0 <= x <= y -> two_p x <= two_p y.
Proof.
  intros.
  replace (two_p x) with (two_p x * 1) by omega.
  replace y with (x + (y - x)) by omega.
  rewrite two_p_is_exp; try omega.
  apply Zmult_le_compat_l.
  assert (two_p (y - x) > 0). apply two_p_gt_ZERO. omega. omega.
  assert (two_p x > 0). apply two_p_gt_ZERO. omega. omega.
Qed.

Lemma two_p_monotone_strict:
  forall x y, 0 <= x < y -> two_p x < two_p y.
Proof.
  intros. assert (two_p x <= two_p (y - 1)). apply two_p_monotone; omega.
  assert (two_p (y - 1) > 0). apply two_p_gt_ZERO. omega.
  replace y with (Zsucc (y - 1)) by omega. rewrite two_p_S. omega. omega.
Qed.

Lemma two_p_strict:
  forall x, x >= 0 -> x < two_p x.
Proof.
  intros x0 GT. pattern x0. apply natlike_ind.
  simpl. omega.
  intros. rewrite two_p_S; auto. generalize (two_p_gt_ZERO x H). omega.
  omega.
Qed.

Lemma two_p_strict_2:
  forall x, x >= 0 -> 2 * x - 1 < two_p x.
Proof.
  intros. assert (x = 0 \/ x - 1 >= 0) by omega. destruct H0.
  subst. vm_compute. auto.
  replace (two_p x) with (2 * two_p (x - 1)).
  generalize (two_p_strict _ H0). omega.
  rewrite <- two_p_S. decEq. omega. omega.
Qed.

(** Properties of [Zmin] and [Zmax] *)

Lemma Zmin_spec:
  forall x y, Zmin x y = if zlt x y then x else y.
Proof.
  intros. case (zlt x y); unfold Zlt, Zge; intros.
  unfold Zmin. rewrite l. auto.
  unfold Zmin. caseEq (x ?= y); intro.
  apply Zcompare_Eq_eq. auto.
  contradiction.
  reflexivity.
Qed.

Lemma Zmax_spec:
  forall x y, Zmax x y = if zlt y x then x else y.
Proof.
  intros. case (zlt y x); unfold Zlt, Zge; intros.
  unfold Zmax. rewrite <- (Zcompare_antisym y x).
  rewrite l. simpl. auto.
  unfold Zmax. rewrite <- (Zcompare_antisym y x).
  caseEq (y ?= x); intro; simpl.
  symmetry. apply Zcompare_Eq_eq. auto.
  contradiction. reflexivity.
Qed.

Lemma Zmax_bound_l:
  forall x y z, x <= y -> x <= Zmax y z.
Proof.
  intros. generalize (Zmax1 y z). omega.
Qed.
Lemma Zmax_bound_r:
  forall x y z, x <= z -> x <= Zmax y z.
Proof.
  intros. generalize (Zmax2 y z). omega.
Qed.

(** Properties of Euclidean division and modulus. *)

Lemma Zdiv_small:
  forall x y, 0 <= x < y -> x / y = 0.
Proof.
  intros. assert (y > 0). omega.
  assert (forall a b,
    0 <= a < y ->
    0 <= y * b + a < y ->
    b = 0).
  intros.
  assert (b = 0 \/ b > 0 \/ (-b) > 0). omega.
  elim H3; intro.
  auto.
  elim H4; intro.
  assert (y * b >= y * 1). apply Zmult_ge_compat_l. omega. omega.
  omegaContradiction.
  assert (y * (-b) >= y * 1). apply Zmult_ge_compat_l. omega. omega.
  rewrite <- Zopp_mult_distr_r in H6. omegaContradiction.
  apply H1 with (x mod y).
  apply Z_mod_lt. auto.
  rewrite <- Z_div_mod_eq. auto. auto.
Qed.

Lemma Zmod_small:
  forall x y, 0 <= x < y -> x mod y = x.
Proof.
  intros. assert (y > 0). omega.
  generalize (Z_div_mod_eq x y H0).
  rewrite (Zdiv_small x y H). omega.
Qed.

Lemma Zmod_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof.
  intros. subst x. rewrite Zplus_comm.
  rewrite Z_mod_plus. apply Zmod_small. auto. omega.
Qed.

Lemma Zdiv_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x / y = a.
Proof.
  intros. subst x. rewrite Zplus_comm.
  rewrite Z_div_plus. rewrite (Zdiv_small b y H0). omega. omega.
Qed.

Lemma Zdiv_Zdiv:
  forall a b c,
  b > 0 -> c > 0 -> (a / b) / c = a / (b * c).
Proof.
  intros.
  generalize (Z_div_mod_eq a b H). generalize (Z_mod_lt a b H). intros.
  generalize (Z_div_mod_eq (a/b) c H0). generalize (Z_mod_lt (a/b) c H0). intros.
  set (q1 := a / b) in *. set (r1 := a mod b) in *.
  set (q2 := q1 / c) in *. set (r2 := q1 mod c) in *.
  symmetry. apply Zdiv_unique with (r2 * b + r1).
  rewrite H2. rewrite H4. ring.
  split.
  assert (0 <= r2 * b). apply Zmult_le_0_compat. omega. omega. omega.
  assert ((r2 + 1) * b <= c * b).
  apply Zmult_le_compat_r. omega. omega.
  replace ((r2 + 1) * b) with (r2 * b + b) in H5 by ring.
  replace (c * b) with (b * c) in H5 by ring.
  omega.
Qed.

Lemma Zmult_le_compat_l_neg :
  forall n m p:Z, n >= m -> p <= 0 -> p * n <= p * m.
Proof.
  intros.
  assert ((-p) * n >= (-p) * m). apply Zmult_ge_compat_l. auto. omega.
  replace (p * n) with (- ((-p) * n)) by ring.
  replace (p * m) with (- ((-p) * m)) by ring.
  omega.
Qed.

Lemma Zdiv_interval_1:
  forall lo hi a b,
  lo <= 0 -> hi > 0 -> b > 0 ->
  lo * b <= a < hi * b ->
  lo <= a/b < hi.
Proof.
  intros.
  generalize (Z_div_mod_eq a b H1). generalize (Z_mod_lt a b H1). intros.
  set (q := a/b) in *. set (r := a mod b) in *.
  split.
  assert (lo < (q + 1)).
  apply Zmult_lt_reg_r with b. omega.
  apply Zle_lt_trans with a. omega.
  replace ((q + 1) * b) with (b * q + b) by ring.
  omega.
  omega.
  apply Zmult_lt_reg_r with b. omega.
  replace (q * b) with (b * q) by ring.
  omega.
Qed.

Lemma Zdiv_interval_2:
  forall lo hi a b,
  lo <= a <= hi -> lo <= 0 -> hi >= 0 -> b > 0 ->
  lo <= a/b <= hi.
Proof.
  intros.
  assert (lo <= a / b < hi+1).
  apply Zdiv_interval_1. omega. omega. auto.
  assert (lo * b <= lo * 1). apply Zmult_le_compat_l_neg. omega. omega.
  replace (lo * 1) with lo in H3 by ring.
  assert ((hi + 1) * 1 <= (hi + 1) * b). apply Zmult_le_compat_l. omega. omega.
  replace ((hi + 1) * 1) with (hi + 1) in H4 by ring.
  omega.
  omega.
Qed.

Lemma Zmod_recombine:
  forall x a b,
  a > 0 -> b > 0 ->
  x mod (a * b) = ((x/b) mod a) * b + (x mod b).
Proof.
  intros.
  set (xb := x/b).
  apply Zmod_unique with (xb/a).
  generalize (Z_div_mod_eq x b H0); fold xb; intro EQ1.
  generalize (Z_div_mod_eq xb a H); intro EQ2.
  rewrite EQ2 in EQ1.
  eapply trans_eq. eexact EQ1. ring.
  generalize (Z_mod_lt x b H0). intro.
  generalize (Z_mod_lt xb a H). intro.
  assert (0 <= xb mod a * b <= a * b - b).
    split. apply Zmult_le_0_compat; omega.
    replace (a * b - b) with ((a - 1) * b) by ring.
    apply Zmult_le_compat; omega.
  omega.
Qed.

(** Properties of divisibility. *)

Lemma Zdivides_trans:
  forall x y z, (x | y) -> (y | z) -> (x | z).
Proof.
  intros. inv H. inv H0. exists (x1 * x0). ring.
Qed.

Definition Zdivide_dec:
  forall (p q: Z), p > 0 -> { (p|q) } + { ~(p|q) }.
Proof.
  intros. destruct (zeq (Zmod q p) 0).
  left. exists (q / p).
  transitivity (p * (q / p) + (q mod p)). apply Z_div_mod_eq; auto.
  transitivity (p * (q / p)). omega. ring.
  right; red; intros. elim n. apply Z_div_exact_1; auto.
  inv H0. rewrite Z_div_mult; auto. ring.
Qed.

(** Conversion from [Z] to [nat]. *)

Definition nat_of_Z (z: Z) : nat :=
  match z with
  | Z0 => O
  | Zpos p => nat_of_P p
  | Zneg p => O
  end.

Lemma nat_of_Z_max:
  forall z, Z_of_nat (nat_of_Z z) = Zmax z 0.
Proof.
  intros. unfold Zmax. destruct z; simpl; auto.
  symmetry. apply Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Lemma nat_of_Z_eq:
  forall z, z >= 0 -> Z_of_nat (nat_of_Z z) = z.
Proof.
  intros. rewrite nat_of_Z_max. apply Zmax_left. auto.
Qed.

Lemma nat_of_Z_neg:
  forall n, n <= 0 -> nat_of_Z n = O.
Proof.
  destruct n; unfold Zle; simpl; auto. congruence.
Qed.

Lemma nat_of_Z_plus:
  forall p q,
  p >= 0 -> q >= 0 ->
  nat_of_Z (p + q) = (nat_of_Z p + nat_of_Z q)%nat.
Proof.
  intros.
  apply inj_eq_rev. rewrite inj_plus.
  repeat rewrite nat_of_Z_eq; auto. omega.
Qed.

Lemma nat_of_Z_inj_ge : forall a b, (a >= b)%Z ->
  (nat_of_Z a >= nat_of_Z b)%nat.
Proof.
  induction a; destruct b; intros; simpl;
    try solve [auto | contradict H; auto | omega].
  apply nat_compare_le.
  rewrite <- nat_of_P_compare_morphism.

  assert (p >= p0)%positive as J. auto with zarith.
  unfold Pge in J.
  remember ((p0 ?= p)%positive) as R.
  destruct R; try solve [congruence].
  symmetry in HeqR. apply Pos.compare_nle_iff in HeqR.
  contradict HeqR.
  apply Pos.compare_ge_iff in J. auto.
Qed.

Lemma nat_of_Z_inj_gt : forall a b, (a > b)%Z -> (b >= 0)%Z ->
  (nat_of_Z a > nat_of_Z b)%nat.
Proof.
  induction a; destruct b; intros; simpl;
    try solve [auto | contradict H; auto | omega].

  assert (J:=@ZL4 p).
  destruct J as [h J]. rewrite J. omega.

  apply nat_compare_lt.
  rewrite <- nat_of_P_compare_morphism.
  assert (p > p0)%positive as J. auto with zarith.
  unfold Pgt in J.
  remember ((p ?= p0)%positive) as R.
  destruct R; try solve [congruence].
    symmetry in HeqR. apply ZC1 in HeqR. rewrite HeqR. congruence.

  apply Zgt_compare in H. inversion H.
Qed.

Lemma S_eq_nat_of_P_o_P_of_succ_nat :
  forall n, S n = nat_of_P (P_of_succ_nat n).
Proof.
  induction n; auto.
    simpl. rewrite nat_of_P_succ_morphism. rewrite IHn. auto.
Qed.

Lemma Z_of_nat_eq:
  forall (n:nat), nat_of_Z (Z_of_nat n) = n.
Proof.
  induction n; auto.
    simpl. rewrite <- S_eq_nat_of_P_o_P_of_succ_nat; auto.
Qed.

Lemma Z_of_Sn_add_z__eq__Z_of_n_add_sz : forall n z,
  Z_of_nat (S n) + z = Z_of_nat n + Zsucc z.
Proof.
  intros. rewrite inj_S. auto with zarith.
Qed.

Lemma O_lt_Z_of_S : forall n, 0 < Z_of_nat (S n).
Proof.
  intros. rewrite <- inj_0. apply inj_lt. omega.
Qed.

Lemma Z_of_S_gt_O : forall n, Z_of_nat (S n) > 0.
Proof.
  intros.
  assert (J:=@O_lt_Z_of_S n).
  auto with zarith.
Qed.

Lemma nat_of_Z_pos:
  forall n, n > 0 -> (nat_of_Z n > O)%nat.
Proof.
  intros.
  destruct n; unfold Zle; simpl; try omega.
    assert (J:=@lt_O_nat_of_P p). auto.

    assert (J:=@Zlt_neg_0 p).
    contradict H; omega.
Qed.

Lemma nat_of_Z_inj : forall z1 z2,
  z1 >= 0 ->
  z2 >= 0 ->
  nat_of_Z z1 = nat_of_Z z2 ->
  z1 = z2.
Proof.
  induction z1; destruct z2; intros H H0 H1;
  try solve [
    auto |
    assert (J:=@Zlt_neg_0 p); contradict H; omega |
    assert (J:=@Zlt_neg_0 p0); contradict H0; omega |
    simpl in H1;
    assert (J:=@lt_O_nat_of_P p);
    rewrite <- H1 in J; contradict J; omega
    ].

    simpl in H1.
    apply nat_of_P_inj in H1.
    subst. auto.
Qed.

Lemma Zpos_P_of_succ_nat_mono : forall m n,
  (m <= n)%nat ->
  Zpos (P_of_succ_nat m) <= Zpos (P_of_succ_nat n).
Proof.
  induction m; destruct n; simpl; intros; auto with zarith.
    rewrite Zpos_succ_morphism. simpl.
    rewrite Zpos_plus_distr.
    assert (Zpos (P_of_succ_nat n) > 0) as F.
      auto with zarith.
    auto with zarith.

    rewrite Zpos_succ_morphism.
    rewrite Zpos_succ_morphism.
    unfold Zsucc.
    assert (Zpos (P_of_succ_nat m) <= Zpos (P_of_succ_nat n)) as J.
      apply IHm; auto with zarith.
    auto with zarith.
Qed.

(** * zdiv zmod *)

Lemma mod_prop1 : forall wz,
  Z_of_nat (S wz) mod 8 >= 0.
Proof.
  intro wz.
  destruct (Z_mod_lt (Z_of_nat (S wz)) 8);
    auto with zarith.
Qed.

Lemma zdiv_zmod_prop1 : forall a1 a2 b,
  b <> 0 ->
  a1 / b = a2 / b ->
  a1 mod b = a2 mod b ->
  a1 = a2.
Proof.
  intros.
  rewrite (@Z_div_mod_eq_full a1 b H).
  rewrite (@Z_div_mod_eq_full a2 b H).
  rewrite H0. rewrite H1.
  auto.
Qed.

(** * ZRdiv *)

Definition ZRdiv (a b:Z) : Z :=
  if zeq (a mod b) 0
  then a / b
  else a / b + 1.

Lemma ZRdiv_prop1 : forall a b, b >0 -> b * (ZRdiv a b) >= a.
Proof.
  intros. unfold ZRdiv.
  destruct (zeq (a mod b) 0).
    rewrite <- Z_div_exact_full_2; auto with zarith.

    rewrite Zmult_plus_distr_r.
    rewrite (Zmult_comm b 1) .
    rewrite Zmult_1_l.
    assert (J:=@Z_mod_lt a b H).
    assert (J':=@Z_div_mod_eq_full a b).
    auto with zarith.
Qed.

Lemma ZRdiv_prop2 : forall a b, a >=0 -> b > 0 -> ZRdiv a b >= 0.
Proof.
  intros.
  unfold ZRdiv.
  destruct (zeq (a mod b) 0).
    apply Z_div_ge0; auto.
    assert (J:=@Z_div_ge0 a b H0 H). auto with zarith.
Qed.

Lemma Zpos_Zneg_Zmul : forall a b, a > 0 -> b < 0 -> a * b < 0.
Proof.
  intros a b Ha Hb.
  destruct a as [|a|a]; try discriminate.
  destruct b as [|b|b]; try discriminate.
  trivial.
Qed.

Lemma Z_of_nat_ge_0 : forall n, Z_of_nat n >= 0.
Proof.
  induction n.
    simpl. auto with zarith.
    assert (J:=@Z_of_S_gt_O n). auto with zarith.
Qed.

Lemma two_power_nat_le_zero : forall n, two_power_nat n >= 0.
Proof.
  induction n; simpl.
    unfold two_power_nat. unfold shift_nat. simpl. auto with zarith.
    rewrite two_power_nat_S. auto with zarith.
Qed.

Lemma roundup_is_correct : forall a b, b >0 -> (a + b) / b * b >= a.
Proof.
  intros.
  assert (b<>0). auto with zarith.
  assert (J:=@Z_div_mod_eq_full (a+b) b H0).
  assert (b * ((a + b) / b) = a + b - (a + b) mod b) as EQ.
    auto with zarith.
  assert (b * ((a + b) / b) = (a + b) / b * b) as EQ'.
    auto with zarith.
  rewrite <- EQ'.
  rewrite EQ.
  assert (J1:=@Z_mod_lt a b H).
  assert (J2:=@Z_mod_plus_full a 1 b).
  rewrite Zmult_1_l in J2.
  rewrite J2.
  clear - J1.
  auto with zarith.
Qed.

Lemma ZRdiv_prop3 : forall a b, a > 0 -> b > 0 -> ZRdiv a b > 0.
Proof.
  intros.
  unfold ZRdiv.
  assert (J:=@Z_div_mod_eq a b H0).
  destruct (zeq (a mod b) 0).
    rewrite e in J.
    ring_simplify in J.
    destruct (a / b).
      ring_simplify in J.
      subst. contradict H; auto with zarith.

      auto with zarith.
      rewrite J in H.
      assert (Zneg p <0) as Hneg. unfold Zlt. simpl. auto.
      assert (b * Zneg p < 0) as J'.
        eapply Zpos_Zneg_Zmul; eauto.
      contradict J'; auto with zarith.

    assert (a / b >= 0) as J'.
      eapply Z_div_ge0; eauto with zarith.
    auto with zarith.
Qed.

Lemma ZRdiv_prop4 : forall wz,
  ZRdiv (Z_of_nat (S wz)) 8 >= 0.
Proof.
  intro.
  apply ZRdiv_prop2; try solve [auto with zarith | apply Z_of_S_gt_O].
Qed.

Lemma ZRdiv_prop5 : forall wz,
  ZRdiv (Z_of_nat (S wz)) 8 > 0.
Proof.
  intro.
  apply ZRdiv_prop3;try solve [auto with zarith].
    apply Z_of_S_gt_O.
Qed.

Lemma ZRdiv_prop6 : forall wz,
  (nat_of_Z (ZRdiv (Z_of_nat (S wz)) 8) > 0)%nat.
Proof.
  intro.
  apply nat_of_Z_pos.
  apply ZRdiv_prop5.
Qed.

Lemma ZRdiv_prop7 : forall z1 z2 (A : z1 <= z2) (C: z1 > 0),
   (if zeq (z1 mod 8) 0 then z1 / 8 else z1 / 8 + 1) <=
   (if zeq (z2 mod 8) 0 then z2 / 8 else z2 / 8 + 1).
Proof.
  intros.
  assert (z1 / 8 <= z2 / 8) as B.
    apply Z_div_le; auto with zarith.
  destruct (zeq (z1 mod 8) 0).
    destruct (zeq (z2 mod 8) 0); auto with zarith.
    destruct (zeq (z2 mod 8) 0); auto with zarith.
      assert (z1 = 8*(z1/8) + (z1 mod 8)) as Z1.
        apply Z_div_mod_eq; auto with zarith.
      assert (z2 = 8*(z2/8) + (z2 mod 8)) as Z2.
        apply Z_div_mod_eq; auto with zarith.
      rewrite e in Z2.
      assert (0 <= z1 mod 8 < 8) as D.
        apply Z_mod_lt; auto with zarith.
      destruct (Z_le_dec (z1 / 8 + 1) (z2 / 8)); auto.
        contradict A.
        rewrite Z1. rewrite Z2.
        clear Z1 Z2 e. auto with zarith.
Qed.

Lemma ZRdiv_prop8 : forall (a c:nat),
  nat_of_Z (ZRdiv (Z_of_nat (a * 8 * c)) 8) = (a * c)%nat.
Proof.
  intros.
  assert (a * 8 * c = a * c * 8)%nat as J5.
    rewrite mult_assoc_reverse.
    assert (8*c = c*8)%nat as EQ. apply mult_comm; auto.
    rewrite EQ. rewrite mult_assoc. auto.
  rewrite J5. clear J5.
  unfold ZRdiv. rewrite inj_mult. rewrite Z_mod_mult. simpl.
  rewrite Z_div_mult_full; try solve [auto with zarith].
  rewrite Z_of_nat_eq; auto.
Qed.

Lemma ZRdiv_prop9 : forall sz1 R4,
  nat_of_Z (ZRdiv (Z_of_nat (sz1 + R4 * 8)) 8) =
    (nat_of_Z (ZRdiv (Z_of_nat sz1) 8) + R4)%nat.
Proof.
  intros.
  unfold ZRdiv. rewrite inj_plus. rewrite inj_mult. simpl.
  rewrite Z_mod_plus; try solve [omega].
  rewrite Z_div_plus; try solve [omega].
  assert (Z_of_nat sz1 / 8 >= 0) as G1.
    apply Z_div_ge0; auto using Z_of_nat_ge_0 with zarith.
  assert (Z_of_nat R4 >= 0) as G2.
    apply Z_of_nat_ge_0.
  destruct (zeq (Z_of_nat sz1 mod 8) 0).
    rewrite nat_of_Z_plus; auto.
      rewrite Z_of_nat_eq; auto.

    rewrite nat_of_Z_plus; try solve [omega].
    rewrite nat_of_Z_plus; try solve [omega].
    rewrite nat_of_Z_plus; try solve [omega].
    rewrite Z_of_nat_eq; try solve [omega].
Qed.

Lemma zrdiv_zmod_prop1 : forall a1 a2 b,
  b <> 0 ->
  ZRdiv a1 b = ZRdiv a2 b ->
  a1 mod b = a2 mod b ->
  a1 = a2.
Proof.
  intros.
  unfold ZRdiv in H0.
  rewrite H1 in H0.
  destruct (zeq (a2 mod b) 0).
    eapply zdiv_zmod_prop1; eauto.
    apply zdiv_zmod_prop1 with (b:=b); auto.
      eauto with zarith.
Qed.

(** Alignment: [align n amount] returns the smallest multiple of [amount]
  greater than or equal to [n]. *)

Definition align (n: Z) (amount: Z) :=
  ((n + amount - 1) / amount) * amount.

Lemma align_le: forall x y, y > 0 -> x <= align x y.
Proof.
  intros. unfold align.
  generalize (Z_div_mod_eq (x + y - 1) y H). intro.
  replace ((x + y - 1) / y * y)
     with ((x + y - 1) - (x + y - 1) mod y).
  generalize (Z_mod_lt (x + y - 1) y H). omega.
  rewrite Zmult_comm. omega.
Qed.

Lemma align_divides: forall x y, y > 0 -> (y | align x y).
Proof.
  intros. unfold align. apply Zdivide_factor_l.
Qed.

(** * Definitions and theorems on the data types [option], [sum] and [list] *)

Set Implicit Arguments.

(** Mapping a function over an option type. *)

Definition option_map (A B: Type) (f: A -> B) (x: option A) : option B :=
  match x with
  | None => None
  | Some y => Some (f y)
  end.

(** Mapping a function over a sum type. *)

Definition sum_left_map (A B C: Type) (f: A -> B) (x: A + C) : B + C :=
  match x with
  | inl y => inl C (f y)
  | inr z => inr B z
  end.

(** Properties of [List.nth] (n-th element of a list). *)

Hint Resolve in_eq in_cons: coqlib.

Lemma nth_error_in:
  forall (A: Type) (n: nat) (l: list A) (x: A),
  List.nth_error l n = Some x -> In x l.
Proof.
  induction n; simpl.
   destruct l; intros.
    discriminate.
    injection H; intro; subst a. apply in_eq.
   destruct l; intros.
    discriminate.
    apply in_cons. auto.
Qed.
Hint Resolve nth_error_in: coqlib.

Lemma nth_error_nil:
  forall (A: Type) (idx: nat), nth_error (@nil A) idx = None.
Proof.
  induction idx; simpl; intros; reflexivity.
Qed.
Hint Resolve nth_error_nil: coqlib.

(** Compute the length of a list, with result in [Z]. *)

Fixpoint list_length_z_aux (A: Type) (l: list A) (acc: Z) {struct l}: Z :=
  match l with
  | nil => acc
  | hd :: tl => list_length_z_aux tl (Zsucc acc)
  end.

Remark list_length_z_aux_shift:
  forall (A: Type) (l: list A) n m,
  list_length_z_aux l n = list_length_z_aux l m + (n - m).
Proof.
  induction l; intros; simpl.
  omega.
  replace (n - m) with (Zsucc n - Zsucc m) by omega. auto.
Qed.

Definition list_length_z (A: Type) (l: list A) : Z :=
  list_length_z_aux l 0.

Lemma list_length_z_cons:
  forall (A: Type) (hd: A) (tl: list A),
  list_length_z (hd :: tl) = list_length_z tl + 1.
Proof.
  intros. unfold list_length_z. simpl.
  rewrite (list_length_z_aux_shift tl 1 0). omega.
Qed.

Lemma list_length_z_pos:
  forall (A: Type) (l: list A),
  list_length_z l >= 0.
Proof.
  induction l; simpl. unfold list_length_z; simpl. omega.
  rewrite list_length_z_cons. omega.
Qed.

Lemma list_length_z_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  list_length_z (map f l) = list_length_z l.
Proof.
  induction l. reflexivity. simpl. repeat rewrite list_length_z_cons. congruence.
Qed.

(** Extract the n-th element of a list, as [List.nth_error] does,
    but the index [n] is of type [Z]. *)

Fixpoint list_nth_z (A: Type) (l: list A) (n: Z) {struct l}: option A :=
  match l with
  | nil => None
  | hd :: tl => if zeq n 0 then Some hd else list_nth_z tl (Zpred n)
  end.

Lemma list_nth_z_in:
  forall (A: Type) (l: list A) n x,
  list_nth_z l n = Some x -> In x l.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct (zeq n 0). left; congruence. right; eauto.
Qed.

Lemma list_nth_z_map:
  forall (A B: Type) (f: A -> B) (l: list A) n,
  list_nth_z (List.map f l) n = option_map f (list_nth_z l n).
Proof.
  induction l; simpl; intros.
  auto.
  destruct (zeq n 0). auto. eauto.
Qed.

Lemma list_nth_z_range:
  forall (A: Type) (l: list A) n x,
  list_nth_z l n = Some x -> 0 <= n < list_length_z l.
Proof.
  induction l; simpl; intros.
  discriminate.
  rewrite list_length_z_cons. destruct (zeq n 0).
  generalize (list_length_z_pos l); omega.
  exploit IHl; eauto. unfold Zpred. omega.
Qed.

Section MoreMove. (* copied from dtree.v *)

Variable A: Type.
Hypothesis Hdec: forall x y : A, {x = y} + {x <> y}.

Lemma remove_length: forall (a: A) (l1: list A),
  (length (List.remove Hdec a l1) <= length l1)%nat.
Proof.
  induction l1; simpl; intros.
    omega.
    destruct (Hdec a a0); subst; simpl; omega.
Qed.

Lemma remove_in_length: forall (a: A) (l1: list A),
  In a l1 -> (length (List.remove Hdec a l1) < length l1)%nat.
Proof.
  induction l1; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      destruct (Hdec a a); try congruence.
      assert (J:=@remove_length a l1). omega.

      destruct (Hdec a a0); subst.
        assert (J:=@remove_length a0 l1). omega.
        assert (J:=@IHl1 H). simpl. omega.
Qed.

Lemma remove_neq_in: forall (a b:A) (l1: list A),
  a <> b ->
  In a l1 ->
  In a (List.remove Hdec b l1).
Proof.
  induction l1; simpl; intros; auto.
    destruct H0 as [H0 | H0]; subst.
      destruct (Hdec b a); subst; simpl; auto.
        congruence.
      destruct (Hdec b a0); subst; simpl; auto.
Qed.

Lemma remove_notin_incl: forall (a : A) (l2 l1 : list A)
  (Hinc : incl l1 l2) (Hnotin : ~ In a l1),
  incl l1 (List.remove Hdec a l2).
Proof.
  intros. intros x Hin.
  destruct (Hdec x a); subst.
    congruence.
    apply remove_neq_in; auto.
Qed.

Lemma remove_neq_in': forall (a b:A) (l1: list A),
  In a (List.remove Hdec b l1) ->
  In a l1 /\ a <> b.
Proof.
  induction l1; simpl; intros; auto.
    destruct (Hdec b a0); subst; simpl.
      apply IHl1 in H.
      destruct H as [H1 H2].
      split; auto.

      simpl in H.
      destruct H as [H | H]; subst; auto.
      apply IHl1 in H.
      destruct H as [H1 H2].
      split; auto.
Qed.

Lemma NoDup_remove: forall x ls2 (Hunip: NoDup ls2),
  NoDup (List.remove Hdec x ls2).
Proof.
  induction 1; simpl.
    constructor.

    destruct_if.
      constructor; auto.
        intro J. apply H.
        apply remove_neq_in' in J.
        tauto.
Qed.

Lemma NoDup_incl_inj_length: forall B f
  (ls1:list B) (Hnp1: NoDup ls1) (ls2:list A) 
  (Hincl: forall a1, In a1 ls1 -> exists b1, In b1 ls2 /\ f b1 = Some a1),
  (length ls1 <= length ls2)%nat.
Proof.
  induction 1 as [|a1 ls1]; simpl; intros.
    omega.

    assert (a1 = a1 \/ In a1 ls1) as Hina1. auto.
    assert (J:=Hina1).
    apply Hincl in J.
    destruct J as [b1 [Hinb1 Hget1]].
    assert (forall a1, In a1 ls1 -> 
              exists b1', In b1' (List.remove Hdec b1 ls2) /\ f b1' = Some a1) 
           as Hinc.
      intros a2 Hina2'.
      assert (a1 = a2 \/ In a2 ls1) as Hina2. auto.
      apply Hincl in Hina2; auto.
      destruct Hina2 as [b1' [J1 J2]].
      exists b1'.
      split; auto.
        apply remove_neq_in; auto.
          intro EQ. subst. 
          rewrite Hget1 in J2. inv J2. auto.
    apply IHHnp1 in Hinc; auto.
      apply remove_in_length in Hinb1.
      omega. 
Qed.

End MoreMove.

(** Properties of [List.incl] (list inclusion). *)

Lemma incl_cons_inv:
  forall (A: Type) (a: A) (b c: list A),
  incl (a :: b) c -> incl b c.
Proof.
  unfold incl; intros. apply H. apply in_cons. auto.
Qed.
Hint Resolve incl_cons_inv: coqlib.

Lemma incl_app_inv_l:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l1 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. left; assumption.
Qed.

Lemma incl_app_inv_r:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l2 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. right; assumption.
Qed.

Hint Resolve  incl_tl incl_refl incl_app_inv_l incl_app_inv_r: coqlib.

Lemma incl_same_head:
  forall (A: Type) (x: A) (l1 l2: list A),
  incl l1 l2 -> incl (x::l1) (x::l2).
Proof.
  intros; red; simpl; intros. intuition.
Qed.

Section InclDec.

Variable A:Type.
Variable Hdec: forall (x y: A), {x = y} + {x <> y}.

Definition incl_dec_prop (n:nat) :=
  forall (l1 l2:list A), length l1 = n -> {incl l1 l2} + {~ incl l1 l2}.

Lemma incl_dec_aux : forall n, incl_dec_prop n.
Proof.
  intro n.
  apply lt_wf_rec. clear n.
  intros n H.
  unfold incl_dec_prop in *.
  destruct l1; intros l2 Hlength.
    left. intros x J. inversion J.

    simpl in *.
    assert (((length (List.remove Hdec a l1)) < n)%nat) as LT.
      assert (J:=@remove_length A Hdec a l1).
      omega.
    destruct (@H (length (List.remove Hdec a l1)) LT
                (List.remove Hdec a l1) l2) as [J1 | J1]; auto.
      destruct(@in_dec _ Hdec a l2) as [J2 | J2].
        left. intros x J. simpl in J.
        destruct J as [J | J]; subst; auto.
        destruct (Hdec x a); subst; auto.
        apply J1.
        apply remove_neq_in; auto.

        right. intros G. apply J2. apply G; simpl; auto.

      destruct(@in_dec _ Hdec a l2) as [J2 | J2].
        right. intros G. apply J1. intros x J3. apply G. simpl.
        destruct (Hdec x a); subst; auto.
          right. eapply remove_neq_in'; eauto.

        right. intro J. apply J2. apply J. simpl; auto.
Qed.

Lemma incl_dec : forall (l1 l2:list A), {incl l1 l2} + {~ incl l1 l2}.
Proof.
  intros l1.
  assert (J:=@incl_dec_aux (length l1)).
  unfold incl_dec_prop in J. eauto.
Qed.

End InclDec.

(** Properties of [List.map] (mapping a function over a list). *)

Lemma list_map_exten:
  forall (A B: Type) (f f': A -> B) (l: list A),
  (forall x, In x l -> f x = f' x) ->
  List.map f' l = List.map f l.
Proof.
  induction l; simpl; intros.
  reflexivity.
  rewrite <- H. rewrite IHl. reflexivity.
  intros. apply H. tauto.
  tauto.
Qed.

Lemma list_map_compose:
  forall (A B C: Type) (f: A -> B) (g: B -> C) (l: list A),
  List.map g (List.map f l) = List.map (fun x => g(f x)) l.
Proof.
  induction l; simpl. reflexivity. rewrite IHl; reflexivity.
Qed.

Lemma list_map_identity:
  forall (A: Type) (l: list A),
  List.map (fun (x:A) => x) l = l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_map_nth:
  forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
  nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  induction l; simpl; intros.
  repeat rewrite nth_error_nil. reflexivity.
  destruct n; simpl. reflexivity. auto.
Qed.

Lemma list_length_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  List.length (List.map f l) = List.length l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_in_map_inv:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (List.map f l) -> exists x:A, y = f x /\ In x l.
Proof.
  induction l; simpl; intros.
  contradiction.
  elim H; intro.
  exists a; intuition auto.
  generalize (IHl y H0). intros [x [EQ IN]].
  exists x; tauto.
Qed.

Lemma list_append_map:
  forall (A B: Type) (f: A -> B) (l1 l2: list A),
  List.map f (l1 ++ l2) = List.map f l1 ++ List.map f l2.
Proof.
  induction l1; simpl; intros.
  auto. rewrite IHl1. auto.
Qed.

Lemma list_append_map_inv:
  forall (A B: Type) (f: A -> B) (m1 m2: list B) (l: list A),
  List.map f l = m1 ++ m2 ->
  exists l1, exists l2, List.map f l1 = m1 /\ List.map f l2 = m2 /\ l = l1 ++ l2.
Proof.
  induction m1; simpl; intros.
  exists (@nil A); exists l; auto.
  destruct l; simpl in H; inv H.
  exploit IHm1; eauto. intros [l1 [l2 [P [Q R]]]]. subst l.
  exists (a0 :: l1); exists l2; intuition. simpl; congruence.
Qed.

(** Properties of list membership. *)

Lemma in_cns:
  forall (A: Type) (x y: A) (l: list A), In x (y :: l) <-> y = x \/ In x l.
Proof.
  intros. simpl. tauto.
Qed.

Lemma in_app:
  forall (A: Type) (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
Qed.

Lemma list_in_insert:
  forall (A: Type) (x: A) (l1 l2: list A) (y: A),
  In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof.
  intros. apply in_or_app; simpl. elim (in_app_or _ _ _ H); intro; auto.
Qed.

(** [list_disjoint l1 l2] holds iff [l1] and [l2] have no elements
  in common. *)

Definition list_disjoint (A: Type) (l1 l2: list A) : Prop :=
  forall (x y: A), In x l1 -> In y l2 -> x <> y.

Lemma list_disjoint_cons_left:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint (a :: l1) l2 -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto.
Qed.

Lemma list_disjoint_cons_right:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint l1 (a :: l2) -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto.
Qed.

Lemma list_disjoint_notin:
  forall (A: Type) (l1 l2: list A) (a: A),
  list_disjoint l1 l2 -> In a l1 -> ~(In a l2).
Proof.
  unfold list_disjoint; intros; red; intros.
  apply H with a a; auto.
Qed.

Lemma list_disjoint_sym:
  forall (A: Type) (l1 l2: list A),
  list_disjoint l1 l2 -> list_disjoint l2 l1.
Proof.
  unfold list_disjoint; intros.
  apply sym_not_equal. apply H; auto.
Qed.

Lemma list_disjoint_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l1 l2: list A),
  {list_disjoint l1 l2} + {~list_disjoint l1 l2}.
Proof.
  induction l1; intros.
  left; red; intros. elim H.
  case (In_dec eqA_dec a l2); intro.
  right; red; intro. apply (H a a); auto with coqlib.
  case (IHl1 l2); intro.
  left; red; intros. elim H; intro.
    red; intro; subst a y. contradiction.
    apply l; auto.
  right; red; intros. elim n0. eapply list_disjoint_cons_left; eauto.
Defined.

(** [list_equiv l1 l2] holds iff the lists [l1] and [l2] contain the same elements. *)

Definition list_equiv (A : Type) (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

Lemma list_equiv_nil: forall A (l1:list A) (Heq: list_equiv nil l1), l1 = nil.
Proof.
  intros.
  destruct l1 as [|x l1]; auto.
  destruct (Heq x) as [_ J1].
  assert (In x (x::l1)) as J. auto with datatypes v62.
  apply J1 in J. inv J.
Qed.

(** [list_norepet l] holds iff the list [l] contains no repetitions,
  i.e. no element occurs twice. *)

Inductive list_norepet (A: Type) : list A -> Prop :=
  | list_norepet_nil:
      list_norepet nil
  | list_norepet_cons:
      forall hd tl,
      ~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).

Lemma list_norepet_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A),
  {list_norepet l} + {~list_norepet l}.
Proof.
  induction l.
  left; constructor.
  destruct IHl.
  case (In_dec eqA_dec a l); intro.
  right. red; intro. inversion H. contradiction.
  left. constructor; auto.
  right. red; intro. inversion H. contradiction.
Defined.

Lemma list_map_norepet:
  forall (A B: Type) (f: A -> B) (l: list A),
  list_norepet l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  list_norepet (List.map f l).
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor.
  red; intro. generalize (list_in_map_inv f _ _ H2).
  intros [x [EQ IN]]. generalize EQ. change (f hd <> f x).
  apply H1. tauto. tauto.
  red; intro; subst x. contradiction.
  apply IHlist_norepet. intros. apply H1. tauto. tauto. auto.
Qed.

Remark list_norepet_append_commut:
  forall (A: Type) (a b: list A),
  list_norepet (a ++ b) -> list_norepet (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A),
           list_norepet (a ++ b) -> ~(In x a) -> ~(In x b) ->
           list_norepet (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto.
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto.
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma list_norepet_app:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) <->
  list_norepet l1 /\ list_norepet l2 /\ list_disjoint l1 l2.
Proof.
  induction l1; simpl; intros; split; intros.
  intuition. constructor. red;simpl;auto.
  tauto.
  inversion H; subst. rewrite IHl1 in H3. rewrite in_app in H2.
  intuition.
  constructor; auto. red; intros. elim H2; intro. congruence. auto.
  destruct H as [B [C D]]. inversion B; subst.
  constructor. rewrite in_app. intuition. elim (D a a); auto. apply in_eq.
  rewrite IHl1. intuition. red; intros. apply D; auto. apply in_cons; auto.
Qed.

Lemma list_norepet_append:
  forall (A: Type) (l1 l2: list A),
  list_norepet l1 -> list_norepet l2 -> list_disjoint l1 l2 ->
  list_norepet (l1 ++ l2).
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_right:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) -> list_norepet l2.
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_left:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) -> list_norepet l1.
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Require Import Program.Tactics.

Ltac destruct_in H :=
match type of H with
| In _ (_::nil) => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_::_) => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_++_) => apply in_app_or in H; destruct H as [H | H]
end.

Lemma norepet_equiv__length_eq: forall A (l1:list A)
  (Huniq1: list_norepet l1) (l2:list A) (Huniq2: list_norepet l2)
  (Heq: list_equiv l1 l2),
  (length l1 = length l2)%nat.
Proof.
  induction 1; simpl; intros.
    apply list_equiv_nil in Heq. subst. auto.

    destruct (Heq hd) as [J1 _].
    assert (In hd (hd::tl)) as J2. auto with datatypes v62.
    apply J1 in J2.
    apply in_split in J2.
    destruct_conjs; subst.
    rewrite app_length. simpl.
    rewrite IHHuniq1 with (l2:=J2++H0).
      rewrite app_length.
      omega.

      apply list_norepet_append_commut in Huniq2.
      rewrite <- app_comm_cons in Huniq2.
      apply list_norepet_append_commut.
      inv Huniq2; auto.

      apply list_norepet_append_commut in Huniq2.
      rewrite <- app_comm_cons in Huniq2.
      destruct_conjs.
      intro x.
      destruct (Heq x) as [J1' J2'].
      split; intro J.
        assert (Hin: In x (hd::tl)). auto with datatypes v62.
        apply J1' in Hin.
        destruct_in Hin; auto with datatypes v62.
        destruct_in Hin; auto with datatypes v62.

        assert (Hin: In x (J2 ++ hd :: H0)). 
          destruct_in J; auto with datatypes v62.
        apply J2' in Hin.
        destruct_in Hin; auto with datatypes v62.
        inv Huniq2.
        elimtype False. apply H3.
        destruct_in J; auto with datatypes v62.
Qed.

Lemma norepet_equiv__length_cons_eq: forall A l1 l2 (a:A)
  (Huniq1: list_norepet l1) (Huniq2: list_norepet l2)
  (Hnotin: ~ In a l1) (Heq: list_equiv l2 (a::l1)),
  (length l2 = length l1 + 1)%nat.
Proof.
  intros.
  apply norepet_equiv__length_eq in Heq; auto.
    simpl in *. omega.
    constructor; auto.
Qed.

Lemma incl__length_le: forall A (eq_dec : forall x y : A, {x = y}+{x <> y})
  (l1:list A) (Huniq: list_norepet l1) (l2:list A) (Hinc: incl l1 l2), 
  (length l1 <= length l2)%nat.
Proof.
  induction 2 as [|hd tl Hnotin Huniq IH]; simpl; intros.
    auto with datatypes v62.

    assert (incl tl (List.remove eq_dec hd l2)) as Hinc'.
      apply remove_notin_incl; eauto with datatypes v62.
    apply IH in Hinc'.
    assert (length (List.remove eq_dec hd l2) < length l2)%nat as Hle.
      apply remove_in_length; auto with datatypes v62.
    omega.
Qed.

(** [is_tail l1 l2] holds iff [l2] is of the form [l ++ l1] for some [l]. *)

Inductive is_tail (A: Type): list A -> list A -> Prop :=
  | is_tail_refl:
      forall c, is_tail c c
  | is_tail_cons:
      forall i c1 c2, is_tail c1 c2 -> is_tail c1 (i :: c2).

Lemma is_tail_nil: forall A (l1:list A), is_tail nil l1.
Proof.
  induction l1; constructor; auto.
Qed.

Lemma is_tail_Forall: forall A (l1 l2:list A) P (Hp2: Forall P l2)
  (Htail: is_tail l1 l2), Forall P l1.
Proof.
  induction 2; auto.
    inv Hp2. auto.
Qed.

Lemma is_tail_sorted: forall l1 l2 (Hsort: Sorted.Sorted Plt l2)
  (Histl: is_tail l1 l2), Sorted.Sorted Plt l1.
Proof.
  intros.
  induction Histl; auto.
    inv Hsort. auto.
Qed.

Lemma Forall_HdRel: forall A P (x:A) l1 (Hlt : Forall (P x) l1),
  Sorted.HdRel P x l1.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall_is_tail_HdRel: forall A P (x:A) l1 l2 (Hlt : Forall (P x) l2)
  (Histl : is_tail l1 l2), Sorted.HdRel P x l1.
Proof.
  intros.
  induction Histl; auto using Forall_HdRel.
    inv Hlt. auto.
Qed.

Lemma is_tail_cons_sorted: forall x l1 l2 (Hsort: Sorted.Sorted Plt (x::l2)) 
  (Hlt : Forall (Plt x) l2) (Histl: is_tail l1 l2), Sorted.Sorted Plt (x :: l1).
Proof.
  intros.
  inv Hsort.
  constructor; eauto using is_tail_sorted, Forall_is_tail_HdRel.
Qed.

Lemma is_tail_in:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> In i c2.
Proof.
  induction c2; simpl; intros.
  inversion H.
  inversion H. tauto. right; auto.
Qed.

Lemma is_tail_cons_left:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> is_tail c1 c2.
Proof.
  induction c2; intros; inversion H.
  constructor. constructor. constructor. auto.
Qed.

Hint Resolve is_tail_refl is_tail_cons is_tail_in is_tail_cons_left: coqlib.

Lemma is_tail_incl:
  forall (A: Type) (l1 l2: list A), is_tail l1 l2 -> incl l1 l2.
Proof.
  induction 1; eauto with coqlib.
Qed.

Lemma is_tail_trans:
  forall (A: Type) (l1 l2: list A),
  is_tail l1 l2 -> forall (l3: list A), is_tail l2 l3 -> is_tail l1 l3.
Proof.
  induction 1; intros. auto. apply IHis_tail. eapply is_tail_cons_left; eauto.
Qed.

(** [list_forall2 P [x1 ... xN] [y1 ... yM]] holds iff [N = M] and
  [P xi yi] holds for all [i]. *)

Section FORALL2.

Variable A: Type.
Variable B: Type.
Variable P: A -> B -> Prop.

Inductive list_forall2: list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 nil nil
  | list_forall2_cons:
      forall a1 al b1 bl,
      P a1 b1 ->
      list_forall2 al bl ->
      list_forall2 (a1 :: al) (b1 :: bl).

Lemma list_forall2_app:
  forall a2 b2 a1 b1,
  list_forall2 a1 b1 -> list_forall2 a2 b2 ->
  list_forall2 (a1 ++ a2) (b1 ++ b2).
Proof.
  induction 1; intros; simpl. auto. constructor; auto.
Qed.

End FORALL2.

Lemma list_forall2_imply:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
  list_forall2 P1 l1 l2 ->
  forall (P2: A -> B -> Prop),
  (forall v1 v2, In v1 l1 -> In v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
  list_forall2 P2 l1 l2.
Proof.
  induction 1; intros.
  constructor.
  constructor. auto with coqlib. apply IHlist_forall2; auto.
  intros. auto with coqlib.
Qed.

Lemma list_forall2_length_eq:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
  list_forall2 P1 l1 l2 -> length l1 = length l2.
Proof.
  induction 1; intros; auto.
    simpl. congruence.
Qed.

(** [list_forall3 P [x1 ... xN] [y1 ... yM] [z1 ... zL]] holds iff [N = M = L] 
  and [P xi yi zi] holds for all [i]. *)

Section FORALL3.

Variable A: Type.
Variable B: Type.
Variable C: Type.
Variable R: A -> B -> C -> Prop.

Inductive Forall3: list A -> list B -> list C -> Prop :=
 | Forall3_nil : Forall3 nil nil nil
 | Forall3_cons : forall x y z l l' l'',
    R x y z -> Forall3 l l' l'' -> Forall3 (x::l) (y::l') (z::l'').
Hint Constructors Forall3.

Theorem Forall3_refl : Forall3 nil nil nil.
Proof. auto. Qed.

Theorem Forall3_app_inv_l : forall l1 l2 l' l'',
  Forall3 (l1 ++ l2) l' l'' ->
  exists l1', exists l2', exists l1'', exists l2'', 
    Forall3 l1 l1' l1'' /\ Forall3 l2 l2' l2'' /\ 
    l' = l1' ++ l2' /\ l'' = l1'' ++ l2''.
Proof.
  intros.
  remember (l1 ++ l2) as l.
  generalize dependent l1.
  generalize dependent l2.
  induction H; intros.
    symmetry in Heql. apply app_eq_nil in Heql.
    destruct Heql; subst.
    exists nil. exists nil. exists nil. exists nil.
    auto.

    apply cons_eq_app in Heql.
    destruct Heql as [[eq [J1 J2]] | [J1 J2]]; subst.
      edestruct IHForall3 as [a [b [c [d [J1 [J2 [J3 J4]]]]]]]; subst; eauto.
      exists (y::a). exists b. exists (z::c). exists d.
      rewrite app_comm_cons. simpl. auto.

      destruct (@IHForall3 l nil) as [a [b [c [d [J1 [J2 [J3 J4]]]]]]]; 
        subst; auto.
      exists nil. exists (y::a++b). exists nil. exists (z::c++d).
      auto.
Qed.

Theorem Forall3_app_inv_m : forall l l1' l2' l'',
  Forall3 l (l1' ++ l2') l'' ->
  exists l1, exists l2, exists l1'', exists l2'', 
    Forall3 l1 l1' l1'' /\ Forall3 l2 l2' l2'' /\ 
    l = l1 ++ l2 /\ l'' = l1'' ++ l2''.
Proof.
  intros.
  remember (l1' ++ l2') as l'.
  generalize dependent l1'.
  generalize dependent l2'.
  induction H; intros.
    symmetry in Heql'. apply app_eq_nil in Heql'.
    destruct Heql'; subst.
    exists nil. exists nil. exists nil. exists nil.
    auto.

    apply cons_eq_app in Heql'.
    destruct Heql' as [[eq [J1 J2]] | [J1 J2]]; subst.
      edestruct IHForall3 as [a [b [c [d [J1 [J2 [J3 J4]]]]]]]; subst; eauto.
      exists (x::a). exists b. exists (z::c). exists d.
      rewrite app_comm_cons. simpl. auto.

      destruct (@IHForall3 l' nil) as [a [b [c [d [J1 [J2 [J3 J4]]]]]]]; 
        subst; auto.
      exists nil. exists (x::a++b). exists nil. exists (z::c++d).
      auto.
Qed.

Theorem Forall3_app_inv_r : forall l l' l1'' l2'',
  Forall3 l l' (l1'' ++ l2'') ->
  exists l1, exists l2, exists l1', exists l2', 
    Forall3 l1 l1' l1'' /\ Forall3 l2 l2' l2'' /\ 
    l = l1 ++ l2 /\ l' = l1' ++ l2'.
Proof.
  intros.
  remember (l1'' ++ l2'') as l''.
  generalize dependent l1''.
  generalize dependent l2''.
  induction H; intros.
    symmetry in Heql''. apply app_eq_nil in Heql''.
    destruct Heql''; subst.
    exists nil. exists nil. exists nil. exists nil.
    auto.

    apply cons_eq_app in Heql''.
    destruct Heql'' as [[eq [J1 J2]] | [J1 J2]]; subst.
      edestruct IHForall3 as [a [b [c [d [J1 [J2 [J3 J4]]]]]]]; subst; eauto.
      exists (x::a). exists b. exists (y::c). exists d.
      rewrite app_comm_cons. simpl. auto.

      destruct (@IHForall3 l'' nil) as [a [b [c [d [J1 [J2 [J3 J4]]]]]]]; 
        subst; auto.
      exists nil. exists (x::a++b). exists nil. exists (y::c++d).
      auto.
Qed.

Theorem Forall3_app : forall l1 l2 l1' l2' l1'' l2'',
  Forall3 l1 l1' l1'' -> Forall3 l2 l2' l2'' -> 
  Forall3 (l1 ++ l2) (l1' ++ l2') (l1'' ++ l2'').
Proof.
  induction 1; intros; auto.
    repeat rewrite <- app_comm_cons. simpl. auto.
Qed.

End FORALL3.

(** Dropping the first N elements of a list. *)

Fixpoint list_drop (A: Type) (n: nat) (x: list A) {struct n} : list A :=
  match n with
  | O => x
  | S n' => match x with nil => nil | hd :: tl => list_drop n' tl end
  end.

Lemma list_drop_incl:
  forall (A: Type) (x: A) n (l: list A), In x (list_drop n l) -> In x l.
Proof.
  induction n; simpl; intros. auto.
  destruct l; auto with coqlib.
Qed.

Lemma list_drop_norepet:
  forall (A: Type) n (l: list A), list_norepet l -> list_norepet (list_drop n l).
Proof.
  induction n; simpl; intros. auto.
  inv H. constructor. auto.
Qed.

Lemma list_map_drop:
  forall (A B: Type) (f: A -> B) n (l: list A),
  list_drop n (List.map f l) = List.map f (list_drop n l).
Proof.
  induction n; simpl; intros. auto.
  destruct l; simpl; auto.
Qed.

(** A list of [n] elements, all equal to [x]. *)

Fixpoint list_repeat {A: Type} (n: nat) (x: A) {struct n} :=
  match n with
  | O => nil
  | S m => x :: list_repeat m x
  end.

Lemma length_list_repeat:
  forall (A: Type) n (x: A), length (list_repeat n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Lemma in_list_repeat:
  forall (A: Type) n (x: A) y, In y (list_repeat n x) -> y = x.
Proof.
  induction n; simpl; intros. elim H. destruct H; auto.
Qed.

(** List misc *)
Lemma list_with_last_neq_nil: forall (X : Type) (x1 : X) (ls2 : list X),
  ls2 ++ x1 :: nil  <> nil.
Proof.
  induction ls2; simpl; try congruence.
Qed.

(** * Definitions and theorems over boolean types *)

Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Implicit Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof.
  intros P Q a. destruct a; simpl. auto. congruence.
Qed.

Lemma proj_sumbool_is_true:
  forall (P: Prop) (a: {P}+{~P}), P -> proj_sumbool a = true.
Proof.
  intros. unfold proj_sumbool. destruct a. auto. contradiction.
Qed.

Section DECIDABLE_EQUALITY.

Variable A: Type.
Variable dec_eq: forall (x y: A), {x=y} + {x<>y}.
Variable B: Type.

Lemma dec_eq_true:
  forall (x: A) (ifso ifnot: B),
  (if dec_eq x x then ifso else ifnot) = ifso.
Proof.
  intros. destruct (dec_eq x x). auto. congruence.
Qed.

Lemma dec_eq_false:
  forall (x y: A) (ifso ifnot: B),
  x <> y -> (if dec_eq x y then ifso else ifnot) = ifnot.
Proof.
  intros. destruct (dec_eq x y). congruence. auto.
Qed.

Lemma dec_eq_sym:
  forall (x y: A) (ifso ifnot: B),
  (if dec_eq x y then ifso else ifnot) =
  (if dec_eq y x then ifso else ifnot).
Proof.
  intros. destruct (dec_eq x y).
  subst y. rewrite dec_eq_true. auto.
  rewrite dec_eq_false; auto.
Qed.

End DECIDABLE_EQUALITY.

Section DECIDABLE_PREDICATE.

Variable P: Prop.
Variable dec: {P} + {~P}.
Variable A: Type.

Lemma pred_dec_true:
  forall (a b: A), P -> (if dec then a else b) = a.
Proof.
  intros. destruct dec. auto. contradiction.
Qed.

Lemma pred_dec_false:
  forall (a b: A), ~P -> (if dec then a else b) = b.
Proof.
  intros. destruct dec. contradiction. auto.
Qed.

End DECIDABLE_PREDICATE.

(***********************************************************************)

Section Sublist.

Variables X : Type.

Inductive sublist : list X -> list X -> Prop :=
| sl_nil : forall (l : list X), sublist nil l
| sl_cons : forall (l1 l2 : list X) (x : X),
  sublist l1 l2 -> sublist (x :: l1) (x :: l2)
| sl_cons_r : forall (l1 l2 : list X) (x : X),
  sublist l1 l2 -> sublist l1 (x :: l2).

Theorem sublist_refl : forall l : list X, sublist l l.
Proof.
  intros l. induction l as [|x l]. apply sl_nil.
  apply sl_cons. trivial.
Qed.

Hint Resolve sublist_refl.

Theorem sublist_app_r : forall (l1 l2 l2' : list X),
  sublist l1 l2 -> sublist l1 (l2' ++ l2).
Proof.
  intros l1 l2 l2' H. induction l2' as [|x l2'];
  [|apply sl_cons_r]; trivial.
Qed.

Theorem sublist_cons_weaken : forall (l1 l2 : list X) (x : X),
  sublist (x :: l1) l2 -> sublist l1 l2.
Proof.
  intros l1 l2 x H.
  remember (x :: l1) as l1'.
  induction H as [|l1' l2' x' H|l1' l2' x' H]. discriminate.
  apply sl_cons_r. inversion Heql1'. subst. trivial.
  apply sl_cons_r. apply IHH. trivial.
Qed.

Theorem sublist_app : forall (l1 l1' l2 l2' : list X),
  sublist l1 l2 -> sublist l1' l2' ->
  sublist (l1 ++ l1') (l2 ++ l2').
Proof.
  intros l1 l1' l2 l2' H1 H2. induction H1 as [l2|l1 l2 x H1|l1 l2 x H1];
  [apply sublist_app_r|apply sl_cons|apply sl_cons_r]; trivial.
Qed.

Theorem sublist_In : forall (l1 l2 : list X),
  sublist l1 l2 -> forall x : X, In x l1 -> In x l2.
Proof.
  intros l1 l2 Hl1l2.
  induction Hl1l2 as [|l1 l2 x Hl1l2|l1 l2 x Hl1l2].
  intros x contra. inversion contra.
  intros y H. inversion H; [left | right; apply IHHl1l2]; trivial.
  intros y H. right. apply IHHl1l2. trivial.
Qed.

Theorem NoDup_sublist : forall (l1 l2 : list X),
  NoDup l1 -> sublist l2 l1 -> NoDup l2.
Proof.
  intros l1 l2 Hl1 Hl1l2.
  generalize dependent l2. induction Hl1 as [|x l1 Hxl1]; intros l2 Hl1l2.
  inversion Hl1l2. constructor.
  destruct l2 as [|y l2]. apply NoDup_nil.
  inversion Hl1l2 as [|l1' l2' x' Hsub|l1' l2' x' Hsub]; subst.
    apply NoDup_cons. contradict Hxl1. apply sublist_In with l2; trivial.
    apply IHHl1. trivial.
  apply IHHl1. trivial.
Qed.

Theorem filter_sublist : forall (test : X -> bool) (l : list X),
  sublist (filter test l) l.
Proof.
  intros test l. induction l as [|x l]. apply sl_nil.
  simpl. destruct (test x). apply sl_cons. trivial.
  apply sl_cons_r. trivial.
Qed.

Require Import Coq.Program.Equality.

Theorem sublist_split : forall (l1 l2: list X) l12'
  (H: sublist (l1++l2) l12'), 
  exists l1', exists l2', 
    l12' = l1' ++ l2' /\ sublist l1 l1' /\ sublist l2 l2'.
Proof.
  intros.
  dependent induction H; simpl; intros.
    symmetry in x. apply app_eq_nil in x; destruct x; subst.
    exists nil. exists l. repeat (split; try solve [constructor | auto]).

    destruct l1 as [|x1 l1]; simpl in x; inv x.
      exists nil. exists (x0::l0).
      repeat (split; try solve [constructor; auto | auto]).

      destruct (IHsublist l2 l1) as [l1' [l2' [EQ [Hsub1 Hsub2]]]]; subst; auto.
      exists (x1::l1'). exists l2'.
      repeat (split; try solve [constructor; auto | auto]).

    destruct IHsublist as [l1' [l2' [EQ [Hsub1 Hsub2]]]]; subst; auto.
    exists (x::l1'). exists l2'.
    repeat (split; try solve [constructor; auto | auto]).
Qed.
 
Theorem sublist_cons_inv : forall a1 (l2: list X) l12'
  (H: sublist (a1::l2) l12'), 
  exists l1', exists l2', 
    l12' = l1' ++ l2' /\ sublist (a1::nil) l1' /\ sublist l2 l2'.
Proof.
  intros. apply sublist_split. simpl. auto.
Qed.

Theorem sublist_cons : forall a1 (l1' l2' l2: list X)
  (H1: sublist (a1::nil) l1') (H2: sublist l2 l2'),
  sublist (a1::l2) (l1' ++ l2').
Proof.
  intros. apply sublist_app with (l1:=a1::nil)(l2:=l1') in H2; auto. 
Qed.

Theorem sublist_trans : forall (l1 l2: list X)
  (H12: sublist l1 l2) l3 (H23: sublist l2 l3), sublist l1 l3.
Proof.
  induction 1; simpl; intros; try constructor.
    apply sublist_cons_inv in H23.
    destruct H23 as [l1' [l2' [EQ [H1' H2']]]]; subst.
    apply sublist_cons; auto.

    apply sublist_cons_weaken in H23. auto.
Qed.

Lemma sublist_Forall: forall (l1 l2:list X) P (Hp2: Forall P l2)
  (Htail: sublist l1 l2), Forall P l1.
Proof.
  induction 2; try solve [auto | inv Hp2; auto].
Qed.

Lemma sublist_StronglySorted: forall R l1 l2 (Hsort: Sorted.StronglySorted R l2)
  (Histl: sublist l1 l2), Sorted.StronglySorted R l1.
Proof.
  intros.
  induction Histl.
    constructor.

    inv Hsort. 
    constructor; eauto using sublist_Forall.

    inv Hsort. auto.
Qed.

Lemma sublist_sorted: forall R (Htrans: Relations_1.Transitive R) l1 l2 
  (Hsort: Sorted.Sorted R l2)
  (Histl: sublist l1 l2), Sorted.Sorted R l1.
Proof.
  intros.
  apply Sorted.Sorted_StronglySorted in Hsort; auto.
  apply Sorted.StronglySorted_Sorted.
  eapply sublist_StronglySorted; eauto.
Qed.

Lemma sublist_cons_sorted: forall x l1 l2 R (Htrans: Relations_1.Transitive R) 
  (Hsort: Sorted.Sorted R (x::l2)) (Hlt : Forall (R x) l2) 
  (Histl: sublist l1 l2), 
  Sorted.Sorted R (x :: l1).
Proof.
  intros.
  inv Hsort.
  constructor; eauto using sublist_sorted, Forall_HdRel, sublist_Forall. 
Qed.

Lemma sublist_cons': forall x l1 l2 (H : sublist l1 l2),
  sublist (x :: l1) (x :: l2).
Proof.
  intros.
  apply sublist_app with (l1:=x::nil) (l2:=x::nil) in H; auto. 
Qed.

Lemma sublist_append_false: forall (ls1 ls2:list X)
  (Hsub: sublist (ls2 ++ ls1) ls1) (Hneq: ls2 <> nil), False.
Proof.
  intros.
  dependent induction Hsub.
    destruct ls2; inv x; auto.
     
    destruct ls2; try congruence.
    inv x. 
    apply IHHsub with (ls3:=ls2++x1::nil).
      rewrite <- app_assoc. simpl. auto.
      apply list_with_last_neq_nil.

    apply IHHsub with (ls3:=ls2++x::nil).
      rewrite <- app_assoc. simpl. auto.
      apply list_with_last_neq_nil.
Qed.

Lemma sublist_cons_false: forall (a:X) (ls1:list X)
  (Hsub: sublist (a :: ls1) ls1), False.
Proof.
  intros.
  change (a::ls1) with ((a::nil)++ls1) in Hsub; auto.
  apply sublist_append_false in Hsub; auto.
    intro J. inv J.
Qed.

Variable Hdec: forall (x y:X), {x = y} + {x <> y}.

Lemma sublist__eq_or_exact: forall (l1 l2:list X) (Htail: sublist l1 l2)
  (Hnodup: NoDup l2),
  l1 = l2 \/ (exists a, In a l2 /\ ~ In a l1).
Proof.
  induction 1; intros.
    destruct l; auto.
      right. exists x; simpl; auto.

    inv Hnodup.
    destruct IHHtail as [IHHtail | [a [J1 J2]]]; subst; auto.
      right. exists a. simpl.
      split; auto.
        intro J.
        destruct J as [J | J]; subst; auto.

    inv Hnodup. 
    destruct IHHtail as [IHHtail | [a [J1 J2]]]; subst; auto.
      right. exists x. simpl. split; auto.

      right. exists a. simpl. 
      split; auto.
Qed.

Lemma sublist_length: forall (l1 l2:list X) (Htail: sublist l1 l2), 
  (length l1 <= length l2)%nat.
Proof.
  induction 1; simpl; try omega.
Qed.

Lemma sublist_antisymm: forall (l1 l2:list X) (Htail: sublist l1 l2)
  (Htail': sublist l2 l1), l1 = l2.
Proof.
  induction 1; simpl; intros.
    inv Htail'; auto.

    inv Htail'; auto.
      rewrite IHHtail; auto.

      apply sublist_length in Htail.
      apply sublist_length in H1. simpl in *.
      contradict Htail. omega.

    apply sublist_length in Htail.
    apply sublist_length in Htail'. simpl in *.
    contradict Htail. omega.
Qed.

Lemma sublist_remove: forall a 
  (l1 l2:list X) (Htail: sublist l1 l2)
  (Hnotin: ~ In a l1), 
  sublist l1 (List.remove Hdec a l2).
Proof.
  induction 1; simpl; intros.
    constructor.

    destruct_if.
      contradict Hnotin; auto.
      constructor; auto.

    destruct_if.
      constructor; auto.
Qed.

Lemma exact_sublist_length: forall (l1 l2:list X) (Htail: sublist l1 l2)
  (Hex: exists a, In a l2 /\ ~ In a l1), 
  (length l1 < length l2)%nat.
Proof.
  induction 1; simpl; intros.
    destruct Hex as [a [J1 J2]].
    destruct l; simpl; try solve [omega | tauto].

    destruct Hex as [a [[J1 | J1] J2]]; subst.
      contradict J2; auto.
      eapply sublist_remove in Htail; eauto.
      apply sublist_length in Htail.
      apply remove_in_length with (Hdec:=Hdec) in J1; auto.
      omega.

    apply sublist_length in Htail. omega.
Qed.

End Sublist.

Implicit Arguments sublist [[X]].

Hint Resolve sublist_refl sublist_trans sublist_app sublist_cons_weaken
             sublist_app_r sublist_Forall sublist_cons sublist_cons' sublist_In 
             : sublist.

Theorem sublist_map : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  sublist l1 l2 -> sublist (List.map f l1) (List.map f l2).
Proof.
  intros X Y f l1 l2 H. induction H as [|l1 l2 x H|l1 l2 x H];
  [apply sl_nil|apply sl_cons|apply sl_cons_r]; trivial.
Qed.

Require Import ListSet.

(*********** NoDup *************)

Section NoDup_More.

Lemma Plt_StronglySorted_NoDup: forall sds (Hsrt: Sorted.StronglySorted Plt sds), 
  NoDup sds.
Proof.
  induction 1.
    constructor.

    constructor; auto.
      intro Hin.
      eapply Forall_forall in Hin; eauto.
      inv Hin. rewrite Pos.compare_refl in H1. inversion H1. 
Qed.

Variable A:Type.
Variable Hdec: forall x y : A, {x = y} + {x <> y}.

Lemma NoDup_remove_notin_length: forall
  a ls2 (Hndp2 : NoDup ls2) (Hin : ~ In a ls2),
  (length (List.remove Hdec a ls2)) = length ls2.
Proof.
  induction 1; simpl; intros; auto.
    destruct_if.
      contradict Hin. simpl. constructor. reflexivity.

      simpl. 
      rewrite IHHndp2; auto.
Qed.

Lemma NoDup_remove_in_length: forall a ls2 (Hndp2 : NoDup ls2)
  (Hin : In a ls2),
  S (length (List.remove Hdec a ls2)) = length ls2.
Proof.
  induction 1; simpl; intros.
    inv Hin.

    destruct_if.
      rewrite NoDup_remove_notin_length; auto.
      simpl. rewrite IHHndp2; auto.
        inv Hin; auto.
          congruence.
Qed.
  
(* go to *)
Lemma NoDup_incl_length: forall (ls1:list A) (Hnp1: NoDup ls1) ls2
  (Hnp2: NoDup ls2) (Hincl: incl ls1 ls2),
  (length ls1 <= length ls2)%nat.
Proof.
  induction 1 as [|a1 ls1]; simpl; intros.
    omega.

    assert (incl ls1 (List.remove Hdec a1 ls2)) as Hinc.
      apply remove_notin_incl; auto.
        eauto with datatypes v62.
    apply IHHnp1 in Hinc; auto.
      assert (In a1 ls2) as Hin. 
        eauto with datatypes v62.
      apply remove_in_length with (Hdec:=Hdec) in Hin.
      omega. 

      apply NoDup_remove; auto.
Qed.

Lemma NoDup_exact_incl_length: forall (ls1:list A) (Hnp1: NoDup ls1) ls2
  (Hnp2: NoDup ls2) 
  (Hincl: incl ls1 ls2) (Hex: exists a, In a ls2 /\ ~ In a ls1),
  (length ls1 < length ls2)%nat.
Proof.
  intros.
  destruct Hex as [a [Hin Hnotin]].
  assert (incl ls1 (List.remove Hdec a ls2)) as Hinc.
    apply remove_notin_incl; auto.
  apply NoDup_incl_length in Hinc; auto.
    apply NoDup_remove_in_length in Hin; auto.
    omega.

    apply NoDup_remove; auto.
Qed.

End NoDup_More.

(*********** Redundancy *************)

Section RemoveRedundant.

Variable A:Type.
Variable Hdec: forall x y : A, {x = y} + {x <> y}.

Fixpoint remove_redundant (input: list A) : list A :=
match input with
| a :: ((b :: _) as input') =>
    if (Hdec a b) then remove_redundant input'
    else a :: remove_redundant input'
| _ => input
end.

Lemma remove_redundant_safe: forall l0 input,
  In l0 (remove_redundant input) <-> In l0 input.
Proof.
  induction input as [|a input]; simpl.
    split; auto.

    destruct input as [|a0 input].
      simpl. split; auto.

      destruct IHinput as [J1 J2].
      destruct (Hdec a a0); subst.
        split; intros.
          apply J1 in H.
            simpl in H. simpl.
            destruct H; auto.

          apply J2.
            simpl in H. simpl.
            destruct H as [H | [H | H]]; auto.

        split; intros.
          Local Opaque remove_redundant.
          simpl in H.
          destruct H as [H | H]; auto.

          simpl.
          destruct H as [H | H]; auto.
          Transparent remove_redundant.
Qed.

Lemma remove_redundant_HdRel: forall R a input,
  Sorted.HdRel R a input ->
  Sorted.HdRel R a (remove_redundant input).
Proof.
  induction input as [|a1 input]; simpl; intros; auto.
    destruct input as [|a2 input]; auto.
      inv H.
      destruct (Hdec a1 a2); subst.
        apply IHinput. apply Sorted.HdRel_cons; auto.
        apply Sorted.HdRel_cons; auto.
Qed.

Lemma remove_redundant_In: forall a input,
  In a (remove_redundant input) -> In a input.
Proof.
  intros. eapply remove_redundant_safe; eauto.
Qed.

Lemma remove_redundant_sorted: forall R input,
  Sorted.Sorted R input -> Sorted.Sorted R (remove_redundant input).
Proof.
  induction input as [|a1 input]; intros; simpl; auto.
    destruct input as [|a2 input]; auto.
      inv H.
      apply IHinput in H2.
      destruct (Hdec a1 a2); subst; auto.
        apply Sorted.Sorted_cons; auto.
          apply remove_redundant_HdRel; auto.
Qed.

Lemma remove_redundant_NoDup: forall (R:A -> A -> Prop) input
  (P0:forall a b c,
        In a input ->
        In b input ->
        In c input -> a <> b -> R a b -> R b c -> a <> c),
  Sorted.StronglySorted R input ->
  NoDup (remove_redundant input).
Proof.
  induction input as [|a1 input]; intros; simpl.
    constructor.
    destruct input as [|a2 input].
      constructor; auto.
        constructor.

      inv H.
      assert (H2':=H2).
      apply IHinput in H2.
        destruct (Hdec a1 a2); subst; auto.
          apply NoDup_cons; auto.
          intro J.
          apply remove_redundant_In in J.
          simpl in J.
          destruct J as [J | J]; subst.
            congruence.

            eapply Forall_forall with (x:=a2) in H3; simpl; eauto.
            inv H2'.
            eapply Forall_forall with (x:=a1) in H4; eauto.
            apply P0 with (c:=a1) in H3; simpl; auto.

        intros. apply P0 with (b:=b); simpl; auto.
Qed.

Lemma remove_redundant_NoDup': forall R input
  (P0:forall a, In a input -> ~ R a a),
  Sorted.StronglySorted R input ->
  NoDup (remove_redundant input).
Proof.
  induction input as [|a1 input]; intros; simpl.
    constructor.
    destruct input as [|a2 input].
      constructor; auto.
        constructor.

      inv H.
      apply IHinput in H2.
        destruct (Hdec a1 a2); subst; auto.
          apply NoDup_cons; auto.
          intro J.
          apply remove_redundant_In in J.
          eapply Forall_forall in H3; eauto.
          revert H3. apply P0. simpl. auto.
        intros. apply P0. simpl. simpl in H.
        destruct H; auto.
Qed.

End RemoveRedundant.

Section RemoveRedundancy.

Variable A:Type.
Variable Hdec: forall x y : A, {x = y} + {x <> y}.

Fixpoint remove_redundancy (acc:list A) (vs:list A) : list A :=
match vs with
| nil => acc
| v::vs' => 
    if (in_dec Hdec v acc) then remove_redundancy acc vs'
    else remove_redundancy (v::acc) vs'
end.

Lemma remove_redundancy_spec_aux: forall vs acc re
  (Hred: re = remove_redundancy acc vs) 
  (Hnodup: NoDup acc),
  (forall v0, (In v0 vs \/ In v0 acc) <-> In v0 re) /\
  NoDup re.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent re.
  induction vs as [|v vs]; simpl; intros; subst.
    tauto.

    destruct_if.
      assert (J:=Hnodup).
      eapply IHvs in J; eauto.
      destruct J as [J1 J2].
      symmetry in HeqR.
      split; auto.
        intro v0.
        split; intro J.
          apply J1. 
          destruct J as [J | J]; auto.
          destruct J as [J | J]; subst; auto.

          apply J1 in J. tauto.

      assert (NoDup (v::acc)) as Hnodup'.
        constructor; auto.
      assert (J:=Hnodup').
      eapply IHvs with (acc:=v::acc) in J; eauto.
      destruct J as [J1 J2].
      split; auto.
        intro v0.
        split; intro J.
          apply J1. simpl. tauto.

          apply J1 in J. simpl in J. tauto.
Qed.

Lemma remove_redundancy_spec: forall vs vs'
  (Hred: vs' = remove_redundancy nil vs),
  (forall v0, In v0 vs <-> In v0 vs') /\
  NoDup vs'.
Proof.
  intros.
  apply remove_redundancy_spec_aux in Hred; simpl; try solve [constructor].
  destruct Hred as [J1 J2].
  split; auto.
    intros v0.  
    destruct (J1 v0) as [J3 J4].
    split; auto.
      intro J.
      apply J4 in J. destruct J; auto. inv H.
Qed.

Lemma remove_redundancy_in: forall vs,
  (forall v0, In v0 vs <-> In v0 (remove_redundancy nil vs)).
Proof.
  intros.
  assert (remove_redundancy nil vs = remove_redundancy nil vs) as EQ.
    auto.
  apply remove_redundancy_spec in EQ. destruct EQ; auto.
Qed.

Lemma remove_redundancy_NoDup: forall vs, NoDup (remove_redundancy nil vs).
Proof.
  intros.
  assert (remove_redundancy nil vs = remove_redundancy nil vs) as EQ.
    auto.
  apply remove_redundancy_spec in EQ. destruct EQ; auto.
Qed.

(* The elemens in ATree, and remove_redundancy in mem2reg is similar to this,
   how to merge them? *)
End RemoveRedundancy.

Implicit Arguments remove_redundancy [A].

(***********************************************************************)

Module AtomSet. Section AtomSet.

  Variable A:Type.
  Variable Hdec: forall x y : A, {x = y} + {x <> y}.

  Definition set_eq (l1 l2:list A) := incl l1 l2 /\ incl l2 l1.

  Lemma set_eq_dec : forall (l1 l2:set A),
    {set_eq l1 l2} + {~ set_eq l1 l2}.
  Proof.
    intros l1 l2.
    destruct (incl_dec Hdec l1 l2) as [J | J].
      destruct (incl_dec Hdec l2 l1) as [J' | J'].
        left. split; auto.
        right. intro G. destruct G as [G1 G2]. auto.
      destruct (incl_dec Hdec l2 l1) as [J' | J'].
        right. intro G. destruct G as [G1 G2]. auto.
        right. intro G. destruct G as [G1 G2]. auto.
  Qed.

  Lemma set_eq_app : forall x1 x2 y1 y2,
    set_eq x1 y1 -> set_eq x2 y2 -> set_eq (x1++x2) (y1++y2).
  Proof.
    intros x1 x2 y1 y2 [Hinc11 Hinc12] [Hinc21 Hinc22].
    split.
      apply incl_app.
        apply incl_appl; auto.
        apply incl_appr; auto.
      apply incl_app.
        apply incl_appl; auto.
        apply incl_appr; auto.
  Qed.

  Lemma set_eq_swap : forall x1 x2,
    set_eq (x1++x2) (x2++x1).
  Proof.
    intros x1 x2.
    split.
      apply incl_app.
        apply incl_appr; auto using incl_refl.
        apply incl_appl; auto using incl_refl.
      apply incl_app.
        apply incl_appr; auto using incl_refl.
        apply incl_appl; auto using incl_refl.
  Qed.

  Lemma set_eq__rewrite_env : forall x1 x2 x3 y1 y2 y3,
    set_eq ((x1 ++ x2) ++ x3) ((y1 ++ y2) ++ y3) ->
    set_eq (x1 ++ x2 ++ x3) (y1 ++ y2 ++ y3).
  Proof.
    intros.
    repeat rewrite <- app_assoc in H. auto.
  Qed.

  Lemma set_eq_refl : forall x, set_eq x x.
    split; apply incl_refl.
  Qed.

  Lemma set_eq_sym: forall x y, set_eq x y -> set_eq y x.
  Proof.
    intros x y J.
    destruct J as [J1 J2]. split; auto.
  Qed.

  Lemma set_eq_trans: forall x y z,
    set_eq x y -> set_eq y z -> set_eq x z.
  Proof.
    intros x y z J1 J2.
    destruct J1 as [J11 J12].
    destruct J2 as [J21 J22].
    split; eapply incl_tran; eauto.
  Qed.

  Lemma incl_empty_inv : forall x,
    incl x (empty_set _) -> x = empty_set A.
  Proof.
    destruct x; intro J; auto.
      assert (J1:=J a).
      contradict J1; simpl; auto.
  Qed.

  Lemma set_eq_empty_inv : forall x,
    set_eq x (empty_set _) -> x = empty_set _.
  Proof.
    destruct x; intro J; auto.
      destruct J as [J1 J2].
      assert (J:=J1 a).
      contradict J; simpl; auto.
  Qed.

  Lemma incl_set_eq_left : forall x1 x2 y,
    set_eq x1 x2 -> incl x1 y -> incl x2 y.
  Proof.
    intros x1 x2 y [J1 J2] Hincl.
    eapply incl_tran; eauto.
  Qed.

  Lemma set_eq__incl : forall x1 x2, set_eq x1 x2 -> incl x1 x2.
  Proof.
    intros x1 x2 J.
    destruct J; auto.
  Qed.

  Lemma incl_set_eq_both : forall x1 x2 y1 y2,
    set_eq x1 x2 ->
    set_eq y1 y2 ->
    incl x1 y1 -> incl x2 y2.
  Proof.
    intros x1 x2 y1 y2 [J1 J2] [J3 J4] J5.
    apply incl_tran with (m:=y1); auto.
    apply incl_tran with (m:=x1); auto.
  Qed.

  Lemma set_eq_empty_inv2 : forall x,
    set_eq (ListSet.empty_set _) x -> x = ListSet.empty_set _.
  Proof.
    intros.
    apply set_eq_sym in H.
    eapply set_eq_empty_inv; eauto.
  Qed.

  Lemma incl_app_invr : forall (l1 l2 l:list A),
    incl (l1++l2) l -> incl l2 l.
  Proof.
    intros l1 l2 l H x J.
    apply H.
    apply (@incl_appr _ l2 l1 l2); auto using incl_refl.
  Qed.

  Lemma incl_app_invl : forall (l1 l2 l:list A),
    incl (l1++l2) l -> incl l1 l.
  Proof.
    intros l1 l2 l H x J.
    apply H.
    apply (@incl_appl _ l1 l2 l1); auto using incl_refl.
  Qed.

  Lemma incl_set_eq_right : forall y1 y2 x,
    set_eq y1 y2 -> incl x y1 -> incl x y2.
  Proof.
    intros y1 y2 x [J1 J2] Hincl.
    eapply incl_tran; eauto.
  Qed.

  Lemma set_eq_inter : forall l1 l2 l1' l2'
    (H : set_eq l1 l1')
    (H0 : set_eq l2 l2'),
    set_eq (ListSet.set_inter Hdec l1 l2)
      (ListSet.set_inter Hdec l1' l2').
  Proof.
    intros.
    destruct H. destruct H0.
    split; intros a J.
      apply ListSet.set_inter_intro.
        apply ListSet.set_inter_elim1 in J; auto.
          apply H; auto.
        apply ListSet.set_inter_elim2 in J; auto.
          apply H0; auto.
      apply ListSet.set_inter_intro.
        apply ListSet.set_inter_elim1 in J; auto.
          apply H1; auto.
        apply ListSet.set_inter_elim2 in J; auto.
          apply H2; auto.
  Qed.

  Lemma set_inter_empty_eq_empty1: forall l1,
     set_eq (set_inter Hdec (empty_set _) l1) (empty_set _).
  Proof.
     intros.
      split; intros x J.
        apply set_inter_elim in J.
        destruct J; auto.
        inv J.
  Qed.

  Lemma set_inter_empty_eq_empty2: forall l1,
     set_eq (set_inter Hdec l1 (empty_set _)) (empty_set _).
  Proof.
     intros.
      split; intros x J.
        apply set_inter_elim in J.
        destruct J; auto.
        inv J.
  Qed.

  Lemma set_inter_incl: forall l1 l2,
    incl l1 l2 -> set_eq (set_inter Hdec l1 l2) l1.
  Proof.
    intros.
    split; intros x J.
      apply set_inter_elim in J.
      destruct J; auto.

      apply set_inter_intro; auto.
        apply H in J; auto.
  Qed.

  Lemma set_inter_refl: forall l1, set_eq (set_inter Hdec l1 l1) l1.
  Proof.
    intro.
    split; intros x J.
      apply set_inter_elim in J.
      destruct J; auto.

      apply set_inter_intro; auto.
  Qed.

  Lemma incl_inter : forall l1 l2 l1' l2'
    (H : incl l1 l1') (H0 : incl l2 l2'),
    incl (ListSet.set_inter Hdec l1 l2)
         (ListSet.set_inter Hdec l1' l2').
  Proof.
    intros.
    intros x J.
    apply set_inter_elim in J. destruct J.
    apply H in H1. apply H0 in H2.
    apply set_inter_intro; auto.
  Qed.

  Lemma set_eq_rev: forall pds,
    set_eq (rev pds) pds.
  Proof.
    induction pds; simpl.
      apply set_eq_refl.
 
      apply set_eq_trans with (y:=pds ++ (a::nil)).
        apply set_eq_app; auto using set_eq_refl.
        apply set_eq_swap; auto using set_eq_refl.
  Qed.

  Lemma incl_empty: forall s, incl (empty_set A) s.
  Proof. intros s. intros x Hinc. inv Hinc. Qed.

  Lemma set_inter_commut: forall (s s0 : set A),
    set_eq (set_inter Hdec s s0) (set_inter Hdec s0 s).
  Proof.
    intros.
    split.
      intros a J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro; auto.

      intros a J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro; auto.
  Qed.

  Lemma set_inter_incll: forall l1 l2,
    incl (set_inter Hdec l1 l2) l1.
  Proof.
    intros.
    intros x J.
    apply set_inter_elim in J; tauto.
  Qed.

  Lemma set_inter_inclr: forall l1 l2,
    incl (set_inter Hdec l1 l2) l2.
  Proof.
    intros.
    intros x J.
    apply set_inter_elim in J; tauto.
  Qed.

  Lemma incl_inter_left: forall s1 s2 s3 (H : incl s1 s3) (H' : incl s2 s3),
    incl (set_inter Hdec s1 s2) s3.
  Proof.
    intros.
    intros x Hin.
    apply set_inter_elim in Hin. 
    destruct Hin.
    eauto with datatypes v62.
  Qed.

  Lemma set_union_eq_right: forall x y z (Heq: set_eq y z),
    set_eq (set_union Hdec x y) (set_union Hdec x z).
  Proof.
    intros.
    destruct Heq as [J1 J2].
    split; intros e Hine.
      apply set_union_elim in Hine.
      apply set_union_intro.
      destruct Hine; auto.
        right. apply J1. auto.
  
      apply set_union_elim in Hine.
      apply set_union_intro.
      destruct Hine; auto.
        right. apply J2. auto.
  Qed.
  
  Lemma set_inter_union_distr_r: forall x1 x2 y,
    set_eq (set_inter Hdec y (x1++x2))
           (set_union Hdec (set_inter Hdec y x1) (set_inter Hdec y x2)).
  Proof.
    intros.
    split; intros e Hine.
      apply set_union_intro.
      apply set_inter_elim in Hine.
      destruct Hine as [J1 J2].
      unfold set_In in J2.
      destruct_in J2.
        left. apply set_inter_intro; auto. 
        right. apply set_inter_intro; auto. 
  
      apply set_union_elim in Hine.
      destruct Hine as [Hine | Hine].
        apply set_inter_elim in Hine.
        destruct Hine as [J1 J2].
        apply set_inter_intro; auto.
          apply in_or_app; auto.
  
        apply set_inter_elim in Hine.
        destruct Hine as [J1 J2].
        apply set_inter_intro; auto.
          apply in_or_app; auto.
  Qed.
  
  Lemma set_inter_notin_r: forall y xs (Hnotin: ~ In y xs),
    set_inter Hdec xs (y::nil) = empty_set _.
  Proof.
    induction xs; simpl; intros; auto.
      destruct_if.
        destruct_if.
        contradict Hnotin. auto.
  Qed.
              
  Lemma set_inter_prefix: forall x1 x2 y,
    set_eq (y ++ set_inter Hdec x1 x2)
           (set_inter Hdec (y++x1) (y++x2)).
  Proof.
    intros.
    split; intros e Hine.
      destruct_in Hine.
        apply set_inter_intro; unfold set_In; apply in_or_app; auto.
   
        apply set_inter_elim in Hine.
        destruct_conjs.
        apply set_inter_intro; unfold set_In in *; apply in_or_app; auto.
  
      apply set_inter_elim in Hine.
      destruct_conjs. unfold set_In in *.
      apply in_or_app.
      destruct_in H; auto.
      destruct_in H0; auto.
      right. apply set_inter_intro; auto.
  Qed.
  
  Lemma set_inter_drop_incl: forall x y1 y2 (Hinc: incl y1 y2),
    set_eq (set_inter Hdec x (y1++y2)) (set_inter Hdec x y2).
  Proof.
    intros.
    split; intros e Hine.
      apply set_inter_elim in Hine.
      destruct Hine as [J1 J2]. 
      unfold set_In in *.
      destruct_in J2.
        apply set_inter_intro; auto. 
          apply Hinc; auto.
        apply set_inter_intro; auto. 
  
      apply set_inter_elim in Hine.
      destruct Hine as [J1 J2]. 
      unfold set_In in *.
      apply set_inter_intro; auto. 
        unfold set_In. apply in_or_app; auto.
  Qed.
  
  Lemma in_incl: forall A (x:A) y (Hin: In x y), incl (x::nil) y.
  Proof.
    intros.
    intros e Hinx. 
    destruct_in Hinx.
  Qed. 
  
  Lemma set_inter_drop_notin_r: forall xs y ys (Hnotin: ~ In y xs),
    set_eq (set_inter Hdec xs (y::ys)) (set_inter Hdec xs ys).
  Proof.
    intros.
    split; intros e Hine.
      apply set_inter_elim in Hine.
      destruct Hine as [J1 J2].
      unfold set_In in *.
      destruct_in J2.
        apply set_inter_intro; auto.
  
      apply set_inter_elim in Hine.
      destruct Hine as [J1 J2].
      apply set_inter_intro; auto.
        unfold set_In. simpl. auto.
  Qed.
  
  Lemma set_inter_drop_notin_l: forall x xs ys (Hnotin: ~ In x ys),
    set_eq (set_inter Hdec (x::xs) ys) (set_inter Hdec xs ys).
  Proof.
    intros.
    apply set_inter_drop_notin_r with (ys:=xs) in Hnotin.
    apply set_eq_trans with (y:=set_inter Hdec ys xs); 
      eauto using set_eq_trans, set_inter_commut.
  Qed.

  Lemma set_union_empty_eq_empty2: forall l1,
    set_eq (set_union Hdec l1 (empty_set _)) l1.
  Proof.
    intros.
    split; intros x Hin.
      apply set_union_elim in Hin.
      destruct Hin as [Hin | Hin]; auto.
        inv Hin.
  
      apply set_union_intro; auto.
  Qed.
  
  Lemma set_eq_union : forall l1 l2 l1' l2'
    (H : set_eq l1 l1')
    (H0 : set_eq l2 l2'),
    set_eq (set_union Hdec l1 l2) (set_union Hdec l1' l2').
  Proof.
    intros.
    destruct H as [J1 J2].
    destruct H0 as [J3 J4].
    split; intros x Hin;
      apply set_union_elim in Hin;
      apply set_union_intro;
      destruct Hin as [Hin | Hin]; auto with datatypes v62.
  Qed.
          
  Lemma set_union_empty_eq_empty1: forall l1,
    set_eq (set_union Hdec (empty_set _) l1) l1.
  Proof.
    intros.
    split; intros x Hin.
      apply set_union_elim in Hin.
      destruct Hin as [Hin | Hin]; auto.
        inv Hin.
  
      apply set_union_intro; auto.
  Qed.
  
  Definition set_disjoint (ls1 ls2 : list A): Prop :=
  set_eq (set_inter Hdec ls1 ls2) (@empty_set A).

  Lemma set_remove_in_length: forall n s (Hin: In n s),
    S (length (set_remove Hdec n s)) = length s.
  Proof.
    induction s; simpl; intros.
      tauto.
  
      destruct_if.
      destruct Hin as [Hin | Hin]; subst; simpl; try solve [congruence | auto].
  Qed.
  
  Lemma set_remove_length: forall n s, 
    (length (set_remove Hdec n s) <= length s)%nat.
  Proof.
    induction s; simpl; intros.
      omega.
      destruct_if. simpl. omega.
  Qed.
  
  Lemma set_add_length: forall n s, 
    (length (set_add Hdec n s) <= S (length s))%nat.
  Proof.
    induction s; simpl; intros.
      omega.
      destruct_if. simpl. omega.
  Qed.
  
  Lemma set_add_NoDup: forall n s (Hnodup: NoDup s), NoDup (set_add Hdec n s).
  Proof.
    induction 1; simpl.
      constructor; auto. constructor. 
  
      destruct_if.
      constructor; auto. 
      constructor; auto.
        intro J. apply set_add_elim in J.
        destruct J as [J | J]; subst; auto.
  Qed.
  
  Lemma set_inter_NoDup: forall s1 s2 (Hnodup1: NoDup s1) (Hnodup2: NoDup s2), 
    NoDup (set_inter Hdec s1 s2).
  Proof.
    induction 1; simpl; intros.
      constructor.
  
      destruct_if.
      constructor; auto. 
        intro J. apply set_inter_elim in J.
        destruct J. auto.
  Qed.
  
  Lemma set_remove_spec1 : forall s n n',
    In n' s -> n <> n' -> In n' (set_remove Hdec n s).
  Proof.
    induction s; intros; simpl in *; auto.
      destruct H as [H | H]; subst.
        destruct (Hdec n n') as [J1 | J2]; subst;
          try solve [simpl; auto | contradict H0; auto].

        destruct (Hdec n a) as [J1 | J2]; subst; simpl; auto.
  Qed.

  Lemma set_remove_spec2 : forall s n n',
    In n' (set_remove Hdec n s) -> In n' s.
  Proof.
    induction s; intros; simpl in *; auto.
      destruct (Hdec n a) as [J1 | J2]; subst; simpl in *; auto.
        destruct H as [H | H]; eauto.
  Qed.
  
  Lemma set_remove_NoDup: forall n s (Hnodup: NoDup s), 
    NoDup (set_remove Hdec n s).
  Proof.
    induction 1; simpl.
      constructor. 
  
      destruct_if.
      constructor; auto. 
        intro J. apply set_remove_spec2 in J.
        auto.
  Qed.

  Lemma incl__eq_or_exact: forall
    (l1 l2:list A) (Hinc: incl l1 l2),
    set_eq l1 l2 \/ (exists a, In a l2 /\ ~ In a l1).
  Proof.
    intros.
    destruct (incl_dec Hdec l2 l1) as [J | J].
      left. split; auto.
  
      right. clear Hinc.
      generalize dependent l1.
      induction l2; intros.
        contradict J. intros x Hinx. inv Hinx.
        
        assert (~ In a l1 \/ ~ incl l2 l1) as G.
          destruct (In_dec Hdec a l1); auto.
            right. intro K. apply J. auto with datatypes v62.
        destruct G as [G | G].
          exists a. simpl. auto.
  
          apply IHl2 in G. destruct G as [a' [Hin Hnotin]]. 
          exists a'. simpl. auto.
  Qed.

  Definition elements_of_set (ls1: list A): list A :=
  remove_redundancy Hdec nil ls1.

  Lemma incl_elements_of_set: forall l1 l2 (Hinc : incl l1 l2),
    incl (elements_of_set l1) (elements_of_set l2).
  Proof.
    intros.
    intros x Hinx.
      apply remove_redundancy_in.
      apply Hinc.
      unfold elements_of_set in Hinx.
      eapply remove_redundancy_in in Hinx; eauto. 
  Qed.
  
  Lemma length_incl_elements_of_set: forall l1 l2 (Hinc : incl l1 l2),
    (length (elements_of_set l1) <= length (elements_of_set l2))%nat.
  Proof.
    intros.
    apply incl_elements_of_set in Hinc.
    apply NoDup_incl_length in Hinc; auto.
      apply remove_redundancy_NoDup.
      apply remove_redundancy_NoDup.
  Qed.

  Lemma exact_incl_elements_of_set: forall l1 l2 
    (Hinc : incl l1 l2) (Hex: exists a, In a l2 /\ ~ In a l1),
    incl (elements_of_set l1) (elements_of_set l2) /\
      exists a, In a (elements_of_set l2) /\ ~ In a (elements_of_set l1).
  Proof.
    intros.
    split.
      apply incl_elements_of_set; auto.
  
      destruct Hex as [a [Hin Hnotin]].
      apply remove_redundancy_in with (Hdec:=Hdec) in Hin.
      exists a.
      split; auto.
        intro J.
        apply Hnotin.
        unfold elements_of_set in J.
        eapply remove_redundancy_in in J; eauto. 
  Qed.
  
  Lemma length_exact_incl_elements_of_set: forall l1 l2 (Hinc : incl l1 l2)
     (Hex: exists a, In a l2 /\ ~ In a l1),
    (length (elements_of_set l1) < length (elements_of_set l2))%nat.
  Proof.
    intros.
    apply exact_incl_elements_of_set in Hinc; auto.
    destruct Hinc as [J1 J2].
    apply NoDup_exact_incl_length in J1; auto.
      apply remove_redundancy_NoDup.
      apply remove_redundancy_NoDup.
  Qed.
  
  Lemma NoDup_set_eq_length_eq: forall 
    (ls1:list A) (Hnp1: NoDup ls1) ls2
    (Hnp2: NoDup ls2) (Heq: AtomSet.set_eq ls1 ls2),
    (length ls1 = length ls2)%nat.
  Proof.
    intros.
    destruct Heq as [J1 J2].
    apply NoDup_incl_length in J1; auto.
    apply NoDup_incl_length in J2; auto.
    omega.
  Qed.

End AtomSet. 

Hint Resolve set_eq_app set_eq_swap set_eq__rewrite_env set_eq_refl
  set_eq_sym set_eq_trans incl_empty_inv set_eq_empty_inv 
  incl_set_eq_left set_eq__incl incl_set_eq_both set_eq_empty_inv2
  incl_app_invr  incl_app_invl incl_set_eq_right set_eq_inter 
  set_inter_empty_eq_empty1 set_inter_empty_eq_empty2 incl_inter_left
  incl_empty set_inter_commut set_inter_incll set_inter_inclr
  set_inter_incl set_inter_refl incl_inter set_eq_rev
  set_union_eq_right set_inter_union_distr_r set_inter_notin_r
  set_inter_prefix set_inter_drop_incl in_incl
  set_inter_drop_notin_r set_inter_drop_notin_l 
  set_union_empty_eq_empty2 set_eq_union set_union_empty_eq_empty1: atomset.

End AtomSet.

(*********** More positive *************)

Lemma Pnlt__Pgt_Peq : forall n m: positive, 
  ~ ((n < m)%positive) -> (n > m)%positive \/ (n = m)%positive.
Proof.
  unfold BinPos.Plt, Pgt.
  intros.
  remember ((n ?= m)%positive) as R.
  destruct R; try solve [congruence | auto].
    symmetry in HeqR.
    apply Pos.compare_eq_iff in HeqR. intuition.
Qed.

Lemma Pgt_trans : forall (n m p : positive)
  (H1: (n > m)%positive) (H2: (m > p)%positive), (n > p)%positive.
Proof.
  unfold Pgt; intros.
  apply ZC2. apply ZC1 in H1. apply ZC1 in H2.
  eapply Plt_trans; eauto.
Qed.

Lemma Plt_succ': forall (x: positive), (x < (Psucc x))%positive.
Proof. apply Pcompare_p_Sp. Qed.

Lemma Pgt_irrefl: forall p, ~ (p>p)%positive.
Proof.
  intros. intros J.
  apply ZC1 in J.
  contradict J. apply Plt_irrefl.
Qed.

Lemma Pgt_neq: forall p1 p2, (p1>p2)%positive -> p1 <> p2.
Proof.
  intros. intro EQ. subst.
  eapply Pgt_irrefl; eauto.
Qed.

Lemma Plt_neq: forall p1 p2, (p1<p2)%positive -> p1 <> p2.
Proof.
  intros. intro EQ. subst.
  eapply Plt_irrefl; eauto.
Qed.

Hint Resolve Pgt_irrefl Pgt_neq Plt_neq Plt_lt_succ Plt_succ' Plt_trans
  : positive.

Ltac Peqb_eq_tac :=
repeat match goal with
| H: Peqb _ _ = true |- _ => eapply Peqb_eq in H; subst
| |- Peqb _ _ = true => eapply Peqb_eq
end.

Fixpoint P_of_plus_nat p (n:nat) : positive :=
  match n with
    | O => p
    | S x => Psucc (P_of_plus_nat p x)
  end.

Lemma P_of_plus_one_nat__P_of_succ_nat: forall n,
  P_of_plus_nat 1 n = P_of_succ_nat n.
Proof.
  induction n; simpl; auto.
    rewrite <- IHn. auto.
Qed.

Lemma P_of_plus_nat__ge_base: forall q n,
  (P_of_plus_nat q n >= q)%positive.
Proof.
  induction n; simpl; intros; zify; omega.
Qed.

Lemma P_of_plus_nat__ge: forall q n1 n2 (Hge: (n1 >= n2)%nat),
  (P_of_plus_nat q n1 >= P_of_plus_nat q n2)%positive.
Proof.
  induction n1; simpl; intros.
    destruct n2; simpl; zify; omega.

    destruct n2; simpl.
      assert (J:=P_of_plus_nat__ge_base q n1).
      zify; omega.

      assert (n1>=n2)%nat as J. omega.   
      apply IHn1 in J. 
      zify; omega.
Qed.

Lemma P_of_plus_nat_Pplus_commut: forall n p1 p2,
  (p1 + (P_of_plus_nat p2 n) = P_of_plus_nat (p1 + p2) n)%positive.
Proof.
  induction n; simpl; auto.
    intros.
    rewrite <- IHn. zify; omega.
Qed.

(*********** Forall *************)

Lemma Forall_split: forall A (R:A->Prop) ls2 ls1
  (Hst: Forall R (ls1++ls2)),
  Forall R ls1 /\ Forall R ls2.
Proof.
  induction ls1; simpl; intros.
    split; auto. 

    inv Hst. 
    split; try tauto. 
      constructor; try tauto.     
Qed.

Lemma Forall_rev_cons: forall A n (R:A->Prop) (Hp: R n) ls1 (H1: Forall R ls1),
  Forall R (ls1 ++ n::nil).
Proof.
  induction 2; simpl; intros; constructor; auto.
Qed.

Lemma order_lt_order: forall p x (Horder : (p > x)%positive) l0
  (Horder : Forall (Plt p) l0),
  Forall (Plt x) l0.
Proof.
  induction 2; simpl; intros; constructor; auto.
    eapply Plt_trans; eauto.
    apply ZC1. auto.
Qed.

Lemma Forall_lt__notin: forall Xd Ysdms (H : Forall (Plt Xd) Ysdms),
  ListSet.set_mem positive_eq_dec Xd Ysdms = false.
Proof.
  induction 1; simpl; auto.
    destruct_if.
      apply Plt_ne in H. congruence.
Qed.

(*********** Sort *************)

Require Import Sorted.

Lemma sorted_append: forall A (R:A -> A -> Prop) a (l1:list A),
  (forall a1 l1',
    l1 = l1'++a1::nil -> R a1 a) ->
  Sorted R l1 -> Sorted R (l1 ++ a :: nil).
Proof.
  induction l1; intros; simpl; auto.
    inv H0.
    constructor; auto.
      apply IHl1; auto.
        intros. subst.
        apply H with (l1'0:=a0 :: l1'); auto.
      inv H4; simpl; auto.
      constructor.
        apply H with (l1':=nil); auto.
Qed.

Lemma HdRel_insert: forall A (R:A -> A -> Prop) a a0 l2 l1
  (H : forall (a1 : A) (l1' : list A), a :: l1 = l1' ++ a1 :: nil -> R a1 a0)
  (H5 : HdRel R a (l1 ++ l2)),
  HdRel R a (l1 ++ a0 :: l2).
Proof.
  induction l1; simpl; intros.
    constructor.
      apply H with (l1':=nil); auto.
    inv H5. constructor; auto.
Qed.

Lemma sorted_insert: forall A (R:A -> A -> Prop) (l2 l1:list A) a,
  (forall a1 l1', l1 = l1'++a1::nil -> R a1 a) ->
  (forall a2 l2', l2 = a2::l2' -> R a a2) ->
  Sorted R (l1 ++ l2) -> Sorted R (l1 ++ a :: l2).
Proof.
  induction l1; simpl; intros.
    constructor; auto.
      destruct l2; constructor.
        eapply H0; eauto.

    inv H1.
    constructor.
      apply IHl1; auto.
        intros. subst.
        apply H with (l1'0:=a::l1'); eauto.
        apply HdRel_insert; auto.
Qed.

Lemma Sorted_HdRel__Forall: forall A (R : A -> A -> Prop) l0 (H0 : Sorted R l0),
  forall a : A,
  (forall x y z : A,
   In x (a :: l0) ->
   In y (a :: l0) -> In z (a :: l0) -> R x y -> R y z -> R x z) ->
  HdRel R a l0 -> Forall (R a) l0.
Proof.
  induction l0; simpl; intros.
    apply Forall_forall.
    intros. inv H2.

    apply Forall_forall.
    intros.
    simpl in H2.
    inv H1.
    destruct H2 as [H2 | H2]; subst; auto.
    inv H0.
    apply IHl0 in H6; auto.
      eapply Forall_forall in H6; eauto.
      apply H with (y:=a); auto.

      intros.
      eapply H with (y:=y); simpl; eauto.
Qed.

Lemma strict_Sorted_StronglySorted : forall A (R:A -> A -> Prop) data,
  (forall x y z,
     In x data -> In y data -> In z data ->
     R x y -> R y z -> R x z) ->
  Sorted R data -> StronglySorted R data.
Proof.
  intros.
  induction H0; constructor.
    apply IHSorted.
      intros. eapply H with (y:=y); simpl; eauto.
      apply Sorted_HdRel__Forall in H; auto.
Qed.

Lemma Plt_Sorted__rev_Pgt_Sorted: forall dts (Hsort : Sorted Plt dts),
  Sorted Pgt (rev dts).
Proof.
  induction 1; simpl; auto.
    apply sorted_append; auto.
      intros.
      rewrite <- rev_involutive in H at 1.
      rewrite H0 in H. rewrite rev_unit in H. inv H. 
      apply ZC2 in H2. auto.
Qed.

Lemma Pgt_Sorted__StronglySorted: forall l1 (Hsort: Sorted Pgt l1), 
  StronglySorted Pgt l1.
Proof.
  intros.
  apply Sorted_StronglySorted; auto.
   unfold Relations_1.Transitive.
   apply Pgt_trans.
Qed.

Lemma StronglySorted_split: forall A (R:A->A->Prop) ls2 ls1
  (Hst: StronglySorted R (ls1++ls2)),
  StronglySorted R ls1 /\ StronglySorted R ls2.
Proof.
  induction ls1; simpl; intros.
    split; auto. 
      constructor.

    inv Hst. 
    apply Forall_split in H2.
    split; try tauto. 
      constructor; try tauto.
Qed.

Lemma StronglySorted__R_front_back: forall A (R:A->A->Prop) ls2 ls1
  (Hst: StronglySorted R (ls1++ls2)) a1 a2 (Hin1: In a1 ls1) (Hin2: In a2 ls2),
  R a1 a2.
Proof.
  induction ls1; simpl; intros.
    tauto.

    inv Hst.
    destruct Hin1 as [Hin1 | Hin1]; subst; eauto.
      eapply Forall_forall in H2; eauto with datatypes v62.
Qed.

Lemma StronglySorted_rev_cons: forall A (R:A->A->Prop) n ls1 
  (Hst: StronglySorted R ls1) (Hp: Forall (fun a => R a n) ls1),
  StronglySorted R (ls1++n::nil).
Proof.
  induction ls1; simpl; intros.
    constructor; auto.

    inv Hst. inv Hp.
    constructor; auto.
      apply Forall_rev_cons; auto. 
Qed.

Lemma Plt_Sorted__StronglySorted: forall l1 (Hsort: Sorted Plt l1), 
  StronglySorted Plt l1.
Proof.
  intros.
  apply Sorted_StronglySorted; auto.
   unfold Relations_1.Transitive.
   eauto with positive.
Qed.

