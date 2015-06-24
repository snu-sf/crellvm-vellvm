(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Formalization of floating-point numbers, using the Flocq library. *)

Require Import Coqlib.
Require Import Integers.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.
Require Import Fappli_IEEE_extra.
Require Import Fcore.
Require Import Program.
Require Archi.

Close Scope R_scope.

Definition float := binary64. (**r the type of IEE754 double-precision FP numbers *)
Definition float32 := binary32. (**r the type of IEE754 single-precision FP numbers *)

(** Boolean-valued comparisons *)

Definition cmp_of_comparison (c: comparison) (x: option Datatypes.comparison) : bool :=
  match c with
  | Ceq =>
      match x with Some Eq => true | _ => false end
  | Cne =>
      match x with Some Eq => false | _ => true end
  | Clt =>
      match x with Some Lt => true | _ => false end
  | Cle =>
      match x with Some(Lt|Eq) => true | _ => false end
  | Cgt =>
      match x with Some Gt => true | _ => false end
  | Cge =>
      match x with Some(Gt|Eq) => true | _ => false end
  end.

Lemma cmp_of_comparison_swap:
  forall c x,
  cmp_of_comparison (swap_comparison c) x =
  cmp_of_comparison c (match x with None => None | Some x => Some (CompOpp x) end).
Proof.
  intros. destruct c; destruct x as [[]|]; reflexivity. 
Qed.

Lemma cmp_of_comparison_ne_eq:
  forall x, cmp_of_comparison Cne x = negb (cmp_of_comparison Ceq x).
Proof.
  intros. destruct x as [[]|]; reflexivity. 
Qed.

Lemma cmp_of_comparison_lt_eq_false:
  forall x, cmp_of_comparison Clt x = true -> cmp_of_comparison Ceq x = true -> False.
Proof.
  destruct x as [[]|]; simpl; intros; discriminate.
Qed.

Lemma cmp_of_comparison_le_lt_eq:
  forall x, cmp_of_comparison Cle x = cmp_of_comparison Clt x || cmp_of_comparison Ceq x.
Proof.
  destruct x as [[]|]; reflexivity.
Qed.

Lemma cmp_of_comparison_gt_eq_false:
  forall x, cmp_of_comparison Cgt x = true -> cmp_of_comparison Ceq x = true -> False.
Proof.
  destruct x as [[]|]; simpl; intros; discriminate.
Qed.

Lemma cmp_of_comparison_ge_gt_eq:
  forall x, cmp_of_comparison Cge x = cmp_of_comparison Cgt x || cmp_of_comparison Ceq x.
Proof.
  destruct x as [[]|]; reflexivity.
Qed.

Lemma cmp_of_comparison_lt_gt_false:
  forall x, cmp_of_comparison Clt x = true -> cmp_of_comparison Cgt x = true -> False.
Proof.
  destruct x as [[]|]; simpl; intros; discriminate.
Qed.

(** Function used to parse floats *)

Program Definition build_from_parsed
  (prec:Z) (emax:Z) (prec_gt_0 : Prec_gt_0 prec) (Hmax:prec < emax)
  (base:positive) (intPart:positive) (expPart:Z) :=
  match expPart return _ with
    | Z0 =>
      binary_normalize prec emax prec_gt_0 Hmax mode_NE (Zpos intPart) Z0 false
    | Zpos p =>
      binary_normalize prec emax prec_gt_0 Hmax mode_NE ((Zpos intPart) * Zpower_pos (Zpos base) p) Z0 false
    | Zneg p =>
      let exp := Zpower_pos (Zpos base) p in
      match exp return 0 < exp -> _ with
        | Zneg _ | Z0 => _
        | Zpos p =>
          fun _ =>
          FF2B prec emax _ (proj1 (Bdiv_correct_aux prec emax prec_gt_0 Hmax mode_NE false intPart Z0 false p Z0))
      end _
  end.
Next Obligation.
  apply Zpower_pos_gt_0. reflexivity.
Qed.

Local Notation __ := (refl_equal Datatypes.Lt).

Local Hint Extern 1 (Prec_gt_0 _) => exact (refl_equal Datatypes.Lt).
Local Hint Extern 1 (_ < _) => exact (refl_equal Datatypes.Lt).

(** * Double-precision FP numbers *)

Module Float.

(** ** NaN payload manipulations *)

(** The following definitions are not part of the IEEE754 standard but
    apply to all architectures supported by CompCert. *)

(** Transform a Nan payload to a quiet Nan payload. *)

Program Definition transform_quiet_pl (pl:nan_pl 53) : nan_pl 53 :=
  Pos.lor pl (nat_iter 51 xO xH).
Next Obligation.
  destruct pl.
  simpl. rewrite Z.ltb_lt in *.
  assert (forall x, S (Fcore_digits.digits2_Pnat x) = Pos.to_nat (Pos.size x)).
  { induction x0; simpl; auto; rewrite IHx0; zify; omega. }
  fold (Z.of_nat (S (Fcore_digits.digits2_Pnat (Pos.lor x 2251799813685248)))).
  rewrite H, positive_nat_Z, Psize_log_inf, <- Zlog2_log_inf in *. clear H.
  change (Z.pos (Pos.lor x 2251799813685248)) with (Z.lor (Z.pos x) 2251799813685248%Z).
  rewrite Z.log2_lor by (zify; omega).
  apply Z.max_case. auto. simpl. omega.
Qed.

Lemma nan_payload_fequal:
  forall prec (p1 p2: nan_pl prec),
  proj1_sig p1 = proj1_sig p2 -> p1 = p2.
Proof.
  intros. destruct p1, p2; simpl in H; subst. f_equal. apply Fcore_Zaux.eqbool_irrelevance.
Qed.

Lemma lor_idempotent:
  forall x y, Pos.lor (Pos.lor x y) y = Pos.lor x y.
Proof.
  induction x; destruct y; simpl; f_equal; auto;
  induction y; simpl; f_equal; auto.
Qed.

Lemma transform_quiet_pl_idempotent:
  forall pl, transform_quiet_pl (transform_quiet_pl pl) = transform_quiet_pl pl.
Proof.
  intros. apply nan_payload_fequal; simpl. apply lor_idempotent.
Qed.

(** Nan payload operations for single <-> double conversions. *)

Definition expand_pl (pl: nan_pl 24) : nan_pl 53.
Proof.
  refine (exist _ (Pos.shiftl_nat (proj1_sig pl) 29) _).
  abstract (
    destruct pl; unfold proj1_sig, Pos.shiftl_nat, nat_iter, Fcore_digits.digits2_Pnat;
    fold (Fcore_digits.digits2_Pnat x);
    rewrite Z.ltb_lt in *;
    zify; omega).
Defined.

Definition of_single_pl (s:bool) (pl:nan_pl 24) : (bool * nan_pl 53) :=
  (s,
   if Archi.float_of_single_preserves_sNaN
   then expand_pl pl
   else transform_quiet_pl (expand_pl pl)).

Definition reduce_pl (pl: nan_pl 53) : nan_pl 24.
Proof.
  refine (exist _ (Pos.shiftr_nat (proj1_sig pl) 29) _).
  abstract (
    destruct pl; unfold proj1_sig, Pos.shiftr_nat, nat_iter;
    rewrite Z.ltb_lt in *;
    assert (forall x, Fcore_digits.digits2_Pnat (Pos.div2 x) =
                      (Fcore_digits.digits2_Pnat x - 1)%nat) by (destruct x0; simpl; zify; omega);
    rewrite !H, <- !NPeano.Nat.sub_add_distr; zify; omega).
Defined.

Definition to_single_pl (s:bool) (pl:nan_pl 53) : (bool * nan_pl 24) :=
  (s, reduce_pl (transform_quiet_pl pl)).

(** NaN payload operations for opposite and absolute value. *)

Definition neg_pl (s:bool) (pl:nan_pl 53) := (negb s, pl).
Definition abs_pl (s:bool) (pl:nan_pl 53) := (false, pl).

(** The NaN payload operations for two-argument arithmetic operations
   are not part of the IEEE754 standard, but all architectures of
   Compcert share a similar NaN behavior, parameterized by:
- a "default" payload which occurs when an operation generates a NaN from
  non-NaN arguments;
- a choice function determining which of the payload arguments to choose,
  when an operation is given two NaN arguments. *)

Definition binop_pl (x y: binary64) : bool*nan_pl 53 :=
  match x, y with
  | B754_nan s1 pl1, B754_nan s2 pl2 =>
      if Archi.choose_binop_pl_64 s1 pl1 s2 pl2
      then (s2, transform_quiet_pl pl2)
      else (s1, transform_quiet_pl pl1)
  | B754_nan s1 pl1, _ => (s1, transform_quiet_pl pl1)
  | _, B754_nan s2 pl2 => (s2, transform_quiet_pl pl2)
  | _, _ => Archi.default_pl_64
  end.

(** ** Operations over double-precision floats *)

Definition zero: float := B754_zero _ _ false. (**r the float [+0.0] *)

Definition eq_dec: forall (f1 f2: float), {f1 = f2} + {f1 <> f2} := b64_eq_dec.

(** Arithmetic operations *)

Definition neg: float -> float := b64_opp neg_pl. (**r opposite (change sign) *)
Definition abs: float -> float := b64_abs abs_pl. (**r absolute value (set sign to [+]) *)
Definition add: float -> float -> float := b64_plus binop_pl mode_NE. (**r addition *)
Definition sub: float -> float -> float := b64_minus binop_pl mode_NE. (**r subtraction *)
Definition mul: float -> float -> float := b64_mult binop_pl mode_NE. (**r multiplication *)
Definition div: float -> float -> float := b64_div binop_pl mode_NE. (**r division *)
Definition cmp (c:comparison) (f1 f2: float) : bool := (**r comparison *)
  cmp_of_comparison c (b64_compare f1 f2).

(** Conversions *)

Definition of_single: float32 -> float := b64_of_b32 of_single_pl mode_NE.
Definition to_single: float -> float32 := b32_of_b64 to_single_pl mode_NE.

Definition to_int (f:float): option int := (**r conversion to signed 32-bit int *)
  option_map Int.repr (b64_to_Z_range f Int.min_signed Int.max_signed).
Definition to_intu (f:float): option int := (**r conversion to unsigned 32-bit int *)
  option_map Int.repr (b64_to_Z_range f 0 Int.max_unsigned).
Definition to_long (f:float): option int64 := (**r conversion to signed 64-bit int *)
  option_map Int64.repr (b64_to_Z_range f Int64.min_signed Int64.max_signed).
Definition to_longu (f:float): option int64 := (**r conversion to unsigned 64-bit int *)
  option_map Int64.repr (b64_to_Z_range f 0 Int64.max_unsigned).

Definition of_int (n:int): float := (**r conversion from signed 32-bit int *)
  b64_of_Z (Int.signed n).
Definition of_intu (n:int): float:= (**r conversion from unsigned 32-bit int *)
  b64_of_Z (Int.unsigned n).

Definition of_long (n:int64): float := (**r conversion from signed 64-bit int *)
  b64_of_Z (Int64.signed n).
Definition of_longu (n:int64): float:= (**r conversion from unsigned 64-bit int *)
  b64_of_Z (Int64.unsigned n).

Definition from_parsed (base:positive) (intPart:positive) (expPart:Z) : float :=
  build_from_parsed 53 1024 __ __ base intPart expPart.

(** Conversions between floats and their concrete in-memory representation
    as a sequence of 64 bits. *)

Definition to_bits (f: float): int64 := Int64.repr (bits_of_b64 f).
Definition of_bits (b: int64): float := b64_of_bits (Int64.unsigned b).

Definition from_words (hi lo: int) : float := of_bits (Int64.ofwords hi lo).

(** ** Properties *)

(** Below are the only properties of floating-point arithmetic that we
  rely on in the compiler proof. *)

(** Some tactics **)

Ltac compute_this val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.

Ltac smart_omega :=
  simpl radix_val in *; simpl Zpower in *;
  compute_this Int.modulus; compute_this Int.half_modulus;
  compute_this Int.max_unsigned;
  compute_this Int.min_signed; compute_this Int.max_signed;
  compute_this Int64.modulus; compute_this Int64.half_modulus;
  compute_this Int64.max_unsigned;
  compute_this (Zpower_pos 2 1024); compute_this (Zpower_pos 2 53); compute_this (Zpower_pos 2 52); compute_this (Zpower_pos 2 32);
  zify; omega.

(** Commutativity properties of addition and multiplication. *)

Theorem add_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> add x y = add y x.
Proof.
  intros. apply Bplus_commut.
  destruct x, y; try reflexivity. simpl in H. intuition congruence.
Qed.

Theorem mul_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> mul x y = mul y x.
Proof.
  intros. apply Bmult_commut.
  destruct x, y; try reflexivity. simpl in H. intuition congruence.
Qed.

(** Multiplication by 2 is diagonal addition. *)

Theorem mul2_add:
  forall f, add f f = mul f (of_int (Int.repr 2%Z)).
Proof.
  intros. apply Bmult2_Bplus. 
  intros. destruct x; try discriminate. simpl. 
  transitivity (b, transform_quiet_pl n). 
  destruct Archi.choose_binop_pl_64; auto. 
  destruct y; auto || discriminate.
Qed.

(** Divisions that can be turned into multiplication by an inverse. *)

Definition exact_inverse : float -> option float := b64_exact_inverse. 

Theorem div_mul_inverse:
  forall x y z, exact_inverse y = Some z -> div x y = mul x z.
Proof.
  intros. apply Bdiv_mult_inverse; auto. 
  intros. destruct x0; try discriminate. simpl. 
  transitivity (b, transform_quiet_pl n). 
  destruct y0; reflexivity || discriminate.
  destruct z0; reflexivity || discriminate.
Qed.

(** Properties of comparisons. *)

Theorem cmp_swap:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  unfold cmp, b64_compare; intros. rewrite (Bcompare_swap _ _ x y).
  apply cmp_of_comparison_swap. 
Qed.

Theorem cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).
Proof.
  intros; apply cmp_of_comparison_ne_eq. 
Qed.

Theorem cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_eq_false.
Qed.

Theorem cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_le_lt_eq.
Qed.

Theorem cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_gt_eq_false.
Qed.

Theorem cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_ge_gt_eq.
Qed.

Theorem cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_gt_false.
Qed.

(** Properties of conversions to/from in-memory representation.
  The conversions are bijective (one-to-one). *)

Theorem of_to_bits:
  forall f, of_bits (to_bits f) = f.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b64, b64_of_bits.
  rewrite Int64.unsigned_repr, binary_float_of_bits_of_binary_float; [reflexivity|].
  generalize (bits_of_binary_float_range 52 11 __ __ f).
  change (2^(52+11+1)) with (Int64.max_unsigned + 1). omega. 
Qed.

Theorem to_of_bits:
  forall b, to_bits (of_bits b) = b.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b64, b64_of_bits.
  rewrite bits_of_binary_float_of_bits. apply Int64.repr_unsigned.
  apply Int64.unsigned_range. 
Qed.

(** Conversions between floats and unsigned ints can be defined
  in terms of conversions between floats and signed ints.
  (Most processors provide only the latter, forcing the compiler
  to emulate the former.)   *)

Definition ox8000_0000 := Int.repr Int.half_modulus.  (**r [0x8000_0000] *)

Theorem of_intu_of_int_1:
  forall x,
  Int.ltu x ox8000_0000 = true ->
  of_intu x = of_int x.
Proof.
  unfold of_intu, of_int, Int.signed, Int.ltu; intro.
  change (Int.unsigned ox8000_0000) with Int.half_modulus.
  destruct (zlt (Int.unsigned x) Int.half_modulus); now intuition.
Qed.

Theorem of_intu_of_int_2:
  forall x,
  Int.ltu x ox8000_0000 = false ->
  of_intu x = add (of_int (Int.sub x ox8000_0000)) (of_intu ox8000_0000).
Proof.
  unfold add, b64_plus, of_intu, of_int, b64_of_Z; intros.
  set (y := Int.sub x ox8000_0000).
  pose proof (Int.unsigned_range x); pose proof (Int.signed_range y).
  assert (Ry: integer_representable 53 1024 (Int.signed y)).
  { apply integer_representable_n; auto; smart_omega. }
  assert (R8: integer_representable 53 1024 (Int.unsigned ox8000_0000)).
  { apply integer_representable_2p with (p := 31);auto; smart_omega. }
  rewrite BofZ_plus by auto.
  f_equal. 
  unfold Int.ltu in H. destruct zlt in H; try discriminate.
  unfold y, Int.sub. rewrite Int.signed_repr. omega.
  compute_this (Int.unsigned ox8000_0000); smart_omega.
Qed.

Theorem to_intu_to_int_1:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = true ->
  to_intu x = Some n ->
  to_int x = Some n.
Proof.
  intros. unfold to_intu in H0. 
  destruct (b64_to_Z_range x 0 Int.max_unsigned) as [p|] eqn:E; simpl in H0; inv H0.
  unfold b64_to_Z_range in E. exploit ZofB_range_inversion; eauto. intros (A & B & C).
  unfold to_int, b64_to_Z_range. unfold ZofB_range. rewrite C. 
  rewrite Zle_bool_true by smart_omega. rewrite Zle_bool_true; auto.
  exploit (BofZ_exact 53 1024 __ __ (Int.unsigned ox8000_0000)).
  vm_compute; intuition congruence.
  set (y := of_intu ox8000_0000) in *.
  change (BofZ 53 1024 eq_refl eq_refl (Int.unsigned ox8000_0000)) with y.
  intros (EQy & FINy & SIGNy).
  assert (FINx: is_finite _ _ x = true).
  { rewrite ZofB_correct in C. destruct (is_finite _ _ x) eqn:FINx; congruence. }
  destruct (zeq p 0). 
  subst p; smart_omega.
  destruct (ZofB_range_pos 53 1024 __ __ x p C) as [P Q]. omega.
  assert (CMP: b64_compare x y = Some Lt). 
  { unfold cmp, cmp_of_comparison in H. destruct (b64_compare x y) as [[]|]; auto; discriminate. }
  unfold b64_compare in CMP. rewrite Bcompare_finite_correct in CMP by auto. 
  inv CMP. apply Rcompare_Lt_inv in H1. rewrite EQy in H1.
  assert (p < Int.unsigned ox8000_0000).
  { apply lt_Z2R. eapply Rle_lt_trans; eauto. }
  change Int.max_signed with (Int.unsigned ox8000_0000 - 1). omega. 
Qed.

Theorem to_intu_to_int_2:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = false ->
  to_intu x = Some n ->
  to_int (sub x (of_intu ox8000_0000)) = Some (Int.sub n ox8000_0000).
Proof.
  intros. unfold to_intu in H0. 
  destruct (b64_to_Z_range x 0 Int.max_unsigned) as [p|] eqn:E; simpl in H0; inv H0.
  unfold b64_to_Z_range in E. exploit ZofB_range_inversion; eauto. intros (A & B & C).
  exploit (BofZ_exact 53 1024 __ __ (Int.unsigned ox8000_0000)).
  vm_compute; intuition congruence.
  set (y := of_intu ox8000_0000) in *.
  change (BofZ 53 1024 __ __ (Int.unsigned ox8000_0000)) with y.
  intros (EQy & FINy & SIGNy).
  assert (FINx: is_finite _ _ x = true).
  { rewrite ZofB_correct in C. destruct (is_finite _ _ x) eqn:FINx; congruence. }
  assert (GE: (B2R _ _ x >= Z2R (Int.unsigned ox8000_0000))%R).
  { rewrite <- EQy. unfold cmp, cmp_of_comparison, b64_compare in H.
    rewrite Bcompare_finite_correct in H by auto. 
    destruct (Rcompare (B2R 53 1024 x) (B2R 53 1024 y)) eqn:CMP.
    apply Req_ge; apply Rcompare_Eq_inv; auto.
    discriminate.
    apply Rgt_ge; apply Rcompare_Gt_inv; auto. 
  } 
  assert (EQ: b64_to_Z_range (sub x y) Int.min_signed Int.max_signed = Some (p - Int.unsigned ox8000_0000)).
  {
    apply ZofB_range_minus. exact E. 
    compute_this (Int.unsigned ox8000_0000). smart_omega.
    apply Rge_le; auto.
  } 
  unfold to_int; rewrite EQ. simpl. f_equal. unfold Int.sub. f_equal. f_equal. 
  symmetry; apply Int.unsigned_repr. omega.
Qed.

(** Conversions from ints to floats can be defined as bitwise manipulations
  over the in-memory representation.  This is what the PowerPC port does.
  The trick is that [from_words 0x4330_0000 x] is the float
  [2^52 + of_intu x]. *)

Definition ox4330_0000 := Int.repr 1127219200.        (**r [0x4330_0000] *)

Lemma split_bits_or:
  forall x,
  split_bits 52 11 (Int64.unsigned (Int64.ofwords ox4330_0000 x)) = (false, Int.unsigned x, 1075).
Proof.
  intros.
  transitivity (split_bits 52 11 (join_bits 52 11 false (Int.unsigned x) 1075)).
  - f_equal. rewrite Int64.ofwords_add'. reflexivity.
  - apply split_join_bits.
    compute; auto.
    generalize (Int.unsigned_range x).
    compute_this Int.modulus; compute_this (2^52); omega.
    compute_this (2^11); omega.
Qed.

Lemma from_words_value:
  forall x,
     B2R _ _ (from_words ox4330_0000 x) = (bpow radix2 52 + Z2R (Int.unsigned x))%R
  /\ is_finite _ _ (from_words ox4330_0000 x) = true
  /\ Bsign _ _ (from_words ox4330_0000 x) = false.
Proof.
  intros; unfold from_words, of_bits, b64_of_bits, binary_float_of_bits.
  rewrite B2R_FF2B, is_finite_FF2B, Bsign_FF2B.
  unfold binary_float_of_bits_aux; rewrite split_bits_or; simpl; pose proof (Int.unsigned_range x).
  destruct (Int.unsigned x + Zpower_pos 2 52) eqn:?.
  exfalso; now smart_omega.
  simpl; rewrite <- Heqz;  unfold F2R; simpl. split; auto.
  rewrite <- (Z2R_plus 4503599627370496), Rmult_1_r. f_equal. rewrite Zplus_comm. auto.
  exfalso; now smart_omega.
Qed.

Lemma from_words_eq:
  forall x, from_words ox4330_0000 x = BofZ 53 1024 __ __ (2^52 + Int.unsigned x).
Proof.
  intros. 
  pose proof (Int.unsigned_range x).
  destruct (from_words_value x) as (A & B & C).
  destruct (BofZ_exact 53 1024 __ __ (2^52 + Int.unsigned x)) as (D & E & F).
  smart_omega.
  apply B2R_Bsign_inj; auto.
  rewrite A, D. rewrite Z2R_plus. auto. 
  rewrite C, F. symmetry. apply Zlt_bool_false. smart_omega. 
Qed.

Theorem of_intu_from_words:
  forall x,
  of_intu x = sub (from_words ox4330_0000 x) (from_words ox4330_0000 Int.zero).
Proof.
  intros. pose proof (Int.unsigned_range x).
  rewrite ! from_words_eq. unfold sub, b64_minus. rewrite BofZ_minus. 
  unfold of_intu, b64_of_Z. f_equal. rewrite Int.unsigned_zero. omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; rewrite Int.unsigned_zero; smart_omega.
Qed.

Lemma ox8000_0000_signed_unsigned:
  forall x,
    Int.unsigned (Int.add x ox8000_0000) = Int.signed x + Int.half_modulus.
Proof.
  intro; unfold Int.signed, Int.add; pose proof (Int.unsigned_range x).
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  rewrite Int.unsigned_repr; compute_this (Int.unsigned ox8000_0000); now smart_omega.
  rewrite (Int.eqm_samerepr _ (Int.unsigned x + -2147483648)).
  rewrite Int.unsigned_repr; now smart_omega.
  apply Int.eqm_add; [now apply Int.eqm_refl|exists 1;reflexivity].
Qed.

Theorem of_int_from_words:
  forall x,
  of_int x = sub (from_words ox4330_0000 (Int.add x ox8000_0000))
                 (from_words ox4330_0000 ox8000_0000).
Proof.
  intros. 
  pose proof (Int.signed_range x).
  rewrite ! from_words_eq. rewrite ox8000_0000_signed_unsigned.
  change (Int.unsigned ox8000_0000) with Int.half_modulus.
  unfold sub, b64_minus. rewrite BofZ_minus. 
  unfold of_int, b64_of_Z. f_equal. omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
Qed.

Definition ox4530_0000 := Int.repr 1160773632.        (**r [0x4530_0000] *)

Lemma split_bits_or':
  forall x,
  split_bits 52 11 (Int64.unsigned (Int64.ofwords ox4530_0000 x)) = (false, Int.unsigned x, 1107).
Proof.
  intros.
  transitivity (split_bits 52 11 (join_bits 52 11 false (Int.unsigned x) 1107)).
  - f_equal. rewrite Int64.ofwords_add'. reflexivity.
  - apply split_join_bits.
    compute; auto.
    generalize (Int.unsigned_range x).
    compute_this Int.modulus; compute_this (2^52); omega.
    compute_this (2^11); omega.
Qed.

Lemma from_words_value':
  forall x,
     B2R _ _ (from_words ox4530_0000 x) = (bpow radix2 84 + Z2R (Int.unsigned x * two_p 32))%R
  /\ is_finite _ _ (from_words ox4530_0000 x) = true
  /\ Bsign _ _ (from_words ox4530_0000 x) = false.
Proof.
  intros; unfold from_words, of_bits, b64_of_bits, binary_float_of_bits.
  rewrite B2R_FF2B, is_finite_FF2B, Bsign_FF2B.
  unfold binary_float_of_bits_aux; rewrite split_bits_or'; simpl; pose proof (Int.unsigned_range x).
  destruct (Int.unsigned x + Zpower_pos 2 52) eqn:?.
  exfalso; now smart_omega.
  simpl; rewrite <- Heqz;  unfold F2R; simpl. split; auto.
  rewrite <- (Z2R_plus 19342813113834066795298816), <- (Z2R_mult _ 4294967296).
  f_equal; compute_this (Zpower_pos 2 52); compute_this (two_power_pos 32); ring.
  assert (Zneg p < 0) by reflexivity.
  exfalso; now smart_omega.
Qed.

Lemma from_words_eq':
  forall x, from_words ox4530_0000 x = BofZ 53 1024 __ __ (2^84 + Int.unsigned x * 2^32).
Proof.
  intros. 
  pose proof (Int.unsigned_range x).
  destruct (from_words_value' x) as (A & B & C).
  destruct (BofZ_representable 53 1024 __ __ (2^84 + Int.unsigned x * 2^32)) as (D & E & F).
  replace (2^84 + Int.unsigned x * 2^32)
    with  ((2^52 + Int.unsigned x) * 2^32) by ring. 
  apply integer_representable_n2p; auto. smart_omega. omega. omega.
  apply B2R_Bsign_inj; auto.
  rewrite A, D. rewrite <- Z2R_Zpower by omega. rewrite <- Z2R_plus. auto. 
  rewrite C, F. symmetry. apply Zlt_bool_false. 
  compute_this (2^84); compute_this (2^32); omega.
Qed.

Theorem of_longu_from_words:
  forall l,
  of_longu l =
    add (sub (from_words ox4530_0000 (Int64.hiword l))
             (from_words ox4530_0000 (Int.repr (two_p 20))))
        (from_words ox4330_0000 (Int64.loword l)).
Proof.
  intros.
  pose proof (Int64.unsigned_range l).
  pose proof (Int.unsigned_range (Int64.hiword l)).
  pose proof (Int.unsigned_range (Int64.loword l)).
  rewrite ! from_words_eq, ! from_words_eq'. 
  set (p20 := Int.unsigned (Int.repr (two_p 20))).
  set (x := Int64.unsigned l) in *;
  set (xl := Int.unsigned (Int64.loword l)) in *;
  set (xh := Int.unsigned (Int64.hiword l)) in *.
  unfold sub, b64_minus. rewrite BofZ_minus.
  replace (2^84 + xh * 2^32 - (2^84 + p20 * 2^32))
     with ((xh - p20) * 2^32) by ring.
  unfold add, b64_plus. rewrite BofZ_plus. 
  unfold of_longu, b64_of_Z. f_equal. 
  rewrite <- (Int64.ofwords_recompose l) at 1. rewrite Int64.ofwords_add'.
  fold xh; fold xl. compute_this (two_p 32); compute_this p20; ring.
  apply integer_representable_n2p; auto.
  compute_this p20; smart_omega. omega. omega.
  apply integer_representable_n; auto; smart_omega. 
  replace (2^84 + xh * 2^32) with ((2^52 + xh) * 2^32) by ring.
  apply integer_representable_n2p; auto. smart_omega. omega. omega.
  change (2^84 + p20 * 2^32) with ((2^52 + 1048576) * 2^32).
  apply integer_representable_n2p; auto. omega. omega. 
Qed.

Theorem of_long_from_words:
  forall l,
  of_long l =
    add (sub (from_words ox4530_0000 (Int.add (Int64.hiword l) ox8000_0000))
             (from_words ox4530_0000 (Int.repr (two_p 20+two_p 31))))
        (from_words ox4330_0000 (Int64.loword l)).
Proof.
  intros.
  pose proof (Int64.signed_range l).
  pose proof (Int.signed_range (Int64.hiword l)).
  pose proof (Int.unsigned_range (Int64.loword l)).
  rewrite ! from_words_eq, ! from_words_eq'. 
  set (p := Int.unsigned (Int.repr (two_p 20 + two_p 31))).
  set (x := Int64.signed l) in *;
  set (xl := Int.unsigned (Int64.loword l)) in *;
  set (xh := Int.signed (Int64.hiword l)) in *.
  rewrite ox8000_0000_signed_unsigned. fold xh. 
  unfold sub, b64_minus. rewrite BofZ_minus.
  replace (2^84 + (xh + Int.half_modulus) * 2^32 - (2^84 + p * 2^32))
     with ((xh - 2^20) * 2^32) 
       by (compute_this p; compute_this Int.half_modulus; ring).
  unfold add, b64_plus. rewrite BofZ_plus. 
  unfold of_long, b64_of_Z. f_equal. 
  rewrite <- (Int64.ofwords_recompose l) at 1. rewrite Int64.ofwords_add''.
  fold xh; fold xl. compute_this (two_p 32); ring. 
  apply integer_representable_n2p; auto.
  compute_this (2^20); smart_omega. omega. omega.
  apply integer_representable_n; auto; smart_omega.
  replace (2^84 + (xh + Int.half_modulus) * 2^32)
     with ((2^52 + xh + Int.half_modulus) * 2^32) 
       by (compute_this Int.half_modulus; ring).
  apply integer_representable_n2p; auto. smart_omega. omega. omega.
  change (2^84 + p * 2^32) with ((2^52 + p) * 2^32).
  apply integer_representable_n2p; auto. 
  compute_this p; smart_omega. omega.
Qed.

(** Conversions from 64-bit integers can be expressed in terms of
  conversions from their 32-bit halves. *)

Theorem of_longu_decomp:
  forall l,
  of_longu l = add (mul (of_intu (Int64.hiword l)) (b64_of_Z (2^32)))
                   (of_intu (Int64.loword l)).
Proof.
  intros.
  unfold of_longu, of_intu, b64_of_Z, add, mul, b64_plus, b64_mult.
  pose proof (Int.unsigned_range (Int64.loword l)).
  pose proof (Int.unsigned_range (Int64.hiword l)).
  pose proof (Int64.unsigned_range l).
  set (x := Int64.unsigned l) in *.
  set (yl := Int.unsigned (Int64.loword l)) in *.
  set (yh := Int.unsigned (Int64.hiword l)) in *.
  assert (DECOMP: x = yh * 2^32 + yl).
  { unfold x. rewrite <- (Int64.ofwords_recompose l). apply Int64.ofwords_add'. }
  rewrite BofZ_mult. rewrite BofZ_plus. rewrite DECOMP; auto.
  apply integer_representable_n2p; auto. smart_omega. omega. omega. 
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
  compute; auto.
Qed.

Theorem of_long_decomp:
  forall l,
  of_long l = add (mul (of_int (Int64.hiword l)) (b64_of_Z (2^32)))
                  (of_intu (Int64.loword l)).
Proof.
  intros.
  unfold of_long, of_int, of_intu, b64_of_Z, add, mul, b64_plus, b64_mult.
  pose proof (Int.unsigned_range (Int64.loword l)).
  pose proof (Int.signed_range (Int64.hiword l)).
  pose proof (Int64.signed_range l).
  set (x := Int64.signed l) in *.
  set (yl := Int.unsigned (Int64.loword l)) in *.
  set (yh := Int.signed (Int64.hiword l)) in *.
  assert (DECOMP: x = yh * 2^32 + yl).
  { unfold x. rewrite <- (Int64.ofwords_recompose l), Int64.ofwords_add''. auto. }
  rewrite BofZ_mult. rewrite BofZ_plus. rewrite DECOMP; auto.
  apply integer_representable_n2p; auto. smart_omega. omega. omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto. compute; intuition congruence.
  compute; auto.
Qed.

(** Conversions from unsigned longs can be expressed in terms of conversions from signed longs.
    If the unsigned long is too big, a round-to-odd must be performed on it
    to avoid double rounding. *)

Theorem of_longu_of_long_1:
  forall x,
  Int64.ltu x (Int64.repr Int64.half_modulus) = true ->
  of_longu x = of_long x.
Proof.
  unfold of_longu, of_long, Int64.signed, Int64.ltu; intro.
  change (Int64.unsigned (Int64.repr Int64.half_modulus)) with Int64.half_modulus.
  destruct (zlt (Int64.unsigned x) Int64.half_modulus); now intuition.
Qed.

Theorem of_longu_of_long_2:
  forall x,
  Int64.ltu x (Int64.repr Int64.half_modulus) = false ->
  of_longu x = mul (of_long (Int64.or (Int64.shru x Int64.one)
                                      (Int64.and x Int64.one)))
                   (of_int (Int.repr 2)).
Proof.
  intros. change (of_int (Int.repr 2)) with (BofZ 53 1024 __ __ (2^1)).
  pose proof (Int64.unsigned_range x).
  unfold Int64.ltu in H. 
  change (Int64.unsigned (Int64.repr Int64.half_modulus)) with (2^63) in H.
  destruct (zlt (Int64.unsigned x) (2^63)); inv H.
  assert (Int64.modulus <= 2^1024 - 2^(1024-53)) by (vm_compute; intuition congruence).
  set (n := Int64.or (Int64.shru x Int64.one) (Int64.and x Int64.one)).
  assert (NB: forall i, 0 <= i < 64 ->
              Int64.testbit n i =
                if zeq i 0 then Int64.testbit x 1 || Int64.testbit x 0
                else if zeq i 63 then false else Int64.testbit x (i + 1)).
  { intros; unfold n; autorewrite with ints; auto. rewrite Int64.unsigned_one.
    rewrite Int64.bits_one. compute_this Int64.zwordsize. 
    destruct (zeq i 0); simpl proj_sumbool.
    rewrite zlt_true by omega. rewrite andb_true_r. subst i; auto. 
    rewrite andb_false_r, orb_false_r. 
    destruct (zeq i 63). subst i. apply zlt_false; omega.
    apply zlt_true; omega. }
  assert (NB2: forall i, 0 <= i ->
               Z.testbit (Int64.signed n * 2^1) i =
               if zeq i 0 then false else
               if zeq i 1 then Int64.testbit x 1 || Int64.testbit x 0 else
               Int64.testbit x i).
  { intros. rewrite Z.mul_pow2_bits by omega. destruct (zeq i 0).
    apply Z.testbit_neg_r; omega.
    rewrite Int64.bits_signed by omega. compute_this Int64.zwordsize. 
    destruct (zlt (i-1) 64). 
    rewrite NB by omega. destruct (zeq i 1).
    subst. rewrite dec_eq_true by auto. auto.
    rewrite dec_eq_false by omega. destruct (zeq (i - 1) 63). 
    symmetry. apply Int64.bits_above. compute_this Int64.zwordsize; omega. 
    f_equal; omega.
    rewrite NB by omega. rewrite dec_eq_false by omega. rewrite dec_eq_true by auto. 
    rewrite dec_eq_false by omega. symmetry. apply Int64.bits_above. compute_this Int64.zwordsize; omega. 
  }
  assert (EQ: Int64.signed n * 2 = int_round_odd (Int64.unsigned x) 1).
  {
  symmetry. apply (int_round_odd_bits 53 1024). omega.
  intros. rewrite NB2 by omega. replace i with 0 by omega. auto. 
  rewrite NB2 by omega. rewrite dec_eq_false by omega. rewrite dec_eq_true. 
  rewrite orb_comm. unfold Int64.testbit. change (2^1) with 2.
  destruct (Z.testbit (Int64.unsigned x) 0) eqn:B0;
  [rewrite Z.testbit_true in B0 by omega|rewrite Z.testbit_false in B0 by omega];
  change (2^0) with 1 in B0; rewrite Zdiv_1_r in B0; rewrite B0; auto.
  intros. rewrite NB2 by omega. rewrite ! dec_eq_false by omega. auto.
  }
  unfold mul, of_long, of_longu, b64_mult, b64_of_Z. 
  rewrite BofZ_mult_2p. 
- change (2^1) with 2. rewrite EQ. apply BofZ_round_odd with (p := 1).
+ omega.
+ apply Zle_trans with Int64.modulus; trivial. smart_omega.
+ omega.
+ apply Zle_trans with (2^63). compute; intuition congruence. xomega.
- apply Zle_trans with Int64.modulus; trivial.
  pose proof (Int64.signed_range n).
  compute_this Int64.min_signed; compute_this Int64.max_signed;
  compute_this Int64.modulus; xomega.
- assert (2^63 <= int_round_odd (Int64.unsigned x) 1).
  { change (2^63) with (int_round_odd (2^63) 1). apply (int_round_odd_le 0 0); omega. }
  rewrite <- EQ in H1. compute_this (2^63). compute_this (2^53). xomega. 
- omega.
Qed.

End Float.

(** * Single-precision FP numbers *)

Module Float32.

(** ** NaN payload manipulations *)

Program Definition transform_quiet_pl (pl:nan_pl 24) : nan_pl 24 :=
  Pos.lor pl (nat_iter 22 xO xH).
Next Obligation.
  destruct pl.
  simpl. rewrite Z.ltb_lt in *.
  assert (forall x, S (Fcore_digits.digits2_Pnat x) = Pos.to_nat (Pos.size x)).
  { induction x0; simpl; auto; rewrite IHx0; zify; omega. }
  fold (Z.of_nat (S (Fcore_digits.digits2_Pnat (Pos.lor x 4194304)))).
  rewrite H, positive_nat_Z, Psize_log_inf, <- Zlog2_log_inf in *. clear H.
  change (Z.pos (Pos.lor x 4194304)) with (Z.lor (Z.pos x) 4194304).
  rewrite Z.log2_lor by (zify; omega).
  apply Z.max_case. auto. simpl. omega.
Qed.

Lemma transform_quiet_pl_idempotent:
  forall pl, transform_quiet_pl (transform_quiet_pl pl) = transform_quiet_pl pl.
Proof.
  intros []; simpl; intros. apply Float.nan_payload_fequal.
  simpl. apply Float.lor_idempotent.
Qed.

Definition neg_pl (s:bool) (pl:nan_pl 24) := (negb s, pl).
Definition abs_pl (s:bool) (pl:nan_pl 24) := (false, pl).

Definition binop_pl (x y: binary32) : bool*nan_pl 24 :=
  match x, y with
  | B754_nan s1 pl1, B754_nan s2 pl2 =>
      if Archi.choose_binop_pl_32 s1 pl1 s2 pl2
      then (s2, transform_quiet_pl pl2)
      else (s1, transform_quiet_pl pl1)
  | B754_nan s1 pl1, _ => (s1, transform_quiet_pl pl1)
  | _, B754_nan s2 pl2 => (s2, transform_quiet_pl pl2)
  | _, _ => Archi.default_pl_32
  end.

(** ** Operations over single-precision floats *)

Definition zero: float32 := B754_zero _ _ false. (**r the float [+0.0] *)

Definition eq_dec: forall (f1 f2: float32), {f1 = f2} + {f1 <> f2} := b32_eq_dec.

(** Arithmetic operations *)

Definition neg: float32 -> float32 := b32_opp neg_pl. (**r opposite (change sign) *)
Definition abs: float32 -> float32 := b32_abs abs_pl. (**r absolute value (set sign to [+]) *)
Definition add: float32 -> float32 -> float32 := b32_plus binop_pl mode_NE. (**r addition *)
Definition sub: float32 -> float32 -> float32 := b32_minus binop_pl mode_NE. (**r subtraction *)
Definition mul: float32 -> float32 -> float32 := b32_mult binop_pl mode_NE. (**r multiplication *)
Definition div: float32 -> float32 -> float32 := b32_div binop_pl mode_NE. (**r division *)
Definition cmp (c:comparison) (f1 f2: float32) : bool := (**r comparison *)
  cmp_of_comparison c (b32_compare f1 f2).

(** Conversions *)

Definition of_double : float -> float32 := Float.to_single.
Definition to_double : float32 -> float := Float.of_single.

Definition to_int (f:float32): option int := (**r conversion to signed 32-bit int *)
  option_map Int.repr (b32_to_Z_range f Int.min_signed Int.max_signed).
Definition to_intu (f:float32): option int := (**r conversion to unsigned 32-bit int *)
  option_map Int.repr (b32_to_Z_range f 0 Int.max_unsigned).
Definition to_long (f:float32): option int64 := (**r conversion to signed 64-bit int *)
  option_map Int64.repr (b32_to_Z_range f Int64.min_signed Int64.max_signed).
Definition to_longu (f:float32): option int64 := (**r conversion to unsigned 64-bit int *)
  option_map Int64.repr (b32_to_Z_range f 0 Int64.max_unsigned).

Definition of_int (n:int): float32 := (**r conversion from signed 32-bit int to single-precision float *)
  b32_of_Z (Int.signed n).
Definition of_intu (n:int): float32 := (**r conversion from unsigned 32-bit int to single-precision float *)
  b32_of_Z (Int.unsigned n).

Definition of_long (n:int64): float32 := (**r conversion from signed 64-bit int to single-precision float *)
  b32_of_Z (Int64.signed n).
Definition of_longu (n:int64): float32 := (**r conversion from unsigned 64-bit int to single-precision float *)
  b32_of_Z (Int64.unsigned n).

Definition from_parsed (base:positive) (intPart:positive) (expPart:Z) : float32 :=
  build_from_parsed 24 128 __ __ base intPart expPart.

(** Conversions between floats and their concrete in-memory representation
    as a sequence of 32 bits. *)

Definition to_bits (f: float32) : int := Int.repr (bits_of_b32 f).
Definition of_bits (b: int): float32 := b32_of_bits (Int.unsigned b).

(** ** Properties *)

(** Commutativity properties of addition and multiplication. *)

Theorem add_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> add x y = add y x.
Proof.
  intros. apply Bplus_commut.
  destruct x, y; try reflexivity. simpl in H. intuition congruence.
Qed.

Theorem mul_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> mul x y = mul y x.
Proof.
  intros. apply Bmult_commut.
  destruct x, y; try reflexivity. simpl in H. intuition congruence.
Qed.

(** Multiplication by 2 is diagonal addition. *)

Theorem mul2_add:
  forall f, add f f = mul f (of_int (Int.repr 2%Z)).
Proof.
  intros. apply Bmult2_Bplus. 
  intros. destruct x; try discriminate. simpl. 
  transitivity (b, transform_quiet_pl n). 
  destruct Archi.choose_binop_pl_32; auto. 
  destruct y; auto || discriminate.
Qed.

(** Divisions that can be turned into multiplication by an inverse. *)

Definition exact_inverse : float32 -> option float32 := b32_exact_inverse. 

Theorem div_mul_inverse:
  forall x y z, exact_inverse y = Some z -> div x y = mul x z.
Proof.
  intros. apply Bdiv_mult_inverse; auto. 
  intros. destruct x0; try discriminate. simpl. 
  transitivity (b, transform_quiet_pl n). 
  destruct y0; reflexivity || discriminate.
  destruct z0; reflexivity || discriminate.
Qed.

(** Properties of comparisons. *)

Theorem cmp_swap:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  unfold cmp, b32_compare; intros. rewrite (Bcompare_swap _ _ x y).
  apply cmp_of_comparison_swap. 
Qed.

Theorem cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).
Proof.
  intros; apply cmp_of_comparison_ne_eq. 
Qed.

Theorem cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_eq_false.
Qed.

Theorem cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_le_lt_eq.
Qed.

Theorem cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_gt_eq_false.
Qed.

Theorem cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_ge_gt_eq.
Qed.

Theorem cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_gt_false.
Qed.

Theorem cmp_double:
  forall f1 f2 c, cmp c f1 f2 = Float.cmp c (to_double f1) (to_double f2).
Proof.
  unfold cmp, Float.cmp; intros. f_equal. symmetry. apply Bcompare_Bconv_widen.
  red; omega. omega. omega.
Qed.

(** Properties of conversions to/from in-memory representation.
  The conversions are bijective (one-to-one). *)

Theorem of_to_bits:
  forall f, of_bits (to_bits f) = f.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b32, b32_of_bits.
  rewrite Int.unsigned_repr, binary_float_of_bits_of_binary_float; [reflexivity|].
  generalize (bits_of_binary_float_range 23 8 __ __ f).
  change (2^(23+8+1)) with (Int.max_unsigned + 1). omega.
Qed.

Theorem to_of_bits:
  forall b, to_bits (of_bits b) = b.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b32, b32_of_bits.
  rewrite bits_of_binary_float_of_bits. apply Int.repr_unsigned.
  apply Int.unsigned_range. 
Qed.

(** Conversions from 32-bit integers to single-precision floats can
  be decomposed into a conversion to a double-precision float,
  followed by a [Float32.of_double] conversion.  No double rounding occurs. *)

Theorem of_int_double:
  forall n, of_int n = of_double (Float.of_int n).
Proof.
  intros. symmetry. apply Bconv_BofZ. 
  apply integer_representable_n; auto. generalize (Int.signed_range n); Float.smart_omega. 
Qed.

Theorem of_intu_double:
  forall n, of_intu n = of_double (Float.of_intu n).
Proof.
  intros. symmetry. apply Bconv_BofZ.
  apply integer_representable_n; auto. generalize (Int.unsigned_range n); Float.smart_omega. 
Qed.

(** Conversion of single-precision floats to integers can be decomposed
  into a [Float32.to_double] extension, followed by a double-precision-to-int
  conversion. *)

Theorem to_int_double:
  forall f n, to_int f = Some n -> Float.to_int (to_double f) = Some n.
Proof.
  intros.
  unfold to_int in H.
  destruct (b32_to_Z_range f Int.min_signed Int.max_signed) as [n'|] eqn:E; inv H.
  unfold Float.to_int, to_double, Float.of_single, b64_to_Z_range, b64_of_b32. 
  erewrite ZofB_range_Bconv; eauto. auto. omega. omega. omega. omega. 
Qed.

Theorem to_intu_double:
  forall f n, to_intu f = Some n -> Float.to_intu (to_double f) = Some n.
Proof.
  intros.
  unfold to_intu in H.
  destruct (b32_to_Z_range f 0 Int.max_unsigned) as [n'|] eqn:E; inv H.
  unfold Float.to_intu, to_double, Float.of_single, b64_to_Z_range, b64_of_b32. 
  erewrite ZofB_range_Bconv; eauto. auto. omega. omega. omega. omega. 
Qed.

Theorem to_long_double:
  forall f n, to_long f = Some n -> Float.to_long (to_double f) = Some n.
Proof.
  intros.
  unfold to_long in H.
  destruct (b32_to_Z_range f Int64.min_signed Int64.max_signed) as [n'|] eqn:E; inv H.
  unfold Float.to_long, to_double, Float.of_single, b64_to_Z_range, b64_of_b32. 
  erewrite ZofB_range_Bconv; eauto. auto. omega. omega. omega. omega. 
Qed.

Theorem to_longu_double:
  forall f n, to_longu f = Some n -> Float.to_longu (to_double f) = Some n.
Proof.
  intros.
  unfold to_longu in H.
  destruct (b32_to_Z_range f 0 Int64.max_unsigned) as [n'|] eqn:E; inv H.
  unfold Float.to_longu, to_double, Float.of_single, b64_to_Z_range, b64_of_b32. 
  erewrite ZofB_range_Bconv; eauto. auto. omega. omega. omega. omega. 
Qed.

(** Conversions from 64-bit integers to single-precision floats can be expressed
  as conversion to a double-precision float followed by a [Float32.of_double] conversion.
  To avoid double rounding when the integer is large (above [2^53]), a round
  to odd must be performed on the integer before conversion to double-precision float. *)

Lemma int_round_odd_plus:
  forall p n, 0 <= p ->
  int_round_odd n p = Z.land (Z.lor n (Z.land n (2^p-1) + (2^p-1))) (-(2^p)).
Proof.
  intros.
  assert (POS: 0 < 2^p) by (apply (Zpower_gt_0 radix2); auto). 
  assert (A: Z.land n (2^p-1) = n mod 2^p).
  { rewrite <- Z.land_ones by auto. f_equal. rewrite Z.ones_equiv. omega. }
  rewrite A.
  assert (B: 0 <= n mod 2^p < 2^p).
  { apply Z_mod_lt. omega. }
  set (m := n mod 2^p + (2^p-1)) in *.
  assert (C: m / 2^p = if zeq (n mod 2^p) 0 then 0 else 1).
  { unfold m. destruct (zeq (n mod 2^p) 0).
    rewrite e. apply Zdiv_small. omega. 
    eapply Zdiv_unique with (n mod 2^p - 1). ring. omega. }
  assert (D: Z.testbit m p = if zeq (n mod 2^p) 0 then false else true).
  { destruct (zeq (n mod 2^p) 0).
    apply Z.testbit_false; auto. rewrite C; auto.
    apply Z.testbit_true; auto. rewrite C; auto. }
  assert (E: forall i, p < i -> Z.testbit m i = false).
  { intros. apply Z.testbit_false. omega. 
    replace (m / 2^i) with 0. auto. symmetry. apply Zdiv_small. 
    unfold m. split. omega. apply Zlt_le_trans with (2 * 2^p). omega. 
    change 2 with (2^1) at 1. rewrite <- (Zpower_plus radix2) by omega. 
    apply Zpower_le. omega. }
  assert (F: forall i, 0 <= i -> Z.testbit (-2^p) i = if zlt i p then false else true).
  { intros. rewrite Z.bits_opp by auto. rewrite <- Z.ones_equiv.
    destruct (zlt i p). 
    rewrite Z.ones_spec_low by omega. auto.
    rewrite Z.ones_spec_high by omega. auto. }
  apply int_round_odd_bits; auto. 
  - intros. rewrite Z.land_spec, F, zlt_true by omega. apply andb_false_r. 
  - rewrite Z.land_spec, Z.lor_spec, D, F, zlt_false, andb_true_r by omega.
    destruct (Z.eqb (n mod 2^p) 0) eqn:Z. 
    rewrite Z.eqb_eq in Z. rewrite Z, zeq_true. apply orb_false_r. 
    rewrite Z.eqb_neq in Z. rewrite zeq_false by auto. apply orb_true_r. 
  - intros. rewrite Z.land_spec, Z.lor_spec, E, F, zlt_false, andb_true_r by omega.
    apply orb_false_r.
Qed.

Lemma of_long_round_odd:
  forall n conv_nan,
  2^36 <= Z.abs n < 2^64 ->
  b32_of_Z n = b32_of_b64 conv_nan mode_NE (b64_of_Z (Z.land (Z.lor n ((Z.land n 2047) + 2047)) (-2048))).
Proof.
  intros. rewrite <- (int_round_odd_plus 11) by omega.
  assert (-2^64 <= int_round_odd n 11). 
  { change (-2^64) with (int_round_odd (-2^64) 11). apply (int_round_odd_le 0 0); xomega. }
  assert (int_round_odd n 11 <= 2^64). 
  { change (2^64) with (int_round_odd (2^64) 11). apply (int_round_odd_le 0 0); xomega. }
  unfold b32_of_Z, b32_of_b64, b64_of_Z. 
  rewrite Bconv_BofZ. 
  apply BofZ_round_odd with (p := 11).
  omega.
  apply Zle_trans with (2^64). omega. compute; intuition congruence.
  omega.
  exact (proj1 H). 
  unfold int_round_odd. apply integer_representable_n2p_wide. auto. omega. 
  unfold int_round_odd in H0, H1. 
  split; (apply Zmult_le_reg_r with (2^11); [compute; auto | assumption]).
  omega.
  omega.
Qed.

Theorem of_longu_double_1:
  forall n,
  Int64.unsigned n <= 2^53 ->
  of_longu n = of_double (Float.of_longu n).
Proof.
  intros. symmetry; apply Bconv_BofZ. apply integer_representable_n; auto. 
  pose proof (Int64.unsigned_range n); omega.
Qed.

Theorem of_longu_double_2:
  forall n,
  2^36 <= Int64.unsigned n ->
  of_longu n = of_double (Float.of_longu 
                           (Int64.and (Int64.or n 
                                                (Int64.add (Int64.and n (Int64.repr 2047))
                                                           (Int64.repr 2047)))
                                      (Int64.repr (-2048)))).
Proof.
  intros.
  pose proof (Int64.unsigned_range n). 
  unfold of_longu. erewrite of_long_round_odd.
  unfold of_double, Float.to_single. instantiate (1 := Float.to_single_pl). 
  f_equal. unfold Float.of_longu. f_equal.
  set (n' := Z.land (Z.lor (Int64.unsigned n) (Z.land (Int64.unsigned n) 2047 + 2047)) (-2048)).
  assert (int_round_odd (Int64.unsigned n) 11 = n') by (apply int_round_odd_plus; omega).
  assert (0 <= n'). 
  { rewrite <- H1. change 0 with (int_round_odd 0 11). apply (int_round_odd_le 0 0); omega. }
  assert (n' < Int64.modulus). 
  { apply Zle_lt_trans with (int_round_odd (Int64.modulus - 1) 11). 
    rewrite <- H1. apply (int_round_odd_le 0 0); omega. 
    compute; auto. }
  rewrite <- (Int64.unsigned_repr n') by (unfold Int64.max_unsigned; omega).
  f_equal. Int64.bit_solve. rewrite Int64.testbit_repr by auto. unfold n'.
  rewrite Z.land_spec, Z.lor_spec. f_equal. f_equal. 
  unfold Int64.testbit. rewrite Int64.add_unsigned.
  fold (Int64.testbit (Int64.repr
        (Int64.unsigned (Int64.and n (Int64.repr 2047)) +
         Int64.unsigned (Int64.repr 2047))) i).
  rewrite Int64.testbit_repr by auto. f_equal. f_equal. unfold Int64.and.
  symmetry. apply Int64.unsigned_repr. change 2047 with (Z.ones 11).
  rewrite Z.land_ones by omega. 
  exploit (Z_mod_lt (Int64.unsigned n) (2^11)). compute; auto. 
  assert (2^11 < Int64.max_unsigned) by (compute; auto). omega. 
  apply Int64.same_bits_eqm; auto. exists (-1); auto.
  split. xomega. change (2^64) with Int64.modulus. xomega. 
Qed.

Theorem of_long_double_1:
  forall n,
  Z.abs (Int64.signed n) <= 2^53 ->
  of_long n = of_double (Float.of_long n).
Proof.
  intros. symmetry; apply Bconv_BofZ. apply integer_representable_n; auto. xomega. 
Qed.

Theorem of_long_double_2:
  forall n,
  2^36 <= Z.abs (Int64.signed n) ->
  of_long n = of_double (Float.of_long
                           (Int64.and (Int64.or n 
                                                (Int64.add (Int64.and n (Int64.repr 2047))
                                                           (Int64.repr 2047)))
                                      (Int64.repr (-2048)))).
Proof.
  intros.
  pose proof (Int64.signed_range n). 
  unfold of_long. erewrite of_long_round_odd.
  unfold of_double, Float.to_single. instantiate (1 := Float.to_single_pl). 
  f_equal. unfold Float.of_long. f_equal.
  set (n' := Z.land (Z.lor (Int64.signed n) (Z.land (Int64.signed n) 2047 + 2047)) (-2048)).
  assert (int_round_odd (Int64.signed n) 11 = n') by (apply int_round_odd_plus; omega).
  assert (Int64.min_signed <= n'). 
  { rewrite <- H1. change Int64.min_signed with (int_round_odd Int64.min_signed 11). apply (int_round_odd_le 0 0); omega. }
  assert (n' <= Int64.max_signed).
  { apply Zle_trans with (int_round_odd Int64.max_signed 11). 
    rewrite <- H1. apply (int_round_odd_le 0 0); omega. 
    compute; intuition congruence. }
  rewrite <- (Int64.signed_repr n') by omega.
  f_equal. Int64.bit_solve. rewrite Int64.testbit_repr by auto. unfold n'.
  rewrite Z.land_spec, Z.lor_spec. f_equal. f_equal.
  rewrite Int64.bits_signed by omega. rewrite zlt_true by omega. auto. 
  unfold Int64.testbit. rewrite Int64.add_unsigned.
  fold (Int64.testbit (Int64.repr
        (Int64.unsigned (Int64.and n (Int64.repr 2047)) +
         Int64.unsigned (Int64.repr 2047))) i).
  rewrite Int64.testbit_repr by auto. f_equal. f_equal. unfold Int64.and.
  change (Int64.unsigned (Int64.repr 2047)) with 2047. 
  change 2047 with (Z.ones 11). rewrite ! Z.land_ones by omega.
  rewrite Int64.unsigned_repr. apply Int64.eqmod_mod_eq. 
  apply Zlt_gt. apply (Zpower_gt_0 radix2); omega.
  apply Int64.eqmod_divides with (2^64). apply Int64.eqm_signed_unsigned. 
  exists (2^(64-11)); auto.
  exploit (Z_mod_lt (Int64.unsigned n) (2^11)). compute; auto. 
  assert (2^11 < Int64.max_unsigned) by (compute; auto). omega. 
  apply Int64.same_bits_eqm; auto. exists (-1); auto.
  split. auto. assert (-2^64 < Int64.min_signed) by (compute; auto). 
  assert (Int64.max_signed < 2^64) by (compute; auto).
  xomega.
Qed.

End Float32.

Global Opaque
  Float.zero Float.eq_dec Float.neg Float.abs Float.of_single Float.to_single
  Float.of_int Float.of_intu Float.of_long Float.of_longu
  Float.to_int Float.to_intu Float.to_long Float.to_longu
  Float.add Float.sub Float.mul Float.div Float.cmp
  Float.to_bits Float.of_bits Float.from_words.

Global Opaque
  Float32.zero Float32.eq_dec Float32.neg Float32.abs
  Float32.of_int Float32.of_intu Float32.of_long Float32.of_longu
  Float32.to_int Float32.to_intu Float32.to_long Float32.to_longu
  Float32.add Float32.sub Float32.mul Float32.div Float32.cmp
  Float32.to_bits Float32.of_bits.

