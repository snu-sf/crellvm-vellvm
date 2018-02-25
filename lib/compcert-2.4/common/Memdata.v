(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** In-memory representation of values. *)

Require Import Znumtheory.
Require Import Program.
Require Import Coqlib.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

(* NOTE: Vellvm Context *)

Definition bytesize_chunk (wz:nat) := ZRdiv (Z_of_nat (S wz)) 8.
Definition bytesize_chunk_nat (wz:nat) := nat_of_Z (bytesize_chunk wz).

Lemma bytesize_chunk_pos:
  forall wz, bytesize_chunk wz > 0.
Proof.
  intros. unfold bytesize_chunk.
  apply ZRdiv_prop5.
Qed.

Lemma bytesize_chunk_conv:
  forall wz, bytesize_chunk wz = Z_of_nat (bytesize_chunk_nat wz).
Proof.
  intros.
  unfold bytesize_chunk, bytesize_chunk_nat, bytesize_chunk.
  decEq. 
  rewrite nat_of_Z_eq. auto.
    apply ZRdiv_prop2; auto with zarith.
Qed.

Lemma bytesize_chunk_nat_pos:
  forall wz, exists n, bytesize_chunk_nat wz = S n.
Proof.
  intros. 
  generalize (bytesize_chunk_pos wz). rewrite bytesize_chunk_conv. 
  destruct (bytesize_chunk_nat wz).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint wz => bytesize_chunk wz
  | Mfloat32 => 4
  | Mfloat64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; try omega.
  apply bytesize_chunk_pos.
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z_of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; try reflexivity.
  simpl. apply bytesize_chunk_conv.
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv. 
  destruct (size_chunk_nat chunk).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

Lemma size_chunk_nat_pos':
  forall chunk, (size_chunk_nat chunk > 0)%nat.
Proof.
  intros.
  destruct (@size_chunk_nat_pos chunk) as [n J].
  rewrite J. omega.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint wz => 
    if le_lt_dec wz 31
    then bytesize_chunk wz
    else if zeq (bytesize_chunk wz) 8 then 8 else 1
  | Mfloat32 => 4
  | Mfloat64 => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; try omega.
    destruct (le_lt_dec n 31); try omega.
      apply bytesize_chunk_pos.
      destruct (zeq (bytesize_chunk n) 8); omega.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try solve [
    apply Zdivide_refl |
    destruct (le_lt_dec n 31); auto with zarith |
    exists 2; auto ]. 

    destruct (le_lt_dec n 31); auto with zarith.
    destruct (zeq (bytesize_chunk n) 8); auto with zarith.
      rewrite e.
      assert (8 = 2 * 4) as EQ. auto with zarith.
      rewrite EQ.
      simpl. apply Zdivide_refl. (* apply Zdivide_factor_l. *)
Qed.

(*
Lemma align_le_divides:
  forall chunk1 chunk2,
  align_chunk chunk1 <= align_chunk chunk2 -> (align_chunk chunk1 | align_chunk chunk2).
Proof.
  intros. destruct chunk1; destruct chunk2; simpl in *;
  solve [ omegaContradiction
        | apply Zdivide_refl
        | exists 2; reflexivity
        | exists 4; reflexivity
        | exists 8; reflexivity ].
Qed.
*)

Inductive quantity : Type := Q32 | Q64.

Definition quantity_eq (q1 q2: quantity) : {q1 = q2} + {q1 <> q2}.
Proof. decide equality. Defined.
Global Opaque quantity_eq.

Definition size_quantity_nat (q: quantity) :=
  match q with Q32 => 4%nat | Q64 => 8%nat end.

Lemma size_quantity_nat_pos:
  forall q, exists n, size_quantity_nat q = S n.
Proof.
  intros. destruct q; [exists 3%nat | exists 7%nat]; auto.
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque value;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Fragment: val -> quantity -> nat -> memval.

(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  of a given length *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Int.repr 7 x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Int.unsigned 7 b + int_of_bytes l' * 256
  end.

Definition rev_if_be (l: list byte) : list byte :=
  if Archi.big_endian then List.rev l else l.

Definition encode_int (sz: nat) (x: Z) : list byte :=
  rev_if_be (bytes_of_int sz x).

Definition decode_int (b: list byte) : Z :=
  int_of_bytes (rev_if_be b).

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma rev_if_be_length:
  forall l, length (rev_if_be l) = length l.
Proof.
  intros; unfold rev_if_be; destruct Archi.big_endian.
  apply List.rev_length.
  auto.
Qed.

Lemma encode_int_length:
  forall sz x, length(encode_int sz x) = sz.
Proof.
  intros. unfold encode_int. rewrite rev_if_be_length. apply length_bytes_of_int.
Qed.

(** Decoding after encoding *)

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
  rewrite inj_S. simpl.
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. 
  change (Int.unsigned 7 (Int.repr 7 x)) with (Int.Z_mod_modulus 7 x). 
  rewrite Int.Z_mod_modulus_eq. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma rev_if_be_involutive:
  forall l, rev_if_be (rev_if_be l) = l.
Proof.
  intros; unfold rev_if_be; destruct Archi.big_endian. 
  apply List.rev_involutive. 
  auto.
Qed.

Lemma decode_encode_int:
  forall n x, decode_int (encode_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  unfold decode_int, encode_int; intros. rewrite rev_if_be_involutive. 
  apply int_of_bytes_of_int.
Qed.

Lemma decode_encode_int_1:
  forall x, Int.repr 31 (decode_int (encode_int 1 (Int.unsigned 31 x))) = Int.zero_ext 31 8 x.
Proof.
  intros. rewrite decode_encode_int. 
  rewrite <- (Int.repr_unsigned 31 (Int.zero_ext 31 8 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute. intuition congruence. 
Qed.

Lemma decode_encode_int_2:
  forall x, Int.repr 31 (decode_int (encode_int 2 (Int.unsigned 31 x))) = Int.zero_ext 31 16 x.
Proof.
  intros. rewrite decode_encode_int. 
  rewrite <- (Int.repr_unsigned 31 (Int.zero_ext 31 16 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute; intuition congruence.
Qed.

Lemma decode_encode_int_4:
  forall x, Int.repr 31 (decode_int (encode_int 4 (Int.unsigned 31 x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Int.repr 31 (Int.unsigned 31 x)).
  decEq. apply Zmod_small. apply Int.unsigned_range. apply Int.repr_unsigned.
Qed.

Lemma decode_encode_int_8:
  forall x, Int.repr 63 (decode_int (encode_int 8 (Int.unsigned 63 x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Int.repr 63 (Int.unsigned 63 x)).
  decEq. apply Zmod_small. apply Int.unsigned_range. apply Int.repr_unsigned.
Qed.

(** A length-[n] encoding depends only on the low [8*n] bits of the integer. *)

Lemma bytes_of_int_mod:
  forall n x y,
  Int.eqmod (two_p (Z_of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite inj_S. 
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  intro EQM.
  simpl; decEq. 
  apply Int.eqm_samerepr. red. 
  eapply Int.eqmod_divides; eauto. apply Zdivide_factor_l.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ. 
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. omega.
Qed.

Lemma encode_int_8_mod:
  forall x y,
  Int.eqmod (two_p 8) x y ->
  encode_int 1%nat x = encode_int 1%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Lemma encode_int_16_mod:
  forall x y,
  Int.eqmod (two_p 16) x y ->
  encode_int 2%nat x = encode_int 2%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

(** * Encoding and decoding values *)

Definition inj_bytes (bl: list byte) : list memval :=
  List.map Byte bl.

Fixpoint proj_bytes (vl: list memval) : option (list byte) :=
  match vl with
  | nil => Some nil
  | Byte b :: vl' =>
      match proj_bytes vl' with None => None | Some bl => Some(b :: bl) end
  | _ => None
  end.

Remark length_inj_bytes:
  forall bl, length (inj_bytes bl) = length bl.
Proof.
  intros. apply List.map_length. 
Qed.

Remark proj_inj_bytes:
  forall bl, proj_bytes (inj_bytes bl) = Some bl.
Proof.
  induction bl; simpl. auto. rewrite IHbl. auto.
Qed.

Lemma inj_proj_bytes:
  forall cl bl, proj_bytes cl = Some bl -> cl = inj_bytes bl.
Proof.
  induction cl; simpl; intros. 
  inv H; auto.
  destruct a; try congruence. destruct (proj_bytes cl); inv H.
  simpl. decEq. auto.
Qed.

Fixpoint inj_value_rec (n: nat) (v: val) (q: quantity) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Fragment v q m :: inj_value_rec m v q
  end.

Definition inj_value (q: quantity) (v: val): list memval :=
  inj_value_rec (size_quantity_nat q) v q.

Fixpoint check_value (n: nat) (v: val) (q: quantity) (vl: list memval) 
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Fragment v' q' m' :: vl' =>
      Val.eq v v' && quantity_eq q q' && beq_nat m m' && check_value m v q vl'
  | _, _ => false
  end.

Definition proj_value (q: quantity) (vl: list memval) : val :=
  match vl with
  | Fragment v q' n :: vl' =>
      if check_value (size_quantity_nat q) v q vl then v else Vundef
  | _ => Vundef
  end.

Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  match v, chunk with
  | Vint wz n, Mint wz0 => inj_bytes (encode_int (bytesize_chunk_nat wz0) (Int.unsigned wz n))
(* 
  | Vint n, Mint8 => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Vint n, Mint16 => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Vint n, Mint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
*)
  | Vptr _ _, Mint wz | Vinttoptr _, Mint wz=> if eq_nat_dec 31 wz then inj_value Q32 v else list_repeat (size_chunk_nat chunk) Undef
(*  
  | Vlong n, Mint64 => inj_bytes (encode_int 8%nat (Int64.unsigned n)) 
*)
  | Vsingle n, Mfloat32 => inj_bytes (encode_int 4%nat (Int.unsigned 31 (Float32.to_bits n)))
  | Vfloat n, Mfloat64 => inj_bytes (encode_int 8%nat (Int.unsigned 63 (Float.to_bits n)))
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  match proj_bytes vl with
  | Some bl =>
      match chunk with
      | Mint wz0 => Vint wz0 (Int.repr wz0 (decode_int bl))
(*
      | Mint8 => Vint(Int.zero_ext 8 (Int.repr (decode_int bl)))
      | Mint16 => Vint(Int.zero_ext 16 (Int.repr (decode_int bl)))
      | Mint32 => Vint(Int.repr(decode_int bl))
      | Mint64 => Vlong(Int64.repr(decode_int bl))
*)
      | Mfloat32 => Vsingle (Float32.of_bits (Int.repr 31 (decode_int bl)))
      | Mfloat64 => Vfloat (Float.of_bits (Int.repr 63 (decode_int bl)))
      end
  | None =>
      match chunk with
      | Mint wz => if eq_nat_dec 31 wz then Val.load_result chunk (proj_value Q32 vl) else Vundef
      | _ => Vundef
      end
  end.

Lemma encode_val_length:
  forall chunk v, length(encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. destruct v; simpl; destruct chunk; Val.simplify_op;
  try solve [ reflexivity
        | apply length_list_repeat
        | rewrite length_inj_bytes; apply encode_int_length ].
Qed.

Lemma check_inj_value:
  forall v q n, check_value n v q (inj_value_rec n v q) = true.
Proof.
  induction n; simpl. auto. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Lemma proj_inj_value:
  forall q v, proj_value q (inj_value q v) = v.
Proof.
  intros. unfold proj_value, inj_value. destruct (size_quantity_nat_pos q) as [n EQ]. 
  rewrite EQ at 1. simpl. rewrite check_inj_value. auto.
Qed.

Remark in_inj_value:
  forall mv v q, In mv (inj_value q v) -> exists n, mv = Fragment v q n.
Proof.
Local Transparent inj_value.
  unfold inj_value; intros until q. generalize (size_quantity_nat q). induction n; simpl; intros.
  contradiction.
  destruct H. exists n; auto. eauto. 
Qed.

Lemma proj_inj_value_mismatch:
  forall q1 q2 v, q1 <> q2 -> proj_value q1 (inj_value q2 v) = Vundef.
Proof.
  intros. unfold proj_value. destruct (inj_value q2 v) eqn:V. auto. destruct m; auto.
  destruct (in_inj_value (Fragment v0 q n) v q2) as [n' EQ]. 
  rewrite V; auto with coqlib. inv EQ.
  destruct (size_quantity_nat_pos q1) as [p EQ1]; rewrite EQ1; simpl.
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_false by congruence. auto.
Qed.

Definition decode_encode_val (v1: val) (chunk1 chunk2: memory_chunk) (v2: val) : Prop :=
  match v1, chunk1, chunk2 with
  | Vundef, _, _ => v2 = Vundef

  | Vint wz n, Mint wz1, Mint wz2 => 
      if eq_nat_dec wz1 wz2 then
        v2 = Vint wz2 (Int.repr wz2 (Int.unsigned wz n))
      else True
  | Vint wz n, Mint wz', Mfloat32 =>
      if eq_nat_dec wz' 31
      then v2 = Vsingle(Float32.of_bits (Int.repr 31 (Int.unsigned wz n)))
(*    then v2 = Vfloat(decode_float Mfloat32 (encode_int (Mint32) wz n)) *)
      else True
  | Vint wz n, Mint wz', Mfloat64 => 
      if eq_nat_dec wz' 63
      then v2 = Vfloat(Float.of_bits (Int.repr 63 (Int.unsigned wz n)))
      else True
  | Vint _ _, (Mfloat32 | Mfloat64), _ => v2 = Vundef
(*  | Vint _ _, _, _ => True (**r nothing meaningful to say about v2 *) *)

  | Vptr b ofs, Mint wz1, Mint wz2 =>
    if eq_nat_dec 31 wz1 then
      if eq_nat_dec 31 wz2 then
        v2 = Vptr b ofs
      else v2 = Vundef
    else v2 = Vundef
  | Vptr b ofs, _, _ => v2 = Vundef

  | Vinttoptr i, Mint wz1, Mint wz2 =>
    if eq_nat_dec 31 wz1 then
      if eq_nat_dec 31 wz2 then
        v2 = Vinttoptr i
      else v2 = Vundef
    else v2 = Vundef
  | Vinttoptr i, _, _ => v2 = Vundef

  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, Mfloat64, Mint wz =>
    if eq_nat_dec 63 wz then
      v2 = Vint 63 (Float.to_bits f)
    else True
  | Vfloat f, (Mint _ | Mfloat32), _ => v2 = Vundef
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)

  | Vsingle f, Mfloat32, Mfloat32 => v2 = Vsingle f
  | Vsingle f, Mfloat32, Mint wz =>
    if eq_nat_dec 31 wz then
      v2 = Vint 31 (Float32.to_bits f)
    else True
  | Vsingle f, (Mint _ | Mfloat64), _ => v2 = Vundef
  | Vsingle f, _, _ => True (* nothing interesting to say about v2 *)
  end.

Remark decode_val_undef:
  forall bl chunk, decode_val chunk (Undef :: bl) = Vundef.
Proof.
  intros. unfold decode_val. simpl. destruct chunk; auto.
  destruct (eq_nat_dec 31 n); auto.
Qed.

Remark proj_bytes_inj_value:
  forall q v, proj_bytes (inj_value q v) = None.
Proof.
  intros. destruct q; reflexivity. 
Qed.


Remark undef_list_undef:
  forall n chunk, decode_val chunk (list_repeat (size_chunk_nat (Mint n)) Undef) = Vundef.
Proof.
  intros. assert (exists n', size_chunk_nat (Mint n) = S n') by apply size_chunk_nat_pos.
  inversion H as [n' Hex]. rewrite Hex.
  unfold decode_val. simpl. destruct chunk; auto.
  destruct (eq_nat_dec 31 n0); auto.
Qed.

Remark injv_proj_none:
  forall v q, proj_bytes (inj_value q v) = None.
Proof.
  intros; unfold inj_value; destruct q
  ; intros; destruct v; simpl; auto.
Qed.

Remark undef_projb_none:
  forall c, proj_bytes (list_repeat (size_chunk_nat c) Undef) = None.
Proof.
  intros; destruct c; auto.
  assert (exists n', size_chunk_nat (Mint n) = S n') by apply size_chunk_nat_pos.
  inversion H as [n' Hex]. rewrite Hex. auto.
Qed.

Remark undef_projb_none':
  forall n, (n > 0)%nat -> proj_bytes (list_repeat n Undef) = None.
Proof.
  intros; destruct n; auto. inv H.
Qed.

Remark undef_projv_undef:
  forall c q, proj_value q (list_repeat (size_chunk_nat c) Undef) = Vundef.
Proof.
  intros; destruct c; auto.
  assert (exists n', size_chunk_nat (Mint n) = S n') by apply size_chunk_nat_pos.
  inversion H as [n' Hex]. rewrite Hex. auto.
Qed.

Remark undef_projv_undef':
  forall n q, (n > 0)%nat -> proj_value q (list_repeat n Undef) = Vundef.
Proof.
  intros; destruct n; auto.
Qed.

Lemma Int_unsigned_inj: forall n (x y: Int.int n)
  (EQ: Int.unsigned _ x = Int.unsigned _ y),
  x = y.
Proof.
  intros. 
  rewrite <-(Int.repr_unsigned _ x), <-(Int.repr_unsigned _ y), EQ. 
  auto.
Qed.

(*
Lemma bytesize_chunk_nat_ge: forall n,
  Z.of_nat (bytesize_chunk_nat n) * 8 >= (Int.zwordsize n).
Proof.
  ...
Qed.
*)

(*
Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
Opaque inj_value.
  intros.
  destruct v; destruct chunk1 eqn:C1; simpl; try (apply undef_list_undef); try (apply decode_val_undef);
  destruct chunk2 eqn:C2; unfold decode_val; auto;
  try (rewrite proj_inj_bytes); try (rewrite proj_bytes_inj_value);
  try (rewrite proj_inj_value); try (rewrite proj_inj_value_mismatch by congruence);
  eauto.
  - (* Vint Mint Mint *)
    destruct (eq_nat_dec _ _); subst; auto. ....
  - (* Vint Mint Mfloat32 *)
    destruct (eq_nat_dec _ _); subst; auto. ....
  - (* Vint Mint Mfloat64 *)
    destruct (eq_nat_dec _ _); subst; auto. ....
  - (* Vfloat Mfloat64 Mint *)
    destruct (eq_nat_dec _ _); subst; auto. ....
  - (* Vfloat Mfloat64 Mfloat64 *)
    ....
  - (* Vsingle Mfloat32 Mint *)
    destruct (eq_nat_dec _ _); subst; auto. ....
  - (* Vsingle Mfloat32 Mfloat32 *)
    ....
  - (* Vptr Mint Mint *)
    destruct (eq_nat_dec 31 n); subst; auto;
    destruct (eq_nat_dec _ _); subst; auto;
    simpl; try rewrite !injv_proj_none;
    try rewrite proj_inj_value; auto;
    rewrite !undef_projb_none.
    rewrite undef_projv_undef. auto. auto.
  - (* Vptr Mint Mfloat32 *)
    destruct (eq_nat_dec _ _); subst; auto.
    rewrite undef_projb_none. auto.
  - (* Vptr Mint Mfloat64 *)
    destruct (eq_nat_dec _ _); subst; auto.
    rewrite undef_projb_none. auto.
  - (* Vinttoptr Mint Mint *)
    destruct (eq_nat_dec 31 n); subst; auto.
    destruct (eq_nat_dec _ _); subst; auto.
    simpl. rewrite !injv_proj_none.
    rewrite proj_inj_value. auto.
    rewrite undef_projb_none. destruct (eq_nat_dec _ _); subst; auto.
    rewrite undef_projv_undef. auto.
  - (* Vinttoptr Mint Mfloat32 *)
    destruct (eq_nat_dec _ _); subst; auto.
    rewrite undef_projb_none. auto.
  - (* Vinttoptr Mint Mfloat64 *)
    destruct (eq_nat_dec _ _); subst; auto.
    rewrite undef_projb_none. auto.
(*
unfold bytesize_chunk_nat. simpl.
unfold Pos.to_nat.
simpl.

decEq.
decEq.

  apply Int_unsigned_inj.

 rewrite !Int.unsigned_repr_eq.
 rewrite decode_encode_int.


rewrite !Int.modulus_power.
....

....

.... .... .... ....
destruct (eq_nat_dec 31 n); subst; auto.
destruct (eq_nat_dec 31 n0); subst; auto.
....
destruct (eq_nat_dec _ _); subst; auto.
.... .... .... ....
....  ....  ....  .... 
destruct (eq_nat_dec 31 n); subst; auto.
destruct (eq_nat_dec 31 n0); subst; auto.
.... destruct (eq_nat_dec _ _); subst; auto. ....
destruct (eq_nat_dec _ n); subst; auto. ....
.... .... .... .... ....


Locate int32. 


  rewrite decode_encode_int.

 decEq. apply Float32.of_to_bits.




SearchAbout (_*8).




SearchAbout (two_p).


x > y -> x = (x-y) + y

SearchAbout ((_ mod _) mod _).

SearchAbout Int.modulus.


unfold Int.modulus.

Print Int.wordsize.

Int.modulus



unfold Int.modulus.
unfold two_power_nat.
unfold shift_nat.
unfold nat_iter.  

rewrite <- Int.repr_unsigned.


SearchAbout (Int.unsigned).
Int.unsigned x = Int.unsigned y -> x = y
(*
Int.unsigned_repr_eq:
  forall (wordsize_one : nat) (x : Z),
  Int.unsigned wordsize_one (Int.repr wordsize_one x) =
  x mod Int.modulus wordsize_one
*)
(*
Int.repr_unsigned:
  forall (wordsize_one : nat) (i : Int.int wordsize_one),
  Int.repr wordsize_one (Int.unsigned wordsize_one i) = i
*)
Print Int.int.

Check Int.repr.


Print Int.unsigned.

rewrite decode_encode_int.

SearchAbout Int.repr.


simpl.

Print bytesize_chunk.
Print Z.to_nat.
SearchAbout bytesize_chunk_nat.

SearchAbout bytesize_chunk.

rewrite decode_encode_int.
simpl.


  destruct (eq_nat_dec _ _); subst; auto.
  ....
  destruct (eq_nat_dec _ _); subst; simpl; auto.
  ....
  destruct (eq_nat_dec _ _); subst; simpl; auto.
  ....
  destruct (eq_nat_dec wz _); subst; simpl; auto. destruct (eq_nat_dec _ _); auto.  

  rewrite decode_encode_int_1. decEq. apply Int.zero_ext_idem. omega.
  rewrite decode_encode_int_2. decEq. apply Int.zero_ext_idem. omega.
  rewrite decode_encode_int_4. auto.
  rewrite decode_encode_int_4. auto.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. decEq. apply Float.of_to_bits.
  rewrite decode_encode_int_4. auto.
  rewrite decode_encode_int_4. decEq. apply Float32.of_to_bits.
*)
Qed.
*)

(*
Lemma decode_encode_val_similar:
  forall v1 chunk1 chunk2 v2,
  type_of_chunk chunk1 = type_of_chunk chunk2 ->
  size_chunk chunk1 = size_chunk chunk2 ->
  decode_encode_val v1 chunk1 chunk2 v2 ->
  v2 = Val.load_result chunk2 v1.
Proof.
(* original
  intros until v2; intros TY SZ DE. 
  destruct chunk1; destruct chunk2; simpl in TY; try discriminate; simpl in SZ; try omegaContradiction;
  destruct v1; auto.
*)
(*
  intros until v2; intros TY SZ DE.
  destruct chunk1; destruct chunk2; simpl in TY; try discriminate; simpl in SZ; try omegaContradiction;
  destruct v1; auto.
  simpl in *. destruct (eq_nat_dec _ _); subst; auto. (* not true *)
  simpl in *; destruct (eq_nat_dec _ n); subst; auto.
  destruct (eq_nat_dec 31 n0); subst; auto.
  destruct (eq_nat_dec 31 n0); subst; auto.
  .... (* not true *)
  simpl in *; destruct (eq_nat_dec _ n); subst; auto.
  destruct (eq_nat_dec 31 n0); subst; auto.
  destruct (eq_nat_dec 31 n0); subst; auto.
  .... (* not true *)
*)
Qed.
*)

Lemma decode_val_type:
  forall chunk cl,
  Val.has_type (decode_val chunk cl) (type_of_chunk chunk).
Proof.
  intros. unfold decode_val. 
  destruct (proj_bytes cl). 
  destruct chunk; simpl; auto.
  destruct chunk; try exact I.
  destruct (eq_nat_dec _ _); subst; try exact I.
  apply Val.load_result_type.
Qed.

Lemma decode_val_chunk:
  forall chunk cl,
  Val.has_chunk (decode_val chunk cl) chunk.
Proof.
  intros. unfold decode_val.
  destruct chunk; simpl; auto. 

    unfold decode_int.
    destruct (proj_bytes cl); simpl.
      split; auto.
      apply Int.Z_mod_modulus_range.

      destruct (eq_nat_dec _ _); simpl; auto.
        unfold proj_value.
        destruct cl; try solve [simpl; auto].
          destruct m; try solve [simpl; auto].
            destruct (check_value (size_quantity_nat Q32) v Q32
                       (Fragment v q n0::cl)); simpl; auto.
            destruct v; unfold Val.has_chunk; auto.
            split; auto; apply Int.Z_mod_modulus_range.

    destruct (proj_bytes cl); simpl; auto.
    destruct (proj_bytes cl); simpl; auto.
Qed.

(* need? *)
(*
Lemma encode_val_int8_zero_ext:
  forall n, encode_val Mint8 (Vint (Int.zero_ext 8 n)) = encode_val Mint8 (Vint n).
Proof.
  intros; unfold encode_val. decEq. apply encode_int_8_mod. apply Int.eqmod_zero_ext. 
  compute; intuition congruence.
Qed.

Lemma encode_val_int16_zero_ext:
  forall n, encode_val Mint16 (Vint (Int.zero_ext 16 n)) = encode_val Mint16 (Vint n).
Proof.
  intros; unfold encode_val. decEq. apply encode_int_16_mod. apply Int.eqmod_zero_ext. compute; intuition congruence.
Qed.

Lemma decode_val_cast:
  forall chunk l,
  let v := decode_val chunk l in
  match chunk with
  | Mint 7 => v = Val.zero_ext 8 v
  | Mint 15 => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  unfold decode_val; intros; destruct chunk; auto; destruct (proj_bytes l); auto.
  unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega. 
  unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega.
Qed.
*)

(* NOTE: not used
Lemma encode_decode_encode_val__eq__encode_val: forall v c,
  encode_val c (decode_val c (encode_val c v)) = encode_val c v.
Proof.
  destruct v; destruct c; simpl; auto; unfold decode_val;
    try (rewrite proj_inj_bytes; simpl).

    rewrite undef_projb_none; rewrite undef_projv_undef;
    destruct (eq_nat_dec 31 n); subst; auto.

Focus.
    unfold encode_int.
    rewrite rev_if_be_involutive.
    f_equal. f_equal. 
    rewrite int_of_bytes_of_int.    
    rewrite nat_of_Z_max.
    rewrite Zmax_spec.
    assert (J:=@bytesize_chunk_pos n).
    destruct (zlt 0 (bytesize_chunk n)); try solve [contradict g; omega].
    rewrite bytes_of_int_mod' with (y:=Int.unsigned wz i mod Int.modulus n); 
      try omega; auto.
    rewrite Zmod_mod_le with (c:=two_p (bytesize_chunk n * 8)); 
      auto using two_p_bytesize_chunk__ge__modulus.
      repeat rewrite Zmod_mod.
      apply Int.eqmod_refl.

    unfold encode_float. unfold encode_int.
    rewrite rev_if_be_involutive.
    f_equal. f_equal. 
    simpl.
    repeat rewrite Floats.Float.bits_of_single_of_bits. simpl.
    repeat rewrite Zmod_0_l. auto.

    unfold encode_float. unfold encode_int.
    rewrite rev_if_be_involutive.
    f_equal. f_equal. 
    simpl.
    repeat rewrite Floats.Float.bits_of_double_of_bits. simpl.
    repeat rewrite Zmod_0_l. auto.

    unfold encode_float. unfold encode_int. unfold decode_int.
    rewrite rev_if_be_involutive. simpl.
    f_equal. f_equal. 
    rewrite int_of_bytes_of_int.    
    rewrite Zmod_0_l. auto.

    unfold encode_float.
    rewrite rev_if_be_involutive. 
    f_equal. f_equal. 
    rewrite int_of_bytes_of_int.   
    rewrite Floats.Float.bits_of_single_of_bits. 
    erewrite bytes_of_int_mod; eauto. 
    apply Int.eqmod_trans with 
      (y:=Int.unsigned 31 (Floats.Float.bits_of_single f) 
            mod two_p (Z_of_nat 4 * 8)).
      apply Int.eqm_unsigned_repr_l.
      apply Int.eqmod_refl.

      apply Int.eqmod_sym.
      apply Int.eqmod_mod.
        apply two_p_gt_ZERO; try omega.

    unfold encode_float.
    rewrite rev_if_be_involutive. 
    f_equal. f_equal. 
    rewrite Floats.Float.bits_of_double_of_bits. 
    rewrite int_of_bytes_of_int.    
    erewrite bytes_of_int_mod; eauto. 
    apply Int.eqmod_trans with 
      (y:=Int.unsigned 63 (Floats.Float.bits_of_double f) 
            mod two_p (Z_of_nat 8 * 8)).
      apply Int.eqm_unsigned_repr_l.
      apply Int.eqmod_refl.

      apply Int.eqmod_sym.
      apply Int.eqmod_mod.
        apply two_p_gt_ZERO; try omega.

    destruct (eq_nat_dec n 31); subst.
      simpl.
      destruct (eq_block b b); simpl; try congruence.
      destruct (Int.eq_dec 31 i i); simpl; try congruence.
      rewrite proj_bytes_undef'; auto using size_chunk_nat_pos'.

    destruct (eq_nat_dec n 31); subst.
      simpl.
      destruct (Int.eq_dec 31 i i); simpl; try congruence.
      rewrite proj_bytes_undef'; auto using size_chunk_nat_pos'.
Qed.
*)

Lemma encode_decode_undef: forall c n,
  (n > 0)%nat ->
  encode_val c (decode_val c (list_repeat n Undef)) = 
    list_repeat (size_chunk_nat c) Undef.
Proof.
  intros.
  destruct c; simpl; unfold decode_val; rewrite undef_projb_none'; auto.
    destruct (eq_nat_dec 31 n0); subst; auto.
      rewrite undef_projv_undef'; auto.
Qed.

(** Pointers cannot be forged. *)

Definition quantity_chunk (chunk: memory_chunk) :=
  match chunk with
  | Mint wz =>
    if eq_nat_dec 31 wz then Q32 else Q64
  | Mfloat64 => Q64
  | _ => Q32
  end.

(*
Definition quantity_chunk (chunk: memory_chunk) :=
  match chunk with
  | Mint 63 | Mfloat64 | Many64 => Q64
  | _ => Q32
  end.
*)

Inductive shape_encoding (chunk: memory_chunk) (v: val): list memval -> Prop :=
  | shape_encoding_f: forall q i mvl,
      chunk = Mint 31 ->
      q = quantity_chunk chunk ->
      S i = size_quantity_nat q ->
      (forall mv, In mv mvl -> exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q) ->
      shape_encoding chunk v (Fragment v q i :: mvl)
  | shape_encoding_b: forall b mvl,
      match v with
        | Vint _ _ => True
        | Vfloat _ => True | Vsingle _ => True
        | _ => False
      end ->
      (forall mv, In mv mvl -> exists b', mv = Byte b') ->
      shape_encoding chunk v (Byte b :: mvl)
  | shape_encoding_u: forall mvl,
      (forall mv, In mv mvl -> mv = Undef) ->
      shape_encoding chunk v (Undef :: mvl).

Lemma encode_val_shape: forall chunk v, shape_encoding chunk v (encode_val chunk v).
Proof.
  intros. 
  destruct (size_chunk_nat_pos chunk) as [sz EQ]. 
  assert (A: forall mv q n,
             (n < size_quantity_nat q)%nat ->
             In mv (inj_value_rec n v q) ->
             exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q).
  {
    induction n; simpl; intros. contradiction. destruct H0. 
    exists n; split; auto. omega. apply IHn; auto. omega. 
  } 
  assert (B: forall q,
             q = quantity_chunk chunk -> 
             chunk = Mint 31 ->
             shape_encoding chunk v (inj_value q v)).
  {
Local Transparent inj_value.
    intros. unfold inj_value. destruct (size_quantity_nat_pos q) as [sz' EQ']. 
    rewrite EQ'. simpl. constructor; auto.
    intros; eapply A; eauto. omega. 
  }
  assert (C: forall bl,
             match v with Vint _ _ => True | Vfloat _ => True | Vsingle _ => True | _ => False end ->
             length (inj_bytes bl) = size_chunk_nat chunk ->
             shape_encoding chunk v (inj_bytes bl)).
  {
    intros. destruct bl as [|b1 bl]. simpl in H0; congruence. simpl. 
    constructor; auto. unfold inj_bytes; intros. exploit list_in_map_inv; eauto. 
    intros (b & P & Q); exists b; auto.
  }
  assert (D: shape_encoding chunk v (list_repeat (size_chunk_nat chunk) Undef)).
  {
    intros. rewrite EQ; simpl; constructor; auto. 
    intros. eapply in_list_repeat; eauto. 
  }
  generalize (encode_val_length chunk v). intros LEN.
  unfold encode_val; unfold encode_val in LEN; destruct v; destruct chunk; try (destruct (eq_nat_dec _ _)); subst; auto; (apply B || apply C || apply D); auto; red; auto.
Qed.

Inductive shape_decoding (chunk: memory_chunk): list memval -> val -> Prop :=
  | shape_decoding_f: forall v q i mvl,
      chunk = Mint 31 ->
      q = quantity_chunk chunk ->
      S i = size_quantity_nat q ->
      (forall mv, In mv mvl -> exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q) ->
      shape_decoding chunk (Fragment v q i :: mvl) (Val.load_result chunk v)
  | shape_decoding_b: forall b mvl v,
      match v with Vint _ _ => True | Vfloat _ => True | Vsingle _ => True |  _ => False end ->
      (forall mv, In mv mvl -> exists b', mv = Byte b') ->
      shape_decoding chunk (Byte b :: mvl) v
  | shape_decoding_u: forall mvl,
      shape_decoding chunk mvl Vundef.

Lemma decode_val_shape: forall chunk mv1 mvl,
  shape_decoding chunk (mv1 :: mvl) (decode_val chunk (mv1 :: mvl)).
Proof.
  intros. 
  assert (A: forall mv mvs bs, proj_bytes mvs = Some bs -> In mv mvs ->
                               exists b, mv = Byte b).
  {
    induction mvs; simpl; intros. 
    contradiction.
    destruct a; try discriminate. destruct H0. exists i; auto. 
    destruct (proj_bytes mvs); try discriminate. eauto. 
  }
  assert (B: forall v q mv n mvs,
             check_value n v q mvs = true -> In mv mvs -> (n < size_quantity_nat q)%nat ->
             exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q).
  {
    induction n; destruct mvs; simpl; intros; try discriminate.
    contradiction.
    destruct m; try discriminate. InvBooleans. apply beq_nat_true in H4. subst. 
    destruct H0. subst mv. exists n0; split; auto. omega. 
    eapply IHn; eauto. omega.  
  }
  assert (U: forall mvs, shape_decoding chunk mvs (Val.load_result chunk Vundef)).
  {
    intros. replace (Val.load_result chunk Vundef) with Vundef. constructor. 
    destruct chunk; auto.
  }
  assert (C: forall q, size_quantity_nat q = size_chunk_nat chunk ->
             chunk = Mint 31 ->
             shape_decoding chunk (mv1 :: mvl) (Val.load_result chunk (proj_value q (mv1 :: mvl)))).
  {
    intros. unfold proj_value. destruct mv1; auto.
    destruct (size_quantity_nat_pos q) as [sz EQ]. rewrite EQ. 
    simpl. unfold proj_sumbool. rewrite dec_eq_true.
    destruct (quantity_eq q q0); auto. 
    destruct (beq_nat sz n) eqn:EQN; auto.
    destruct (check_value sz v q mvl) eqn:CHECK; auto. 
    simpl. apply beq_nat_true in EQN. subst n q0. constructor. auto. 
    subst chunk; destruct q; auto || discriminate.
    congruence. 
    intros. eapply B; eauto. omega. 
  }
  unfold decode_val. 
  destruct (proj_bytes (mv1 :: mvl)) as [bl|] eqn:PB. 
  exploit (A mv1); eauto with coqlib. intros [b1 EQ1]; subst mv1. 
  destruct chunk; (apply shape_decoding_u || apply shape_decoding_b); eauto with coqlib.
  destruct chunk; (apply shape_decoding_u || (destruct (eq_nat_dec _ _); subst; auto; apply C)); auto. 
Qed.

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall n, memval_inject f (Byte n) (Byte n)
  | memval_inject_frag:
      forall v1 v2 q n,
      val_inject f v1 v2 ->
      memval_inject f (Fragment v1 q n) (Fragment v2 q n)
  | memval_inject_undef:
      forall mv, memval_inject f Undef mv.

Lemma memval_inject_incr:
  forall f f' v1 v2, memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. eapply val_inject_incr; eauto. 
Qed.

(** [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [val_inject]. *)

Lemma proj_bytes_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall bl,
  proj_bytes vl = Some bl ->
  proj_bytes vl' = Some bl.
Proof.
  induction 1; simpl. congruence.
  inv H; try congruence.
  destruct (proj_bytes al); intros. 
  inv H. rewrite (IHlist_forall2 l); auto. 
  congruence.
Qed.

Lemma check_value_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall v v' q n,
  check_value n v q vl = true ->
  val_inject f v v' -> v <> Vundef ->
  check_value n v' q vl' = true.
Proof.
  induction 1; intros; destruct n; simpl in *; auto. 
  inv H; auto.
  InvBooleans. assert (n = n0) by (apply beq_nat_true; auto). subst v1 q0 n0.
  replace v2 with v'. 
  unfold proj_sumbool; rewrite ! dec_eq_true. rewrite <- beq_nat_refl. simpl; eauto. 
  inv H2; try discriminate; inv H4; try congruence.
  dependent destruction H2; auto.
  discriminate.
Qed.

Lemma proj_value_inject:
  forall f q vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_value q vl1) (proj_value q vl2).
Proof.
  intros. unfold proj_value. 
  inversion H; subst. auto. inversion H0; subst; auto.
  destruct (check_value (size_quantity_nat q) v1 q (Fragment v1 q0 n :: al)) eqn:B; auto.
  destruct (Val.eq v1 Vundef). subst; auto. 
  erewrite check_value_inject by eauto. auto.
Qed.

Lemma proj_bytes_not_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  proj_bytes vl = None -> proj_bytes vl' <> None -> In Undef vl.
Proof.
  induction 1; simpl; intros.
  congruence.
  inv H; try congruence. 
  right. apply IHlist_forall2.
  destruct (proj_bytes al); congruence.
  destruct (proj_bytes bl); congruence.
  auto.
Qed.

Lemma check_value_undef:
  forall n q v vl,
  In Undef vl -> check_value n v q vl = false.
Proof.
  induction n; intros; simpl. 
  destruct vl. elim H. auto.
  destruct vl. auto.
  destruct m; auto. simpl in H; destruct H. congruence.
  rewrite IHn; auto. apply andb_false_r. 
Qed.

Lemma proj_value_undef:
  forall q vl, In Undef vl -> proj_value q vl = Vundef.
Proof.
  intros; unfold proj_value.
  destruct vl; auto. destruct m; auto. 
  rewrite check_value_undef. auto. auto.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros. unfold decode_val. 
  destruct (proj_bytes vl1) as [bl1|] eqn:PB1.
  exploit proj_bytes_inject; eauto. intros PB2. rewrite PB2. 
  destruct chunk; constructor.
  assert (A: forall q fn,
     val_inject f (Val.load_result chunk (proj_value q vl1))
                  (match proj_bytes vl2 with
                   | Some bl => fn bl
                   | None => Val.load_result chunk (proj_value q vl2)
                   end)).
  { intros. destruct (proj_bytes vl2) as [bl2|] eqn:PB2.
    rewrite proj_value_undef. destruct chunk; auto. eapply proj_bytes_not_inject; eauto. congruence.
    apply val_load_result_inject. apply proj_value_inject; auto.
  }
  destruct chunk; auto.
  destruct (eq_nat_dec 31 _); subst; auto.
Qed.

(** Symmetrically, [encode_val], applied to values related by [val_inject],
  returns lists of memory values that are pairwise
  related by [memval_inject]. *)

Lemma inj_bytes_inject:
  forall f bl, list_forall2 (memval_inject f) (inj_bytes bl) (inj_bytes bl).
Proof.
  induction bl; constructor; auto. constructor.
Qed.

Lemma repeat_Undef_inject_any:
  forall f vl,
  list_forall2 (memval_inject f) (list_repeat (length vl) Undef) vl.
Proof.
  induction vl; simpl; constructor; auto. constructor. 
Qed.  

Lemma repeat_Undef_inject_encode_val:
  forall f chunk v,
  list_forall2 (memval_inject f) (list_repeat (size_chunk_nat chunk) Undef) (encode_val chunk v).
Proof.
  intros. rewrite <- (encode_val_length chunk v). apply repeat_Undef_inject_any.
Qed.

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.  

Lemma inj_value_inject:
  forall f v1 v2 q, val_inject f v1 v2 -> list_forall2 (memval_inject f) (inj_value q v1) (inj_value q v2).
Proof.
  intros.
Local Transparent inj_value.
  unfold inj_value. generalize (size_quantity_nat q). induction n; simpl; constructor; auto.
  constructor; auto. 
Qed.

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  val_inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
  intros. inversion H; subst; simpl; destruct chunk;
  auto using inj_bytes_inject, inj_value_inject, repeat_Undef_inject_self, repeat_Undef_inject_encode_val.
  unfold encode_val. destruct (eq_nat_dec 31 _); subst; auto. apply inj_value_inject; auto.
  apply repeat_Undef_inject_self.
  destruct (eq_nat_dec 31 _); subst; auto. apply inj_value_inject; auto.
  apply repeat_Undef_inject_self.
Qed.

Definition memval_lessdef: memval -> memval -> Prop := memval_inject inject_id.

Lemma memval_lessdef_refl:
  forall mv, memval_lessdef mv mv.
Proof.
  red. destruct mv; econstructor. apply val_inject_id. auto.
Qed.

(** [memval_inject] and compositions *)

Lemma memval_inject_compose:
  forall f f' v1 v2 v3,
  memval_inject f v1 v2 -> memval_inject f' v2 v3 ->
  memval_inject (compose_meminj f f') v1 v3.
Proof.
  intros. inv H.
  inv H0. constructor.
  inv H0. econstructor.
  eapply val_inject_compose; eauto. 
  constructor.
Qed. 

(** * Breaking 64-bit memory accesses into two 32-bit accesses *)

Lemma int_of_bytes_append:
  forall l2 l1, 
  int_of_bytes (l1 ++ l2) = int_of_bytes l1 + int_of_bytes l2 * two_p (Z_of_nat (length l1) * 8).
Proof.
  induction l1; simpl int_of_bytes; intros.
  simpl. ring.
  simpl length. rewrite inj_S. 
  replace (Z.succ (Z.of_nat (length l1)) * 8) with (Z_of_nat (length l1) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. rewrite IHl1. ring.
  omega. omega.
Qed.

Lemma int_of_bytes_range:
  forall l, 0 <= int_of_bytes l < two_p (Z_of_nat (length l) * 8).
Proof.
  induction l; intros. 
  simpl. omega.
  simpl length. rewrite inj_S. 
  replace (Z.succ (Z.of_nat (length l)) * 8) with (Z.of_nat (length l) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. 
  simpl int_of_bytes. generalize (Int.unsigned_range 7 a). 
  change (Int.modulus 7) with 256. omega. 
  omega. omega. 
Qed.

Lemma length_proj_bytes:
  forall l b, proj_bytes l = Some b -> length b = length l.
Proof.
  induction l; simpl; intros. 
  inv H; auto.
  destruct a; try discriminate. 
  destruct (proj_bytes l) eqn:E; inv H. 
  simpl. f_equal. auto.
Qed.

Lemma proj_bytes_append:
  forall l2 l1,
  proj_bytes (l1 ++ l2) =
  match proj_bytes l1, proj_bytes l2 with
  | Some b1, Some b2 => Some (b1 ++ b2)
  | _, _ => None
  end.
Proof.
  induction l1; simpl.
  destruct (proj_bytes l2); auto.
  destruct a; auto. rewrite IHl1. 
  destruct (proj_bytes l1); auto. destruct (proj_bytes l2); auto. 
Qed.
(* need? *)
(*
Lemma decode_val_int64:
  forall l1 l2,
  length l1 = 4%nat -> length l2 = 4%nat ->
  Val.lessdef
    (decode_val Mint64 (l1 ++ l2))
    (Val.longofwords (decode_val Mint32 (if Archi.big_endian then l1 else l2))
                     (decode_val Mint32 (if Archi.big_endian then l2 else l1))).
Proof.
  intros. unfold decode_val.
  rewrite proj_bytes_append. 
  destruct (proj_bytes l1) as [b1|] eqn:B1; destruct (proj_bytes l2) as [b2|] eqn:B2; auto.
  exploit length_proj_bytes. eexact B1. rewrite H; intro L1.
  exploit length_proj_bytes. eexact B2. rewrite H0; intro L2.
  assert (UR: forall l, length l = 4%nat -> Int.unsigned (Int.repr (int_of_bytes l)) = int_of_bytes l).
    intros. apply Int.unsigned_repr. 
    generalize (int_of_bytes_range l). rewrite H1. 
    change (two_p (Z.of_nat 4 * 8)) with (Int.max_unsigned + 1). 
    omega.
  apply Val.lessdef_same.
  unfold decode_int, rev_if_be. destruct Archi.big_endian; rewrite B1; rewrite B2.
  + rewrite <- (rev_length b1) in L1. 
    rewrite <- (rev_length b2) in L2.
    rewrite rev_app_distr.
    set (b1' := rev b1) in *; set (b2' := rev b2) in *.
    unfold Val.longofwords. f_equal. rewrite Int64.ofwords_add. f_equal.
    rewrite !UR by auto. rewrite int_of_bytes_append. 
    rewrite L2. change (Z.of_nat 4 * 8) with 32. ring.
  + unfold Val.longofwords. f_equal. rewrite Int64.ofwords_add. f_equal.
    rewrite !UR by auto. rewrite int_of_bytes_append. 
    rewrite L1. change (Z.of_nat 4 * 8) with 32. ring.
Qed.
*)
Lemma bytes_of_int_append:
  forall n2 x2 n1 x1,
  0 <= x1 < two_p (Z_of_nat n1 * 8) ->
  bytes_of_int (n1 + n2) (x1 + x2 * two_p (Z_of_nat n1 * 8)) =
  bytes_of_int n1 x1 ++ bytes_of_int n2 x2.
Proof.
  induction n1; intros.
- simpl in *. f_equal. omega. 
- assert (E: two_p (Z.of_nat (S n1) * 8) = two_p (Z.of_nat n1 * 8) * 256).
  {
    rewrite inj_S. change 256 with (two_p 8). rewrite <- two_p_is_exp. 
    f_equal. omega. omega. omega. 
  }
  rewrite E in *. simpl. f_equal.
  apply Int.eqm_samerepr. exists (x2 * two_p (Z.of_nat n1 * 8)). 
  change (Int.modulus 7) with 256. ring.
  rewrite Zmult_assoc. rewrite Z_div_plus. apply IHn1.
  apply Zdiv_interval_1. omega. apply two_p_gt_ZERO; omega. omega. 
  assumption. omega.
Qed.
(* need? *)
(*
Lemma bytes_of_int64:
  forall i,
  bytes_of_int 8 (Int64.unsigned i) =
  bytes_of_int 4 (Int.unsigned (Int64.loword i)) ++ bytes_of_int 4 (Int.unsigned (Int64.hiword i)).
Proof.
  intros. transitivity (bytes_of_int (4 + 4) (Int64.unsigned (Int64.ofwords (Int64.hiword i) (Int64.loword i)))).
  f_equal. f_equal. rewrite Int64.ofwords_recompose. auto.
  rewrite Int64.ofwords_add'.
  change 32 with (Z_of_nat 4 * 8). 
  rewrite Zplus_comm. apply bytes_of_int_append. apply Int.unsigned_range. 
Qed.

Lemma encode_val_int64:
  forall v,
  encode_val Mint64 v =
     encode_val Mint32 (if Archi.big_endian then Val.hiword v else Val.loword v)
  ++ encode_val Mint32 (if Archi.big_endian then Val.loword v else Val.hiword v).
Proof.
  intros. destruct v; destruct Archi.big_endian eqn:BI; try reflexivity;
  unfold Val.loword, Val.hiword, encode_val.
  unfold inj_bytes. rewrite <- map_app. f_equal. 
  unfold encode_int, rev_if_be. rewrite BI. rewrite <- rev_app_distr. f_equal.
  apply bytes_of_int64. 
  unfold inj_bytes. rewrite <- map_app. f_equal. 
  unfold encode_int, rev_if_be. rewrite BI.
  apply bytes_of_int64.
Qed.
*)
