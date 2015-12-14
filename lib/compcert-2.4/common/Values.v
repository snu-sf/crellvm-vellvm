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

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import Program.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.

Arguments eq_nat_dec _ _ : simpl never.

Definition block : Type := positive.
Definition eq_block := peq.

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

Inductive val: Type :=
  | Vundef: val
  | Vint: forall (wz:nat), Int.int wz -> val
  | Vfloat: float -> val
  | Vsingle: float32 -> val
  | Vptr: block -> int32 -> val
  | Vinttoptr: int32 -> val.

Definition zero (wz:nat) := (Int.zero wz).
Definition one (wz:nat) := (Int.one wz).
Definition mone (wz:nat) := (Int.mone wz).

Definition Vzero (wz:nat): val := Vint wz (zero wz).
Definition Vone (wz:nat): val := Vint wz (one wz).
Definition Vmone (wz:nat): val := Vint wz (mone wz).

Definition Vtrue := Vone 0.
Definition Vfalse := Vzero 0.

Definition eq_Vbool (wz:nat) (v v':val) := 
  (v = Vone wz <-> v'= Vtrue) /\
  (v = Vzero wz <-> v'= Vfalse).

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

Definition eq (x y: val): {x=y} + {x<>y}.
Proof.
  destruct x, y; 
  try (destruct (Float.eq_dec f f0)); 
  try (destruct (Float32.eq_dec f f0)); 
  try (destruct (eq_block b b0)); 
  try (destruct (eq_nat_dec wz wz0)); subst;
  try (destruct (Int.eq_dec _ i i0)); subst;
  auto; 
  try (now right; intro H; dependent destruction H; auto).
Defined.
Global Opaque eq.

Definition get_wordsize (v : val) : option nat :=
  match v with
  | Vint wz _ => Some wz
  | Vptr _ _ | Vinttoptr _ => 
      (* This is incorrect, size of ptr is configured differently. *)
      Some 31%nat
  | _ => None
  end.

Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _ _, Tint => True
  | Vfloat _, Tfloat => True
  | Vsingle _, Tsingle => True
  | Vptr _ _, Tint => True
  | Vinttoptr _, Tint => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

Definition has_opttype (v: val) (ot: option typ) : Prop :=
  match ot with
  | None => v = Vundef
  | Some t => has_type v t
  end.

Lemma has_subtype:
  forall ty1 ty2 v,
  subtype ty1 ty2 = true -> has_type v ty1 -> has_type v ty2.
Proof.
  intros. destruct ty1; destruct ty2; simpl in H; discriminate || assumption || idtac;
  unfold has_type in *; destruct v; auto.
Qed.

Lemma has_subtype_list:
  forall tyl1 tyl2 vl,
  subtype_list tyl1 tyl2 = true -> has_type_list vl tyl1 -> has_type_list vl tyl2.
Proof.
  induction tyl1; intros; destruct tyl2; try discriminate; destruct vl; try contradiction.
  red; auto.
  simpl in *. InvBooleans. destruct H0. split; auto. eapply has_subtype; eauto.
Qed.

(** Truth values.  Pointers and non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  [Vundef] and floats are neither true nor false. *)

Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int_true:
      forall wz n, n <> zero wz -> bool_of_val (Vint wz n) true
  | bool_of_val_int_false:
      forall wz, bool_of_val (Vzero wz) false
  | bool_of_val_ptr:
      forall b ofs, bool_of_val (Vptr b ofs) true
  | bool_of_val_inttoptr:
      forall n, bool_of_val (Vinttoptr n) true.

(** Arithmetic operations *)

Definition neg (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.neg wz n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition negfs (v: val) : val :=
  match v with
  | Vsingle f => Vsingle (Float32.neg f)
  | _ => Vundef
  end.

Definition absfs (v: val) : val :=
  match v with
  | Vsingle f => Vsingle (Float32.abs f)
  | _ => Vundef
  end.

Definition maketotal (ov: option val) : val :=
  match ov with Some v => v | None => Vundef end.

Definition trunc (v: val) (wz':nat) : val :=
match v with
| Vint wz n => if le_lt_dec wz wz'
               then Vundef
               else Vint wz' (Int.repr wz' (Int.unsigned wz n))
| _ => Vundef
end.

Definition ftrunc (v: val) : val :=
match v with
| Vfloat f => v
| _ => Vundef
end.

Definition intoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map (Vint 31) (Float.to_int f)
  | _ => None
  end.

Definition intuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map (Vint 31) (Float.to_intu f)
  | _ => None
  end.

Definition floatofint (v: val) : option val :=
  match v with
  | Vint 31 n => Some (Vfloat (Float.of_int n))
  | _ => None
  end.

Definition floatofintu (v: val) : option val :=
  match v with
  | Vint 31 n => Some (Vfloat (Float.of_intu n))
  | _ => None
  end.

Definition intofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map (Vint 31) (Float32.to_int f)
  | _ => None
  end.

Definition intuofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map (Vint 31) (Float32.to_intu f)
  | _ => None
  end.

Definition singleofint (v: val) : option val :=
  match v with
  | Vint 31 n => Some (Vsingle (Float32.of_int n))
  | _ => None
  end.

Definition singleofintu (v: val) : option val :=
  match v with
  | Vint 31 n => Some (Vsingle (Float32.of_intu n))
  | _ => None
  end.

Definition negint (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.neg wz n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.not wz n)
  | _ => Vundef
  end.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition boolval (v: val) : val :=
  match v with
  | Vint wz n => of_bool (negb (Int.eq wz n (Int.zero wz)))
  | Vptr b ofs => Vtrue
  | _ => Vundef
  end.

Definition notbool (v: val) : val :=
  match v with
  | Vint wz n => of_bool (Int.eq wz n (Int.zero wz))
  | Vptr _ _ | Vinttoptr _ => Vfalse
  | _ => Vundef
  end.

(* If v is a wz-bit of int, zero_ext v zeros the nbits-to-(wz-1) bits *)
Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.zero_ext wz nbits n)
  | _ => Vundef
  end.

(* If v is wz m-bit of int, 
   zero_ext' v first converts v to v' that is of nbits bits,
   then zeros the wz-to-(nbits-1) bits *)
Definition zero_ext' (nbits: nat) (v: val) : val :=
  match v with
  | Vint wz n => 
      Vint nbits
        (Int.zero_ext nbits (Z_of_nat wz)
          (Int.repr nbits (Int.unsigned wz n)))
  | _ => Vundef
  end.

(* If v is a wz-bit of int, sign_ext v signs the nbits-to-(wz-1) bits *)
Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.sign_ext wz nbits n)
  | _ => Vundef
  end.

(* If v is wz m-bit of int, 
   sign_ext' v first converts v to v' that is of nbits bits,
   then signs the wz-to-(nbits-1) bits *)
Definition sign_ext' (nbits: nat) (v: val) : val :=
  match v with
  | Vint wz n => 
      Vint nbits
        (Int.sign_ext nbits (Z_of_nat wz)
          (Int.repr nbits (Int.unsigned wz n)))
  | _ => Vundef
  end.
(*
Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vsingle (Float.to_single f)
  | _ => Vundef
  end.

Definition floatofsingle (v: val) : val :=
  match v with
  | Vsingle f => Vfloat (Float.of_single f)
  | _ => Vundef
  end.
*)
Definition hcast {U : Type} (Sig : U -> Type) (u:U) {v : U} (pf : u = v) (a : Sig u) : Sig v := @eq_rect U u Sig a v pf. 

Lemma hcast_eq: forall T S u pf x,
  @hcast T S u u pf x = x.
Proof.
  intros; unfold hcast.
  rewrite <- eq_rect_eq. auto.
Qed.

Definition add (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq => Vint wz1 (Int.add wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | Vptr b1 ofs1, Vint wz2 n2 =>
    match eq_nat_dec 31 wz2 with
    | left pfeq => Vptr b1 (Int.add 31 ofs1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | Vint wz1 n1, Vptr b2 ofs2 =>
    match eq_nat_dec 31 wz1 with
    | left pfeq => Vptr b2 (Int.add 31 ofs2 (hcast Int.int _ (eq_sym pfeq) n1))
    | right _ => Vundef
    end
  | Vinttoptr n1, Vint wz2 n2 =>
    match eq_nat_dec 31 wz2 with
    | left pfeq => Vinttoptr (Int.add 31 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | Vint wz1 n1, Vinttoptr n2 =>
    match eq_nat_dec 31 wz1 with
    | left pfeq => Vinttoptr (Int.add 31 n2 (hcast Int.int _ (eq_sym pfeq) n1))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Arguments add _ _ : simpl never.

Definition sub (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq => Vint wz1 (Int.sub wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | Vptr b1 ofs1, Vint wz2 n2 =>
    match eq_nat_dec 31 wz2 with
    | left pfeq => Vptr b1 (Int.sub 31 ofs1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if peq b1 b2 then Vint 31 (Int.sub 31 ofs1 ofs2) else Vundef
  | Vinttoptr n1, Vint wz2 n2 =>
    match eq_nat_dec 31 wz2 with
    | left pfeq => Vinttoptr (Int.sub 31 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | Vinttoptr n1, Vinttoptr n2 =>
    Vint 31 (Int.sub 31 n1 n2)
  | _, _ => Vundef
  end.

Arguments sub _ _ : simpl never.

Definition mul (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq => Vint wz1 (Int.mul wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition mulhs (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq => Vint wz1 (Int.mulhs wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition mulhu (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq => Vint wz1 (Int.mulhu wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition divs (v1 v2: val): option val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.eq wz1 (hcast Int.int _ (eq_sym pfeq) n2) (Int.zero wz1)
      || Int.eq wz1 n1 (Int.repr wz1 (Int.min_signed wz1)) && Int.eq wz1 (hcast Int.int _ (eq_sym pfeq) n2) (Int.mone wz1)
      then None
      else Some (Vint wz1 (Int.divs wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2)))
    | right _ => None
    end
  | _, _ => None
  end.

Definition mods (v1 v2: val): option val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.eq wz2 n2 (Int.zero wz2)
      || Int.eq wz1 n1 (Int.repr wz1 (Int.min_signed wz1)) && Int.eq wz2 n2 (Int.mone wz2)
      then None
      else Some(Vint wz1 (Int.mods wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2)))
    | right _ => None
    end
  | _, _ => None
  end.

Definition divu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.eq wz2 n2 (Int.zero wz2) then None
      else Some(Vint wz1 (Int.divu wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2)))
    | right _ => None
    end
  | _, _ => None
  end.

Definition modu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.eq wz2 n2 (Int.zero wz2) then None
      else Some(Vint wz1 (Int.modu wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2)))
    | right _ => None
    end
  | _, _ => None
  end.

Definition add_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vint wz1 n1, Vint wz2 n2, Vint wz3 c =>
    match eq_nat_dec wz1 wz2, eq_nat_dec wz1 wz3 with
    | left pfeq2, left pfeq3 =>
      Vint wz1 (Int.add_carry wz1 n1 (hcast Int.int _ (eq_sym pfeq2) n2) (hcast Int.int _ (eq_sym pfeq3) c))
    | _, _ => Vundef
    end
  | _, _, _ => Vundef
  end.

Definition sub_overflow (v1 v2: val) : val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      Vint wz1 (Int.sub_overflow wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2) (Int.zero wz1))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition negative (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.negative wz n)
  | _ => Vundef
  end.

Definition and (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      Vint wz1 (Int.and wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition or (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      Vint wz1 (Int.or wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition xor (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      Vint wz1 (Int.xor wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition shl (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.ltu wz2 n2 (Int.iwordsize wz2)
      then Vint wz1 (Int.shl wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
      else Vundef
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition shr (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.ltu wz2 n2 (Int.iwordsize wz2)
      then Vint wz1 (Int.shr wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
      else Vundef
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition shr_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.ltu wz2 n2 (Int.iwordsize wz2)
      then Vint wz1 (Int.shr_carry wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
      else Vundef
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition shrx (v1 v2: val): option val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.ltu wz1
        (hcast Int.int _ (eq_sym pfeq) n2)
        (Int.repr wz1 (Int.zwordsize wz1 - 1))
      then Some (Vint wz1 (Int.shrx wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2)))
      else None
    | right _ => None
    end
  | _, _ => None
  end.

Definition shru (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.ltu wz2 n2 (Int.iwordsize wz2)
      then Vint wz1 (Int.shru wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
      else Vundef
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition rolm (v: val) (amount mask: int32): val :=
  match v with
  | Vint wz n =>
    match eq_nat_dec 31 wz with
    | left pfeq => Vint 31 (Int.rolm 31 (hcast Int.int _ (eq_sym pfeq) n) amount mask)
    | right _ => Vundef
    end
  | _ => Vundef
  end.

Definition ror (v1 v2: val): val :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      if Int.ltu wz2 n2 (Int.iwordsize wz2)
      then Vint wz1 (Int.ror wz1 n1 (hcast Int.int _ (eq_sym pfeq) n2))
      else Vundef
    | right _ => Vundef
    end
  | _, _ => Vundef
  end.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition modf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.rem f1 f2)
  | _, _ => Vundef
  end.

Definition floatofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint 31 n1, Vint 31 n2 => Vfloat (Float.from_words n1 n2)
  | _, _ => Vundef
  end.

Definition addfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.add f1 f2)
  | _, _ => Vundef
  end.

Definition subfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.div f1 f2)
  | _, _ => Vundef
  end.

Definition modfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.rem f1 f2)
  | _, _ => Vundef
  end.

(** Operations on 64-bit integers *)
(* removed because Vint is now handle arbitrary-bit integers *)

(** Comparisons *)

Section COMPARISONS.

Variable valid_ptr: block -> Z -> bool.
Let weak_valid_ptr (b: block) (ofs: Z) := valid_ptr b ofs || valid_ptr b (ofs - 1).

Definition cmp_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      Some (Int.cmp wz1 c n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => None
    end
  | _, _ => None
  end.

Definition cmp_different_blocks (c: comparison): option bool :=
  match c with
  | Ceq => Some false
  | Cne => Some true
  | _   => None
  end.

Definition cmpu_bool_int (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    match eq_nat_dec wz1 wz2 with
    | left pfeq =>
      Some (Int.cmpu wz1 c n1 (hcast Int.int _ (eq_sym pfeq) n2))
    | right _ => None
    end
  | _, _ => None
  end.

Definition cmpu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint wz1 n1, Vint wz2 n2 =>
    cmpu_bool_int c v1 v2
  | Vint wz1 n1, Vptr b2 ofs2 =>
    match eq_nat_dec 31 wz1 with
    | left pfeq =>
        if Int.eq 31 (hcast Int.int _ (eq_sym pfeq) n1) (Int.zero 31)
        then cmp_different_blocks c
        else None
    | right _ => None
    end
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if eq_block b1 b2 then
        if weak_valid_ptr b1 (Int.unsigned 31 ofs1)
           && weak_valid_ptr b2 (Int.unsigned 31 ofs2)
        then Some (Int.cmpu 31 c ofs1 ofs2)
        else None
      else
        if valid_ptr b1 (Int.unsigned 31 ofs1)
           && valid_ptr b2 (Int.unsigned 31 ofs2)
        then cmp_different_blocks c
        else None
  | Vptr b1 ofs1, Vint wz2 n2 =>
    match eq_nat_dec 31 wz2 with
    | left pfeq =>
        if Int.eq 31 (hcast Int.int _ (eq_sym pfeq) n2) (Int.zero 31)
        then cmp_different_blocks c
        else None
    | right _ => None
    end
  | Vinttoptr n1, Vinttoptr n2 => Some (Int.cmpu 31 c n1 n2)
(* FIXME: Vptr and Vinttoptr are not compariable. *)
  | _, _ => None
  end.

Definition cmpf_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Some (Float.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpfs_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Some (Float32.cmp c f1 f2)
  | _, _ => None
  end.

Definition of_optbool (ob: option bool): val :=
  match ob with Some true => Vtrue | Some false => Vfalse | None => Vundef end.

Definition cmp (c: comparison) (v1 v2: val): val :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu_int (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpu_bool_int c v1 v2).

Definition cmpu (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpf (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpf_bool c v1 v2).

Definition cmpfs (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpfs_bool c v1 v2).

(* NOTE: Vellvm Context *)
Definition maskzero_bool (v: val) (mask: int32): option bool :=
  match v with
  | Vint 31 n => Some (Int.eq 31 (Int.and 31 n mask) (Int.zero 31))
  | _ => None
  end.

End COMPARISONS.

Ltac simplify_op :=
  let HEQ := fresh "_Heqdec_" in
  simpl
  ; repeat match goal with [|- context[eq_nat_dec ?a ?b]] => 
      destruct (eq_nat_dec a b) eqn: HEQ; subst; try clear HEQ 
    end
  ; simpl; auto; try tauto
  ; repeat rewrite hcast_eq.

(** [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned.
  fixed: vellvm does not need signedness *)

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint wz1, Vint wz2 n => Vint wz1 (Int.repr wz1 (Int.unsigned wz2 n))
  | Mint wz, Vptr b ofs => if eq_nat_dec 31 wz then Vptr b ofs else Vundef
  | Mint wz, Vinttoptr i => if eq_nat_dec 31 wz then Vinttoptr i else Vundef
  | Mfloat32, Vsingle f => Vsingle f
  | Mfloat64, Vfloat f => Vfloat f
  | _, _ => Vundef
  end.

Lemma load_result_type:
  forall chunk v, has_type (load_result chunk v) (type_of_chunk chunk).
Proof.
  intros. destruct chunk; destruct v; simpl; auto.
  destruct (eq_nat_dec _ _); unfold has_type; subst; auto.
  destruct (eq_nat_dec _ _); unfold has_type; subst; auto.
Qed.

(* NOTE: Vellvm Context - load_result_same_type removed *)
(** Theorems on arithmetic operations. *)

Section ArithOperations.

Variable x : val.

Hypothesis x_is_int : get_wordsize x = Some 31%nat.

Theorem cast8unsigned_and:
  zero_ext 8 x = and x (Vint 31 (Int.repr 31 255)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 255 with (two_p 8 - 1).
  inv x_is_int. simpl. rewrite Int.zero_ext_and. auto. omega.
Qed.

Theorem cast16unsigned_and:
  zero_ext 16 x = and x (Vint 31 (Int.repr 31 65535)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 65535 with (two_p 16 - 1).
  inv x_is_int. simpl. rewrite Int.zero_ext_and. auto. omega.
Qed.

End ArithOperations. 

Theorem bool_of_val_of_bool:
  forall b1 b2, bool_of_val (of_bool b1) b2 -> b1 = b2.
Proof.
  intros. destruct b1; simpl in H; inv H; auto.
  exfalso;apply H3.
  dependent destruction H2;auto.
Qed.

Theorem bool_of_val_of_optbool:
  forall ob b, bool_of_val (of_optbool ob) b -> ob = Some b.
Proof.
  intros. destruct ob; simpl in H. 
  destruct b0; simpl in H; inv H; auto.
  dependent destruction H2; auto.
  exfalso;auto.
  inv H.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_3:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto. 
  case (Int.eq wz i (Int.zero wz)); reflexivity.
Qed.

Theorem notbool_idem4:
  forall ob, notbool (notbool (of_optbool ob)) = of_optbool ob.
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; unfold add; simpl; auto; simplify_op;
  rewrite Int.add_commut; auto.
Qed.

Lemma add_undef_left: forall x y, x = Vundef -> add x y = Vundef.
Proof.
  induction x; intros; simpl; inv H; auto.
Qed.

Lemma add_undef_right: forall x y, y = Vundef -> add x y = Vundef.
Proof.
  intros. rewrite add_commut. revert H. revert x. revert y. apply add_undef_left.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto; unfold add 
  ; simplify_op; decEq; rewrite Int.add_assoc; auto.
  - decEq; apply Int.add_commut.
  - decEq; apply Int.add_commut.
  - rewrite Int.add_assoc; decEq; apply Int.add_commut.
  - rewrite Int.add_assoc. decEq; apply Int.add_commut.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut. rewrite add_assoc. 
  rewrite add_permut. symmetry. apply add_assoc. 
Qed.

Theorem neg_zero: forall wz, neg (Vzero wz) = Vzero wz.
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  destruct x; destruct y; unfold add; simplify_op; auto.
  decEq. apply Int.neg_add_distr.
Qed.

Theorem sub_zero_r: forall x wz,
  get_wordsize x = Some wz -> sub (Vzero wz) x = neg x.
Proof.
  destruct x; unfold sub; simpl; auto.
  intro wz0; destruct (eq_nat_dec wz0 wz) eqn:Heq.
  - subst; reflexivity.
  - intros. inv H. exfalso;apply n;auto.
Qed.

Theorem sub_add_opp: forall x wz y,
  get_wordsize x = Some wz -> 
  sub x (Vint wz y) = add x (Vint wz (Int.neg wz y)).
Proof.
  intros; destruct x; inv H;
  unfold sub, add; simplify_op; auto;
  rewrite Int.sub_add_opp; auto.
Qed.

Theorem sub_opp_add: forall x wz y,
  get_wordsize x = Some wz -> 
  sub x (Vint wz (Int.neg wz y)) = add x (Vint wz y).
Proof.
  intros. unfold sub, add;
  destruct x; simplify_op; auto;
  rewrite Int.sub_add_opp; rewrite Int.neg_involutive; auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 wz i,
  get_wordsize v1 = Some wz -> 
  sub (add v1 (Vint wz i)) v2 = add (sub v1 v2) (Vint wz i).
Proof.
  intros; unfold sub, add;
  destruct v1; destruct v2; inversion H; simplify_op;
  try rewrite Int.sub_add_l; auto.
  case (peq b b0); intro; reflexivity.
Qed.

Theorem sub_add_r:
  forall v1 v2 wz i,
  get_wordsize v1 = Some wz -> 
  sub v1 (add v2 (Vint wz i)) = add (sub v1 v2) (Vint wz (Int.neg wz i)).
Proof.
  intros; unfold sub, add;
  destruct v1; destruct v2; inversion H; simplify_op.
  - rewrite Int.sub_add_r. rewrite Int.sub_add_opp.
    rewrite Int.add_assoc. rewrite (Int.add_commut wz (Int.neg wz i) (Int.neg wz i1)).
    rewrite <- Int.add_assoc. rewrite Int.sub_add_opp. auto.
  - repeat rewrite Int.sub_add_opp. decEq. 
    repeat rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.
  - case (peq b b0); intro; simpl. decEq. 
    repeat rewrite Int.sub_add_opp. rewrite Int.add_assoc. decEq.
    apply Int.neg_add_distr.
    reflexivity.
  - repeat rewrite Int.sub_add_opp. decEq. 
    repeat rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.
  - repeat rewrite Int.sub_add_opp. decEq. 
    repeat rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl; auto; simplify_op.
  rewrite Int.mul_commut. auto.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; unfold mul; simpl; auto; simplify_op;
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  destruct x; destruct y; destruct z; unfold add, mul; simpl; auto; simplify_op;
  decEq. apply Int.mul_add_distr_l.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  destruct x; destruct y; destruct z; unfold add, mul; simpl; auto; simplify_op.
  decEq. apply Int.mul_add_distr_r.
Qed.

Theorem mul_pow2:
  forall x wz n logn,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  mul x (Vint wz n) = shl x (Vint wz logn).
Proof.
  intros; destruct x; simpl; auto; simplify_op;
  change 32 with Int.zwordsize.
  rewrite (Int.is_power2_range _ _ _ H0). decEq. apply Int.mul_pow2. auto.
Qed.

Theorem mods_divs:
  forall x y z,
  mods x y = Some z -> exists v, divs x y = Some v /\ z = sub x (mul v y).
Proof.
  intros; destruct x; destruct y; unfold sub; simpl in *; simplify_op; try discriminate.
  destruct (Int.eq wz0 i0 (Int.zero wz0)
        || Int.eq wz0 i (Int.repr wz0 (Int.min_signed wz0)) && Int.eq wz0 i0 (Int.mone wz0)) eqn:Heqn; inv H.
  exists (Vint wz0 (Int.divs wz0 i i0)); split; auto. 
  simpl. rewrite Int.mods_divs. simplify_op. auto.
Qed.

Theorem modu_divu:
  forall x y z,
  modu x y = Some z -> exists v, divu x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; unfold sub; simpl in *; simplify_op; try discriminate.
  destruct (Int.eq wz0 i0 (Int.zero wz0)) eqn:?; inv H. 
  exists (Vint wz0 (Int.divu wz0 i i0)); split; auto. 
  simpl. rewrite Int.modu_divu. simplify_op. auto.
  generalize (Int.eq_spec wz0 i0 (Int.zero wz0)). rewrite Heqb; auto. 
Qed.

Theorem divs_pow2:
  forall x wz n logn y,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  Int.ltu wz logn (Int.repr wz (Int.zwordsize wz - 1)) = true ->
  divs x (Vint wz n) = Some y ->
  shrx x (Vint wz logn) = Some y.
Proof.
  Arguments Zminus: simpl never.
  intros x wz n logn y Hwz Hp2 Hltu Hdiv
  ; destruct x; simpl in Hdiv; inv Hdiv; simplify_op.
  rewrite hcast_eq in *.
  destruct (Int.eq wz n (Int.zero wz)
         || Int.eq wz i (Int.repr wz (Int.min_signed wz)) && Int.eq wz n (Int.mone wz)); inv H0.
  rewrite Hltu. decEq. rewrite (Int.divs_pow2 wz i n logn); auto.
Qed.

Theorem divu_pow2:
  forall x wz n logn y,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  divu x (Vint wz n) = Some y ->
  shru x (Vint wz logn) = y.
Proof.
  intros x wz n logn y Hwz Hpw Hdiv; destruct x; simpl in Hdiv; inv Hdiv.
  simplify_op; inv H0.
  destruct (Int.eq wz n (Int.zero wz)); inv H1.
  rewrite (Int.is_power2_range wz _ _ Hpw).
  decEq. symmetry. apply Int.divu_pow2. auto.
Qed.

Theorem modu_pow2:
  forall x wz n logn y,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  modu x (Vint wz n) = Some y ->
  and x (Vint wz (Int.sub wz n (Int.one wz))) = y.
Proof.
  intros x wz n logn y Hwz Hpw Hmod; destruct x; simpl in Hmod; inv Hmod.
  simplify_op; inv H0.
  destruct (Int.eq wz n (Int.zero wz)); inv H1. 
  simpl. decEq. symmetry. eapply Int.modu_and; eauto.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simplify_op.
  simplify_op. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simplify_op; simplify_op.
  decEq. apply Int.and_assoc.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simplify_op.
  decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simplify_op; simplify_op.
  decEq. apply Int.or_assoc.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simplify_op.
  decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simplify_op; simplify_op.
  decEq. apply Int.xor_assoc.
Qed.

Theorem not_xor: forall wz x
  (Hwz: get_wordsize x = Some wz), notint x = xor x (Vint wz (Int.mone wz)).
Proof.
  intros; destruct x; inv Hwz; simplify_op; auto.
Qed.

Theorem shl_mul: forall wz x y
  (Hwz: get_wordsize x = Some wz),
  mul x (shl (Vone wz) y) = shl x y.
Proof.
  intros; destruct x; destruct y; inv Hwz; simplify_op; auto. 
  case (Int.ltu wz1 i0 (Int.iwordsize wz1)); simplify_op.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n
  (Hwz: get_wordsize x = Some 31%nat),
  Int.ltu 31 n (Int.iwordsize 31) = true ->
  shl x (Vint 31 n) = rolm x n (Int.shl 31 (Int.mone 31) n).
Proof.
  intros; destruct x; inv Hwz; simpl; auto.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shru_rolm:
  forall x n
  (Hwz: get_wordsize x = Some 31%nat),
  Int.ltu 31 n (Int.iwordsize 31) = true ->
  shru x (Vint 31 n) = rolm x (Int.sub 31 (Int.iwordsize 31) n) (Int.shru 31 (Int.mone 31) n).
Proof.
  intros; destruct x; inv Hwz; simpl; auto.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

(*
Theorem shrx_carry:
  forall x y z,
  shrx x y = Some z ->
  add (shr x y) (shr_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *.
  destruct (Int.ltu wz0 i0 (Int.repr wz0 (Int.zwordsize wz0 - 1))) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto.
  intros.
(*
    change (Int.unsigned wz0 (Int.repr wz0 (Int.zwordsize wz0 - 1))) with (Int.zwordsize wz0 - 1).
*)
  assert (Int.ltu wz0 i0 (Int.iwordsize wz0) = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned wz0 (Int.iwordsize wz0)) with wz0. omega. 
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto.


  intros. destruct x; destruct y; simplify_op; inv H
  ; destruct (eq_nat_dec _ _); inv H1; rewrite hcast_eq in *.
  - destruct (Int.ltu wz0 i0 (Int.repr wz0 (Int.zwordsize wz0 -1))) eqn:Hltu.
    + unfold add; simplify_op.
      exploit (Int.ltu_inv wz0 i0 (Int.repr wz0 (Int.zwordsize wz0 - 1))); eauto.
      rewrite <- Int.shrx_carry.
      
  - exfalso; apply n; auto.
  rewrite Hltu in H0. inv H0.
  decEq. symmetry. apply Int.shrx_carry. unfold Int.iwordsize in Hltu.
  apply Int.ltu_inv in Hltu.
  assert (Int.ltu wz0 i0 (Int.iwordsize wz0) = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega. 
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto.
Qed.
*)

Theorem shrx_shr:
  forall x y z,
  get_wordsize x = Some 31%nat ->
  shrx x y = Some z ->
  exists p, exists q,
    x = Vint 31 p /\ y = Vint 31 q /\
    z = shr (if Int.lt 31 p (Int.zero 31) then add x (Vint 31 (Int.sub 31 (Int.shl 31 (Int.one 31) q) (Int.one 31))) else x) (Vint 31 q).
Proof.
  destruct x; destruct y; simplify_op; intros; inv H0; inv H; subst.
  destruct (Int.ltu 31 i0 (Int.repr 31 (Int.zwordsize 31 - 1))) eqn:?; inv H2.
  exploit Int.ltu_inv; eauto. change (Int.unsigned 31 (Int.repr 31 (Int.zwordsize 31 - 1))) with 31. intros.
  assert (Int.ltu 31 i0 (Int.iwordsize 31) = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned 31 (Int.iwordsize 31)) with 32. omega. 
  exists i; exists i0; intuition. 
  rewrite Int.shrx_shr; auto. destruct (Int.lt 31 i (Int.zero 31)); simpl; rewrite H0; auto.
Qed.

Theorem or_rolm:
  forall x n m1 m2
  (Hwz: get_wordsize x = Some 31%nat),
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or 31 m1 m2).
Proof.
  intros; destruct x; inv Hwz; simplify_op.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2
  (Hwz: get_wordsize x = Some 31%nat),
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu 31 (Int.add 31 n1 n2) (Int.iwordsize 31))
           (Int.and 31 (Int.rol 31 m1 n2) m2).
Proof.
  intros; destruct x; inv Hwz; simplify_op.
  decEq. 
  apply Int.rolm_rolm. apply int32_wordsize_divides_modulus.
Qed.

Theorem rolm_zero:
  forall x m
  (Hwz: get_wordsize x = Some 31%nat),
  rolm x (Int.zero 31) m = and x (Vint 31 m).
Proof.
  intros; destruct x; inv Hwz; simplify_op. decEq. apply Int.rolm_zero.
Qed.

Theorem negate_cmp_bool:
  forall c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y).
Proof.
  destruct x; destruct y; simplify_op. rewrite Int.negate_cmp. auto.
Qed.

Theorem negate_cmpu_bool_int:
  forall c x y,
  cmpu_bool_int (negate_comparison c) x y = option_map negb (cmpu_bool_int c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c))
    by (destruct c; auto). 
  destruct x; destruct y; simplify_op.
  rewrite Int.negate_cmpu; auto.
Qed.

Theorem negate_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmpu_bool valid_ptr c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c))
    by (destruct c; auto). 
  destruct x; destruct y; simplify_op.
  - rewrite Int.negate_cmpu. auto.
  - destruct (Int.eq 31 i (Int.zero 31)); auto. 
  - destruct (Int.eq 31 i0 (Int.zero 31)); auto.
  - destruct (eq_block b b0).
    destruct ((valid_ptr b (Int.unsigned 31 i) || valid_ptr b (Int.unsigned 31 i - 1)) &&
            (valid_ptr b0 (Int.unsigned 31 i0) || valid_ptr b0 (Int.unsigned 31 i0 - 1))).
    rewrite Int.negate_cmpu. auto.
    auto.
  destruct (valid_ptr b (Int.unsigned 31 i) && valid_ptr b0 (Int.unsigned 31 i0)); auto.
  - decEq. apply Int.negate_cmpu. 
Qed.

Lemma not_of_optbool:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto. 
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  intros. unfold cmp. rewrite negate_cmp_bool. apply not_of_optbool.
Qed.

Theorem negate_cmpu_int:
  forall c x y,
  cmpu_int (negate_comparison c) x y =
    notbool (cmpu_int c x y).
Proof.
  intros. unfold cmpu_int. rewrite negate_cmpu_bool_int. apply not_of_optbool.
Qed.

Theorem negate_cmpu:
  forall valid_ptr c x y,
  cmpu valid_ptr (negate_comparison c) x y =
    notbool (cmpu valid_ptr c x y).
Proof.
  intros. unfold cmpu. rewrite negate_cmpu_bool. apply not_of_optbool.
Qed.

Theorem swap_cmp_bool:
  forall c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x.
Proof.
  destruct x; destruct y; simplify_op; auto. rewrite Int.swap_cmp. auto.
Qed.

Theorem swap_cmpu_bool_int:
  forall c x y,
  cmpu_bool_int (swap_comparison c) x y =
    cmpu_bool_int c y x.
Proof.
  assert (forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c)
    by (destruct c; auto).
  destruct x; destruct y; simplify_op.
  rewrite Int.swap_cmpu; auto.
Qed.

Theorem swap_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (swap_comparison c) x y =
    cmpu_bool valid_ptr c y x.
Proof.
  assert (forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c)
    by (destruct c; auto).
  destruct x; destruct y; simplify_op.
  - rewrite Int.swap_cmpu. auto.
  - case (Int.eq 31 i (Int.zero 31)); auto.
  - case (Int.eq 31 i0 (Int.zero 31)); auto.
  - destruct (eq_block b b0); subst.
    rewrite dec_eq_true.
    destruct (valid_ptr b0 (Int.unsigned 31 i) || valid_ptr b0 (Int.unsigned 31 i - 1));
    destruct (valid_ptr b0 (Int.unsigned 31 i0) || valid_ptr b0 (Int.unsigned 31 i0 - 1));
    simpl; auto.
    rewrite Int.swap_cmpu. auto.
    rewrite dec_eq_false by auto.
    destruct (valid_ptr b (Int.unsigned 31 i));
    destruct (valid_ptr b0 (Int.unsigned 31 i0)); simpl; auto.
  - decEq. apply Int.swap_cmpu.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Cgt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmp_ne_0_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint 0 (Int.zero 0)) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmp_eq_1_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint 0 (Int.one 0)) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmp_eq_0_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint 0 (Int.zero 0)) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmp_ne_1_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint 0 (Int.one 0)) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_int_ne_0_optbool:
  forall ob,
  cmpu_int Cne (of_optbool ob) (Vint 0 (Int.zero 0)) = of_optbool ob.
Proof.
  intros; destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_ne_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint 0 (Int.zero 0)) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_int_eq_1_optbool:
  forall ob,
  cmpu_int Ceq (of_optbool ob) (Vint 0 (Int.one 0)) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_eq_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint 0 (Int.one 0)) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_int_eq_0_optbool:
  forall ob,
  cmpu_int Ceq (of_optbool ob) (Vint 0 (Int.zero 0)) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_eq_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint 0 (Int.zero 0)) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_int_ne_1_optbool:
  forall ob,
  cmpu_int Cne (of_optbool ob) (Vint 0 (Int.one 0)) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_ne_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint 0 (Int.one 0)) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Definition is_bool (v: val) :=
  v = Vundef \/ v = Vtrue \/ v = Vfalse.

Definition cmp_mismatch (c: comparison): val :=
  match c with
  | Ceq => Vfalse
  | Cne => Vtrue
  | _   => Vundef
  end.

Lemma of_bool_is_bool:
  forall b, is_bool (of_bool b).
Proof.
  destruct b; unfold is_bool; simpl; tauto.
Qed.

Lemma undef_is_bool: is_bool Vundef.
Proof.
  unfold is_bool; tauto.
Qed.

Lemma cmp_mismatch_is_bool:
  forall c, is_bool (cmp_mismatch c).
Proof.
  destruct c; simpl; unfold is_bool; tauto.
Qed.

Lemma cmp_is_bool:
  forall c v1 v2, is_bool (cmp c v1 v2).
Proof.
  destruct v1; destruct v2; simplify_op; try apply undef_is_bool;
    try solve [apply of_bool_is_bool].
  destruct c; unfold cmp; simpl; destruct (eq_nat_dec wz wz0); subst
  ; try rewrite hcast_eq; simpl
  ; try match goal with
  | |- context [if ?c then _ else _] => destruct c
  end; unfold is_bool; auto.
Qed.

Lemma cmpu_int_is_bool:
  forall c v1 v2, is_bool (cmpu_int c v1 v2).
Proof.
  destruct v1; destruct v2; simplify_op; try apply undef_is_bool;
    try solve [apply of_bool_is_bool]
  ; try (destruct c; unfold cmpu_int; simpl
  ; try destruct (eq_nat_dec _ _); subst
  ; try rewrite hcast_eq; simpl
  ; try match goal with
  | |- context [if ?c then _ else _] => destruct c
  end; unfold is_bool; auto; fail).
Qed.

Lemma cmpu_is_bool:
  forall valid_ptr c v1 v2, is_bool (cmpu valid_ptr c v1 v2).
Proof.
  destruct v1; destruct v2; simplify_op; try apply undef_is_bool;
    try solve [apply of_bool_is_bool]
  ; try (destruct c; unfold cmpu; simpl
  ; try destruct (eq_nat_dec _ _); subst
  ; try rewrite hcast_eq; simpl
  ; try match goal with
  | |- context [if ?c then _ else _] => destruct c
  end; unfold is_bool; auto; fail).

  destruct c; unfold cmpu; simpl; try destruct (eq_block _ _); subst
  ; repeat match goal with
  | |- context [if ?c then _ else _] => destruct c; unfold is_bool; simpl
  end; auto.
Qed.

Lemma cmpf_is_bool:
  forall c v1 v2, is_bool (cmpf c v1 v2).
Proof.
  destruct v1; destruct v2; simplify_op;
  apply undef_is_bool || apply of_bool_is_bool.
Qed.

Lemma notbool_is_bool:
  forall v, is_bool (notbool v).
Proof.
  destruct v; simplify_op.
  apply undef_is_bool. apply of_bool_is_bool. 
  apply undef_is_bool. unfold is_bool; tauto.
  unfold is_bool. auto. unfold is_bool; auto.
Qed.

Lemma zero_ext_and:
  forall n wz v
  (Hwz: get_wordsize v = Some wz),
  0 < n < Z_of_nat wz ->
  Val.zero_ext n v = Val.and v (Vint wz (Int.repr wz (two_p n - 1))).
Proof.
  intros. inv Hwz; destruct v; simplify_op. decEq. apply Int.zero_ext_and; auto. omega.
  inv H1. exfalso; apply n0; auto.
Qed.

Lemma Vundef__eq_Vbool__Vundef : forall wz, eq_Vbool wz Vundef Vundef.
Proof.
  intros wz. unfold eq_Vbool.
  split; split; intro J; inversion J.
Qed.

Lemma Vone__eq_Vbool__Vtrue : forall wz, eq_Vbool wz (Vone wz) Vtrue.
Proof.
  intros wz. unfold eq_Vbool.
  split; split; intro J; try solve [auto | inversion J].
Qed.

Lemma Vzero__eq_Vbool__Vfalse : forall wz, eq_Vbool wz (Vzero wz) Vfalse.
Proof.
  intros wz. unfold eq_Vbool.
  split; split; intro J; try solve [auto | inversion J].
Qed.

Lemma rolm_lt_zero:
  forall v,
  get_wordsize v = Some 31%nat ->
  eq_Vbool 31 (rolm v (Int.one 31) (Int.one 31)) (cmp Clt v (Vint 31 (Int.zero 31))).
Proof.
  intros. unfold cmp, cmp_bool; destruct v; simplify_op
  ; try solve [apply Vundef__eq_Vbool__Vundef].
  assert (Vint 31 (Int.shru 31 i (Int.repr 31 (Z_of_nat 32 - 1))) =
    Vint 31 (Int.rolm 31 i (Int.one 31) (Int.one 31))) as EQ.
    decEq. symmetry. rewrite Int.shru_rolm. auto. auto.
  rewrite <- EQ.
  rewrite Int.shru_lt_zero.
  destruct (Int.lt 31 i (Int.zero 31)).
  apply Vone__eq_Vbool__Vtrue.
  apply Vzero__eq_Vbool__Vfalse.
Qed.

Lemma rolm_ge_zero:
  forall v,
  get_wordsize v = Some 31%nat ->
  eq_Vbool 31 (xor (rolm v (Int.one 31) (Int.one 31)) (Vint 31 (Int.one 31))) 
    (cmp Cge v (Vint 31 (Int.zero 31))).
Proof.
  intros. destruct v; simplify_op; try solve [apply Vundef__eq_Vbool__Vundef].
  assert ((Int.shru 31 i (Int.repr 31 (Z_of_nat 32 - 1))) =
    (Int.rolm 31 i (Int.one 31) (Int.one 31))) as EQ.
    decEq. symmetry. rewrite Int.shru_rolm. auto. auto.
  rewrite <- EQ.
  rewrite Int.shru_lt_zero.
  unfold cmp.
  destruct (Int.lt 31 i (Int.zero 31)) eqn:Heqn; simpl.
  rewrite Int.xor_one_one. rewrite Heqn. simpl. apply Vzero__eq_Vbool__Vfalse.
  rewrite Int.xor_zero_one. rewrite Heqn. simpl. apply Vone__eq_Vbool__Vtrue.
  inv H. exfalso; apply n; auto.
Qed.

(** The ``is less defined'' relation between values. 
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Lemma lessdef_same:
  forall v1 v2, v1 = v2 -> lessdef v1 v2.
Proof.
  intros. subst v2. constructor.
Qed.

Lemma lessdef_trans:
  forall v1 v2 v3, lessdef v1 v2 -> lessdef v2 v3 -> lessdef v1 v3.
Proof.
  intros. inv H. auto. constructor.
Qed.

Inductive lessdef_list: list val -> list val -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In Vundef vl1.
Proof.
  induction 1; simpl.
  tauto.
  inv H. destruct IHlessdef_list. 
  left; congruence. tauto. tauto.
Qed.

(** Compatibility of operations with the [lessdef] relation. *)

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
Proof.
  intros. inv H. auto. destruct chunk; simpl; auto.
Qed.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.
(*
Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
Proof.
  intros; inv H; simpl; auto.
Qed.
*)
Lemma add_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (add v1 v2) (add v1' v2').
Proof.
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto.
Qed.

Lemma cmpu_bool_int_lessdef:
  forall c v1 v1' v2 v2' b,
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmpu_bool_int c v1 v2 = Some b ->
  cmpu_bool_int c v1' v2' = Some b.
Proof.
  intros. 
  destruct v1; simpl in H; try discriminate;
  destruct v2; simpl in H; try discriminate;
  inv H; inv H0; simpl; auto.
Qed.

Lemma cmpu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall b ofs, valid_ptr b ofs = true -> valid_ptr' b ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmpu_bool valid_ptr c v1 v2 = Some b ->
  cmpu_bool valid_ptr' c v1' v2' = Some b.
Proof.
  intros. 
  destruct v1; simpl in H2; try discriminate;
  destruct v2; simpl in H2; try discriminate;
  inv H0; inv H1; simpl; auto.
  destruct (eq_block b0 b1).
  assert (forall b ofs, valid_ptr b ofs || valid_ptr b (ofs - 1) = true ->
                        valid_ptr' b ofs || valid_ptr' b (ofs - 1) = true).
    intros until ofs. rewrite ! orb_true_iff. intuition. 
  destruct (valid_ptr b0 (Int.unsigned 31 i) || valid_ptr b0 (Int.unsigned 31 i - 1)) eqn:?; try discriminate.
  destruct (valid_ptr b1 (Int.unsigned 31 i0) || valid_ptr b1 (Int.unsigned 31 i0 - 1)) eqn:?; try discriminate.
  erewrite !H0 by eauto. auto.
  destruct (valid_ptr b0 (Int.unsigned 31 i)) eqn:?; try discriminate.
  destruct (valid_ptr b1 (Int.unsigned 31 i0)) eqn:?; try discriminate.
  erewrite !H by eauto. auto.
Qed.

Lemma of_optbool_lessdef:
  forall ob ob',
  (forall b, ob = Some b -> ob' = Some b) ->
  lessdef (of_optbool ob) (of_optbool ob').
Proof.
  intros. destruct ob; simpl; auto. rewrite (H b); auto. 
Qed.

(* NOTE: added for vellvm *)
Definition has_chunk := fun (v : val) (chk : memory_chunk) =>
match v with
| Vundef => True
| Vint wz i0 => match chk with
              | Mint wz' => wz = wz' /\
                            0 <= Int.unsigned wz i0 < Int.modulus wz
              | _ => False
              end
| Vsingle f => match chk with
              | Mfloat32 => True
              | _ => False
              end
| Vfloat f => match chk with
              | Mfloat64 => True
              | _ => False
              end
| _ => match chk with
       | Mint wz => wz = 31%nat
       | _ => False
       end
end.

Definition has_chunkb (v : val) (chk : AST.memory_chunk) : bool :=
match v with
| Vundef => true
| Vint wz i0 => match chk with
                | AST.Mint wz' => 
                   eq_nat_dec wz wz' &&
                   zle 0 (Int.unsigned wz i0) &&
                   zlt (Int.unsigned wz i0) (Int.modulus wz)
                | _ => false
                end
| Vfloat f => match chk with
              | AST.Mint _ => false
              | AST.Mfloat32 => false
              | AST.Mfloat64 => true
              end
| Vsingle f => match chk with
              | AST.Mint _ => false
              | AST.Mfloat32 => true
              | AST.Mfloat64 => false
              end
| _ => match chk with
       | AST.Mint wz => eq_nat_dec wz 31%nat
       | _ => false
       end
end.

Lemma has_chunkb__has_chunk: forall v chk,
  has_chunkb v chk = true ->
  has_chunk v chk.
Proof.
  destruct v, chk; simpl; intros; try solve [auto | congruence].
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff in H1. destruct H1 as [H1 H3].
    destruct (eq_nat_dec wz n); try inv H1. subst.
    destruct (zle 0 (Int.unsigned n i)); try inv H3.
    destruct (zlt (Int.unsigned n i) (Int.modulus n)); try inv H2.
    auto.
    destruct (eq_nat_dec n 31); try inv H; auto.
    destruct (eq_nat_dec n 31); try inv H; auto.
Qed.

Lemma cmp_has_Mint0: forall c0 v1 v2,
  has_chunk (Val.cmp c0 v1 v2) (Mint 0).
Proof.
  intros.
  match goal with
  | |- context [cmp ?c ?v1 ?v2] => assert (J:=cmp_is_bool c v1 v2)
  end. 
    destruct J as [J | [ J | J ]]; rewrite J; constructor; try solve [
      auto |
      unfold Int.unsigned, one, zero, Int.one, Int.zero, Int.repr; simpl;
      apply Z_mod_lt; apply Int.modulus_pos
    ].
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
Qed.

Lemma cmpu_int_has_Mint0: forall c0 v1 v2,
  has_chunk (cmpu_int c0 v1 v2) (Mint 0).
Proof.
  intros.
  match goal with
  | |- context [cmpu_int ?c ?v1 ?v2] => assert (J:=cmpu_int_is_bool c v1 v2)
  end. 
    destruct J as [J | [ J | J ]]; rewrite J; constructor; try solve [
      auto |
      unfold Int.unsigned, one, zero, Int.one, Int.zero, Int.repr; simpl;
      apply Z_mod_lt; apply Int.modulus_pos
    ].
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
Qed.

Lemma cmpu_has_Mint0: forall valid_ptr c0 v1 v2,
  has_chunk (cmpu valid_ptr c0 v1 v2) (Mint 0).
Proof.
  intros.
  match goal with
  | |- context [cmpu ?val ?c ?v1 ?v2] => assert (J:=cmpu_is_bool val c v1 v2)
  end. 
    destruct J as [J | [ J | J ]]; rewrite J; constructor; try solve [
      auto |
      unfold Int.unsigned, one, zero, Int.one, Int.zero, Int.repr; simpl;
      apply Z_mod_lt; apply Int.modulus_pos
    ].
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
Qed.

Lemma cmpf_has_Mint0: forall c0 v1 v2,
  has_chunk (cmpf c0 v1 v2) (Mint 0).
Proof.
  intros.
  match goal with
  | |- context [cmpf ?c ?v1 ?v2] => assert (J:=cmpf_is_bool c v1 v2)
  end. 
    destruct J as [J | [ J | J ]]; rewrite J; constructor; try solve [
      auto |
      unfold Int.unsigned, one, zero, Int.one, Int.zero, Int.repr; simpl;
      apply Z_mod_lt; apply Int.modulus_pos
    ].
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
  unfold Int.modulus, two_power_nat, Int.wordsize, shift_nat; simpl; omega.
Qed.

Ltac bop_has_chunk :=
  intros;
  simplify_op; try solve [
    auto |
    match goal with
    | |- context [if ?e then _ else _] =>
      destruct e; simpl; eauto
    | |- _ => idtac
    end;
    split; try solve [
      auto |
      apply Int.Z_mod_modulus_range
    ]
  ].

Lemma add_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (add (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof.
  unfold add; bop_has_chunk.
Qed.

Lemma add_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (add (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. unfold add; bop_has_chunk. Qed.

Lemma sub_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (sub (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. unfold sub; bop_has_chunk. Qed.

Lemma sub_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (sub (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. unfold sub; bop_has_chunk. Qed.

Lemma mul_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (mul (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma mul_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (mul (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma divs_has_chunk1 : forall wz i0 wz0 i1 v
  (DS: divs (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz).
Proof.
  intros. inv DS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (_ || _ && _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma divs_has_chunk2 : forall wz i0 wz0 i1 v
  (DS: divs (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz0).
Proof.
  intros. inv DS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (_ || _ && _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma mods_has_chunk1 : forall wz i0 wz0 i1 v
  (MS: mods (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz).
Proof.
  intros. inv MS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (_ || _ && _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma mods_has_chunk2 : forall wz i0 wz0 i1 v
  (MS: mods (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz0).
Proof.
  intros. inv MS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (_ || _ && _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma divu_has_chunk1 : forall wz i0 wz0 i1 v
  (DS: divu (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz).
Proof.
  intros. inv DS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (Int.eq _ _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma divu_has_chunk2 : forall wz i0 wz0 i1 v
  (DS: divu (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz0).
Proof.
  intros. inv DS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (Int.eq _ _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma modu_has_chunk1 : forall wz i0 wz0 i1 v
  (MS: modu (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz).
Proof.
  intros. inv MS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (Int.eq _ _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma modu_has_chunk2 : forall wz i0 wz0 i1 v
  (MS: modu (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz0).
Proof.
  intros. inv MS.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (Int.eq _ _); subst; auto; inv H0.
  bop_has_chunk. inv H0.
Qed.

Lemma and_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (and (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma and_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (and (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma or_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (or (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma or_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (or (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma xor_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (xor (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma xor_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (xor (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma shl_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (shl (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma shl_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (shl (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma shr_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (shr (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma shr_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (shr (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma shr_carry_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (shr_carry (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof.
  unfold shr_carry; bop_has_chunk.
  destruct (Int.ltu _ _ _); subst; auto.
  bop_has_chunk.
  split; auto.
  SearchAbout Int.modulus.
  apply Int.unsigned_range.
  simpl; auto.
Qed.

Lemma shr_carry_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (shr_carry (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. 
  unfold shr_carry; bop_has_chunk.
  destruct (Int.ltu _ _ _); subst; auto.
  bop_has_chunk.
  split; auto.
  SearchAbout Int.modulus.
  apply Int.unsigned_range.
  simpl; auto.
Qed.

Lemma shrx_has_chunk1 : forall wz i0 wz0 i1 v
  (S: shrx (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz).
Proof.
  intros; inv S.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (Int.ltu _ _ _); subst; inv H0; simpl.
  split; auto.
  apply Int.Z_mod_modulus_range.
  inv H0.
Qed.

Lemma shrx_has_chunk2 : forall wz i0 wz0 i1 v
  (S: shrx (Vint wz i0) (Vint wz0 i1) = Some v),
  has_chunk v (Mint wz0).
Proof.
  intros; inv S.
  destruct (eq_nat_dec _ _); subst; try rewrite hcast_eq in *; auto.
  destruct (Int.ltu _ _ _); subst; inv H0; simpl.
  split; auto.
  apply Int.Z_mod_modulus_range.
  inv H0.
Qed.

Lemma shru_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (shru (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma shru_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (shru (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma ror_has_chunk1 : forall wz i0 wz0 i1,
  has_chunk (ror (Vint wz i0) (Vint wz0 i1)) (Mint wz).
Proof. bop_has_chunk. Qed.

Lemma ror_has_chunk2 : forall wz i0 wz0 i1,
  has_chunk (ror (Vint wz i0) (Vint wz0 i1)) (Mint wz0).
Proof. bop_has_chunk. Qed.

Lemma zero_ext'_has_chunk : forall nbits v,
  has_chunk (zero_ext' nbits v) (Mint nbits).
Proof.
  destruct v; simpl; auto.
  split; auto.
  apply Int.Z_mod_modulus_range.
Qed.

Lemma sign_ext'_has_chunk : forall nbits v,
  has_chunk (sign_ext' nbits v) (Mint nbits).
Proof.
  destruct v; simpl; auto.
  split; auto.
    apply Int.Z_mod_modulus_range.
Qed.

End Val.

(** * Values and memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

Definition meminj : Type := block -> option (block * Z).

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. *)

Inductive val_inject (mi: meminj): val -> val -> Prop :=
  | val_inject_int:
      forall wz i, val_inject mi (Vint wz i) (Vint wz i)
  | val_inject_float:
      forall f, val_inject mi (Vfloat f) (Vfloat f)
  | val_inject_single:
      forall f, val_inject mi (Vsingle f) (Vsingle f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta,
      mi b1 = Some (b2, delta) ->
      ofs2 = Int.add 31 ofs1 (Int.repr 31 delta) ->
      val_inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_inttoptr:
      forall i, val_inject mi (Vinttoptr i) (Vinttoptr i)
  | val_inject_undef: forall v,
      val_inject mi Vundef v.

Hint Constructors val_inject.
Hint Resolve val_inject_int val_inject_float val_inject_ptr val_inject_inttoptr
             val_inject_undef.

Inductive val_list_inject (mi: meminj): list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject mi nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject mi v v' -> val_list_inject mi vl vl'->
      val_list_inject mi (v :: vl) (v' :: vl').  

Hint Resolve val_nil_inject val_cons_inject.

Section VAL_INJ_OPS.

Variable f: meminj.

Lemma val_load_result_inject:
  forall chunk v1 v2,
  val_inject f v1 v2 ->
  val_inject f (Val.load_result chunk v1) (Val.load_result chunk v2).
Proof.
  intros. inv H; destruct chunk; simpl; try econstructor; eauto.
    destruct (eq_nat_dec _ _); try econstructor; eauto.
    destruct (eq_nat_dec _ _); try econstructor; eauto.
Qed.

Remark val_add_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.add v1 v2) (Val.add v1' v2').
Proof.
  intros. inv H; inv H0; simpl; try econstructor; eauto;
  unfold Val.add; Val.simplify_op.
  - econstructor. apply H.
    repeat rewrite Int.add_assoc. decEq. rewrite Int.add_commut. auto.
  - econstructor. apply H1.
    repeat rewrite Int.add_assoc. decEq. rewrite Int.add_commut. auto.
Qed.

Remark val_sub_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.sub v1 v2) (Val.sub v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto;
  unfold Val.sub; Val.simplify_op.
  - econstructor; eauto. rewrite Int.sub_add_l. auto.
  - destruct (peq b1 b0); auto.
    subst. rewrite H1 in H. inv H. rewrite dec_eq_true.
    rewrite Int.sub_shifted.
    econstructor; eauto.
Qed.

Lemma val_cmp_bool_inject:
  forall c v1 v2 v1' v2' b,
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  Val.cmp_bool c v1 v2 = Some b ->
  Val.cmp_bool c v1' v2' = Some b.
Proof.
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
Qed.

Variable (valid_ptr1 valid_ptr2 : block -> Z -> bool).

Let weak_valid_ptr1 b ofs := valid_ptr1 b ofs || valid_ptr1 b (ofs - 1).
Let weak_valid_ptr2 b ofs := valid_ptr2 b ofs || valid_ptr2 b (ofs - 1).

Hypothesis valid_ptr_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  valid_ptr1 b1 (Int.unsigned 31 ofs) = true ->
  valid_ptr2 b2 (Int.unsigned 31 (Int.add 31 ofs (Int.repr 31 delta))) = true.

Hypothesis weak_valid_ptr_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  weak_valid_ptr1 b1 (Int.unsigned 31 ofs) = true ->
  weak_valid_ptr2 b2 (Int.unsigned 31 (Int.add 31 ofs (Int.repr 31 delta))) = true.

Hypothesis weak_valid_ptr_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  weak_valid_ptr1 b1 (Int.unsigned 31 ofs) = true ->
  0 <= Int.unsigned 31 ofs + Int.unsigned 31 (Int.repr 31 delta) <= Int.max_unsigned 31.

Hypothesis valid_different_ptrs_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  valid_ptr1 b1 (Int.unsigned 31 ofs1) = true ->
  valid_ptr1 b2 (Int.unsigned 31 ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned 31 (Int.add 31 ofs1 (Int.repr 31 delta1)) <> Int.unsigned 31 (Int.add 31 ofs2 (Int.repr 31 delta2)).

Lemma val_cmpu_bool_int_inject:
  forall c v1 v2 v1' v2' b,
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  Val.cmpu_bool_int c v1 v2 = Some b ->
  Val.cmpu_bool_int c v1' v2' = Some b.
Proof.
  Local Opaque Int.add.
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
Qed.

Lemma val_cmpu_bool_inject:
  forall c v1 v2 v1' v2' b,
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  Val.cmpu_bool valid_ptr1 c v1 v2 = Some b ->
  Val.cmpu_bool valid_ptr2 c v1' v2' = Some b.
Proof.
  Local Opaque Int.add.
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
  fold (weak_valid_ptr1 b1 (Int.unsigned 31 ofs1)) in H1.
  fold (weak_valid_ptr1 b0 (Int.unsigned 31 ofs0)) in H1.
  fold (weak_valid_ptr2 b2 (Int.unsigned 31 (Int.add 31 ofs1 (Int.repr 31 delta)))).
  fold (weak_valid_ptr2 b3 (Int.unsigned 31 (Int.add 31 ofs0 (Int.repr 31 delta0)))). 
  destruct (eq_block b1 b0); subst.
  rewrite H in H2. inv H2. rewrite dec_eq_true.
  destruct (weak_valid_ptr1 b0 (Int.unsigned 31 ofs1)) eqn:?; try discriminate.
  destruct (weak_valid_ptr1 b0 (Int.unsigned 31 ofs0)) eqn:?; try discriminate.
  erewrite !weak_valid_ptr_inj by eauto. simpl.
  rewrite <-H1. simpl. decEq. apply Int.translate_cmpu; eauto.
  destruct (valid_ptr1 b1 (Int.unsigned 31 ofs1)) eqn:?; try discriminate.
  destruct (valid_ptr1 b0 (Int.unsigned 31 ofs0)) eqn:?; try discriminate.
  destruct (eq_block b2 b3); subst.
  assert (valid_ptr_implies: forall b ofs, valid_ptr1 b ofs = true -> weak_valid_ptr1 b ofs = true).
    intros. unfold weak_valid_ptr1. rewrite H0; auto. 
  erewrite !weak_valid_ptr_inj by eauto using valid_ptr_implies. simpl.
  exploit valid_different_ptrs_inj; eauto. intros [?|?]; [congruence |].
  destruct c; simpl in H1; inv H1.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.
  now erewrite !valid_ptr_inj by eauto.
Qed.

End VAL_INJ_OPS.

(** Monotone evolution of a memory injection. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta).

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr. auto. Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3, 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof.
  unfold inject_incr; intros. eauto. 
Qed.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  val_inject f1 v v' ->
  val_inject f2 v v'.
Proof.
  intros. inv H0; eauto.
Qed.

Lemma val_list_inject_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> val_list_inject f1 vl vl' ->
  val_list_inject f2 vl vl'.
Proof.
  induction vl; intros; inv H0. auto.
  constructor. eapply val_inject_incr; eauto. auto.
Qed.

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

Lemma val_inject_lessdef:
  forall v1 v2, Val.lessdef v1 v2 <-> val_inject (fun b => Some(b, 0)) v1 v2.
Proof.
  intros; split; intros.
  inv H; auto. destruct v2; econstructor; eauto. rewrite Int.add_zero; auto. 
  inv H; auto. inv H0. rewrite Int.add_zero; auto.
Qed.

Lemma val_list_inject_lessdef:
  forall vl1 vl2, Val.lessdef_list vl1 vl2 <-> val_list_inject (fun b => Some(b, 0)) vl1 vl2.
Proof.
  intros; split.
  induction 1; constructor; auto. apply val_inject_lessdef; auto.
  induction 1; constructor; auto. apply val_inject_lessdef; auto.
Qed.

(** The identity injection gives rise to the "less defined than" relation. *)

Definition inject_id : meminj := fun b => Some(b, 0).

Lemma val_inject_id:
  forall v1 v2,
  val_inject inject_id v1 v2 <-> Val.lessdef v1 v2.
Proof.
  intros; split; intros.
  inv H; auto. 
  unfold inject_id in H0. inv H0. rewrite Int.add_zero. constructor.
  inv H. destruct v2; econstructor. unfold inject_id; reflexivity. rewrite Int.add_zero; auto.
  constructor.
Qed.

(** Composing two memory injections *)

Definition compose_meminj (f f': meminj) : meminj :=
  fun b =>
    match f b with
    | None => None
    | Some(b', delta) =>
        match f' b' with
        | None => None
        | Some(b'', delta') => Some(b'', delta + delta')
        end
    end.

Lemma val_inject_compose:
  forall f f' v1 v2 v3,
  val_inject f v1 v2 -> val_inject f' v2 v3 ->
  val_inject (compose_meminj f f') v1 v3.
Proof.
  intros. inv H; auto; inv H0; auto. dependent destruction H2; auto. econstructor.
  unfold compose_meminj; rewrite H1; rewrite H3; eauto. 
  rewrite Int.add_assoc. decEq. unfold Int.add. apply Int.eqm_samerepr. auto with ints.
Qed.

(** More properties for Val. *)
(* NOTE: Vellvm Context *)

Lemma add_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.add (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  unfold Val.add; Val.simplify_op; try congruence.
Qed.

Lemma sub_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.sub (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  unfold Val.sub; Val.simplify_op; try congruence.
Qed.

Lemma mul_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.mul (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simplify_op; try congruence.
Qed.

Lemma divu_isnt_ptr : forall wz i0 wz0 i1 v b ofs,
  Val.divu (Vint wz i0) (Vint wz0 i1) = Some v ->
  v <> Vptr b ofs.
Proof.
  intros.
  inv H; destruct (eq_nat_dec _ _); subst
  ; try match goal with
    | _: context[if ?s then _ else _] |- _ => destruct s end
  ; subst; inv H1.
  congruence.
Qed.

Lemma divs_isnt_ptr : forall wz i0 wz0 i1 v b ofs,
  Val.divs (Vint wz i0) (Vint wz0 i1) = Some v ->
  v <> Vptr b ofs.
Proof.
  intros.
  inv H; destruct (eq_nat_dec _ _); subst
  ; try match goal with
    | _: context[if ?s then _ else _] |- _ => destruct s end
  ; subst; inv H1.
  congruence.
Qed.

Lemma modu_isnt_ptr : forall wz i0 wz0 i1 v b ofs,
  Val.modu (Vint wz i0) (Vint wz0 i1) = Some v ->
  v <> Vptr b ofs.
Proof.
  intros.
  inv H; destruct (eq_nat_dec _ _); subst
  ; try match goal with
    | _: context[if ?s then _ else _] |- _ => destruct s end
  ; subst; inv H1.
  congruence.
Qed.

Lemma mods_isnt_ptr : forall wz i0 wz0 i1 v b ofs,
  Val.mods (Vint wz i0) (Vint wz0 i1) = Some v ->
  v <> Vptr b ofs.
Proof.
  intros.
  inv H; destruct (eq_nat_dec _ _); subst
  ; try match goal with
    | _: context[if ?s then _ else _] |- _ => destruct s end
  ; subst; inv H1.
  congruence.
Qed.

Lemma shl_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shl (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simplify_op; try congruence.
  destruct (Int.ltu _ _ _); congruence.
Qed.

Lemma shrx_isnt_ptr : forall wz i0 wz0 i1 v b ofs,
  Val.shrx (Vint wz i0) (Vint wz0 i1) = Some v ->
  v <> Vptr b ofs.
Proof.
  intros.
  inv H; destruct (eq_nat_dec _ _); subst
  ; try match goal with
    | _: context[if ?s then _ else _] |- _ => destruct s end
  ; subst; inv H1.
  congruence.
Qed.

Lemma shr_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shr (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simplify_op; try congruence.
  destruct (Int.ltu _ _ _); congruence.
Qed.

Lemma and_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.and (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simplify_op; try congruence.
Qed.

Lemma or_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.or (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simplify_op; try congruence.
Qed.

Lemma xor_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.xor (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simplify_op; try congruence.
Qed.

Lemma cmp_isnt_ptr : forall c wz i0 wz0 i1 b ofs,
  Val.cmp c (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  unfold Val.cmp; Val.simplify_op; try congruence.
  destruct (Int.cmp _ _ _); unfold Vtrue, Vfalse, Vone, Vzero; congruence.
Qed.

Lemma cmpu_int_isnt_ptr :
  forall (c:comparison) (wz0:nat) (i0: Int.int wz0)
         (wz1:nat) (i1: Int.int wz1) (b:block) (ofs:Int.int 31),
  Val.cmpu_int c (Vint wz0 i0) (Vint wz1 i1) <> Vptr b ofs.
Proof.
  intros.
  unfold Val.cmpu_int; Val.simplify_op; try congruence.
  destruct (Int.cmpu _ _); unfold Vtrue, Vfalse, Vone, Vzero; congruence.
Qed.

Lemma cmpu_isnt_ptr :
  forall valid_ptr (c:comparison) (wz0:nat) (i0: Int.int wz0)
         (wz1:nat) (i1: Int.int wz1) (b:block) (ofs:Int.int 31),
  Val.cmpu valid_ptr c (Vint wz0 i0) (Vint wz1 i1) <> Vptr b ofs.
Proof.
  intros.
  unfold Val.cmpu; Val.simplify_op; try congruence.
  destruct (Int.cmpu _ _ _); unfold Vtrue, Vfalse, Vone, Vzero; congruence.
Qed.

Lemma val_of_bool_isnt_ptr : forall v b ofs,
  Val.of_bool v <> Vptr b ofs.
Proof.
  intros. unfold Val.of_bool. destruct v. 
    unfold Vtrue. unfold Vone. congruence.
    unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma Vfalse_isnt_ptr : forall b ofs,
  Vfalse <> Vptr b ofs.
Proof.
  intros. unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma Vtrue_isnt_ptr : forall b ofs,
  Vtrue <> Vptr b ofs.
Proof.
  intros. unfold Vtrue. unfold Vone. congruence.
Qed.

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Proof.
  induction vs1; destruct vs2; simpl; intros; inv H; auto.
Qed.
