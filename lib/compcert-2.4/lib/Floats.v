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

Parameter float: Set.                  (**r the type of IEE754 double-precision FP numbers *)
Parameter float32: Set.                  (**r the type of IEE754 single-precision FP numbers *)

(** * Double-precision FP numbers *)

Module Float.

(** ** Operations over double-precision floats *)

Parameter zero: float.                  (**r the float [+0.0] *)

Axiom eq_dec: forall (f1 f2: float), {f1 = f2} + {f1 <> f2}.

(** Arithmetic operations *)

Parameter neg: float -> float.          (**r opposite (change sign) *)
Parameter abs: float -> float.          (**r absolute value (set sign to [+]) *)
Parameter add: float -> float -> float. (**r addition *)
Parameter sub: float -> float -> float. (**r subtraction *)
Parameter mul: float -> float -> float. (**r multiplication *)
Parameter div: float -> float -> float. (**r division *)
Parameter rem: float -> float -> float. (**r mod *)
Parameter cmp: comparison -> float -> float -> bool.  (**r comparison *)

(** Conversions *)

Parameter of_single: float32 -> float.
Parameter to_single: float -> float32.

Parameter to_int : float -> option int32.   (**r conversion to signed 32-bit int *)
Parameter to_intu: float -> option int32.  (**r conversion to unsigned 32-bit int *)
Parameter to_long: float -> option int64.  (**r conversion to signed 64-bit int *)
Parameter to_longu: float -> option int64. (**r conversion to unsigned 64-bit int *)

Parameter of_int: int32 -> float.     (**r conversion from signed 32-bit int *)
Parameter of_intu: int32 -> float.    (**r conversion from unsigned 32-bit int *)

Parameter of_long: int64 -> float.   (**r conversion from signed 64-bit int *)
Parameter of_longu: int64 -> float.  (**r conversion from unsigned 64-bit int *)
(*
Parameter from_parsed (base:positive) (intPart:positive) (expPart:Z) : float.
*)
(** Conversions between floats and their concrete in-memory representation
    as a sequence of 64 bits. *)

Parameter to_bits: float -> int64.
Parameter of_bits: int64 -> float.

Definition from_words (hi lo: int32) : float :=
  of_bits
    (Int.or 63 (Int.shl 63 (Int.repr 63 (Int.unsigned 31 hi)) (Int.repr 63 32))
              (Int.repr 63 (Int.unsigned 31 lo))).

(** ** Properties *)

Axiom add_commut:
  forall x y, add x y = add y x.

Axiom mul_commut:
  forall x y, mul x y = mul y x.

(** Multiplication by 2 is diagonal addition. *)

Axiom mul2_add:
  forall f, add f f = mul f (of_int (Int.repr 31 2%Z)).

(** Properties of comparisons. *)

Axiom cmp_swap:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.

Axiom cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).

Axiom cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.

Axiom cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.

Axiom cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.

Axiom cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.

Axiom cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.

(** Properties of conversions to/from in-memory representation.
  The conversions are bijective (one-to-one). *)

Axiom of_to_bits:
  forall f, of_bits (to_bits f) = f.

Axiom to_of_bits:
  forall b, to_bits (of_bits b) = b.

(** Conversions between floats and unsigned ints can be defined
  in terms of conversions between floats and signed ints.
  (Most processors provide only the latter, forcing the compiler
  to emulate the former.)   *)

Definition ox8000_0000 := Int.repr 31 (Int.half_modulus 31).  (**r [0x8000_0000] *)

Axiom of_intu_of_int_1:
  forall x,
  Int.ltu 31 x ox8000_0000 = true ->
  of_intu x = of_int x.

Axiom of_intu_of_int_2:
  forall x,
  Int.ltu 31 x ox8000_0000 = false ->
  of_intu x = add (of_int (Int.sub 31 x ox8000_0000)) (of_intu ox8000_0000).

Axiom to_intu_to_int_1:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = true ->
  to_intu x = Some n ->
  to_int x = Some n.

Axiom to_intu_to_int_2:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = false ->
  to_intu x = Some n ->
  to_int (sub x (of_intu ox8000_0000)) = Some (Int.sub 31 n ox8000_0000).

(** Conversions from ints to floats can be defined as bitwise manipulations
  over the in-memory representation.  This is what the PowerPC port does.
  The trick is that [from_words 0x4330_0000 x] is the float
  [2^52 + of_intu x]. *)

Definition ox4330_0000 := Int.repr 31 1127219200.        (**r [0x4330_0000] *)

Axiom of_intu_from_words:
  forall x,
  of_intu x = sub (from_words ox4330_0000 x) (from_words ox4330_0000 (Int.zero 31)).

Axiom of_int_from_words:
  forall x,
  of_int x = sub (from_words ox4330_0000 (Int.add 31 x ox8000_0000))
                 (from_words ox4330_0000 ox8000_0000).

Definition ox4530_0000 := Int.repr 31 1160773632.        (**r [0x4530_0000] *)

(** Conversions from unsigned longs can be expressed in terms of conversions from signed longs.
    If the unsigned long is too big, a round-to-odd must be performed on it
    to avoid double rounding. *)

Axiom of_longu_of_long_1:
  forall x,
  Int.ltu 63 x (Int.repr 63 (Int.half_modulus 63)) = true ->
  of_longu x = of_long x.

Axiom of_longu_of_long_2:
  forall x,
  Int.ltu 63 x (Int.repr 63 (Int.half_modulus 63)) = false ->
  of_longu x = mul (of_long (Int.or 63 (Int.shru 63 x (Int.one 63))
                                      (Int.and 63 x (Int.one 63))))
                   (of_int (Int.repr 31 2)).

End Float.

(** * Single-precision FP numbers *)

Module Float32.

(** ** Operations over single-precision floats *)

Parameter zero: float32.                   (**r the float [+0.0] *)

Axiom eq_dec: forall (f1 f2: float32), {f1 = f2} + {f1 <> f2}.

(** Arithmetic operations *)

Parameter neg: float32 -> float32.                   (**r opposite (change sign) *)
Parameter abs: float32 -> float32.                   (**r absolute value (set sign to [+]) *)
Parameter add: float32 -> float32 -> float32.        (**r addition *)
Parameter sub: float32 -> float32 -> float32.        (**r subtraction *)
Parameter mul: float32 -> float32 -> float32.        (**r multiplication *)
Parameter div: float32 -> float32 -> float32.        (**r division *)
Parameter rem: float32 -> float32 -> float32.
Parameter cmp: comparison -> float32 -> float32 -> bool. (**r comparison *)

(** Conversions *)

Parameter of_double : float -> float32.
Parameter to_double : float32 -> float.

Parameter to_int: float32 -> option int32.    (**r conversion to signed 32-bit int *)
Parameter to_intu: float32 -> option int32.   (**r conversion to unsigned 32-bit int *)
Parameter to_long: float32 -> option int64.   (**r conversion to signed 64-bit int *)
Parameter to_longu: float32 -> option int64.  (**r conversion to unsigned 64-bit int *)

Parameter of_int: int32 -> float32.        (**r conversion from signed 32-bit int to single-precision float *)
Parameter of_intu: int32 -> float32.       (**r conversion from unsigned 32-bit int to single-precision float *)

Parameter of_long: int64 -> float32.       (**r conversion from signed 64-bit int to single-precision float *)
Parameter of_longu: int64 -> float32.      (**r conversion from unsigned 64-bit int to single-precision float *)

(*
Definition from_parsed (base:positive) (intPart:positive) (expPart:Z) : float32 :=
  build_from_parsed 24 128 __ __ base intPart expPart.
*)
(** Conversions between floats and their concrete in-memory representation
    as a sequence of 32 bits. *)

Parameter to_bits: float32 -> int32.
Parameter of_bits: int32 -> float32.

(** ** Properties *)

(** Commutativity properties of addition and multiplication. *)

Axiom add_commut:
  forall x y, add x y = add y x.

Axiom mul_commut:
  forall x y, mul x y = mul y x.

(** Multiplication by 2 is diagonal addition. *)

Axiom mul2_add:
  forall f, add f f = mul f (of_int (Int.repr 31 2%Z)).

(** Properties of comparisons. *)

Axiom cmp_swap:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.

Axiom cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).

Axiom cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.

Axiom cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.

Axiom cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.

Axiom cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.

Axiom cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.

Axiom cmp_double:
  forall f1 f2 c, cmp c f1 f2 = Float.cmp c (to_double f1) (to_double f2).

(** Properties of conversions to/from in-memory representation.
  The conversions are bijective (one-to-one). *)

Axiom of_to_bits:
  forall f, of_bits (to_bits f) = f.

Axiom to_of_bits:
  forall b, to_bits (of_bits b) = b.

(** Conversions from 32-bit integers to single-precision floats can
  be decomposed into a conversion to a double-precision float,
  followed by a [Float32.of_double] conversion.  No double rounding occurs. *)

Axiom of_int_double:
  forall n, of_int n = of_double (Float.of_int n).

Axiom of_intu_double:
  forall n, of_intu n = of_double (Float.of_intu n).

(** Conversion of single-precision floats to integers can be decomposed
  into a [Float32.to_double] extension, followed by a double-precision-to-int
  conversion. *)

Axiom to_int_double:
  forall f n, to_int f = Some n -> Float.to_int (to_double f) = Some n.

Axiom to_intu_double:
  forall f n, to_intu f = Some n -> Float.to_intu (to_double f) = Some n.

Axiom to_long_double:
  forall f n, to_long f = Some n -> Float.to_long (to_double f) = Some n.

Axiom to_longu_double:
  forall f n, to_longu f = Some n -> Float.to_longu (to_double f) = Some n.

Axiom of_longu_double_1:
  forall n,
  Int.unsigned 63 n <= 2^53 ->
  of_longu n = of_double (Float.of_longu n).

Axiom of_longu_double_2:
  forall n,
  2^36 <= Int.unsigned 63 n ->
  of_longu n = of_double (Float.of_longu 
                           (Int.and 63 (Int.or 63 n 
                                                (Int.add 63 (Int.and 63 n (Int.repr 63 2047))
                                                           (Int.repr 63 2047)))
                                      (Int.repr 63 (-2048)))).

Axiom of_long_double_1:
  forall n,
  Z.abs (Int.signed 63 n) <= 2^53 ->
  of_long n = of_double (Float.of_long n).

Axiom of_long_double_2:
  forall n,
  2^36 <= Z.abs (Int.signed 63 n) ->
  of_long n = of_double (Float.of_long
                           (Int.and 63 (Int.or 63 n 
                                                (Int.add 63 (Int.and 63 n (Int.repr 63 2047))
                                                           (Int.repr 63 2047)))
                                      (Int.repr 63 (-2048)))).

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

