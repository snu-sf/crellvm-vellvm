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

(* Library of useful Caml <-> Coq conversions *)

open Datatypes
open BinPos
open BinInt
open BinNums

(* Integers *)

let rec camlint_of_positive = function
  | Coq_xI p -> Int32.add (Int32.shift_left (camlint_of_positive p) 1) 1l
  | Coq_xO p -> Int32.shift_left (camlint_of_positive p) 1
  | Coq_xH -> 1l

let camlint_of_z = function
  | Z0 -> 0l
  | Zpos p -> camlint_of_positive p
  | Zneg p -> Int32.neg (camlint_of_positive p)

let camlint_of_coqint : Integers.Int.int -> int32 = camlint_of_z

let rec camlint64_of_positive = function
  | Coq_xI p -> Int64.add (Int64.shift_left (camlint64_of_positive p) 1) 1L
  | Coq_xO p -> Int64.shift_left (camlint64_of_positive p) 1
  | Coq_xH -> 1L

let camlint64_of_z = function
  | Z0 -> 0L
  | Zpos p -> camlint64_of_positive p
  | Zneg p -> Int64.neg (camlint64_of_positive p)

let camlint64_of_coqint : Integers.Int.int -> int64 = camlint64_of_z

let rec camlint_of_nat = function
  | O -> 0
  | S n -> camlint_of_nat n + 1

let rec nat_of_camlint n =
  assert (n >= 0l);
  if n = 0l then O else S (nat_of_camlint (Int32.sub n 1l))

let rec positive_of_camlint n =
  if n = 0l then assert false else
  if n = 1l then Coq_xH else
  if Int32.logand n 1l = 0l
  then Coq_xO (positive_of_camlint (Int32.shift_right_logical n 1))
  else Coq_xI (positive_of_camlint (Int32.shift_right_logical n 1))

let z_of_camlint n =
  if n = 0l then Z0 else
  if n > 0l then Zpos (positive_of_camlint n)
  else Zneg (positive_of_camlint (Int32.neg n))

let coqint_of_camlint (n: int32) : Integers.Int.int =
  (* Interpret n as unsigned so that resulting Z is in range *)
  if n = 0l then Z0 else Zpos (positive_of_camlint n)

let rec positive_of_camlint64 n =
  if n = 0L then assert false else
  if n = 1L then Coq_xH else
  if Int64.logand n 1L = 0L
  then Coq_xO (positive_of_camlint64 (Int64.shift_right_logical n 1))
  else Coq_xI (positive_of_camlint64 (Int64.shift_right_logical n 1))

let z_of_camlint64 n =
  if n = 0L then Z0 else
  if n > 0L then Zpos (positive_of_camlint64 n)
  else Zneg (positive_of_camlint64 (Int64.neg n))

let coqint_of_camlint64 (n: int64) : Integers.Int.int =
  (* Interpret n as unsigned so that resulting Z is in range *)
  if n = 0L then Z0 else Zpos (positive_of_camlint64 n)

(* Atoms (positive integers representing strings) *)

let atom_of_string = (Hashtbl.create 17 : (string, positive) Hashtbl.t)
let string_of_atom = (Hashtbl.create 17 : (positive, string) Hashtbl.t)
let next_atom = ref Coq_xH

let intern_string s =
  try
    Hashtbl.find atom_of_string s
  with Not_found ->
    let a = !next_atom in
    next_atom := Pos.succ !next_atom;
    Hashtbl.add atom_of_string s a;
    Hashtbl.add string_of_atom a s;
    a

let extern_atom a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "<unknown atom %ld>" (camlint_of_positive a)

(* Strings *)

let char_of_ascii (Ascii.Ascii(a0, a1, a2, a3, a4, a5, a6, a7)) =
  Char.chr(  (if a0 then 1 else 0)
           + (if a1 then 2 else 0)
           + (if a2 then 4 else 0)
           + (if a3 then 8 else 0)
           + (if a4 then 16 else 0)
           + (if a5 then 32 else 0)
           + (if a6 then 64 else 0)
           + (if a7 then 128 else 0))

let coqstring_length s =
  let rec len accu = function
  | String0.EmptyString -> accu
  | String0.String(_, s) -> len (accu + 1) s
  in len 0 s

let camlstring_of_coqstring s =
  let r = Bytes.create (coqstring_length s) in
  let rec fill pos = function
  | String0.EmptyString -> r
  | String0.String(c, s) -> Bytes.set r pos (char_of_ascii c); fill (pos + 1) s
  in fill 0 s

(* Timing facility *)

(*
let timers = (Hashtbl.create 9 : (string, float) Hashtbl.t)

let add_to_timer name time =
  let old = try Hashtbl.find timers name with Not_found -> 0.0 in
  Hashtbl.replace timers name (old +. time)

let time name fn arg =
  let start = Unix.gettimeofday() in
  try
    let res = fn arg in
    add_to_timer name (Unix.gettimeofday() -. start);
    res
  with x ->
    add_to_timer name (Unix.gettimeofday() -. start);
    raise x

let print_timers () =
  Hashtbl.iter
    (fun name time -> Printf.printf "%-20s %.3f\n" name time)
    timers

let _ = at_exit print_timers
*)

(* Heap profiling facility *)

(*
let heap_info msg =
  Gc.full_major();
  let s = Gc.stat() in
  Printf.printf "%s: size %d live %d\n " msg s.Gc.heap_words s.Gc.live_words;
  flush stdout
*)

(* Generating a fresh atom. *)

let tmp_index =
  let idx = ref 0 in
  fun () -> idx := !idx + 1 ; !idx

let atom_fresh_for_list a =
  "%_tmp_" ^ string_of_int (tmp_index ())

(* let atom_fresh_for_list a =  *)
(*   let rec loop () = *)
(*     let s = "%_tmp_" ^ string_of_int (tmp_index ()) in *)
(*     if (List0.in_dec (fun a b -> a = b) s a) then  *)
(*       loop ()  *)
(*     else s  *)
(*   in loop () *)

(* These conversion functions are very efficient, because the machine represent-
   ation of nat is not practice. We should figure out if we can remove these
   functions later... *)
let llapint2nat i =
  nat_of_camlint (Int32.of_int (Int64.to_int (Llvm.APInt.get_sext_value i)))

let llapint2z i =
  z_of_camlint64 (Llvm.APInt.get_sext_value i)

let z2llapint bit_width v is_signed =
  let bit_width32 = camlint_of_z bit_width in
  let bit_widthi = Int32.to_int bit_width32 in
  let v64 = camlint64_of_z v in
  Llvm.APInt.of_int64 bit_widthi v64 is_signed

let pcubeplus (p: positive) : positive =
  let i = camlint_of_positive p in
  positive_of_camlint (Int32.add (Int32.mul i (Int32.mul i i)) i)

let string_compare (s1: String.t) (s2: String.t)
  : String.t OrderedType.coq_Compare =
  let c = String.compare s1 s2 in
  if c > 0 then OrderedType.GT
  else if c = 0 then OrderedType.EQ
  else OrderedType.LT

