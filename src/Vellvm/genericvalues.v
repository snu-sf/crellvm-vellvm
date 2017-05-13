Require Import List.
Require Import Arith.
Require Import monad.
Require Import Metatheory.
Require Import alist.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import targetdata.
Require Import ZArith.
Require Import Floats.
Require Import vellvm_tactics.
Require Import util.

(* The file defines generic values that represent values at runtime. *)
Module LLVMgv.

Import LLVMsyntax.
Import LLVMinfra.
Import LLVMtd.

(******************************************************************************)
(* We first define a generic value that is a list of memory values with memory 
   chunks. *)
Definition moffset := Int.int 31.
Definition mem := Mem.mem.
Definition GenericValue := list (val*memory_chunk).
Definition GVMap := list (id*GenericValue).

Definition mblock := Values.block.
Definition mptr := GenericValue.
Definition null : GenericValue := (Vint 31 (Int.repr 31 0), Mint 31):: nil.

(******************************************************************************)
(* Predicate of generic values. *)

(* One generic value is less defined than the other in terms of Val.lessdef. *)
Definition gv_lessdef (gv1 gv2:GenericValue) : Prop :=
List.Forall2 (fun vm1 vm2 =>
              let '(v1, cm1) := vm1 in
              let '(v2, cm2) := vm2 in
              Val.lessdef v1 v2 /\ cm1 = cm2) gv1 gv2.

Definition gv_lessdef_list (gvs1 gvs2:list GenericValue) : Prop :=
List.Forall2 gv_lessdef gvs1 gvs2.

(* Check if memory values in a gv match their corresponding chunks. *)
Definition gv_has_chunk (gv:GenericValue): Prop :=
List.Forall (fun vm => 
             let '(v, mc) := vm in
             Val.has_chunk v mc) gv.

(* A computable version of gv_has_chunk. *)
Fixpoint gv_has_chunkb (gv : GenericValue) : bool := 
match gv with
| nil => true
| (v,m)::gv' => Val.has_chunkb v m && gv_has_chunkb gv'
end.

(* Equivalence of gvs. *)
Fixpoint eq_gv (gv1 gv2:GenericValue) : bool :=
match gv1, gv2 with
| nil, nil => true
| (v1,c1)::gv1', (v2,c2)::gv2' => if Val.eq v1 v2
                                  then memory_chunk_eq c1 c2 &&
                                    eq_gv gv1' gv2'
                                  else false
| _, _ => false
end.

(* a list of undefined memory chunks with size n. *)
Definition uninitMCs (n:nat) : list memory_chunk :=
  Coqlib.list_repeat n (Mint 7).

(* a list of repeated memory chunks. *)
Fixpoint repeatMC (mcs:list memory_chunk) (n:nat) : list memory_chunk :=
match n with
| O => nil
| S n' => mcs ++ repeatMC mcs n'
end.

(* Return the size of a list of memory chunks. *)
Fixpoint sizeMC (mc:list memory_chunk) : nat :=
match mc with
| nil => 0%nat
| c::mc' => (size_chunk_nat c + sizeMC mc')%nat
end.

(* Compute the list of memory chunks that represents a type. *)
Definition flatten_typs_aux_
  (flatten_typ_aux :
    TargetData -> list (id * option (list memory_chunk)) ->
    typ -> option (list memory_chunk)) :=
fix flatten_typs_aux (TD:TargetData) acc (lt:list typ)
  : option (list memory_chunk) :=
match lt with
| nil => Some nil
| t :: lt' =>
  match (flatten_typs_aux TD acc lt', flatten_typ_aux TD acc t) with
  | (Some mc, Some mc0) =>
       match getTypeAllocSize TD t with
       | Some asz => Some (mc0++uninitMCs (asz - sizeMC mc0)++mc)
       | _ => None
       end
  | _ => None
  end
end.

Fixpoint flatten_typ_aux (TD:TargetData)
  (acc:list (id*option (list memory_chunk))) (t:typ)
  : option (list memory_chunk) :=
match t with
| typ_int sz => Some (Mint (Size.to_nat sz - 1) :: nil)
| typ_floatpoint fp =>
  match fp with
  | fp_float => Some (Mfloat32 :: nil)
  | fp_double => Some (Mfloat64 :: nil)
  | _ => None (* FIXME: not supported 80 and 128 yet. *)
  end
| typ_void => None
| typ_label => None
| typ_metadata => None
| typ_array sz t =>
  match sz with
  | O => Some (uninitMCs 1)
  | _ =>
    match flatten_typ_aux TD acc t with
    | Some mc0 =>
      match getTypeAllocSize TD t with
      | Some asz =>
         Some (repeatMC (mc0++uninitMCs (Size.to_nat asz - sizeMC mc0))
                 (Size.to_nat sz))
      | _ => None
      end
    | _ => None
    end
  end
| typ_struct ts =>
  match flatten_typs_aux_ flatten_typ_aux TD acc ts with
  | Some nil => Some (uninitMCs 1)
  | Some gv0 => Some gv0
  | None => None
  end
| typ_pointer t' => Some (Mint 31::nil)
| typ_function _ _ _ => None
| typ_namedt nid => 
  match lookupAL _ acc nid with
  | Some re => re
  | _ => None
  end
end.

Definition flatten_typs_aux :=
  flatten_typs_aux_ flatten_typ_aux.

Fixpoint flatten_typ_for_namedts TD (los:layouts) (nts:namedts) 
  : list (id*option (list memory_chunk)) :=
match nts with
| nil => nil 
| (id0, ts0)::nts' =>
  let results := flatten_typ_for_namedts TD los nts' in
  (id0, flatten_typ_aux TD results (typ_struct ts0))::results
end.

Definition flatten_typ (TD:TargetData) (t:typ) : option (list memory_chunk) :=
let '(los, nts) := TD in
flatten_typ_aux TD (flatten_typ_for_namedts TD los nts) t.

Definition flatten_typs (TD:TargetData) (lt:list typ)
  : option (list memory_chunk) :=
let '(los, nts) := TD in
flatten_typs_aux TD (flatten_typ_for_namedts TD los nts) lt.

(* Check if gv has type t. *)
Definition gv_has_type (TD:LLVMtd.TargetData) (gv:GenericValue) 
  (t:typ) : Prop :=
match flatten_typ TD t with
| None => False
| Some ts =>
    List.Forall2 (fun v mc => Val.has_type v (AST.type_of_chunk mc)) 
                 (fst (List.split gv)) ts
end.

(* Check if gv contains undefined memory values. *)
Fixpoint isGVUndef (gv:GenericValue) : Prop :=
match gv with
| nil => False
| (Vundef,_)::gv' => True
| _::gv' => isGVUndef gv'
end.

(* Check if a generic value matches its memory chunks. *)
Definition vm_matches_typ :=
  fun (vm:val*memory_chunk) (mc:memory_chunk) => 
    snd vm = mc /\ Val.has_chunk (fst vm) (snd vm).

Definition gv_chunks_match_typ (TD:TargetData) (gv:GenericValue) (t:typ) 
  : Prop :=
match flatten_typ TD t with
| None => False
| Some ts => List.Forall2 vm_matches_typ gv ts
end.

Definition gv_chunks_match_list_typ (TD:TargetData) (gv:GenericValue)
  (ts:list typ) : Prop :=
match flatten_typs TD ts with
| None => False
| Some mcs => List.Forall2 vm_matches_typ gv mcs
end.

(******************************************************************************)
(* Operations of generic values. *)

(* a list of undefined memory values with size n. *)
Definition uninits (n:nat) : GenericValue :=
   Coqlib.list_repeat n (Vundef, Mint 7).

(* Generate an undefined generic values in terms of memory chunks. *)
Definition mc2undefs (mc:list memory_chunk) : GenericValue :=
List.fold_right 
  (fun c acc => (Vundef, c) :: acc) nil mc.

(* Generate an undefined generic values in terms of type. *)
Definition gundef (TD:TargetData) (t:typ) : option GenericValue :=
match (flatten_typ TD t) with
| Some mc => Some (mc2undefs mc)
| None => None
end.

(* Convert between generic values and basic memory values. *)
Definition GV2val (TD:TargetData) (gv:GenericValue) : option val :=
match gv with
| (v,c)::nil => Some v
| _ => Some Vundef
end.

Definition GV2int (TD:TargetData) (bsz:sz) (gv:GenericValue) : option Z :=
match gv with
| (Vint wz i,c)::nil =>
  if eq_nat_dec (wz+1) (Size.to_nat bsz)
  then Some (Int.signed wz i)
  else None
| _ => None
end.

Definition GV2ptr (TD:TargetData) (bsz:sz) (gv:GenericValue) : option val :=
match gv with
| (Vptr a b,c)::nil => Some (Vptr a b)
| _ => None
end.
Definition val2GV (TD:TargetData) (v:val) (c:memory_chunk) : GenericValue :=
(v,c)::nil.
Definition ptr2GV (TD:TargetData) (ptr:val) : GenericValue :=
val2GV TD ptr (Mint (Size.mul Size.Eight (getPointerSize TD)-1)).
Definition blk2GV (TD:TargetData) (b:mblock) : GenericValue :=
ptr2GV TD (Vptr b (Int.repr 31 0)).
Definition isGVZero (TD:TargetData) (gv:GenericValue) : bool :=
match (GV2int TD Size.One gv) with
| Some z => if Coqlib.zeq z 0 then true else false
| _ => false
end.

(* Internal operations of generic values that Vellvm provides *)
Definition mgep (TD:TargetData) (t:typ) (ma:val) (idxs:list Z) : option val :=
match ma with
| Vptr b ofs =>
  match idxs with
  | nil => None
  | _ =>
    match (mgetoffset TD (typ_array 0%nat t) idxs) with
    | Some (offset, _) => Some (Vptr b (Int.add 31 ofs (Int.repr 31 offset)))
    | _ => None
    end
  end
| _ => None
end.

Fixpoint sizeGenericValue (gv:GenericValue) : nat :=
match gv with
| nil => 0%nat
| (v,c)::gv' => (size_chunk_nat c + sizeGenericValue gv')%nat
end.

Fixpoint splitGenericValue (gv:GenericValue) (pos:Z):
  option (GenericValue*GenericValue) :=
if (Coqlib.zeq pos 0) then Some (nil, gv)
else
  if (Coqlib.zlt pos 0) then None
  else
    match gv with
    | nil => None
    | (v,c)::gv' =>
        match splitGenericValue gv' (pos - size_chunk c) with
        | Some (gvl', gvr') => Some ((v,c)::gvl', gvr')
        | None => None
        end
    end.

Fixpoint gv_chunks_match_typb_aux (gv:GenericValue) (mcs:list memory_chunk)
  : bool :=
match gv, mcs with
| nil, nil => true
| (v1, mc1)::gv', mc2::mcs' => 
    AST.memory_chunk_eq mc1 mc2 && Val.has_chunkb v1 mc1 &&
      gv_chunks_match_typb_aux gv' mcs'
| _, _ => false
end.

Definition gv_chunks_match_typb (TD:TargetData) (gv:GenericValue) (t:typ) 
  : bool :=
match flatten_typ TD t with
| None => false
| Some mcs => gv_chunks_match_typb_aux gv mcs
end.

Definition mget (TD:TargetData) (gv:GenericValue) (o:Z) (t:typ)
  : option GenericValue :=
do s <- getTypeStoreSize TD t;
  match (splitGenericValue gv o) with
  | Some (gvl, gvr) =>
      match (splitGenericValue gvr (Z_of_nat s)) with
      | Some (gvrl, gvrr) => 
          if gv_chunks_match_typb TD gvrl t then Some gvrl else None
      | None => None
      end
  | None => None
  end.

Definition mset (TD:TargetData) (gv:GenericValue) (o:Z) (t0:typ)
  (gv0:GenericValue) : option GenericValue :=
let n := Coqlib.nat_of_Z o in
do s <- getTypeStoreSize TD t0;
  if (beq_nat s (length gv0)) then
    match (splitGenericValue gv o) with
    | Some (gvl, gvr) =>
       match (splitGenericValue gvr (Z_of_nat s)) with
       | Some (gvrl, gvrr) => 
          if gv_chunks_match_typb TD gvrl t0 
          then Some (gvl++gv0++gvrr) else None
       | None => None
       end
    | None => None
    end
  else None.

Fixpoint GVs2Nats (TD:TargetData) (lgv:list GenericValue) : option (list Z):=
match lgv with
| nil => Some nil
| gv::lgv' =>
    match (GV2int TD Size.ThirtyTwo gv) with
    | Some z =>
        match (GVs2Nats TD lgv') with
        | Some ns => Some (z::ns)
        | None => None
        end
    | _ => None
    end
end.

(* FIXME : bounds check *)
Definition extractGenericValue (TD:TargetData) (t:typ) (gv : GenericValue)
  (cidxs : list const) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, t') => match mget TD gv o t' with
                    | Some gv' => Some gv'
                    | None => gundef TD t'
                    end
  | None => None
  end
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gv:GenericValue)
  (cidxs:list const) (t0:typ) (gv0:GenericValue) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, _) => match (mset TD gv o t0 gv0) with
                   | Some gv' => Some gv'
                   | None => gundef TD t
                   end
  | None => None
  end
end.

Definition mtrunc (TD:TargetData) (op:truncop) (t1:typ) (t2:typ)
  (gv1:GenericValue) : option GenericValue :=
match GV2val TD gv1 with
| Some (Vint wz1 i1) =>
    match (t1, t2) with
    | (typ_int sz1, typ_int sz2) =>
        Some (val2GV TD (Val.trunc (Vint wz1 i1) (sz2-1)) (Mint (sz2-1)))
    | _ => gundef TD t2
    end
| Some (Vfloat f) =>
    match (t1, t2) with
    | (typ_floatpoint fp1, typ_floatpoint fp2) =>
        if floating_point_order fp2 fp1
        then
          match fp1 with
          | fp_double => 
               Some (val2GV TD (Vsingle (Float.to_single f)) Mfloat32)
          | _ => None (* FIXME: not supported 80 and 128 yet. *)
          end
        else None
    | _ => gundef TD t2
    end
| Some (Vsingle f) =>
    match (t1, t2) with
    | (typ_floatpoint _, typ_floatpoint _) => gundef TD t2
    | _ => gundef TD t2
    end
| _ => gundef TD t2
end.

Definition mbop (TD:TargetData) (op:bop) (bsz:sz) (gv1 gv2:GenericValue)
  : option GenericValue :=
let bsz' := (Size.to_nat bsz) in
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vint wz1 i1), Some (Vint wz2 i2)) =>
  if eq_nat_dec (wz1+1) bsz'
  then
     match op with
     | bop_add =>
         Some (val2GV TD (Val.add (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_sub =>
         Some (val2GV TD (Val.sub (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_mul =>
         Some (val2GV TD (Val.mul (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_udiv =>
         match Val.divu (Vint wz1 i1) (Vint wz2 i2) with
         | Some vresult => Some (val2GV TD vresult (Mint (bsz'-1)))
         | None => gundef TD (typ_int bsz')
         end
     | bop_sdiv =>
         match Val.divs (Vint wz1 i1) (Vint wz2 i2) with
         | Some vresult => Some (val2GV TD vresult (Mint (bsz'-1)))
         | None => gundef TD (typ_int bsz')
         end
     | bop_urem =>
         match Val.modu (Vint wz1 i1) (Vint wz2 i2) with
         | Some vresult => Some (val2GV TD vresult (Mint (bsz'-1)))
         | None => gundef TD (typ_int bsz')
         end
     | bop_srem =>
         match Val.mods (Vint wz1 i1) (Vint wz2 i2) with
         | Some vresult => Some (val2GV TD vresult (Mint (bsz'-1)))
         | None => gundef TD (typ_int bsz')
         end
     | bop_shl =>
         Some (val2GV TD (Val.shl (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_lshr =>
         match Val.shrx (Vint wz1 i1) (Vint wz2 i2) with
         | Some vresult => Some (val2GV TD vresult (Mint (bsz'-1)))
         | None => gundef TD (typ_int bsz')
         end
     | bop_ashr =>
         Some (val2GV TD (Val.shr (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_and =>
         Some (val2GV TD (Val.and (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_or =>
         Some (val2GV TD (Val.or (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_xor =>
         Some (val2GV TD (Val.xor (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     end
  else gundef TD (typ_int bsz')
| _ => gundef TD (typ_int bsz')
end.

Definition mfbop (TD:TargetData) (op:fbop) (fp:floating_point)
  (gv1 gv2:GenericValue) : option GenericValue :=
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vfloat f1), Some (Vfloat f2)) =>
  let v :=
     match op with
     | fbop_fadd => Val.addf (Vfloat f1) (Vfloat f2)
     | fbop_fsub => Val.subf (Vfloat f1) (Vfloat f2)
     | fbop_fmul => Val.mulf (Vfloat f1) (Vfloat f2)
     | fbop_fdiv => Val.divf (Vfloat f1) (Vfloat f2)
     | fbop_frem => Val.modf (Vfloat f1) (Vfloat f2)
     end in
  match fp with
  | fp_double => Some (val2GV TD v Mfloat64)
  | fp_float => gundef TD (typ_floatpoint fp)
  | _ => None
  end
| (Some (Vsingle f1), Some (Vsingle f2)) =>
  let v :=
     match op with
     | fbop_fadd => Val.addfs (Vsingle f1) (Vsingle f2)
     | fbop_fsub => Val.subfs (Vsingle f1) (Vsingle f2)
     | fbop_fmul => Val.mulfs (Vsingle f1) (Vsingle f2)
     | fbop_fdiv => Val.divfs (Vsingle f1) (Vsingle f2)
     | fbop_frem => Val.modfs (Vsingle f1) (Vsingle f2)
     end in
  match fp with
  | fp_float => Some (val2GV TD v Mfloat32)
  | fp_double => gundef TD (typ_floatpoint fp)
  | _ => None
  end
| _ => gundef TD (typ_floatpoint fp)
end.

(*
Definition mptrtoint (TD:TargetData) (M:mem) (gv1:GenericValue) (sz2:nat)
 : option GenericValue :=
    match GV2val TD gv1 with
    | Some (Vptr b1 ofs1) =>
        match Mem.ptr2int M b1 0 with
        | Some z =>
            Some (val2GV TD
                   (Vint sz2 (Int.repr sz2 (z + Int.signed 31 ofs1)))
                   (Mint (sz2-1)))
        | None => Some (val2GV TD (Vint sz2 (Int.zero sz2)) (Mint (sz2-1)))
        end
    | Some (Vinttoptr i) =>
        Some (val2GV TD (Vint sz2 (Int.repr sz2 (Int.unsigned 31 i)))
               (Mint (sz2-1)))
    | _ => gundef TD (typ_int sz2)
    end.
*)

Definition mbitcast (t1:typ) (gv1:GenericValue)(t2:typ) : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) => Some gv1
| (typ_pointer _, typ_pointer _) => Some gv1
| _ => None
end.

(*
Definition minttoptr (TD:TargetData) (M:mem) (gv1:GenericValue)
  : option GenericValue :=
  match GV2val TD gv1 with
  | Some (Vint wz1 i1) =>
      match Mem.int2ptr M (Int.signed wz1 i1) with
      | Some (b,ofs) => Some (ptr2GV TD (Vptr b (Int.repr 31 ofs)))
      | None =>
          Some (ptr2GV TD (Vinttoptr (Int.repr 31 (Int.unsigned wz1 i1))))
      end
  | _ => gundef TD (typ_pointer typ_void)
  end.
*)

(* Here is another idea to support inttoptr and ptrtoint. We should
   distinguish two kinds of ptr: at global spaces, and at heap or stack. The
   first kind of ptr has an known address at compile time, and at runtime
   their addresses cannot be reused; the second kind of ptr has no such
   properties.

   So, we can support i2p and p2i for the first ptr w/o parameterizing Mem
   everywhere (at const2GV and getOperandValue), because we can maintain a
   fixed mapping that is created at program initialization.

   For p2i, it is total. i2p can be undef if the int value is not in the map.

   This makes values in registers hold the substitution properities. If const2GV
   is with Mem, that means its result can be affected by memory state, so we can-
   not substitute it arbitrarily.

   Having Mem  everywhere, and not distinguishing the two kinds of
   ptr, complicates proofs, because we need to argue that
   1) memory model does not reuse addresses for globals, this is true for our
      corrent memory model, because it has inifite memory, and never reuses,
      but needs more work if we support finite memory later.

   2) It is hard to define simulation relations between the pointers or
      intergers casted from two programs, because related pointers can be in
      different memory addresses.

   This also indicates that the 2nd kind of ptr should eval to undef by i2p or
   p2i, because what their values are depends on runtime and platform.

   For the time being, we simply consider both of the kinds of ptrs fomr i2p
   to be undef, and integers from p2i to be undef, too.

*)
Definition mcast (TD:TargetData) (op:castop) (t1:typ) (t2:typ) (gv1:GenericValue)
 : option GenericValue :=
match op with
| castop_inttoptr => gundef TD t2
| castop_ptrtoint => gundef TD t2
| castop_bitcase => mbitcast t1 gv1 t2
end.

Definition mext (TD:TargetData) (op:extop) (t1:typ) (t2:typ) (gv1:GenericValue)
  : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) =>
   match (GV2val TD gv1) with
   | Some (Vint wz1 i1) =>
     match op with
     | extop_z => Some (val2GV TD (Val.zero_ext' (sz2-1) (Vint wz1 i1))
                        (Mint (sz2-1)))
     | extop_s => Some (val2GV TD (Val.sign_ext' (sz2-1) (Vint wz1 i1))
                        (Mint (sz2-1)))
     | _ => None
     end
   | _ => gundef TD t2
   end
| (typ_floatpoint fp1, typ_floatpoint fp2) =>
  if floating_point_order fp1 fp2
  then
    match (GV2val TD gv1) with
    | Some (Vfloat f1) =>
      match op with
      | extop_fp =>
         match fp2 with
         | fp_double => Some (val2GV TD (Vfloat f1) Mfloat64)
         | _ => None (* FIXME: not supported 80 and 128 yet. *)
         end
      | _ => None
      end
    | _ => gundef TD t2
    end
  else None
| (_, _) => None
end.

Definition micmp_int TD c gv1 gv2 : option GenericValue :=
  match (GV2val TD gv1, GV2val TD gv2) with
  | (Some (Vint wz1 i1), Some (Vint wz2 i2)) =>
     match c with
     | cond_eq =>
         Some (val2GV TD (Val.cmp Ceq (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ne =>
         Some (val2GV TD (Val.cmp Cne (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ugt =>
         Some (val2GV TD (Val.cmpu_int Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_uge =>
         Some (val2GV TD (Val.cmpu_int Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ult =>
         Some (val2GV TD (Val.cmpu_int Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ule =>
         Some (val2GV TD (Val.cmpu_int Cle (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sgt =>
         Some (val2GV TD (Val.cmp Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sge =>
         Some (val2GV TD (Val.cmp Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_slt =>
         Some (val2GV TD (Val.cmp Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sle =>
         Some (val2GV TD (Val.cmp Cle (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     end
  | _ => gundef TD (typ_int 1%nat)
  end.

Definition micmp (TD:TargetData) (c:cond) (t:typ) (gv1 gv2:GenericValue)
  : option GenericValue :=
match t with
| typ_int sz => micmp_int TD c gv1 gv2
| typ_pointer _ => gundef TD (typ_int 1%nat)
| _ => None
end.

(* TODO: issue. Single vs Float. *)
Definition mfcmp (TD:TargetData) (c:fcond) (fp:floating_point)
  (gv1 gv2:GenericValue) : option GenericValue :=
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vfloat f1), Some (Vfloat f2)) =>
   let ov :=
     match c with
     | fcond_false => Some (val2GV TD Vfalse (Mint 0))
     | fcond_oeq =>
         Some (val2GV TD (Val.cmpf Ceq (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ogt =>
         Some (val2GV TD (Val.cmpf Cgt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_oge =>
         Some (val2GV TD (Val.cmpf Cge (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_olt =>
         Some (val2GV TD (Val.cmpf Clt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ole =>
         Some (val2GV TD (Val.cmpf Cle (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_one =>
         Some (val2GV TD (Val.cmpf Cne (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ord => None (*FIXME: not supported yet. *)
     | fcond_ueq =>
         Some (val2GV TD (Val.cmpf Ceq (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ugt =>
         Some (val2GV TD (Val.cmpf Cgt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_uge =>
         Some (val2GV TD (Val.cmpf Cge (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ult =>
         Some (val2GV TD (Val.cmpf Clt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ule =>
         Some (val2GV TD (Val.cmpf Cle (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_une =>
         Some (val2GV TD (Val.cmpf Cne (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_uno => None (*FIXME: not supported yet. *)
     | fcond_true => Some (val2GV TD Vtrue (Mint 0))
     end in
   match fp with
   | fp_float => ov
   | fp_double => ov
   | _ => None (*FIXME: not supported 80 and 128 yet. *)
   end
| _ => gundef TD (typ_int 1%nat)
end.

(* Convert constants to generic values *)
Fixpoint repeatGV (gv:GenericValue) (n:nat) : GenericValue :=
match n with
| O => nil
| S n' => gv++repeatGV gv n'
end.

Definition zeroconsts2GV_aux_
  (zeroconst2GV_aux :
    TargetData -> list (id * option GenericValue) ->
    typ -> option GenericValue) :=
fix zeroconsts2GV_aux (TD:TargetData) acc (lt:list typ) : option GenericValue :=
match lt with
| nil => Some nil
| t :: lt' =>
  match (zeroconsts2GV_aux TD acc lt', zeroconst2GV_aux TD acc t) with
  | (Some gv, Some gv0) =>
       match getTypeAllocSize TD t with
       | Some asz => Some (gv0++uninits (asz - sizeGenericValue gv0)++gv)
       | _ => None
       end
  | _ => None
  end
end.

Fixpoint zeroconst2GV_aux (TD:TargetData) (acc:list (id*option GenericValue))
  (t:typ) : option GenericValue :=
match t with
| typ_int sz =>
  let wz := ((Size.to_nat sz) - 1)%nat in
  Some (val2GV TD (Vint wz (Int.repr wz 0)) (Mint wz))
| typ_floatpoint fp =>
  match fp with
  | fp_float => Some (val2GV TD (Vsingle Float32.zero) Mfloat32)
  | fp_double => Some (val2GV TD (Vfloat Float.zero) Mfloat64)
  | _ => None (* FIXME: not supported 80 and 128 yet. *)
  end
| typ_void => None
| typ_label => None
| typ_metadata => None
| typ_array sz t =>
  match sz with
  | O => Some (uninits 1)
  | _ =>
    match zeroconst2GV_aux TD acc t with
    | Some gv0 =>
      match getTypeAllocSize TD t with
      | Some asz =>
         Some (repeatGV (gv0++uninits (Size.to_nat asz - sizeGenericValue gv0))
                 (Size.to_nat sz))
      | _ => None
      end
    | _ => None
    end
  end
| typ_struct ts =>
  match zeroconsts2GV_aux_ zeroconst2GV_aux TD acc ts with
  | Some nil => Some (uninits 1)
  | Some gv0 => Some gv0
  | None => None
  end
| typ_pointer t' => Some null
| typ_function _ _ _ => None
| typ_namedt nid => 
  match lookupAL _ acc nid with
  | Some re => re
  | _ => None
  end
end.

Definition zeroconsts2GV_aux :=
  zeroconsts2GV_aux_ zeroconst2GV_aux.

Fixpoint zeroconst2GV_for_namedts TD (los:layouts) (nts:namedts) 
  : list (id*option GenericValue) :=
match nts with
| nil => nil 
| (id0, ts0)::nts' =>
  let results := zeroconst2GV_for_namedts TD los nts' in
  (id0, zeroconst2GV_aux TD results (typ_struct ts0))::results
end.

Definition zeroconst2GV (TD:TargetData) (t:typ) : option GenericValue :=
let '(los, nts) := TD in
zeroconst2GV_aux TD (zeroconst2GV_for_namedts TD los nts) t.

Definition zeroconsts2GV (TD:TargetData) (lt:list typ)
  : option GenericValue :=
let '(los, nts) := TD in
zeroconsts2GV_aux TD (zeroconst2GV_for_namedts TD los nts) lt.

Definition _list_const_arr2GV_
  (_const2GV : TargetData -> GVMap ->
    const -> option (GenericValue * typ)) :=
fix _list_const_arr2GV (TD:TargetData) (gl:GVMap) (t:typ) (cs:list const)
  : option GenericValue :=
match cs with
| nil => Some nil
| c :: lc' =>
  match (_list_const_arr2GV TD gl t lc', _const2GV TD gl c) with
  | (Some gv, Some (gv0, t0)) =>
      if typ_dec t t0 then
             match getTypeAllocSize TD t0 with
             | Some asz0 =>
                 Some (gv0++uninits (asz0 - sizeGenericValue gv0) ++ gv)
             | _ => None
             end
      else None
  | _ => None
  end
end.

Definition _list_const_struct2GV_
  (_const2GV : TargetData -> GVMap ->
    const -> option (GenericValue * typ)) :=
fix _list_const_struct2GV (TD:TargetData) (gl:GVMap) (cs:list const)
  : option (GenericValue * list typ) :=
match cs with
| nil => Some (nil, nil)
| c :: lc' =>
  match (_list_const_struct2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, ts), Some (gv0,t0)) =>
       match getTypeAllocSize TD t0 with
       | Some asz =>
            Some (gv0++uninits (asz - sizeGenericValue gv0)++gv,
                  t0 :: ts)
       | _ => None
       end
  | _ => None
  end
end.

Fixpoint _const2GV (TD:TargetData) (gl:GVMap) (c:const)
  : option (GenericValue*typ) :=
match c with
| const_zeroinitializer t =>
  match zeroconst2GV TD t with
  | Some gv => Some (gv, t)
  | None => None
  end
| const_int sz n =>
         let wz := (Size.to_nat sz - 1)%nat in
         Some (val2GV TD (Vint wz (Int.repr wz (INTEGER.to_Z n))) (Mint wz),
               typ_int sz)
| const_floatpoint fp f =>
         match fp with
         | fp_float => Some (val2GV TD (Vsingle (Float.to_single f)) Mfloat32, 
                             typ_floatpoint fp)
         | fp_double => Some (val2GV TD (Vfloat f) Mfloat64, typ_floatpoint fp)
         | _ => None (* FIXME: not supported 80 and 128 yet. *)
         end
| const_undef t =>
         match (gundef TD t) with
         | Some gv => Some (gv, t)
         | None => None
         end
| const_null t =>
         Some (null, typ_pointer t)
| const_arr t lc =>
         match _list_const_arr2GV_ _const2GV TD gl t lc with
         | Some gv =>
             match length lc with
             | O => Some (uninits 1,
                            typ_array (length lc) t)
             | _ => Some (gv,
                            typ_array (length lc) t)
             end
         | _ => None
         end
| const_struct t lc =>
         match (_list_const_struct2GV_ _const2GV TD gl lc) with
         | None => None
         | Some (gv0, ts) =>
             let '(_, nts) := TD in
             if typ_eq_list_typ nts t ts then
               match gv0 with
               | nil => Some (uninits 1, t)
               | gv => Some (gv, t)
               end
             else None
         end
| const_gid t id =>
         match (lookupAL _ gl id) with
         | Some gv => Some (gv, typ_pointer t)
         | None => None
         end
| const_truncop op c1 t2 =>
         match _const2GV TD gl c1 with
         | Some (gv1, t1) =>
           match mtrunc TD op t1 t2 gv1 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
| const_extop op c1 t2 =>
         match _const2GV TD gl c1 with
         | Some (gv1, t1) =>
           match mext TD op t1 t2 gv1 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
| const_castop op c1 t2 =>
         match _const2GV TD gl c1 with
         | Some (gv1, t1) =>
           match mcast TD op t1 t2 gv1 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
| const_gep ib c1 cs2 =>
       match _const2GV TD gl c1 with
       | Some (gv1, typ_pointer t1) =>
         match getConstGEPTyp cs2 (typ_pointer t1) with
         | Some t2 =>
           match GV2ptr TD (getPointerSize TD) gv1 with
           | Some ptr =>
             match intConsts2Nats TD cs2 with
             | None => match gundef TD t2 with
                       | Some gv => Some (gv, t2)
                       | None => None
                       end
             | Some idxs =>
               match (mgep TD t1 ptr idxs) with
               | Some ptr0 => Some (ptr2GV TD ptr0, t2)
               | None => match gundef TD t2 with
                         | Some gv => Some (gv, t2)
                         | None => None
                         end
               end
             end
           | None => match gundef TD t2 with
                     | Some gv => Some (gv, t2)
                     | None => None
                     end
           end
         | _ => None
         end
       | _ => None
       end
| const_select c0 c1 c2 =>
  match _const2GV TD gl c0, _const2GV TD gl c1, _const2GV TD gl c2 with
  | Some (gv0, t0), Some gvt1, Some gvt2 => if isGVZero TD gv0
                                            then Some gvt2
                                            else Some gvt1
  | _, _, _ => None
  end
| const_icmp cond c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, t1), Some (gv2, _) =>
             match micmp TD cond t1 gv1 gv2 with
             | Some gv2 => Some (gv2, typ_int Size.One)
             | _ => None
             end
         | _, _ => None
         end
| const_fcmp cond c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, typ_floatpoint fp1), Some (gv2, _) =>
           match mfcmp TD cond fp1 gv1 gv2 with
           | Some gv2 => Some (gv2, typ_int Size.One)
           | _ => None
           end
         | _, _ => None
         end
| const_extractvalue c1 cs2 =>
       match _const2GV TD gl c1 with
       | Some (gv1, t1) =>
         match getSubTypFromConstIdxs cs2 t1 with
         | Some t2 =>
           match extractGenericValue TD t1 gv1 cs2 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
       | _ => None
       end
| const_insertvalue c1 c2 cs3 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, t1), Some (gv2, t2) =>
           match insertGenericValue TD t1 gv1 cs3 t2 gv2 with
           | Some gv3 => Some (gv3, t1)
           | _ => None
           end
         | _, _ => None
         end
| const_bop op c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, typ_int sz1), Some (gv2, _) =>
           match mbop TD op sz1 gv1 gv2 with
           | Some gv3 => Some (gv3, typ_int sz1)
           | _ => None
           end
         | _, _ => None
         end
| const_fbop op c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, typ_floatpoint fp1), Some (gv2, _) =>
           match mfbop TD op fp1 gv1 gv2 with
           | Some gv3 => Some (gv3, typ_floatpoint fp1)
           | _ => None
           end
         | _, _ => None
         end
end.

Definition _list_const_struct2GV :=
  _list_const_struct2GV_ _const2GV.

Definition _list_const_arr2GV :=
  _list_const_arr2GV_ _const2GV.

Definition cundef_gv gv t : GenericValue :=
match t with
| typ_int sz => (Vint (sz-1) (Int.zero (sz-1)), Mint (sz -1))::nil
| typ_floatpoint fp_float => (Vsingle Float32.zero, Mfloat32)::nil
| typ_floatpoint fp_double => (Vfloat Float.zero, Mfloat64)::nil
| typ_pointer _ => null
| _ => gv
end.

Definition cgv2gv (gv:GenericValue) (t:typ) : GenericValue := gv.

Notation "? gv # t ?" := (cgv2gv gv t) (at level 41).

Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GenericValue :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, t) => Some (? gv # t ?)
end.

(* Compute the generic value of a program value. *)
Definition getOperandValue (TD:TargetData) (v:value) (locals:GVMap)
  (globals:GVMap) : option GenericValue :=
match v with
| value_id id => lookupAL _ locals id
| value_const c => const2GV TD globals c
end.

Definition getOperandInt (TD:TargetData) (bsz:sz) (v:value) (locals:GVMap)
  (globals:GVMap) : option Z :=
match (getOperandValue TD v locals globals) with
| Some gi => GV2int TD bsz gi
| None => None
end.

Definition getOperandPtr (TD:TargetData) (v:value) (locals:GVMap)
  (globals:GVMap) : option val :=
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD (getPointerSize TD) gi
| None => None
end.

Definition getOperandPtrInBits (TD:TargetData) (s:sz) (v:value) (locals:GVMap)
  (globals:GVMap) : option val :=
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD s gi
| None => None
end.

(* Check if the runtime of a program value is undefined. *)
Definition isOperandUndef (TD:TargetData) (t:typ) (v:value) (locals:GVMap)
  (globals:GVMap) : Prop  :=
match (getOperandValue TD v locals globals) with
| Some gi => isGVUndef gi
| None => False
end.

(* convert parameters and values to generic values *)
Fixpoint params2GVs (TD:TargetData) (lp:params) (locals:GVMap)
  (globals:GVMap) : option (list GenericValue) :=
match lp with
| nil => Some nil
| (_, v)::lp' =>
    match (getOperandValue TD v locals globals,
          params2GVs TD lp' locals globals) with
    | (Some gv, Some gvs) => Some (gv::gvs)
    | _ => None
    end
end.

Fixpoint values2GVs (TD:TargetData) (lv:list (sz * value)) (locals:GVMap)
  (globals:GVMap) : option (list GenericValue):=
match lv with
| nil => Some nil
| (_, v) :: lv' =>
  match (getOperandValue TD v locals globals) with
  | Some GV =>
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint intValues2Nats (TD:TargetData) (lv:list (sz * value)) (locals:GVMap)
  (globals:GVMap) : option (list Z):=
match lv with
| nil => Some nil
| (_, v) :: lv' =>
  match (getOperandValue TD v locals globals) with
  | Some GV =>
    match (GV2int TD Size.ThirtyTwo GV) with
    | Some z =>
        match (intValues2Nats TD lv' locals globals) with
        | Some ns => Some (z::ns)
        | None => None
        end
    | _ => None
    end
  | None => None
  end
end.

(* Initialize locals of funtions *)
Definition fit_gv TD (t:typ) (gv:GenericValue) : option GenericValue :=
match (getTypeSizeInBits TD t) with
| Some sz =>
    if beq_nat (sizeGenericValue gv)
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) &&
       gv_chunks_match_typb TD gv t
    then Some gv
    else gundef TD t
| None => None
end.

Fixpoint _initializeFrameValues TD (la:args) (lg:list GenericValue)
  (locals:GVMap) : option GVMap :=
match (la, lg) with
| (((t, _), id)::la', g::lg') =>
  match _initializeFrameValues TD la' lg' locals, fit_gv TD t g with
  | Some lc', Some gv => Some (updateAddAL _ lc' id (? gv # t ?))
  | _, _ => None
  end
| (((t, _), id)::la', nil) =>
  (* FIXME: We should initalize them w.r.t their type size. *)
  match _initializeFrameValues TD la' nil locals, gundef TD t with
  | Some lc', Some gv => Some (updateAddAL _ lc' id (? gv # t ?))
  | _, _ => None
  end
| _ => Some locals
end.

Definition initLocals TD (la:args) (lg:list GenericValue): option GVMap :=
_initializeFrameValues TD la lg nil.

(* Operations of generic values used by Vellvm's operational semantics *)
Definition BOP (TD:TargetData) (lc gl:GVMap) (op:bop) (bsz:sz)
  (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end.

Definition FBOP (TD:TargetData) (lc gl:GVMap) (op:fbop)
  (fp:floating_point) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mfbop TD op fp gv1 gv2
| _ => None
end
.

Definition TRUNC (TD:TargetData) (lc gl:GVMap) (op:truncop) (t1:typ)
  (v1:value) (t2:typ) : option GenericValue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mtrunc TD op t1 t2 gv1
| _ => None
end
.

Definition CAST (TD:TargetData) (lc gl:GVMap) (op:castop) (t1:typ)
  (v1:value) (t2:typ) : option GenericValue:=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mcast TD op t1 t2 gv1
| _ => None
end
.

Definition EXT (TD:TargetData) (lc gl:GVMap) (op:extop) (t1:typ)
  (v1:value) (t2:typ) : option GenericValue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mext TD op t1 t2 gv1
| _ => None
end
.

Definition ICMP (TD:TargetData) (lc gl:GVMap) (c:cond) (t:typ)
  (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => micmp TD c t gv1 gv2
| _ => None
end.

Definition FCMP (TD:TargetData) (lc gl:GVMap) (c:fcond)
  (fp:floating_point) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mfcmp TD c fp gv1 gv2
| _ => None
end.

(* t' is from getGEPtyp that always returns Some t'* or None *)
Definition GEP (TD:TargetData) (t:typ) (ma:GenericValue)
  (vidxs:list GenericValue) (inbounds:bool) (t':typ) : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ma with
| Some ptr =>
  match GVs2Nats TD vidxs with
  | None => gundef TD (typ_pointer t')
  | Some idxs =>
    match (mgep TD t ptr idxs) with
    | Some ptr0 => Some (ptr2GV TD ptr0)
    | None => gundef TD (typ_pointer t')
    end
  end
| None => gundef TD (typ_pointer t')
end.

Definition malloc (TD:TargetData) (M:mem) (bsz:sz) (gn:GenericValue) (al:align)
  : option (mem * mblock)%type :=
  Some (Mem.alloc M 0
          match GV2int TD Size.ThirtyTwo gn with
            | Some n => (Size.to_Z bsz) * n
            | None => 0
          end).

Definition alloca (TD:TargetData) (M:mem) (bsz:sz) (gn:GenericValue) (al:align)
  : option (mem * mblock)%type :=
  let hi :=
      (match GV2int TD Size.ThirtyTwo gn with
       | Some n => (Size.to_Z bsz) * n
       | None => 0
       end)%Z
  in
  let (M', nb) := (Mem.alloc M 0 hi) in
  option_map ((flip pair) nb) (Mem.drop_perm M' nb 0 hi Writable)
.

Definition malloc_one (TD:TargetData) (M:mem) (bsz:sz) (al:align)
  : option (mem * mblock)%type :=
  Some (Mem.alloc M 0 (Size.to_Z bsz)).

Definition free (TD:TargetData) (M:mem) (ptr:mptr) : option mem :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b i) =>
  if Coqlib.zeq (Int.signed 31 i) 0
  then
    match (Mem.bounds M b) with
    | (l, h) => Mem.free M b l h
    end
  else None
| _ => None
end.

Fixpoint free_allocas (TD:TargetData) (Mem:mem) (allocas:list mblock)
  : option mem :=
match allocas with
| nil => Some Mem
| alloca::allocas' =>
  let (lo, hi) := Mem.bounds Mem alloca in
  free_allocas TD (Mem.unchecked_free Mem alloca lo hi) allocas'
end.

Fixpoint mload_aux M (mc:list memory_chunk) b ofs : option GenericValue :=
match mc with
| nil => Some nil
| c::mc' =>
    match (Mem.load c M b ofs, mload_aux M mc' b (ofs+size_chunk c)%Z) with
    | (Some v, Some gv) => Some ((v,c) :: gv)
    | _ => None
    end
end.

Definition mload (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (a:align)
  : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match flatten_typ TD t with
  | Some mc => mload_aux M mc b (Int.signed 31 ofs)
  | _ => None
  end
| _ => None
end.

Definition has_chunk_eq (v : val) (chk : AST.memory_chunk) : bool :=
  match v, chk with
    | Vundef, _ => true
    | Vint wz i0, AST.Mint wz' =>
      beq_nat wz wz'
    | Vsingle f, AST.Mfloat32 =>
      true
    | Vfloat f, AST.Mfloat64 =>
      true
    | Vptr _ _, AST.Mint wz =>
      beq_nat wz 31%nat
    | Vinttoptr _, AST.Mint wz =>
      beq_nat wz 31%nat
    | _, _ =>
      false
  end.

Lemma has_chunk_eq_prop v chk (H: has_chunk_eq v chk) :
  Val.has_chunk v chk.
Proof.
  destruct v, chk; simpl in *; auto;
    repeat
      match goal with
        | [H: is_true false |- _] =>
          unfold is_true in H; inversion H
        | [H: is_true (beq_nat ?a ?b) |- _] =>
          apply beq_nat_true in H; subst
        | [H: context[Floats.Float.eq_dec ?a ?b] |- _] =>
          destruct (Floats.Float.eq_dec a b); try inversion H
      end;
    auto.
  split; [auto|].
  apply Int.unsigned_range.
Qed.

Lemma memory_chunk_eq_prop a b
  (H: AST.memory_chunk_eq a b) : a = b.
Proof.
  destruct a, b; unfold AST.memory_chunk_eq in H; simpl in *; auto;
    try match goal with
          | [H: is_true false |- _] =>
            unfold is_true in H; inversion H
        end.
  apply beq_nat_true in H; subst; auto.
Qed.

Fixpoint mstore_aux M (mc:list memory_chunk) (gv:GenericValue) b ofs : option mem :=
  match mc, gv with
    | nil, nil => Some M
    | c'::mc', (v,c)::gv' =>
      if memory_chunk_eq c' c && has_chunk_eq v c
      then
        match (Mem.store c M b ofs v) with
          | Some M' => mstore_aux M' mc' gv' b (ofs+size_chunk c)%Z
          | _ => None
        end
      else None
    | _, _ => None
  end.

Definition mstore (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (gv:GenericValue)
           (a:align) : option mem :=
  match GV2ptr TD (getPointerSize TD) ptr with
    | Some (Vptr b ofs) =>
      match flatten_typ TD t with
        | Some mc => mstore_aux M mc gv b (Int.signed 31 ofs)
        | None => None
      end
    | _ => None
  end.

Definition gep (TD:TargetData) (ty:typ) (vidxs:list GenericValue) (inbounds:bool)
  (ty':typ) (ma:GenericValue) : option GenericValue :=
LLVMgv.GEP TD ty ma vidxs inbounds ty'.

Definition mget' TD o t' gv: option GenericValue :=
match mget TD gv o t' with
| Some gv' => Some gv'
| None => gundef TD t'
end.

Definition mset' TD o t t0 gv gv0 : option GenericValue :=
match (mset TD gv o t0 gv0) with
| Some gv' => Some gv'
| None => gundef TD t
end.

Ltac inv H := inversion H; subst; clear H.

(********** Properties of sizeGenericValue *******************)
Lemma sizeGenericValue__app : forall gv1 gv2,
  sizeGenericValue (gv1 ++ gv2) = sizeGenericValue gv1 + sizeGenericValue gv2.
Proof.
  induction gv1; intros; simpl; auto.
    destruct a. rewrite IHgv1. omega.
Qed.

Lemma sizeGenericValue__repeatGV : forall gv n,
  sizeGenericValue (repeatGV gv n) = n * sizeGenericValue gv.
Proof.
  induction n; simpl; auto.
    rewrite sizeGenericValue__app. rewrite IHn. auto.
Qed.

Lemma sizeGenericValue__uninits : forall n, sizeGenericValue (uninits n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma sizeGenericValue_cons_pos : forall p gv0,
  (sizeGenericValue (p :: gv0) > 0)%nat.
Proof.
  intros. destruct p. simpl.
  assert (J:=@size_chunk_nat_pos' m).
  omega.
Qed.

Lemma sizeGenericValue_mc2undefs__sizeMC : forall mc, 
  sizeGenericValue (mc2undefs mc) = sizeMC mc.
Proof.
  induction mc; simpl; auto.
Qed.

(********** Properties of memory chunk *******************)
Lemma memory_chuck_dec : forall (mc1 mc2:AST.memory_chunk), 
  mc1 = mc2 \/ mc1 <> mc2.
Proof.
  destruct mc1; destruct mc2; try solve [auto | right; congruence].
    destruct (eq_nat_dec n n0); auto.
      right. intros J. inv J. auto.
Qed.

(********** Properties of getSubTypFromConstIdxs *******************)
Definition wf_global TD system5 gl := forall id5 typ5,
  lookupTypViaGIDFromSystem system5 id5 = ret typ5 ->
  exists gv, exists sz,
    lookupAL GenericValue gl id5 = Some gv /\
    getTypeSizeInBits TD typ5 = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv /\
    gv_chunks_match_typ TD gv typ5.

Lemma getSubTypFromConstIdxs__mgetoffset_aux : forall TD const_list idxs o t'
    t1 typ' o0
  (HeqR1 : ret idxs = intConsts2Nats TD const_list)
  (HeqR2 : ret (o, t') = mgetoffset_aux TD t1 idxs o0)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ'),
  t' = typ'.
Proof.
  induction const_list; simpl; intros.
    inv HeqR1. simpl in HeqR2. inv HeqR2. inv e0; auto.

    destruct_const a; tinv HeqR1.
    destruct (Size.dec sz5 Size.ThirtyTwo); tinv HeqR1.
    remember (intConsts2Nats TD const_list) as R3.
    destruct R3; inv HeqR1.
    destruct t1; tinv e0.
      simpl in HeqR2.
      destruct (getTypeAllocSize TD t1); inv HeqR2; eauto.

      simpl in HeqR2.
      destruct (_getStructElementOffset TD l1 (Coqlib.nat_of_Z
        (INTEGER.to_Z Int5)) 0); inv HeqR2; eauto.
      unfold INTEGER.to_nat in e0.
      unfold INTEGER.to_Z in H0.
      destruct (nth_error l1 (Coqlib.nat_of_Z Int5)); inv e0.
      simpl in H0. eauto.
Qed.

Lemma getSubTypFromConstIdxs__mgetoffset : forall TD const_list idxs o t' t1
    typ'
  (HeqR1 : ret idxs = intConsts2Nats TD const_list)
  (HeqR2 : ret (o, t') = mgetoffset TD t1 idxs)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ'),
  t' = typ'.
Proof.
  unfold mgetoffset. intros.
  eapply getSubTypFromConstIdxs__mgetoffset_aux; eauto.
Qed.

(********** Properties of splitGenericValue *******************)
Lemma splitGenericValue_spec0 : forall gv pos gv1 gv2,
  splitGenericValue gv pos = Some (gv1, gv2) -> (pos >= 0)%Z.
Proof.
  induction gv; simpl; intros.
    destruct (Coqlib.zeq pos 0); subst.
      auto with zarith.
      destruct (Coqlib.zlt pos 0); inv H.

    destruct (Coqlib.zeq pos 0); subst.
      auto with zarith.

      destruct (Coqlib.zlt pos 0); tinv H; auto.
Qed.

Lemma splitGenericValue_spec : forall gv pos gv1 gv2,
  splitGenericValue gv pos = Some (gv1, gv2) ->
  sizeGenericValue gv1 = Coqlib.nat_of_Z pos /\
  (sizeGenericValue gv1 + sizeGenericValue gv2 = sizeGenericValue gv)%nat.
Proof.
  induction gv; simpl; intros.
    destruct (Coqlib.zeq pos 0); subst.
      inv H. auto.
      destruct (Coqlib.zlt pos 0); inv H.

    destruct a.
    destruct (Coqlib.zeq pos 0); subst.
      inv H. auto.

      destruct (Coqlib.zlt pos 0); tinv H.
      remember (splitGenericValue gv (pos - size_chunk m)) as R.
      destruct R as [[]|]; inv H.
      simpl.
      symmetry in HeqR.
      assert (J:=HeqR). apply splitGenericValue_spec0 in J.
      eapply IHgv in HeqR; eauto.
      destruct HeqR as [J1 J2].
      rewrite <- J2. rewrite J1.
      assert ((size_chunk_nat m + Coqlib.nat_of_Z (pos - size_chunk m))%nat =
        Coqlib.nat_of_Z pos) as J3.
        unfold size_chunk_nat.
        assert (J0:=@size_chunk_pos m).
        rewrite <- Coqlib.nat_of_Z_plus; auto.
          assert (size_chunk m + (pos - size_chunk m) = pos)%Z as EQ.
            ring.
          rewrite EQ. auto.

          auto with zarith.
      rewrite J3. rewrite <- plus_assoc_reverse. rewrite J3.
      split; auto.
Qed.

Lemma splitGenericValue_spec1: forall gv o gv1 gv2, 
  splitGenericValue gv o = Some (gv1, gv2) ->
  gv = gv1 ++ gv2 /\ sizeGenericValue gv1 = Coqlib.nat_of_Z o.
Proof.
  induction gv as [|[]]; simpl; intros.
    repeat (destruct_if; auto).

    repeat (destruct_if; auto).
    inv_mbind. uniq_result. symmetry_ctx.
    assert (J:=HeqR1). apply splitGenericValue_spec0 in J.
    apply IHgv in HeqR1. 
    destruct HeqR1 as [J1 J2]; subst.
    split; simpl; auto.
      rewrite J2.
      unfold size_chunk_nat.
      assert (J0:=@size_chunk_pos m).
      rewrite <- Coqlib.nat_of_Z_plus; auto.
        assert (size_chunk m + (o - size_chunk m) = o)%Z as EQ.
          ring.
        rewrite EQ. auto.

        auto with zarith.
Qed.

(********** Properties of gv_chunks_match_typ *******************)
Lemma gv_chunks_match_typb_aux__gv_chunks_match_typ: forall mcs gv,
  gv_chunks_match_typb_aux gv mcs = true ->
  Forall2 vm_matches_typ gv mcs.
Proof.
  induction mcs; simpl; intros.
    destruct gv as [|[]]; auto.
      inv H.
    destruct gv as [|[]].
      inv H.

      simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply andb_true_iff in H1.
      destruct H1 as [H1 H3].
      constructor; eauto.
        unfold vm_matches_typ. simpl.
        split; auto using Val.has_chunkb__has_chunk.
        destruct m, a; tinv H1; auto.
          apply neq_inv in H1. congruence.
Qed.

Lemma gv_chunks_match_typb__gv_chunks_match_typ: forall td gv ty,
  gv_chunks_match_typb td gv ty = true ->
  gv_chunks_match_typ td gv ty.
Proof.
  unfold gv_chunks_match_typb, gv_chunks_match_typ.
  intros.
  inv_mbind.
  apply gv_chunks_match_typb_aux__gv_chunks_match_typ; auto.
Qed.

(********** Properties of vm_matches_typ *******************)
Lemma match_chunks_app: forall gv2 mcs2 (H2: Forall2 vm_matches_typ gv2 mcs2)
  gv1 mcs1 (H1: Forall2 vm_matches_typ gv1 mcs1),
    Forall2 vm_matches_typ (gv1++gv2) (mcs1++mcs2).
Proof.
  induction 2; simpl; auto.
Qed.

Lemma match_chunks_repeat: forall gv mcs (H1: Forall2 vm_matches_typ gv mcs) 
  n, Forall2 vm_matches_typ (repeatGV gv n) (repeatMC mcs n).
Proof.
  induction n; simpl; auto.
    apply match_chunks_app; auto.
Qed.

Lemma match_chunks_eq_size: forall gv mcs,
  Forall2 vm_matches_typ gv mcs ->
  sizeGenericValue gv = sizeMC mcs.
Proof.
  induction 1 as [|[]]; simpl; auto.
    inv H. simpl. congruence.
Qed.

Lemma match_chunks_app_inv: forall gv2 mcs2 gv1 mcs1 
  (H:Forall2 vm_matches_typ (gv1++gv2) (mcs1++mcs2))
  (EQ1: sizeGenericValue gv1 = sizeMC mcs1),
  Forall2 vm_matches_typ gv1 mcs1 /\ Forall2 vm_matches_typ gv2 mcs2.
Proof.
  induction gv1 as [|[]]; destruct mcs1; simpl; intros; auto.
    assert (J:=@size_chunk_nat_pos m).
    destruct J as [n J].
    rewrite J in EQ1.
    inv EQ1.

    assert (J:=@size_chunk_nat_pos m).
    destruct J as [n J].
    rewrite J in EQ1.
    inv EQ1.

    inv H. 
    apply IHgv1 in H5.
      destruct H5 as [H5 H6].
      split; auto.

      inv H3. simpl in *. clear - EQ1. omega.
Qed.

Lemma match_chunks_split_right: forall gv2 gv1 mcs
  (H:Forall2 vm_matches_typ (gv1++gv2) mcs),
  exists mcs1, exists mcs2,
    mcs = mcs1 ++ mcs2 /\
    Forall2 vm_matches_typ gv1 mcs1 /\ 
    Forall2 vm_matches_typ gv2 mcs2.
Proof.
  induction gv1; simpl; intros.
    exists nil. exists mcs.
    split; auto.

    inv H.
    apply IHgv1 in H4.
    destruct H4 as [mcs1 [mcs2 [J1 [J2 J3]]]]; subst.
    exists (y::mcs1). exists mcs2.
    split; auto.
Qed.

Lemma match_chunks_det: forall gv mcs1 
  (H1: Forall2 vm_matches_typ gv mcs1)
  mcs2 (H2: Forall2 vm_matches_typ gv mcs2),
  mcs1 = mcs2.
Proof.
  induction 1; simpl; intros; inv H2; auto.
    inv H. inv H4.
    erewrite IHForall2; eauto.
Qed.

Lemma uninits_match_uninitMCs: forall n,
  Forall2 vm_matches_typ (uninits n) (uninitMCs n).
Proof.
  unfold uninits, uninitMCs, vm_matches_typ.
  induction n; simpl; auto.
    constructor; simpl; auto.
Qed.

Lemma mset_matches_chunks : forall td gv1 o t2 gv2 gv t1 
  (J1: gv_chunks_match_typ td gv1 t1) (J2: gv_chunks_match_typ td gv2 t2)
  (HeqR4 : ret gv = mset td gv1 o t2 gv2),
  gv_chunks_match_typ td gv t1.
Proof.
  intros.
  unfold mset in HeqR4.
  remember (getTypeStoreSize td t2) as R.
  destruct R; tinv HeqR4.
  simpl in HeqR4.
  destruct (n =n= length gv2); tinv HeqR4.
  remember (splitGenericValue gv1 o) as R1.
  destruct R1 as [[? gvr]|]; tinv HeqR4.
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[gvrl ?]|]; inv HeqR4.
  destruct_if.
  unfold gv_chunks_match_typ in *.
  inv_mbind. symmetry_ctx.
  apply splitGenericValue_spec1 in HeqR1.
  apply splitGenericValue_spec1 in HeqR2.
  destruct HeqR1 as [HeqR11 HeqR12]; subst.
  destruct HeqR2 as [HeqR21 HeqR22]; subst.
  apply match_chunks_split_right in J1.
  destruct J1 as [mcs1 [mcs2 [EQ [J1 J3]]]]; subst.
  apply match_chunks_split_right in J3.
  destruct J3 as [mcs3 [mcs4 [EQ [J3 J4]]]]; subst.
  repeat (apply match_chunks_app; auto).
  symmetry in HeqR0.
  apply gv_chunks_match_typb__gv_chunks_match_typ in HeqR0; auto.
  unfold gv_chunks_match_typ in HeqR0.
  rewrite HeqR3 in HeqR0.
  eapply match_chunks_det with (mcs2:=l0) in J3; eauto.
  subst. auto.
Qed.

Lemma mget_matches_chunks : forall td gv1 o typ' gv'
  (HeqR4 : ret gv' = mget td gv1 o typ'),
  gv_chunks_match_typ td gv' typ'.
Proof.
  intros.
  unfold mget in HeqR4.
  remember (getTypeStoreSize td typ') as R.
  destruct R; tinv HeqR4.
  simpl in HeqR4.
  remember (splitGenericValue gv1 o) as R1.
  destruct R1 as [[? gvr]|]; tinv HeqR4.
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[gvrl ?]|]; inv HeqR4.
  remember (gv_chunks_match_typb td gvrl typ') as R.
  destruct R; inv H0.
  apply gv_chunks_match_typb__gv_chunks_match_typ; auto.
Qed.

Lemma mcmp_matches_chunks_helper : forall TD gv,
  gundef TD (typ_int 1%nat) = ret gv ->
  gv_chunks_match_typ TD gv (typ_int 1%nat).
Proof.
  intros. destruct TD.
  unfold gundef in H. simpl in H. inv H. 
  unfold gv_chunks_match_typ, vm_matches_typ. 
  simpl. constructor; simpl; auto.
Qed.

Lemma micmp_matches_chunks : forall TD cond5 t1 gv1 gv2 gv,
  micmp TD cond5 t1 gv1 gv2 = Some gv ->
  gv_chunks_match_typ TD gv (typ_int 1%nat).
Proof.
  intros. unfold micmp in H.
  destruct t1;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  unfold micmp_int, GV2val in H.
  destruct gv1;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct p.
  destruct gv1;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct gv2;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct p.
  destruct gv2;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct TD.
  Local Opaque Val.cmp Val.cmpu Val.cmpu_int.
  destruct cond5; inv H; unfold gv_chunks_match_typ, vm_matches_typ, val2GV;
    simpl; constructor; try solve [
      auto |
      split; try solve [auto | apply Val.cmp_has_Mint0 | 
                        apply Val.cmpu_has_Mint0 |
                        apply Val.cmpu_int_has_Mint0]
    ].
  Transparent Val.cmp Val.cmpu Val.cmpu_int.
Qed.

Lemma mfcmp_matches_chunks : forall TD fcond5 fp gv1 gv2 gv,
  mfcmp TD fcond5 fp gv1 gv2 = Some gv ->
  gv_chunks_match_typ TD gv (typ_int 1%nat).
Proof.
  intros. unfold mfcmp, GV2val in H.
  destruct gv1;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct p.
  destruct gv1;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct gv2;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct p.
  destruct gv2;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_matches_chunks_helper; eauto].
  destruct TD.
  Local Opaque Val.cmpf.
  destruct fp; try solve [
    inv H | 
    destruct fcond5; inv H; unfold gv_chunks_match_typ, vm_matches_typ, val2GV;
      try solve [
      auto |
      simpl; constructor; try solve [
        auto |
        simpl; split; try solve [auto | apply Val.cmpf_has_Mint0 |
                                 simpl; split; try solve [
                                   auto |
                                   unfold Int.modulus, two_power_nat, shift_nat; simpl; omega
                                ]
                      ]
        ]
      ]
    ].
  Transparent Val.cmpf.
Qed.

Lemma vm_matches_typ__eq__snd: forall gv1 mc 
  (Hmatch : Forall2 vm_matches_typ gv1 mc), snd (split gv1) = mc.
Proof.
  induction 1; simpl; subst; auto.
    destruct x. inv H.
    destruct (split l0). auto.
Qed.

Lemma vm_matches_typ__gv_has_chunk: forall gv1 mc 
  (Hmatch : Forall2 vm_matches_typ gv1 mc), gv_has_chunk gv1.
Proof.
  unfold gv_has_chunk.
  induction 1; simpl; subst; auto.
    destruct x. inv H. constructor; auto.
Qed.

Lemma vm_matches_typ__sizeMC_eq_sizeGenericValue: forall gvs mcs 
  (Hmatch : Forall2 vm_matches_typ gvs mcs), 
  sizeMC mcs = sizeGenericValue gvs.
Proof.
  induction 1; simpl; subst; auto.
    destruct x. inv H.
    simpl. congruence.
Qed.

(* Inversion *)
Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv,
  BOP TD lc gl b s v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mbop TD b s gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b s v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
      remember (mbop TD b s g g0) as R.
      destruct R; inversion HBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma FBOP_inversion : forall TD lc gl b fp v1 v2 gv,
  FBOP TD lc gl b fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mfbop TD b fp gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b fp v1 v2 gv HFBOP.
  unfold FBOP in HFBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HFBOP].
      remember (mfbop TD b fp g g0) as R.
      destruct R; inversion HFBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma getOperandPtr_inversion : forall TD lc gl v mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2ptr TD (getPointerSize TD) gv = Some mptr.
Proof.
  intros TD lc gl v mptr HgetOperandPtr.
  unfold getOperandPtr in HgetOperandPtr.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandPtr].
    exists g. auto.
Qed.

Lemma getOperandInt_inversion : forall TD sz lc gl v n,
  getOperandInt TD sz v lc gl = Some n ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2int TD sz gv = Some n.
Proof.
  intros TD sz0 lc gl v mptr HgetOperandInt.
  unfold getOperandInt in HgetOperandInt.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandInt].
    exists g. auto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mcast TD op t1 t2 gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HCAST].
    remember (mcast TD op t1 t2 g) as R.
    destruct R; inversion HCAST; subst.
      exists g. auto.
Qed.

Lemma TRUNC_inversion : forall TD lc gl op t1 v1 t2 gv,
  TRUNC TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mtrunc TD op t1 t2 gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HTRUNC.
  unfold TRUNC in HTRUNC.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HTRUNC].
    remember (mtrunc TD op t1 t2 g) as R.
    destruct R; inversion HTRUNC; subst.
      exists g. auto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mext TD op t1 t2 gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HEXT].
    remember (mext TD op t1 t2 g) as R.
    destruct R; inversion HEXT; subst.
      exists g. auto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    micmp TD cond t gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
      remember (micmp TD cond0 t g g0) as R.
      destruct R; inversion HICMP; subst.
        exists g. exists g0. auto.
Qed.

Lemma FCMP_inversion : forall TD lc gl cond fp v1 v2 gv,
  FCMP TD lc gl cond fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mfcmp TD cond fp gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 fp v1 v2 gv HFCMP.
  unfold FCMP in HFCMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFCMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HFCMP].
      remember (mfcmp TD cond0 fp g g0) as R.
      destruct R; inversion HFCMP; subst.
        exists g. exists g0. auto.
Qed.

Lemma intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0,
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.
Proof.
  induction l0; intros; simpl in *.
    inversion H. exists nil. auto.

    destruct a as [s v].
    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H].
    remember (GV2int TD Size.ThirtyTwo g) as on.
    destruct on; try solve [inversion H].
    remember (intValues2Nats TD l0 lc gl) as ons.
    destruct ons; inversion H; subst.
    symmetry in Heqons.
    apply IHl0 in Heqons.
    destruct Heqons as [gvs [J1 J2]].
    exists (g::gvs).
    rewrite J1.
    split; auto.
      simpl. rewrite J2. rewrite <- Heqon. auto.
Qed.

Lemma values2GVs_GVs2Nats__intValues2Nats : forall l0 lc gl TD gvs0,
  values2GVs TD l0 lc gl = Some gvs0 ->
  GVs2Nats TD gvs0 = intValues2Nats TD l0 lc gl.
Proof.
  induction l0; intros lc gl TD gvs0 H; simpl in *.
    inversion H. auto.

    destruct a as [s v].
    destruct (getOperandValue TD v lc gl); try solve [inversion H].
      remember (values2GVs TD l0 lc gl)as ogv.
      destruct ogv; inversion H; subst.
        rewrite <- IHl0 with (gvs0:=l1); auto.
Qed.

(* Properties of eqAL *)
Lemma const2GV_eqAL_aux :
  (forall c gl1 gl2 TD, eqAL _ gl1 gl2 ->
     _const2GV TD gl1 c = _const2GV TD gl2 c) /\
  (forall cs gl1 gl2 TD, eqAL _ gl1 gl2 ->
    (forall t, _list_const_arr2GV TD gl1 t cs = _list_const_arr2GV TD gl2 t cs)
    /\
    _list_const_struct2GV TD gl1 cs = _list_const_struct2GV TD gl2 cs).
Proof.
  apply const_mutind; intros; simpl;
  try solve [
    auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
      destruct H0; auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
    destruct H0;
    unfold _list_const_arr2GV in H0; rewrite H0; auto |

    rewrite H; auto |

    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J;
    rewrite J; auto
  ];
  fold _list_const_struct2GV.

  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0.
  rewrite (proj2 H0). auto.

  assert (J:=H1).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
  rewrite H1.
  assert (J':=J). trivial.

  assert (J:=H2).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H2.
  rewrite H2.
  assert (J':=J).
  apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
  rewrite J.
  apply H1 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J'.
  rewrite J'. auto.

  assert (J:=H1).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
  rewrite H1. auto.

  assert (J:=H2).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H2.
  rewrite H2.
  assert (J':=J).
  apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
  rewrite J. auto.

  split.
    intros.
    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
    destruct J. rewrite H2; auto.

    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
    destruct J. rewrite H3; auto.
Qed.

Lemma const2GV_eqAL : forall c gl1 gl2 TD,
  eqAL _ gl1 gl2 ->
  const2GV TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct const2GV_eqAL_aux.
  erewrite H0; eauto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FBOP_eqAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD HeqEnv.
  unfold FBOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma getOperandPtr_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtr TD v lc1 gl = getOperandPtr TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqEnv.
  unfold getOperandPtr in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandInt_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandInt TD sz v lc1 gl = getOperandInt TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandInt in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandPtrInBits_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtrInBits TD sz v lc1 gl = getOperandPtrInBits TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandPtrInBits in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma TRUNC_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  TRUNC TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold TRUNC in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FCMP_eqAL : forall lc1 gl lc2 cond fp v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FCMP TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD HeqAL.
  unfold FCMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma intValues2Nats_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  intValues2Nats TD l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    destruct a.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    destruct a.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma mload_aux__sizeGenericValue : forall M b mc ofs gv,
  mload_aux M mc b ofs = Some gv ->
  sizeMC mc = sizeGenericValue gv.
Proof.
  induction mc; simpl; intros.
    inv H. auto.

    destruct (Mem.load a M b ofs); tinv H.
    remember (mload_aux M mc b (ofs + size_chunk a)) as R.
    destruct R; inv H.
    simpl.
    erewrite IHmc; eauto.
Qed.

Lemma mload_inv : forall Mem2 t align0 TD gvp2
  (gv2 : GenericValue)
  (H21 : mload TD Mem2 gvp2 t align0 = ret gv2),
  exists b, exists ofs, exists m, exists mc,
    gvp2 = (Vptr b ofs,m)::nil /\ flatten_typ TD t = Some mc /\
    mload_aux Mem2 mc b (Int.signed 31 ofs) = Some gv2.
Proof.
  intros.
  unfold mload in H21.
  remember (GV2ptr TD (getPointerSize TD) gvp2) as R.
  destruct R; try solve [inversion H21].
  destruct v; try solve [inversion H21].
  unfold GV2ptr in HeqR.
  destruct gvp2; try solve [inversion HeqR].
  destruct p.
  destruct v; try solve [inversion HeqR].
  destruct gvp2; inv HeqR.
  exists b0. exists i1. exists m.
  destruct (flatten_typ TD t); inv H21.
  eauto.
Qed.

Lemma free_inv : forall TD Mem0 gv Mem',
  free TD Mem0 gv = ret Mem' ->
  exists blk, exists ofs, exists hi, exists lo,
    GV2ptr TD (getPointerSize TD) gv = Some (Vptr blk ofs) /\
    Int.signed 31 ofs = 0%Z /\
    (lo, hi) = Mem.bounds Mem0 blk /\
    Mem.free Mem0 blk lo hi = Some Mem'.
Proof.
  intros TD Mem0 gv Mem' H0.
  unfold free in H0.
  destruct (GV2ptr TD (getPointerSize TD) gv); try solve [inversion H0; subst].
  destruct v; try solve [inversion H0; subst].
  destruct (Coqlib.zeq (Int.signed 31 i0) 0); try solve [inversion H0; subst].
  remember (Mem.bounds Mem0 b) as R.
  destruct R as [l h].
  exists b. exists i0. rewrite e. rewrite <- HeqR. exists h. exists l.
  repeat (split; auto).
Qed.

Lemma malloc_inv : forall TD Mem0 tsz gn align0 Mem' mb,
  malloc TD Mem0 tsz gn align0 = ret (Mem', mb) ->
  Mem.alloc Mem0 0
        match GV2int TD Size.ThirtyTwo gn with
          | Some n => (Size.to_Z tsz) * n
          | None => 0
        end = (Mem', mb).
Proof.
  intros. inv H. auto.
Qed.

Lemma alloca_inv : forall TD Mem0 tsz gn align0 Mem' mb,
  alloca TD Mem0 tsz gn align0 = ret (Mem', mb) ->
  let hi :=
  match GV2int TD Size.ThirtyTwo gn with
  | ret n => (Size.to_Z tsz * n)%Z
  | merror => 0%Z
  end in
  let (M', nb) := Mem.alloc Mem0 0 hi in
  option_map (flip pair nb) (Mem.drop_perm M' nb 0 hi Writable) = ret (Mem', mb)
.
Proof.
  intros. unfold alloca in *. eauto.
Qed.

Lemma store_inv : forall TD Mem0 gvp t gv align Mem',
  mstore TD Mem0 gvp t gv align = Some Mem' ->
  exists b, exists ofs, exists mc,
    GV2ptr TD (getPointerSize TD) gvp = Some (Vptr b ofs) /\
    flatten_typ TD t = Some mc /\
    mstore_aux Mem0 mc gv b (Int.signed 31 ofs) = Some Mem'.
Proof.
  intros TD Mem0 gvp t gv align Mem' H.
  unfold mstore in H.
  destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H; subst].
  destruct v; try solve [inversion H; subst].
  exists b. exists i0.
  destruct (flatten_typ TD t); inv H.
  exists l0. split; auto.
Qed.

 Lemma mstore_inversion : forall Mem2 t align0 TD gvp2 Mem2'
   (gv2 : GenericValue)
   (H21 : mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2'),
  exists b, exists ofs, exists cm, exists mc,
    gvp2 = (Vptr b ofs,cm)::nil /\
    flatten_typ TD t = Some mc /\
    mstore_aux Mem2 mc gv2 b (Int.signed 31 ofs) = ret Mem2'.
 Proof.
  intros.
  unfold mstore in H21.
  remember (GV2ptr TD (getPointerSize TD) gvp2) as R.
  destruct R; try solve [inversion H21].
  destruct v; try solve [inversion H21].
  unfold GV2ptr in HeqR.
  destruct gvp2; try solve [inversion HeqR].
  destruct p.
  destruct v; try solve [inversion HeqR].
  destruct gvp2; inv HeqR.
  exists b0. exists i1. exists m.
  destruct (flatten_typ TD t); inv H21.
  exists l0. eauto.
Qed.

(* Properties of sizeMC *)
Lemma sizeMC__app : forall mc1 mc2,
  sizeMC (mc1 ++ mc2) = (sizeMC mc1 + sizeMC mc2)%nat.
Proof.
  induction mc1; intros; simpl; auto.
    rewrite IHmc1. omega.
Qed.

Lemma sizeMC__repeatMC : forall mc n,
  sizeMC (repeatMC mc n) = (n * sizeMC mc)%nat.
Proof.
  induction n; simpl; auto.
    rewrite sizeMC__app. rewrite IHn. auto.
Qed.

Lemma sizeMC__uninitMCs : forall n, sizeMC (uninitMCs n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(* Properties of initLocals *)
Lemma initLocals_spec : forall TD la gvs id1 lc,
  In id1 (getArgsIDs la) ->
  initLocals TD la gvs = Some lc ->
  exists gv, lookupAL _ lc id1 = Some gv.
Proof.
  unfold initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a as [[t c] id0].
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs.
        remember (_initializeFrameValues TD la nil nil) as R1.
        destruct R1; tinv H0.
        remember (gundef TD t) as R2.
        destruct R2; inv H0.
        exists (? g0 # t ?). apply lookupAL_updateAddAL_eq; auto.

        remember (_initializeFrameValues TD la gvs nil) as R1.
        destruct R1; tinv H0.
        remember (fit_gv TD t g) as R2.
        destruct R2; inv H0.
        exists (? g1 # t ?). apply lookupAL_updateAddAL_eq; auto.

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (_initializeFrameValues TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          exists (? g0 # t ?). apply lookupAL_updateAddAL_eq; auto.

          remember (_initializeFrameValues TD la gvs nil) as R1.
          destruct R1; tinv H0.
          remember (fit_gv TD t g) as R2.
          destruct R2; inv H0.
          exists (? g1 # t ?). apply lookupAL_updateAddAL_eq; auto.

        destruct gvs.
          remember (_initializeFrameValues TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1].
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.

          remember (_initializeFrameValues TD la gvs nil) as R1.
          destruct R1; tinv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1].
          remember (fit_gv TD t g) as R2.
          destruct R2; inv H0.
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

(* Properties of gundef *)
Lemma gundef_p1__total : forall TD, exists mp', gundef TD (typ_pointer (typ_int 1%nat)) = ret mp'.
Proof.
  intros. unfold gundef. destruct TD. simpl. eauto.
Qed.

Lemma gundef_i1__total : forall TD, exists mp', gundef TD (typ_int 1%nat) = ret mp'.
Proof.
  intros. unfold gundef. destruct TD. simpl. eauto.
Qed.

(* Properties of typesize *)
Lemma mget_typsize : forall los nts gv1 o typ' gv'
  (HeqR4 : ret gv' = mget (los, nts) gv1 o typ'),
   exists sz1 : nat,
     exists al0 : nat,
       _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
         true typ' = ret (sz1, al0) /\
       Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8) = sizeGenericValue gv'.
Proof.
  intros.
  unfold mget in HeqR4.
  remember (getTypeStoreSize (los, nts) typ') as R.
  destruct R; tinv HeqR4.
  simpl in HeqR4.
  remember (splitGenericValue gv1 o) as R1.
  destruct R1 as [[? gvr]|]; tinv HeqR4.
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[gvrl ?]|]; inv HeqR4.
  destruct (gv_chunks_match_typb (los, nts) gvrl typ'); inv H0.
  unfold getTypeStoreSize, getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR.
  remember (_getTypeSizeInBits_and_Alignment los
               (_getTypeSizeInBits_and_Alignment_for_namedts los
                  nts true) true typ') as R3.
  destruct R3 as [[sz ?]|]; tinv HeqR.
  exists sz. exists n0.
  split; auto. inv HeqR.
    symmetry in HeqR2.
    apply splitGenericValue_spec in HeqR2.
    destruct HeqR2 as [J1 J2].
    rewrite J1.
    erewrite Coqlib.Z_of_nat_eq; eauto.
Qed.

Lemma mset_typsize : forall los nts gv1 o t2 gv2 gv sz2 al2
  (J3 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
         true t2 = ret (sz2, al2))
  (J4 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8) = sizeGenericValue gv2)
  (HeqR4 : ret gv = mset (los, nts) gv1 o t2 gv2),
  sizeGenericValue gv1 = sizeGenericValue gv.
Proof.
  intros.
  unfold mset in HeqR4.
  remember (getTypeStoreSize (los, nts) t2) as R.
  destruct R; tinv HeqR4.
  simpl in HeqR4.
  destruct (n =n= length gv2); tinv HeqR4.
  remember (splitGenericValue gv1 o) as R1.
  destruct R1 as [[? gvr]|]; tinv HeqR4.
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[gvrl ?]|]; inv HeqR4.
  symmetry in HeqR2.
  apply splitGenericValue_spec in HeqR2.
  destruct HeqR2 as [J1 J2].
  symmetry in HeqR1.
  apply splitGenericValue_spec in HeqR1.
  destruct HeqR1 as [J3' J4'].
  rewrite <- J4'. rewrite <- J2.
  destruct_if.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__app.
  unfold getTypeStoreSize, getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR.
  rewrite J3 in HeqR.
  inv HeqR.
  rewrite Coqlib.Z_of_nat_eq in J1.
  rewrite <- J1 in J4. rewrite J4. auto.
Qed.

Lemma feasible_typ_inv'' : forall TD t,
  LLVMtd.feasible_typ TD t ->
  exists ssz, exists asz,
    getTypeStoreSize TD t = Some ssz /\ getTypeAllocSize TD t = Some asz.
Proof.
  intros TD t Hs.
  apply feasible_typ_inv' in Hs.
  destruct Hs as [sz [al [J1 J2]]].
  unfold getTypeAllocSize, getTypeStoreSize, getTypeSizeInBits,
    getABITypeAlignment, getAlignment.
  rewrite J1. eauto.
Qed.

Lemma mcmp_typsize_helper : forall TD gv,
  gundef TD (typ_int 1%nat) = ret gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat Size.One) 8) = sizeGenericValue gv.
Proof.
  intros. destruct TD.
  unfold gundef in H. simpl in H. inv H. simpl. auto.
Qed.

Lemma micmp_typsize : forall los nts cond5 t1 gv1 gv2 gv,
  micmp (los,nts) cond5 t1 gv1 gv2 = Some gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat Size.One) 8) = sizeGenericValue gv.
Proof.
  intros. unfold micmp in H.
  destruct t1;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  unfold micmp_int, GV2val in H.
  destruct gv1;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv1;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct gv2;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv2;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct cond5; inv H; auto.
Qed.

Lemma mfcmp_typsize : forall los nts fcond5 fp gv1 gv2 gv,
  mfcmp (los,nts) fcond5 fp gv1 gv2 = Some gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat Size.One) 8) = sizeGenericValue gv.
Proof.
  intros. unfold mfcmp, GV2val in H.
  destruct gv1;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv1;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct gv2;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv2;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct fp; try solve [inv H | destruct fcond5; inv H; auto].
Qed.

(* Properties of gv_lessdef *)
Lemma gv_lessdef_ref: forall gv, gv_lessdef gv gv.
Proof.
  unfold gv_lessdef.
  induction gv as [|[]]; auto.
Qed.
    
(* Properties of gv_has_chunk *)
Lemma gv_has_chunkb__gv_has_chunk: forall gv (Hchk: gv_has_chunkb gv), 
  gv_has_chunk gv.
Proof.
  unfold gv_has_chunk.
  induction gv as [|[]]; simpl; intros; auto.
    apply andb_true_iff in Hchk.
    destruct Hchk as [J1 J2].
    constructor; auto using Val.has_chunkb__has_chunk.
Qed.

End LLVMgv.