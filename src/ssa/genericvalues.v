Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import List.
Require Import Arith.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import alist.
Require Import ssa_def.
Require Import ssa_lib.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import targetdata.
Require Import ZArith.
Require Import Floats.

Module LLVMgv.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMtd.

Definition moffset := Int.int 31.
Definition mem := Mem.mem.
Definition GenericValue := list (val*memory_chunk).
Definition GVMap := list (id*GenericValue).

Definition mblock := Values.block.
Definition mptr := GenericValue.
Definition null : GenericValue := 
  (Vptr Mem.nullptr (Int.repr 31 0), Mint 31)::nil.

Fixpoint eq_gv (gv1 gv2:GenericValue) : bool :=
match gv1, gv2 with
| nil, nil => true
| (v1,c1)::gv1', (v2,c2)::gv2' => Val.eq v1 v2 && 
                                  memory_chunk_eq c1 c2 && 
                                  eq_gv gv1' gv2'
| _, _ => false
end.

Definition uninits (n:nat) : GenericValue := 
   Coqlib.list_repeat n (Vundef, Mint 7).

Definition gundef (t:typ) : GenericValue := 
match (typ2memory_chunk t) with
| Some c => (Vundef, c)::nil
| None => uninits 1
end.

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
Fixpoint isGVUndef (gv:GenericValue) : Prop :=
match gv with
| nil => False
| (Vundef,_)::gv' => True
| _::gv' => isGVUndef gv'
end.
Definition val2GV (TD:TargetData) (v:val) (c:memory_chunk) : GenericValue :=
(v,c)::nil.
Definition ptr2GV (TD:TargetData) (ptr:val) : GenericValue :=
val2GV TD ptr (Mint (getPointerSize TD-1)).
Definition blk2GV (TD:TargetData) (b:mblock) : GenericValue :=
ptr2GV TD (Vptr b (Int.repr 31 0)).
Definition isGVZero (TD:TargetData) (gv:GenericValue) : bool :=
match (GV2int TD Size.One gv) with
| Some z => if Coqlib.zeq z 0 then true else false
| _ => false
end.

Fixpoint mgetoffset_aux (TD:TargetData) (t:typ) (idxs:list Z) (accum:Z) 
  : option (Z * typ) := 
  match idxs with
  | nil => Some (accum, t)
  | idx::idxs' =>
     match t with
     | typ_array _ t' =>
         match (getTypeAllocSize TD t') with
         | Some sz => 
             mgetoffset_aux TD t' idxs' (accum + (Z_of_nat sz) * idx)
         | _ => None
         end
     | typ_struct lt => 
         match (getStructElementOffset TD t (Coqlib.nat_of_Z idx)) 
         with
         | Some ofs =>
             do t' <- nth_list_typ (Coqlib.nat_of_Z idx) lt;
               mgetoffset_aux TD t' idxs' (accum + (Z_of_nat ofs))
         | _ => None
         end
     | _ => None
     end
  end.  

Definition mgetoffset (TD:TargetData) (t:typ) (idxs:list Z) 
  : option (int32 * typ) := 
let (_, nts) := TD in
do ut <- Constant.typ2utyp nts t;
match mgetoffset_aux TD ut idxs 0 with
| Some (z, t') => Some (Int.repr 31 z, t')
| None => None
end.

Definition mgep (TD:TargetData) (t:typ) (ma:val) (idxs:list Z) : option val :=
match ma with
| Vptr b ofs => 
  match idxs with
  | nil => None
  | _ =>
    match (mgetoffset TD (typ_array 0 t) idxs) with
    | Some (offset, _) => Some (Vptr b (Int.add 31 ofs offset))
    | _ => None
    end
  end
| _ => None
end.

Fixpoint sizeGenericValue (gv:GenericValue) : nat :=
match gv with
| nil => 0
| (v,c)::gv' => size_chunk_nat c + sizeGenericValue gv'
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

Definition mget (TD:TargetData) (gv:GenericValue) (o:int32) (t:typ) 
  : option GenericValue :=
do s <- getTypeStoreSize TD t;
  match (splitGenericValue gv (Int.signed 31 o)) with
  | Some (gvl, gvr) =>
      match (splitGenericValue gvr (Z_of_nat s)) with
      | Some (gvrl, gvrr) => Some gvrl
      | None => None
      end
  | None => None
  end.

Definition mset (TD:TargetData) (gv:GenericValue) (o:int32) (t0:typ) 
  (gv0:GenericValue) : option GenericValue :=
let n := Coqlib.nat_of_Z (Int.signed 31 o) in
do s <- getTypeStoreSize TD t0;
  if (beq_nat s (length gv0)) then 
    match (splitGenericValue gv (Int.signed 31 o)) with
    | Some (gvl, gvr) =>
       match (splitGenericValue gvr (Z_of_nat s)) with
       | Some (gvrl, gvrr) => Some (gvl++gv0++gvrr)
       | None => None
       end
    | None => None
    end
  else None.

Fixpoint intConsts2Nats (TD:TargetData) (lv:list_const) : option (list Z):=
match lv with
| Nil_list_const => Some nil
| Cons_list_const (const_int sz0 n) lv' => 
  if Size.dec sz0 Size.ThirtyTwo 
  then
    match (intConsts2Nats TD lv') with
    | Some ns => Some ((INTEGER.to_Z n)::ns)
    | None => None
    end
  else None
| _ => None
end.

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
  (cidxs : list_const) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => Some (uninits 1)
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, t') => match mget TD gv o t' with 
                    | Some gv' => Some gv'
                    | None => Some (gundef t')
                    end
  | None => Some (uninits 1)
  end
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gv:GenericValue)
  (cidxs:list_const) (t0:typ) (gv0:GenericValue) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => Some (gundef t)
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, _) => match (mset TD gv o t0 gv0) with
                   | Some gv' => Some gv'
                   | None => Some (gundef t)
                   end
  | None => Some (gundef t)
  end
end.

Definition mtrunc (TD:TargetData) (op:truncop) (t1:typ) (t2:typ) 
  (gv1:GenericValue) : option GenericValue :=
match GV2val TD gv1 with
| Some (Vint wz1 i1) =>
    match (t1, t2) with
    | (typ_int sz1, typ_int sz2) =>
        Some (val2GV TD (Val.trunc (Vint wz1 i1) sz2) (Mint sz2))
    | _ => Some (gundef t2)
    end
| Some (Vfloat f) =>
    match (t1, t2) with
    | (typ_floatpoint fp1, typ_floatpoint fp2) =>
        if floating_point_order fp2 fp1 
        then 
          match fp2 with
          | fp_float => Some (val2GV TD (Val.ftrunc (Vfloat f)) Mfloat32)
          | fp_double => Some (val2GV TD (Val.ftrunc (Vfloat f)) Mfloat64)
          | _ => Some (gundef t2) (* FIXME: not supported 80 and 128 yet. *)
          end
        else Some (gundef t2)
    | _ => Some (gundef t2)
    end
| _ => Some (gundef t2)
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
         Some (val2GV TD (Val.divu (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_sdiv => 
         Some (val2GV TD (Val.divs (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_urem => 
         Some (val2GV TD (Val.modu (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_srem => 
         Some (val2GV TD (Val.mods (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_shl => 
         Some (val2GV TD (Val.shl (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_lshr => 
         Some (val2GV TD (Val.shrx (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_ashr => 
         Some (val2GV TD (Val.shr (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_and => 
         Some (val2GV TD (Val.and (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_or => 
         Some (val2GV TD (Val.or (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_xor => 
         Some (val2GV TD (Val.xor (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     end
  else Some (gundef (typ_int (bsz'-1)))
| _ => Some (gundef (typ_int (bsz'-1)))
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
  | fp_float => Some (val2GV TD v Mfloat32)
  | fp_double => Some (val2GV TD v Mfloat64)
  | _ => Some (gundef (typ_floatpoint fp)) 
         (* FIXME: not supported 80 and 128 yet. *)
  end
| _ => Some (gundef (typ_floatpoint fp))
end.

Definition mptrtoint (TD:TargetData) (M:mem) (gv1:GenericValue) (sz2:nat)
 : option GenericValue :=
    match GV2val TD gv1 with
    | Some (Vptr b1 ofs1) =>
        match Mem.ptr2int M b1 0 with
        | Some z => 
            Some (val2GV TD 
                   (Vint sz2 (Int.repr sz2 (z + Int.signed 31 ofs1))) 
                   (Mint sz2))
        | None => Some (val2GV TD (Vint sz2 (Int.zero sz2)) (Mint sz2))
        end
    | Some (Vinttoptr i) => 
        Some (val2GV TD (Vint sz2 (Int.repr sz2 (Int.unsigned 31 i))) (Mint sz2))
    | _ => Some (gundef (typ_int (sz2+1)))
    end.

Definition mbitcast (t1:typ) (gv1:GenericValue)(t2:typ) : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) => Some gv1
| (typ_pointer _, typ_pointer _) => Some gv1
| _ => Some (gundef t2)
end.

Definition minttoptr (TD:TargetData) (M:mem) (gv1:GenericValue) 
  : option GenericValue :=
  match GV2val TD gv1 with
  | Some (Vint wz1 i1) =>
      match Mem.int2ptr M (Int.signed wz1 i1) with
      | Some (b,ofs) => Some (ptr2GV TD (Vptr b (Int.repr 31 ofs)))
      | None => 
          Some (ptr2GV TD (Vinttoptr (Int.repr 31 (Int.unsigned wz1 i1))))
      end
  | _ => Some (gundef (typ_pointer typ_void))
  end.

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
| castop_inttoptr => 
  match (t1, t2) with
  | (typ_int sz1, typ_pointer _) => Some (gundef t2)
  | _ => Some (gundef t2)
  end
| castop_ptrtoint => 
  match (t1, t2) with
  | (typ_pointer _, typ_int sz2) => Some (gundef t2)
  | _ => Some (gundef t2)
  end
| castop_bitcase => mbitcast t1 gv1 t2 
end.

Definition mext (TD:TargetData) (op:extop) (t1:typ) (t2:typ) (gv1:GenericValue) 
  : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) => 
   match (GV2val TD gv1) with
   | Some (Vint wz1 i1) =>
     match op with
     | extop_z => Some (val2GV TD (Val.zero_ext (Size.to_Z sz2) (Vint wz1 i1)) 
                        (Mint (Size.to_nat sz2-1)))
     | extop_s => Some (val2GV TD (Val.sign_ext (Size.to_Z sz2) (Vint wz1 i1)) 
                        (Mint (Size.to_nat sz2-1)))
     | _ => Some (gundef t2)
     end
   | _ => Some (gundef t2)
   end
| (typ_floatpoint fp1, typ_floatpoint fp2) => 
  if floating_point_order fp1 fp2 
  then
    match (GV2val TD gv1) with
    | Some (Vfloat f1) =>
      match op with
      | extop_fp => Some gv1
      | _ => Some (gundef t2)
      end
    | _ => Some (gundef t2)
    end
  else Some (gundef t2)
| (_, _) => Some (gundef t2)
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
         Some (val2GV TD (Val.cmpu Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_uge => 
         Some (val2GV TD (Val.cmpu Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ult => 
         Some (val2GV TD (Val.cmpu Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ule => 
         Some (val2GV TD (Val.cmpu Cle (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sgt => 
         Some (val2GV TD (Val.cmp Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sge => 
         Some (val2GV TD (Val.cmp Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_slt => 
         Some (val2GV TD (Val.cmp Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sle => 
         Some (val2GV TD (Val.cmp Cle (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     end
  | _ => Some (gundef (typ_int 1))
  end.  

Definition micmp_ptr (TD:TargetData) (M:mem) (c:cond) (gv1 gv2:GenericValue) 
  : option GenericValue :=
  match (mptrtoint TD M gv1 Size.ThirtyTwo, mptrtoint TD M gv2 Size.ThirtyTwo)
    with
  | (Some gv1', Some gv2') => micmp_int TD c gv1' gv2'
  | _ => Some (gundef (typ_int 1))
  end.

Definition micmp (TD:TargetData) (c:cond) (t:typ) (gv1 gv2:GenericValue) 
  : option GenericValue :=
match t with
| typ_int sz => micmp_int TD c gv1 gv2
| typ_pointer _ => Some (gundef (typ_int 1))
| _ => Some (gundef (typ_int 1))
end.

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
     | fcond_ord => Some (gundef (typ_int 1)) (*FIXME: not supported yet. *)
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
     | fcond_uno => Some (gundef (typ_int 1)) (*FIXME: not supported yet. *)
     | fcond_true => Some (val2GV TD Vtrue (Mint 0))
     end in
   match fp with
   | fp_float => ov
   | fp_double => ov
   | _ => Some (gundef (typ_int 1)) (*FIXME: not supported 80 and 128 yet. *)
   end  
| _ => Some (gundef (typ_int 1))
end.

(**************************************)
(** Convert const to GV with storesize, and look up GV from operands. *)

Fixpoint repeatGV (gv:GenericValue) (n:nat) : GenericValue :=
match n with
| O => nil
| S n' => gv++repeatGV gv n'
end.

Fixpoint zeroconst2GV (TD:TargetData) (t:typ) : option GenericValue :=
match t with
| typ_int sz => 
  let wz := (Size.to_nat sz) - 1 in
  Some (val2GV TD (Vint wz (Int.repr wz 0)) (Mint wz))
| typ_floatpoint fp =>
  match fp with
  | fp_float => Some (val2GV TD (Vfloat Float.zero) Mfloat32)
  | fp_double => Some (val2GV TD (Vfloat Float.zero) Mfloat64)
  | _ => None (* FIXME: not supported 80 and 128 yet. *)
  end
| typ_void => None          
| typ_label => None                     
| typ_metadata => None                
| typ_array sz t => 
  match zeroconst2GV TD t with
  | Some gv0 =>
    match (getTypeStoreSize TD t, getTypeAllocSize TD t) with
    | (Some ssz, Some asz) => 
       Some (repeatGV (gv0++uninits (Size.to_nat asz - Size.to_nat ssz)) 
             (Size.to_nat sz))
    | _ => None 
    end
  | _ => None
  end
| typ_struct ts => 
  match zeroconsts2GV TD ts with
  | Some (gv0, tsz) => 
      match getTypeAllocSize TD t with
      | Some asz => 
          match ts with
          | Nil_list_typ => Some (uninits asz)
          | _ =>  Some (gv0++uninits (tsz - asz)) 
          end
      | None => None
      end
  | None => None
  end
| typ_pointer t' => Some null
| typ_function _ _ _ => None
| typ_opaque => None
| typ_namedt _ => None (*FIXME: Can zeroconstant be of named type? How about termination. *)
end             
with zeroconsts2GV (TD:TargetData) (lt:list_typ) 
  : option (GenericValue * nat) := 
match lt with
| Nil_list_typ => Some (nil, 0)
| Cons_list_typ t lt' =>
  match (zeroconsts2GV TD lt', zeroconst2GV TD t) with
  | (Some (gv, tsz), Some gv0) =>
       match (getTypeStoreSize TD t, getTypeAllocSize TD t) with
       | (Some ssz, Some asz) => Some (gv++gv0++uninits (asz - ssz), tsz+asz)
       | _ => None 
       end
  | _ => None
  end
end
.

Fixpoint _const2GV (TD:TargetData) (gl:GVMap) (c:const) 
  : option (GenericValue*typ) := 
match c with
| const_zeroinitializer t => 
  match zeroconst2GV TD t with
  | Some gv => Some (gv, t)
  | None => None
  end
| const_int sz n => 
         let wz := (Size.to_nat sz) - 1 in
         Some (val2GV TD (Vint wz (Int.repr wz (INTEGER.to_Z n))) (Mint wz), 
               typ_int sz)
| const_floatpoint fp f =>
         match fp with
         | fp_float => Some (val2GV TD (Vfloat f) Mfloat32, typ_floatpoint fp)
         | fp_double => Some (val2GV TD (Vfloat f) Mfloat64, typ_floatpoint fp)
         | _ => None (* FIXME: not supported 80 and 128 yet. *)
         end
| const_undef t =>  
         match (getTypeSizeInBits TD t) with
         | Some wz => Some (gundef t, t)
         | None => None
         end
| const_null t => 
         Some (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (Mint 31), 
               typ_pointer t)
| const_arr t lc => 
         match _list_const_arr2GV TD gl lc with
         | Some gv => Some (gv, 
                            typ_array (length (unmake_list_const lc)) t)
         | _ => None
         end
| const_struct lc =>
         match (_list_const_struct2GV TD gl lc) with
         | None => None
         | Some ((gv, ts), tsz) => 
             match getTypeAllocSize TD (typ_struct ts) with
             | Some asz => 
                 match lc with
                 | Nil_list_const => Some (uninits asz, typ_struct ts)
                 | _ =>  Some (gv++uninits (tsz - asz), typ_struct ts) 
                 end
             | None => None
             end
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
             | None => Some (gundef t2, t2)
             | Some idxs => 
               match (mgep TD t1 ptr idxs) with
               | Some ptr0 => Some (ptr2GV TD ptr0, t2)
               | None => Some (gundef t2, t2)
               end
             end
           | None => Some (gundef t2, t2)
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
end
with _list_const_arr2GV (TD:TargetData) (gl:GVMap) (cs:list_const) 
  : option GenericValue := 
match cs with
| Nil_list_const => Some nil
| Cons_list_const c lc' =>
  match (_list_const_arr2GV TD gl lc', _const2GV TD gl c) with
  | (Some gv, Some (gv0, t0)) =>
             match (getTypeStoreSize TD t0, getTypeAllocSize TD t0) with
             | (Some ssz0, Some asz0) => 
                 Some ((gv++gv0)++uninits (asz0 - ssz0))
             | _ => None 
             end
  | _ => None
  end
end
with _list_const_struct2GV (TD:TargetData) (gl:GVMap) (cs:list_const) 
  : option (GenericValue*list_typ*nat) := 
match cs with
| Nil_list_const => Some ((nil, Nil_list_typ), 0)
| Cons_list_const c lc' =>
  match (_list_const_struct2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, ts, tsz), Some (gv0,t0)) =>
       match (getTypeStoreSize TD t0, getTypeAllocSize TD t0) with
       | (Some ssz, Some asz) => 
            Some (gv++gv0++uninits (asz - ssz), Cons_list_typ t0 ts, tsz+asz)
       | _ => None 
       end
  | _ => None
  end
end
.

Definition cundef_gv gv c t : GenericValue :=
match t with
| typ_int sz => (Vint sz (Int.zero sz), c)::nil
| typ_floatpoint _ => (Vfloat Float.zero, c)::nil
| typ_pointer _ => null
| _ => gv
end.

Definition cgv2gv (gv:GenericValue) (t:typ) : GenericValue :=
match gv with
| (Vundef, c)::nil => cundef_gv gv c t
| _ => gv
end.

Notation "? gv # t ?" := (cgv2gv gv t) (at level 41).

Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GenericValue :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, t) => Some (? gv # t ?)
end.

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

Definition isOperandUndef (TD:TargetData) (t:typ) (v:value) (locals:GVMap) 
  (globals:GVMap) : Prop  := 
match (getOperandValue TD v locals globals) with
| Some gi => isGVUndef gi
| None => False
end.

(**************************************)
(* conversion between different lists *)

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

Fixpoint values2GVs (TD:TargetData) (lv:list_value) (locals:GVMap) 
  (globals:GVMap) : option (list GenericValue):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint intValues2Nats (TD:TargetData) (lv:list_value) (locals:GVMap)
  (globals:GVMap) : option (list Z):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
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

(**************************************)
(* helping functions *)

Fixpoint _initializeFrameValues (la:args) (lg:list GenericValue) (locals:GVMap) 
  : GVMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => 
  updateAddAL _ (_initializeFrameValues la' lg' locals) id g
| (((t, _), id)::la', nil) => 
  (* FIXME: We should initalize them w.r.t their type size. *)
  updateAddAL _ (_initializeFrameValues la' nil locals) id (gundef t)
| _ => locals
end.

Definition initLocals (la:args) (lg:list GenericValue): GVMap := 
_initializeFrameValues la lg nil.

Definition BOP (TD:TargetData) (lc gl:GVMap) (op:bop) (bsz:sz) 
  (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end
.

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

Definition GEP (TD:TargetData) (t:typ) (ma:GenericValue) 
  (vidxs:list GenericValue) (inbounds:bool) : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ma with
| Some ptr =>
  match GVs2Nats TD vidxs with
  | None => Some (gundef (typ_pointer typ_void))
  | Some idxs => 
    match (mgep TD t ptr idxs) with
    | Some ptr0 => Some (ptr2GV TD ptr0)
    | None => Some (gundef (typ_pointer typ_void))
    end
  end
| None => Some (gundef (typ_pointer typ_void))
end.

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

(*
Lemma GEP_inversion : forall (TD:TargetData) (t:typ) (ma:GenericValue) 
  (vidxs:list GenericValue) ib mptr0,
  GEP TD t ma vidxs ib = Some mptr0 ->
  exists idxs, exists ptr, exists ptr0, 
    GVs2Nats TD vidxs = Some idxs /\ 
    GV2ptr TD (getPointerSize TD) ma = Some ptr /\
    mgep TD t ptr idxs = Some ptr0 /\
    ptr2GV TD ptr0 = mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (GVs2Nats TD vidxs) as oidxs.
  remember (GV2ptr TD (getPointerSize TD) ma) as R.
  destruct R.
    destruct oidxs.
      remember (mgep TD t v l0) as og.
      destruct og; inversion H; subst.
        exists l0. exists v. exists v0. auto.
        exists l0. exists v. exists v0. auto.

Qed.
*)

Lemma intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0, 
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.
Proof.
  induction l0; intros; simpl in *.
    inversion H. exists nil. auto.

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

    destruct (getOperandValue TD v lc gl); try solve [inversion H].
      remember (values2GVs TD l0 lc gl)as ogv.
      destruct ogv; inversion H; subst.
        rewrite <- IHl0 with (gvs0:=l1); auto.
Qed.

Lemma const2GV_eqAL_aux : 
  (forall c gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    _const2GV TD gl1 c = _const2GV TD gl2 c) /\
  (forall cs gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    _list_const_arr2GV TD gl1 cs = _list_const_arr2GV TD gl2 cs /\
    _list_const_struct2GV TD gl1 cs = _list_const_struct2GV TD gl2 cs).
Proof.
  apply const_mutind; intros; simpl; 
  try solve [
    auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
      destruct H0; auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
    destruct H0;
    rewrite H1; auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
    destruct H0;
    rewrite H0; auto |

    rewrite H; auto |

    assert (J:=H1);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    destruct H1;
    rewrite H2; rewrite H1; erewrite H; eauto |

    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J;
    rewrite J; auto

  ].

  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
  rewrite H1. auto.

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
  intValues2Nats TD  l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

(*
Lemma GEP_eqAL : forall lc1 gl lc2 t ma vidxs ib TD,
  eqAL _ lc1 lc2 ->
  GEP TD lc1 gl t ma vidxs ib = GEP TD lc2 gl t ma vidxs ib.
Proof.
  intros lc1 gl lc2 t ma vidxs ib TD HeqAL.
  unfold GEP in *. auto.
  erewrite intValues2Nats_eqAL; eauto. 
Qed.
*)

(** allocate memory with size and alignment *)

Definition malloc (TD:TargetData) (M:mem) (bsz:sz) (gn:GenericValue) (al:align) 
  : option (mem * mblock)%type :=
match GV2int TD Size.ThirtyTwo gn with
| Some n => 
    if (Coqlib.zle 0 ((Size.to_Z bsz) * n)) then
      Some (Mem.alloc M 0 ((Size.to_Z bsz) * n))
    else None
| None => None
end.

Definition malloc_one (TD:TargetData) (M:mem) (bsz:sz) (al:align) 
  : option (mem * mblock)%type :=
if (Coqlib.zle 0 (Size.to_Z bsz)) then
  Some (Mem.alloc M 0 (Size.to_Z bsz))
else None.

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
  match (free TD Mem (blk2GV TD alloca)) with
  | Some Mem' => free_allocas TD Mem' allocas'
  | None => None
  end
end.

Definition mload (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (a:align) 
  : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match typ2memory_chunk t with
  | Some c => 
    match (Mem.load c M b (Int.signed 31 ofs)) with
    | Some v => Some (val2GV TD v c)
    | None => None
    end
  | _ => None
  end
| _ => None
end.

Definition mstore (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (gv:GenericValue) 
  (a:align) : option mem :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match typ2memory_chunk t, GV2val TD gv with
  | Some c, Some v => Mem.store c M b (Int.signed 31 ofs) v
  | _, _ => None
  end
| _ => None
end.

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
  exists n, GV2int TD Size.ThirtyTwo gn = Some n /\
    (0 <= (Size.to_Z tsz) * n)%Z /\
    Mem.alloc Mem0 0 (Size.to_Z tsz * n) = (Mem', mb).
Proof.
  intros.
  unfold malloc in H.
  destruct (GV2int TD Size.ThirtyTwo gn); try solve [inversion H; subst].
  destruct (Coqlib.zle 0 (Size.to_Z tsz * z)); inversion H; subst.
  exists z.
  destruct (Mem.alloc Mem0 0 (Size.to_Z tsz * z)).
  repeat (split; auto).
Qed.

Lemma store_inv : forall TD Mem0 gvp t gv align Mem',
  mstore TD Mem0 gvp t gv align = Some Mem' ->
  exists b, exists ofs, exists c, exists v0,
    GV2ptr TD (getPointerSize TD) gvp = Some (Vptr b ofs) /\
    typ2memory_chunk t = Some c /\
    GV2val TD gv = Some v0 /\
    Mem.store c Mem0 b (Int.signed 31 ofs) v0 = Some Mem'.
Proof.
  intros TD Mem0 gvp t gv align Mem' H.
  unfold mstore in H.
  destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H; subst].
  destruct v; try solve [inversion H; subst].
  destruct (typ2memory_chunk t); try solve [inversion H; subst].
  destruct (GV2val TD gv); try solve [inversion H; subst].
  exists b. exists i0. exists m. exists v. split; auto.
Qed.

End LLVMgv.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
