Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import assoclist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import sb_def.
Require Import symexe_def.
Require Import sb_tactic.
Require Import sub_tv.
Require Import sb_pp.

Module SBpass.

Export LLVMsyntax.
Export LLVMgv.

Definition simpl_typ (nts:namedts) (t:typ) : option typ :=
do ut <- typ2utyp nts t; ret (utyp2typ ut).

Definition getGEPTyp (nts:namedts) (idxs : list_value) (t : typ) : option typ :=
match idxs with
| Nil_list_value => None
| Cons_list_value idx idxs' =>
    do t <- simpl_typ nts t;
    (* The input t is already an element of a pointer typ *)
    do t' <- getSubTypFromValueIdxs idxs' t;
    ret (typ_pointer t')
end.

Definition getCmdTyp (nts:namedts) (i:cmd) : option typ :=
match i with
| insn_bop _ _ sz _ _ => Some (typ_int sz)
| insn_fbop _ _ ft _ _ => Some (typ_floatpoint ft)
(*
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ *)
| insn_extractvalue _ typ _ idxs => 
    do t <- simpl_typ nts typ;
    getSubTypFromConstIdxs idxs t
| insn_insertvalue _ typ _ _ _ _ => Some typ
| insn_malloc _ typ _ _ => Some (typ_pointer typ)
| insn_free _ typ _ => Some typ_void
| insn_alloca _ typ _ _ => Some (typ_pointer typ)
| insn_load _ typ _ _ => Some typ
| insn_store _ _ _ _ _ => Some typ_void
| insn_gep _ _ typ _ idxs => getGEPTyp nts idxs typ
| insn_trunc _ _ _ _ typ => Some typ
| insn_ext _ _ _ _ typ2 => Some typ2
| insn_cast _ _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_fcmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_select _ _ typ _ _ => Some typ
| insn_call _ true _ typ _ _ => Some typ_void
| insn_call _ false _ typ _ _ => Some typ
end.

Definition rmap := list (id*(id*id)).

Definition getFdefIDs fdef : ids :=
match fdef with
| fdef_intro (fheader_intro _ _ la) bs => 
  let '(_, ids0) := List.split la in
  ids0 ++ getBlocksIDs bs 
end.

Definition gen_metadata_id (ex_ids:ids) (rm:rmap) (id0:id) 
  : id * id * ids * rmap :=
let '(exist b _) := AtomImpl.atom_fresh_for_list ex_ids in
let '(exist e _) := AtomImpl.atom_fresh_for_list (b::ex_ids) in
(b, e, b::e::ex_ids, (id0,(b,e))::rm).

Fixpoint gen_metedata_cmds nts (ex_ids:ids) (rm:rmap) (cs:cmds) 
  : option(ids*rmap) :=
match cs with
| nil => Some (ex_ids,rm)
| c::cs' => 
   do t <- getCmdTyp nts c;
   if isPointerTypB t then
     let id0 := getCmdID c in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_cmds nts ex_ids' rm' cs'
   else gen_metedata_cmds nts ex_ids rm cs'
end.

Fixpoint gen_metedata_phinodes (ex_ids:ids) (rm:rmap) (ps:phinodes) : ids*rmap :=
match ps with
| nil => (ex_ids,rm)
| p::ps' => 
   let t := getPhiNodeTyp p in
   if isPointerTypB t then
     let id0 := getPhiNodeID p in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_phinodes ex_ids' rm' ps'
   else gen_metedata_phinodes ex_ids rm ps'
end.

Definition gen_metedata_block nts (ex_ids:ids) (rm:rmap) (b:block) 
  : option(ids*rmap) :=
let '(block_intro _ ps cs _) := b in
let '(ex_ids', rm') := gen_metedata_phinodes ex_ids rm ps in
gen_metedata_cmds nts ex_ids' rm' cs.

Fixpoint gen_metedata_blocks nts (ex_ids:ids) (rm:rmap) (bs:blocks) 
  : option(ids*rmap) :=
match bs with
| nil => Some (ex_ids,rm)
| b::bs' => 
    match gen_metedata_block nts ex_ids rm b with
    | Some (ex_ids',rm') => gen_metedata_blocks nts ex_ids' rm' bs'
    | None => None
    end
end.

Fixpoint gen_metedata_args (ex_ids:ids) (rm:rmap) (la:args) : ids*rmap :=
match la with
| nil => (ex_ids,rm)
| (t,id0)::la' => 
   if isPointerTypB t then
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_args ex_ids' rm' la'
   else gen_metedata_args ex_ids rm la'
end.

Definition gen_metedata_fdef nts (ex_ids:ids) (rm:rmap) (f:fdef) 
  : option(ids*rmap) :=
let '(fdef_intro (fheader_intro _ _ la) bs) := f in
let '(ex_ids', rm') := gen_metedata_args ex_ids rm la in
gen_metedata_blocks nts ex_ids' rm' bs.

Definition mk_tmp (ex_ids:ids) : id * ids :=
let '(exist tmp _) := AtomImpl.atom_fresh_for_list ex_ids in
(tmp, tmp::ex_ids).

Definition i8 := typ_int Size.Eight.
Definition i32 := typ_int Size.ThirtyTwo.
Definition p8 := typ_pointer i8.
Definition pp8 := typ_pointer p8.
Definition p32 := typ_pointer i32.
Definition int1 := const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 1%Z false).
Definition vint1 := value_const int1.
Definition c1 := Cons_list_value vint1 Nil_list_value.
Definition vnullp8 := value_const (const_null p8).
Definition vnullp32 := value_const (const_null p32).

Definition get_reg_metadata (rm:rmap) (v:value) : option (typ * value * value) :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some (bid, eid) => Some (p8, value_id bid, value_id eid)
      | None => None
      end
  | value_const c => 
      match (SoftBound.get_const_metadata c, Constant.getTyp c) with
      | (Some (bc, ec), Some t) => Some (t, value_const bc, value_const ec)
      | (None, Some t) => Some (t, value_const (const_null t), 
                                   value_const (const_null t))
      | _ => None
      end
  end.

Parameter assert_mptr_fid : id.
Parameter fake_id : id.
Parameter get_mmetadata_fid : id.
Parameter set_mmetadata_fid : id.

Definition assert_mptr_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ i32 Nil_list_typ))))))
      assert_mptr_fid).

Definition get_mmetadata_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ pp8 
        (Cons_list_typ pp8
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ p32 Nil_list_typ)))))))
      get_mmetadata_fid).

Definition set_mmetadata_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ i32 Nil_list_typ)))))))
      set_mmetadata_fid).

Definition prop_metadata (ex_ids tmps:ids) (optaddrb optaddre: option id) rm c v1
  id0 :=
  match (get_reg_metadata rm v1, lookupAL _ rm id0) with
  | (Some (t, bv, ev), Some (bid0, eid0)) =>
      Some (ex_ids, tmps,
        c::
        insn_cast bid0 castop_bitcast t bv p8:: 
        insn_cast eid0 castop_bitcast t ev p8:: 
        nil, 
        optaddrb, optaddre)
  | _ => None
  end.

Fixpoint trans_params (ex_ids tmps:ids) (rm:rmap) (lp:params) 
  : option (ids*ids*cmds*params) :=
match lp with
| nil => Some (ex_ids, tmps, nil, nil)
| (t0,v0) as p::lp' =>
    match trans_params ex_ids tmps rm lp' with
    | None => None
    | Some (ex_ids',tmps',cs,lp2) =>
      if isPointerTypB t0 then
        match get_reg_metadata rm v0 with
        | Some (mt, bv0, ev0) =>
            let '(btmp,ex_ids') := mk_tmp ex_ids' in
            let '(etmp,ex_ids') := mk_tmp ex_ids' in
            Some (
               ex_ids',
               btmp::etmp::tmps',
               insn_cast btmp castop_bitcast mt bv0 p8:: 
               insn_cast etmp castop_bitcast mt ev0 p8:: 
               cs,
               (p8,value_id btmp)::(p8,value_id etmp)::lp2
             )
        | _ => None
        end
      else Some (ex_ids',tmps',cs,lp2)
    end
end.

Axiom isSysLib : id -> bool.

Definition type_size t :=
  value_const
    (const_castop 
      castop_ptrtoint 
      (const_gep false 
        (const_null t) 
        (Cons_list_const int1 Nil_list_const))
      (typ_int Size.ThirtyTwo)
    ).

Definition trans_cmd (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap) 
  (c:cmd) : option (ids*ids*cmds*option id*option id) :=
match c with 
| insn_malloc id0 t1 v1 al1 | insn_alloca id0 t1 v1 al1 =>
    match lookupAL _ rm id0 with
    | Some (bid, eid) =>
      let '(tmp,ex_ids') := mk_tmp ex_ids in
      Some (ex_ids', tmp::tmps,
       c::
       insn_cast bid castop_bitcast (typ_pointer t1) (value_id id0) p8:: 
       insn_gep tmp false t1 (value_id id0) 
         (Cons_list_value v1 Nil_list_value) :: 
       insn_cast eid castop_bitcast (typ_pointer t1) (value_id tmp) p8:: 
       nil,
       optaddrb, optaddre)
    | _ => None
    end

| insn_load id0 t2 v2 align => 
    match get_reg_metadata rm v2 with
    | Some (mt, bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(btmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      let '(optcs, ex_ids, tmps, optaddrb, optaddre) := 
        if isPointerTypB t2 then
          match lookupAL _ rm id0 with
          | Some (bid0, eid0) =>
              match (optaddrb, optaddre) with
              | (Some addrb, Some addre) =>
                   (Some
                     (insn_call fake_id true false typ_void get_mmetadata_fn 
                       ((p8,(value_id ptmp))::
                        (pp8,(value_id addrb))::
                        (pp8,(value_id addre))::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
                      insn_load bid0 p8 (value_id addrb) Align.Zero::
                      insn_load eid0 p8 (value_id addre) Align.Zero::   
                      nil), ex_ids, tmps, Some addrb, Some addre)
              | (None, None) =>
                   let '(addrb,ex_ids) := mk_tmp ex_ids in
                   let '(addre,ex_ids) := mk_tmp ex_ids in
                   (Some
                     (insn_call fake_id true false typ_void get_mmetadata_fn 
                       ((p8,(value_id ptmp))::
                        (pp8,(value_id addrb))::
                        (pp8,(value_id addre))::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
                      insn_load bid0 p8 (value_id addrb) Align.Zero::
                      insn_load eid0 p8 (value_id addre) Align.Zero::   
                      nil), ex_ids, addrb::addre::tmps, Some addrb, Some addre)
              | _ => (None, ex_ids, tmps, optaddrb, optaddre)
              end
          | None => (None, ex_ids, tmps, optaddrb, optaddre)
          end
        else (Some nil, ex_ids, tmps, optaddrb, optaddre) in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids, ptmp::btmp::etmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t2) v2 p8:: 
         insn_cast btmp castop_bitcast mt bv p8:: 
         insn_cast etmp castop_bitcast mt ev p8:: 
         insn_call fake_id true false typ_void assert_mptr_fn 
           ((p8,(value_id ptmp))::
            (p8,(value_id btmp))::
            (p8,(value_id etmp))::
            (i32,type_size t2)::
            (i32,vint1)::nil)::
         c::
         cs, optaddrb, optaddre)
      end
    | None => None
    end

| insn_store id0 t0 v1 v2 align =>
    match get_reg_metadata rm v2 with
    | Some (mt2, bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(btmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      let optcs := 
        if isPointerTypB t0 then
          match get_reg_metadata rm v1 with
          | Some (mt1, bv0, ev0) =>
              Some
                (insn_call fake_id true false typ_void set_mmetadata_fn 
                  ((p8,(value_id ptmp))::
                   (p8,bv0)::
                   (p8,ev0)::
                   (p8,vnullp8)::
                   (i32,vint1)::
                   (i32,vint1)::
                   nil)::
                 nil)
          | None => None
          end
        else Some nil in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids, ptmp::btmp::etmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t0) v2 p8:: 
         insn_cast btmp castop_bitcast mt2 bv p8:: 
         insn_cast etmp castop_bitcast mt2 ev p8:: 
         insn_call fake_id true false typ_void assert_mptr_fn 
           ((p8,(value_id ptmp))::
            (p8,(value_id btmp))::
            (p8,(value_id etmp))::
            (i32,(type_size t0))::
            (i32,vint1)::nil)::
         c::
         cs, optaddrb, optaddre)
      end
    | None => None
    end

| insn_gep id0 inbounds0 t1 v1 lv2 => 
    prop_metadata ex_ids tmps optaddrb optaddre rm c v1 id0

| insn_cast id0 op0 t1 v1 t2 => 
    match op0 with
    | castop_bitcast =>
        if isPointerTypB t1 then
          prop_metadata ex_ids tmps optaddrb optaddre rm c v1 id0
        else Some (ex_ids, tmps, [c], optaddrb, optaddre)
    | castop_inttoptr =>
        match lookupAL _ rm id0 with
        | Some (bid0, eid0) =>
            Some (ex_ids, tmps,
              c::
              insn_cast bid0 castop_bitcast p8 vnullp8 p8::
              insn_cast eid0 castop_bitcast p8 vnullp8 p8::
              nil, optaddrb, optaddre)
        | _ => None
        end
    | _ => Some (ex_ids, tmps, [c], optaddrb, optaddre)
    end

| insn_select id0 v0 t0 v1 v2 =>
    if isPointerTypB t0 then
      match (get_reg_metadata rm v1, get_reg_metadata rm v2, 
             lookupAL _ rm id0) with
      | (Some (mt1, bv1, ev1), Some (mt2, bv2, ev2), Some (bid0, eid0)) =>
          Some (ex_ids, tmps,
            c::
            insn_select bid0 v0 mt1 bv1 bv2:: 
            insn_select eid0 v0 mt1 ev1 ev2:: 
            nil, optaddrb, optaddre)
      | _ => None
      end
    else Some (ex_ids, tmps, [c], optaddrb, optaddre)

| insn_call id0 noret0 tailc0 rt fv lp =>
    match
      (match fv with
       | value_const (const_gid _ fid) =>
           if isSysLib fid then 
             Some (ex_ids, tmps, nil, nil) 
           else trans_params ex_ids tmps rm lp
       | _ => trans_params ex_ids tmps rm lp
       end) with
    | Some (ex_ids', tmps', cs, lp') =>
        Some (ex_ids', tmps', cs++[insn_call id0 noret0 tailc0 rt fv (lp++lp')],
              optaddrb, optaddre)
    | None => None
    end

| _ => Some (ex_ids, tmps, [c], optaddrb, optaddre)
end.

Fixpoint trans_cmds (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap) 
  (cs:cmds) : option (ids*ids*cmds*option id*option id) :=
match cs with
| nil => Some (ex_ids, tmps, nil, optaddrb, optaddre)
| c::cs' =>
    match (trans_cmd ex_ids tmps optaddrb optaddre rm c) with
    | Some (ex_ids1, tmps1, cs1, optaddrb, optaddre) =>
        match (trans_cmds ex_ids1 tmps1 optaddrb optaddre rm cs') with
        | Some (ex_ids2, tmps2, cs2, optaddrb, optaddre) => 
            Some (ex_ids2, tmps2, cs1++cs2, optaddrb, optaddre)
        | _ => None
        end
    | _ => None
    end
end.

Fixpoint get_metadata_from_list_value_l (rm:rmap) (vls:list_value_l) 
  (baccum eaccum : list_value_l): option (list_value_l * list_value_l) :=
match vls with
| Nil_list_value_l => Some (baccum, eaccum)
| Cons_list_value_l v0 l0 vls' => 
    match get_reg_metadata rm v0 with
    | Some (mt, bv, ev) =>
        get_metadata_from_list_value_l rm vls' 
          (Cons_list_value_l bv l0 baccum) (Cons_list_value_l ev l0 eaccum)
    | _ => None
    end
end.

Fixpoint trans_phinodes (rm:rmap) (ps:phinodes) : option phinodes :=
match ps with
| nil => Some nil
| (insn_phi id0 t0 vls0 as p)::ps' =>
    match trans_phinodes rm ps' with
    | None => None
    | Some ps2 =>
        if isPointerTypB t0 then
          match (get_metadata_from_list_value_l rm vls0 Nil_list_value_l 
                 Nil_list_value_l,
                lookupAL _ rm id0) with
          | (Some (bvls0, evls0), Some (bid0, eid0)) => 
              Some (p::insn_phi bid0 p8 bvls0::insn_phi eid0 p8 evls0::ps2)
          | _ => None
          end
        else Some (p::ps2)
    end
end.

Definition trans_block (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap)
  (b:block) : option (ids*ids*option id*option id*block) :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
match trans_phinodes rm ps1 with
| None => None
| Some ps2 => 
    match trans_cmds ex_ids tmps optaddrb optaddre rm cs1 with
    | Some (ex_ids',tmps',cs2,optaddrb,optaddre) => 
        Some (ex_ids',tmps',optaddrb,optaddre,block_intro l1 ps2 cs2 tmn1)
    | None => None
    end
end.

Fixpoint trans_blocks (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap) 
  (bs:blocks) : option (ids*ids*option id*option id*blocks) :=
match bs with
| nil => Some (ex_ids, tmps, optaddrb, optaddre, nil)
| b::bs' =>
    match (trans_block ex_ids tmps optaddrb optaddre rm b) with
    | Some (ex_ids1, tmps1, optaddrb, optaddre, b1) =>
        match (trans_blocks ex_ids1 tmps1 optaddrb optaddre rm bs') with
        | Some (ex_ids2, tmps2, optaddrb, optaddre, bs2) => 
            Some (ex_ids2, tmps2, optaddrb, optaddre, b1::bs2)
        | _ => None
        end
    | _ => None
    end
end.

Fixpoint trans_args (rm:rmap) (la:args) : option args :=
match la with
| nil => Some nil
| (t0,id0) as a::la' =>
    match trans_args rm la' with
    | None => None
    | Some la2 =>
      if isPointerTypB t0 then
        match (lookupAL _ rm id0) with
        | Some (bid0, eid0) => 
            Some ((p8,bid0)::(p8,eid0)::la2)
        | _ => None
        end
      else Some la2
    end
end.

Definition insert_more_allocas (optaddrb optaddre:option id) (b:block) : block :=
match (optaddrb, optaddre) with
| (Some addrb, Some addre) =>
  let '(block_intro l1 ps1 cs1 tmn1) := b in  
  block_intro l1 ps1
    (insn_alloca addrb p8 vint1 Align.Zero::
    insn_alloca addre p8 vint1 Align.Zero::cs1) tmn1
| _ => b
end.

Axiom rename_fid : id -> id.

Definition trans_fdef nts (f:fdef) : option (rmap*ids*fdef) :=
let '(fdef_intro (fheader_intro t fid la) bs) := f in
if SimpleSE.isCallLib fid then Some (nil, nil, f)
else
  let ex_ids := getFdefIDs f in
  match gen_metedata_fdef nts ex_ids nil f with
  | Some (ex_ids,rm) =>
      match (trans_args rm la) with
      | Some la' =>
          match (trans_blocks ex_ids nil None None rm bs) with
          | Some (ex_ids, tmps, optaddrb, optaddre, b'::bs') => 
              Some (rm, tmps, 
                fdef_intro 
                  (fheader_intro t (rename_fid fid) (la++la')) 
                  ((insert_more_allocas optaddrb optaddre b')::bs'))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Fixpoint trans_product nts (p:product) : option product :=
match p with
| product_fdef f =>
    match trans_fdef nts f with
    | None => None
    | Some (_,_,f') => Some (product_fdef f')
    end
| _ => Some p
end.

Fixpoint trans_products nts (ps:products) : option products :=
match ps with
| nil => Some nil
| p::ps' =>
    match (trans_product nts p) with
    | Some p1 =>
        match (trans_products nts ps') with
        | Some ps2 => Some (p1::ps2)
        | _ => None
        end
    | _ => None
    end
end.

Definition trans_module (m:module) : option module :=
let '(module_intro los nts ps) := m in
do ps' <- trans_products nts ps;
ret (module_intro los nts ps').

Fixpoint trans_system (ms:system) : option system :=
match ms with
| nil => Some nil
| m::ms' =>
    match (trans_module m) with
    | Some m1 =>
        match (trans_system ms') with
        | Some ms2 => Some (m1::ms2)
        | _ => None
        end
    | _ => None
    end
end.

(* Simulation *)

Definition gv_inject (mi: Values.meminj) (gv gv':GenericValue) : Prop :=
let '(vals,mks) := List.split gv in 
let '(vals',mks') := List.split gv' in 
val_list_inject mi vals vals' /\ mks = mks'.

Definition reg_simulation (mi:Values.meminj) TD gl (rm1:SoftBound.rmetadata) 
  (rm2:rmap) Mem1 Mem2 (lc1 lc2:GVMap) : Prop :=
(forall i0 gv1, 
  lookupAL _ lc1 i0 = Some gv1 -> 
  exists gv2, 
    lookupAL _ lc2 i0 = Some gv2 /\ gv_inject mi gv1 gv2
) /\
(forall vp bgv1 egv1, 
  SoftBound.get_reg_metadata TD Mem1 gl rm1 vp = 
    Some (SoftBound.mkMD bgv1 egv1) -> 
  exists t2, exists bv2, exists ev2, exists bgv2, exists egv2,
    get_reg_metadata rm2 vp = Some (t2, bv2, ev2) /\
    getOperandValue TD Mem2 bv2 lc2 gl = Some bgv2 /\
    getOperandValue TD Mem2 ev2 lc2 gl = Some egv2 /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2
) /\
(forall pid bid eid bgv2 egv2, 
  lookupAL _ rm2 pid = Some (bid, eid) ->
  lookupAL _ lc2 bid = Some bgv2 ->
  lookupAL _ lc2 eid = Some egv2 ->
  exists bgv1, exists egv1,
    lookupAL _ rm1 pid = Some (SoftBound.mkMD bgv1 egv1) /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2
).

Definition mem_simulation (mi:Values.meminj) TD (MM1:SoftBound.mmetadata) 
  (Mem1 Mem2:mem) : Prop :=
Mem.mem_inj mi Mem1 Mem2 /\
(forall lc2 gl pgv bgv egv als addrb addre bid0 eid0 v pgv',  
  SoftBound.get_mem_metadata TD MM1 pgv = SoftBound.mkMD bgv egv -> 
  gv_inject mi pgv pgv' ->
  getOperandValue TD Mem2 v lc2 gl = Some pgv' ->
  exists bgv', exists egv', exists Mem2',
  SimpleSE.dbCmds TD gl lc2 als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als Mem2' 
     trace_nil /\
    gv_inject mi bgv bgv' /\
    gv_inject mi egv egv' /\
    Mem.mem_inj Memdata.inject_id Mem2 Mem2'
) /\
(forall gl b2 i2 bgv' egv' als lc2 lc2' addrb addre bid0 eid0 v Mem2', 
  getOperandValue TD Mem2 v lc2 gl = Some (ptr2GV TD (Vptr b2 i2)) ->
  SimpleSE.dbCmds TD gl lc2 als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc2' als Mem2' trace_nil ->
  lookupAL _ lc2' bid0 = Some bgv' ->
  lookupAL _ lc2' eid0 = Some egv' ->
  exists bgv, exists egv, exists b1, exists i1,
    MM1 b1 i1 = Some (SoftBound.mkMD bgv egv) /\
    Values.val_inject mi (Vptr b1 i1) (Vptr b2 i2) /\
    gv_inject mi bgv bgv' /\
    gv_inject mi egv egv' /\
    Mem.mem_inj mi Mem2 Mem2'
).

Fixpoint codom (rm:rmap) : atoms :=
match rm with
| nil => empty
| (_,(bid,eid))::rm' => singleton bid `union` singleton eid `union` codom rm'
end.

Lemma in_codom_of_rmap : forall rm2 pid bid eid,
  lookupAL (id * id) rm2 pid = ret (bid, eid) ->
  bid `in` codom rm2 /\ eid `in` codom rm2.
Proof.
  induction rm2; intros pid bid eid J.
    inversion J.  

    simpl in J.
    destruct a.
    destruct (pid == a); subst.
      inv J.
      simpl. auto.

      apply IHrm2 in J.
      destruct J as [J1 J2].
      simpl. destruct p.
      auto.
Qed.

Lemma reg_simulation__updateAddAL : forall mi TD gl M1 M2 rm1 rm2 lc1 lc2 i0 gv 
    gv',
  reg_simulation mi TD gl rm1 rm2 M1 M2 lc1 lc2 ->
  i0 `notin` codom rm2 ->
  gv_inject mi gv gv' ->
  reg_simulation mi TD gl rm1 rm2 M1 M2 (updateAddAL GenericValue lc1 i0 gv)
    (updateAddAL GenericValue lc2 i0 gv').
Proof.
  intros mi TD gl M1 M2 rm1 rm2 lc1 lc2 i0 gv gv' Hsim Hnotin. 
  destruct Hsim as [J1 [J2 J3]].    
  split.
    intros i1 gv1 J.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in *; auto.
      inv J.
      exists gv'. auto.
    
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
  split.
    intros vp bgv1 egv1 J.
    apply J2 in J. 
    destruct J as [t2 [bv2 [ev2 [bgv2 [egv2 [J11 [J12 [J13 [J14 J15]]]]]]]]].
    exists t2. exists bv2. exists ev2. exists bgv2. exists egv2.
    split; auto.
    destruct vp as [pid |]; simpl in J11.
      case_eq (lookupAL (id * id) rm2 pid).
        intros [bid eid] J.
        rewrite J in J11.    
        inv J11.
        simpl.
        assert (J':=J).
        apply in_codom_of_rmap in J'.    
        destruct J' as [J16 J17].      
        rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
        rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
        repeat (split; auto).

        intro J.
        rewrite J in J11. inversion J11.

      case_eq (SoftBound.get_const_metadata c).
        intros [bid eid] J.
        rewrite J in J11.
        destruct (Constant.getTyp c); inv J11.
        simpl in *.
        repeat (split; auto).

        intro J.  rewrite J in J11.
        destruct (Constant.getTyp c); inv J11.
        simpl in *.
        repeat (split; auto).

    intros pid bid eid bgv2 egv2 H1 H2 H3.
    assert (H1':=H1).
    apply in_codom_of_rmap in H1'.    
    destruct H1' as [H11 H12].
    rewrite <- lookupAL_updateAddAL_neq in H2; try solve [fsetdec].
    rewrite <- lookupAL_updateAddAL_neq in H3; try solve [fsetdec].
    eauto.
Qed.

Lemma _zeroconst2GV__gv_inject_refl : forall TD t gv mi,
  _zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
Admitted.

Lemma gv_inject__eq__sizeGenericValue : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Admitted.

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Admitted.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Admitted.

Lemma global_gv_inject_refl : forall mi gl i0 gv,
  lookupAL _ gl i0 = Some gv ->
  gv_inject mi gv gv.
Admitted.
    
Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mtrunc TD top t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__mext : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mext TD eop t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__mbop : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mfbop : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mcast : forall mi TD Mem1 Mem2 op t1 gv1 gv1' t2 gv2,
  gv_inject mi gv1 gv1' ->
  Mem.mem_inj mi Mem1 Mem2 ->  
  mcast TD Mem1 op t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mcast TD Mem2 op t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__micmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mfcmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__GV2ptr : forall mi TD gv1 gv1' v,
  gv_inject mi gv1 gv1' ->
  GV2ptr TD (getPointerSize TD) gv1 = Some v ->
  exists v',
    GV2ptr TD (getPointerSize TD) gv1' = Some v' /\
    Values.val_inject mi v v'.
Admitted.

Lemma simulation__mgep : forall mi TD v v' v0 t0 l1,
  Values.val_inject mi v v' ->
  mgep TD t0 v l1 = Some v0 ->
  exists v0',
    mgep TD t0 v' l1 = Some v0' /\
    Values.val_inject mi v0 v0'.
Admitted.
   
Lemma gv_inject__eq__isGVZero : forall mi TD gv gv',
  gv_inject mi gv gv' ->
  isGVZero TD gv = isGVZero TD gv'.
Admitted.

Lemma simulation__extractGenericValue : forall mi gv1 gv1' TD t1 l0 gv,
  gv_inject mi gv1 gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  exists gv',
    extractGenericValue TD t1 gv1' l0 = Some gv' /\
    gv_inject mi gv gv'.
Admitted.

Lemma simulation__insertGenericValue : forall mi gv1 gv1' TD t1 l0 gv t2 gv2 
                                              gv2',
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  exists gv',
    insertGenericValue TD t1 gv1' l0 t2 gv2' = Some gv' /\
    gv_inject mi gv gv'.
Admitted.

Definition sb_mem_inj__const2GV_prop (c:const) := forall mi Mem1 Mem2 TD gl gv t,
  Mem.mem_inj mi Mem1 Mem2 ->
  _const2GV TD Mem1 gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD Mem2 gl c = Some (gv',t) /\
    gv_inject mi gv gv'.

Definition sb_mem_inj__list_const2GV_prop (lc:list_const) := 
  forall mi Mem1 Mem2 TD gl,
  Mem.mem_inj mi Mem1 Mem2 ->
  (forall gv t, 
    _list_const_arr2GV TD Mem1 gl lc = Some (gv,t) ->
    exists gv',
      _list_const_arr2GV TD Mem2 gl lc = Some (gv',t) /\
      gv_inject mi gv gv'
  ) /\
  (forall gv t a, 
    _list_const_struct2GV TD Mem1 gl lc = Some (gv,t,a) ->
    exists gv',
      _list_const_struct2GV TD Mem2 gl lc = Some (gv',t,a) /\
      gv_inject mi gv gv'
  ).

Lemma sb_mem_inj__const2GV_mutrec :
  (forall c, sb_mem_inj__const2GV_prop c) *
  (forall lc, sb_mem_inj__list_const2GV_prop lc).
Proof.
  apply const_mutrec; 
    unfold sb_mem_inj__const2GV_prop, sb_mem_inj__list_const2GV_prop;
    intros; simpl in *; eauto.

  remember (_zeroconst2GV TD t) as R.
  destruct R; inv H0.
  exists gv. split; eauto using _zeroconst2GV__gv_inject_refl.

  inv H0.
  exists (val2GV TD
            (Vint (Size.to_nat s - 1)
               (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z i0)))
            (AST.Mint (Size.to_nat s - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

  destruct f; inv H0.
    exists (val2GV TD (Vfloat f0) AST.Mfloat32).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

    exists (val2GV TD (Vfloat f0) AST.Mfloat64).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

  remember (getTypeSizeInBits TD t) as R.
  destruct R; inv H0.
  exists (val2GV TD Vundef (AST.Mint (n - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
  
  inv H0.
  exists (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (AST.Mint 31)).
  split; auto. 
    unfold val2GV, gv_inject; simpl.
    split; auto.
      apply val_cons_inject; auto.
      apply val_inject_ptr with (delta:=0); auto.
      admit. (* mi should map null to null. *)
 
  apply H with (TD:=TD)(gl:=gl) in H0.
  destruct H0; eauto.

  apply H with (TD:=TD)(gl:=gl) in H0.
  destruct H0 as [H00 H01].
  remember (_list_const_struct2GV TD Mem1 gl l0) as R.
  destruct R as [[[gv1 t1] a1]|]; inv H1.
  destruct (@H01 gv1 t1 a1) as [gv' [H02 H03]]; auto.
  rewrite H02; auto.
  erewrite <- gv_inject__eq__sizeGenericValue; eauto.
  remember (sizeGenericValue gv1) as R1.
  destruct R1; inv H2.
    exists (uninits (Align.to_nat a1)).
    split; auto.
      unfold uninits, gv_inject; simpl; auto.

    exists (gv' ++ uninits (Align.to_nat a1 - S R1)).
    split; auto.
      unfold uninits.
      apply gv_inject_app; auto.
        unfold gv_inject; simpl; auto.       

  remember (lookupAL GenericValue gl i0) as R.
  destruct R; inv H0.
  exists gv. split; eauto using global_gv_inject_refl.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1']|]; inv H1.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mtrunc TD t t1' gv1 t0) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mtrunc in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1']|]; inv H1.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mext TD e t1' gv1 t) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mext in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.

  remember (_const2GV TD Mem1 gl c0) as R.
  destruct R as [[gv1 t1']|]; inv H1.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mcast TD Mem1 c t1' gv1 t) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mcast in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.

  remember (Constant.getTyp c) as R.
  destruct R; inv H2.       
  destruct t0; inv H4.       
  remember (_const2GV TD Mem1 gl c) as R1.
  destruct R1 as [[gv1 t1]|]; inv H3.
  remember (getConstGEPTyp l0 t0) as R2.
  destruct R2; inv H4.
  remember (GV2ptr TD (getPointerSize TD) gv1) as R3.
  destruct R3; inv H3.
  remember (intConsts2Nats TD l0) as R4.
  destruct R4; inv H4.
  remember (mgep TD t0 v l1) as R5.
  destruct R5; inv H3.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  destruct HeqR1 as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3.
  eapply simulation__GV2ptr in HeqR3; eauto.
  destruct HeqR3 as [v' [J3 J4]].
  rewrite J3.  
  symmetry in HeqR5.
  eapply simulation__mgep in HeqR5; eauto.
  destruct HeqR5 as [v0' [J5 J6]].
  rewrite J5.
  exists (ptr2GV TD v0').
  split; auto.
    unfold ptr2GV, val2GV, gv_inject. simpl. auto.

  remember (_const2GV TD Mem1 gl c) as R2.
  destruct R2 as [[gv2 t2]|]; inv H3.
  remember (_const2GV TD Mem1 gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; inv H5.
  remember (_const2GV TD Mem1 gl c2) as R4.
  destruct R4 as [[gv4 t4]|]; inv H4.
  symmetry in HeqR2. 
  eapply H in HeqR2; eauto.
  destruct HeqR2 as [gv2' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3. 
  eapply H0 in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H1 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  erewrite <- gv_inject__eq__isGVZero; eauto.
  destruct (isGVZero TD gv2); inv H5.
    exists gv4'. split; auto.
    exists gv3'. split; auto.

  remember (_const2GV TD Mem1 gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  remember (_const2GV TD Mem1 gl c2) as R4.
  destruct R4 as [[gv4 t4]|]; inv H4.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (micmp TD c t3 gv3 gv4) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__micmp in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  destruct t3; inv H4.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mfcmp TD f f0 gv3 gv4) as R1.
  destruct R1; inv H4.
  symmetry in HeqR1.
  eapply simulation__mfcmp in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.
     
  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H2.
  remember (Constant.getTyp c) as R1.
  destruct R1; inv H4.       
  remember (getSubTypFromConstIdxs l0 t0) as R2.
  destruct R2; inv H3.   
  remember (extractGenericValue TD t1 gv1 l0) as R3.
  destruct R3; inv H4.   
  symmetry in HeqR. 
  eapply H in HeqR; eauto.
  destruct HeqR as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3.
  eapply simulation__extractGenericValue in HeqR3; eauto.
  destruct HeqR3 as [gv' [J3 J4]].
  rewrite J3.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H3.
  remember (_const2GV TD Mem1 gl c0) as R2.
  destruct R2 as [[gv2 t2]|]; inv H5.
  remember (Constant.getTyp c0) as R1.
  destruct R1; inv H4.       
  remember (insertGenericValue TD t1 gv1 l0 t2 gv2) as R3.
  destruct R3; inv H5.   
  symmetry in HeqR. 
  eapply H in HeqR; eauto.
  destruct HeqR as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2. 
  eapply H0 in HeqR2; eauto.
  destruct HeqR2 as [gv2' [J3 J4]].
  rewrite J3.
  symmetry in HeqR3.
  eapply simulation__insertGenericValue in HeqR3; eauto.
  destruct HeqR3 as [gv' [J5 J6]].
  rewrite J5.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  destruct t3; inv H4.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mbop TD b s gv3 gv4) as R1.
  destruct R1; inv H4.
  symmetry in HeqR1.
  eapply simulation__mbop in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  destruct t3; inv H4.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mfbop TD f f0 gv3 gv4) as R1.
  destruct R1; inv H4.
  symmetry in HeqR1.
  eapply simulation__mfbop in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  split.
    intros gv t J.
    inv J.
    exists nil. unfold gv_inject. simpl. split; auto.
 
    intros gv t a J.
    inv J.
    exists nil. unfold gv_inject. simpl. split; auto.  

  assert (H1':=H1).
  apply H0 with (TD:=TD)(gl:=gl) in H1'.
  destruct H1' as [H10 H11].
  split; intros.
    remember (_list_const_arr2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[gv3 t3]|]; inv H2.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H4.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    destruct HeqR4 as [gv4' [J1 J2]].
    rewrite J1.
    destruct (@H10 gv3 t3) as [gv3' [J3 J4]]; auto.
    rewrite J3.
    destruct (getTypeAllocSize TD t4); inv H3.
    exists ((gv3' ++ gv4') ++ uninits (s - sizeGenericValue gv4')).
    erewrite <- gv_inject__eq__sizeGenericValue; eauto.
    split; auto.    
      apply gv_inject_app.
        apply gv_inject_app; auto.
          unfold uninits, gv_inject. simpl. auto.

    remember (_list_const_struct2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[[gv3 t3] a3]|]; inv H2.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H4.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    destruct HeqR4 as [gv4' [J1 J2]].
    rewrite J1.
    symmetry in HeqR3.
    destruct (@H11 gv3 t3 a3) as [gv3' [J3 J4]]; auto.
    rewrite J3.
    destruct (getABITypeAlignment TD t4); inv H3.
    destruct (getTypeAllocSize TD t4); inv H4.
    exists (gv3' ++
            [(Vundef, AST.Mint ((n - sizeGenericValue gv4') * 8 - 1))]
            ++ gv4' ++ uninits (s - sizeGenericValue gv4')).
    erewrite <- gv_inject__eq__sizeGenericValue; eauto.
    destruct (le_lt_dec n (Align.to_nat a3)); inv H3.
      simpl_env.
      split; auto.
        apply gv_inject_app; auto.
         apply gv_inject_app; auto.
            unfold gv_inject. simpl. auto.
         apply gv_inject_app; auto.
            unfold uninits, gv_inject. simpl. auto.

      simpl_env.
      split; auto.
        apply gv_inject_app; auto.
         apply gv_inject_app; auto.
            unfold gv_inject. simpl. auto.
         apply gv_inject_app; auto.
            unfold uninits, gv_inject. simpl. auto.
Qed.

Lemma sb_mem_inj___const2GV : forall mi Mem1 Mem2 TD gl c gv t,
  Mem.mem_inj mi Mem1 Mem2 ->
  _const2GV TD Mem1 gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD Mem2 gl c = Some (gv',t) /\
    gv_inject mi gv gv'.
Proof.
  destruct sb_mem_inj__const2GV_mutrec as [J _].
  unfold sb_mem_inj__const2GV_prop in J. eauto.
Qed.

Lemma sb_mem_inj__const2GV : forall mi Mem Mem' TD gl c gv,
  Mem.mem_inj mi Mem Mem' ->
  const2GV TD Mem gl c = Some gv ->
  exists gv',
    const2GV TD Mem' gl c = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros.
  unfold const2GV in *.
  remember (_const2GV TD Mem0 gl c) as R.
  destruct R; try solve [inversion H0].
  destruct p.
  inv H0.
  symmetry in HeqR.
  eapply sb_mem_inj___const2GV in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  exists gv'. rewrite J1. auto.
Qed.

Lemma simulation__getOperandValue : forall mi rm rm2 lc lc2 TD MM Mem Mem2 gl v 
                                           gv,
  reg_simulation mi TD gl rm rm2 Mem Mem2 lc lc2 ->
  mem_simulation mi TD MM Mem Mem2 ->
  getOperandValue TD Mem v lc gl = ret gv ->
  exists gv', 
    getOperandValue TD Mem2 v lc2 gl = ret gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi rm rm2 lc lc2 TD MM Mem Mem2 gl v gv H1 H2 H3.
  unfold getOperandValue in *.
  destruct v.
    destruct H1 as [H1 _]; auto.

    destruct H2 as [H2 _].
    eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__BOP : forall mi rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 
                        gv3,
  reg_simulation mi TD gl rm rm2 Mem Mem2 lc lc2 ->
  mem_simulation mi TD MM Mem Mem2 ->
  BOP TD Mem lc gl bop0 sz0 v1 v2 = ret gv3 ->
  exists gv3',
    BOP TD Mem2 lc2 gl bop0 sz0 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof.  
  intros mi rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 gv3 H1 H2 H3.
  unfold BOP in *.
  remember (getOperandValue TD Mem v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD Mem v2 lc gl) as R2.
  destruct R2; inv H0.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__mbop in H3; eauto.
Qed.

Lemma alloc__const2GV_inv : forall Mem2 lo hi Mem2' mb2 c TD gl gv t,
  Mem.alloc Mem2 lo hi = (Mem2', mb2) ->
  _const2GV TD Mem2' gl c = Some (gv,t) ->
  _const2GV TD Mem2 gl c = Some (gv,t) \/
  (exists i2, gv = ptr2GV TD (Vptr mb2 i2)) \/
  (forall b2 i2, gv <> ptr2GV TD (Vptr b2 i2)).
Proof.
  induction c; intros; simpl in *.
Case "zero".
    destruct (_zeroconst2GV TD t); inv H0; auto. 
Case "int".
    inv H0; auto.
Case "float".
    destruct f; inv H0; auto.
Case "undef".
    destruct (getTypeSizeInBits TD t); inv H0; auto.
Case "null".
    inv H0; auto.
Case "arr".
    admit.
Case "struct".
    admit.
Case "gid".
    destruct (lookupAL GenericValue gl i0); inv H0; auto.
Case "trunc".   
    remember (_const2GV TD Mem2' gl c) as R.
    destruct R; try solve [inversion H0].
    destruct p.  
    symmetry in HeqR.
    apply IHc in HeqR; auto.
    destruct HeqR as [HeqR | [[i2 HeqR] | HeqR]]; subst.
      rewrite HeqR; auto.
      inv H0.

      unfold mtrunc in H0.
      remember (GV2val TD g) as R1.
      destruct R1; try solve [inversion H0].
      destruct v; try solve [inversion H0].
        destruct t2; try solve [inversion H0].
        destruct t0; try solve [inversion H0].
        destruct (eq_nat_dec wz s); inv H0.
          right. right.
            intros.
            unfold ptr2GV, val2GV.
            destruct (le_lt_dec s s0); intros J; inversion J.

        destruct t2; try solve [inversion H0].
        destruct t0; try solve [inversion H0].
        destruct (floating_point_order f1 f0); try solve [inversion H0].
        right. right. intros. unfold ptr2GV, val2GV. 
        destruct f1; inv H0; intros J; inversion J.

Case "ext". admit.
(* 
    remember (_const2GV TD Mem2' gl c) as R.
    destruct R; try solve [inversion H0].
    destruct p.  
    symmetry in HeqR.
    apply IHc in HeqR; auto.
    destruct HeqR as [HeqR | [i2 HeqR]]; subst.
      rewrite HeqR; auto.

      unfold mext, ptr2GV, val2GV, GV2val in H0. 
      destruct t1; try solve [inversion H0].
        destruct t; try solve [inversion H0].
        destruct t; try solve [inversion H0].
        destruct (floating_point_order f f0); try solve [inversion H0].
*)
Case "cast". 
    remember (_const2GV TD Mem2' gl c0) as R.
    destruct R; try solve [inversion H0].
    destruct p.  
    symmetry in HeqR.
    apply IHc in HeqR; auto.
    destruct HeqR as [HeqR | [[i2 HeqR] | HeqR]]; subst.
    SCase "cast.1".
      rewrite HeqR.
      unfold mcast, ptr2GV, val2GV, GV2val in *. 
      destruct c; try solve [
        inversion H0 |
        destruct t1; try solve [
          inversion H0 |
          destruct t; try solve [
            inv H0; auto |
            inv H0; right; unfold ptr2GV, val2GV; exists i2; auto
            ]
          ]
        ].
      SSCase "cast.1.1".
        destruct t1; try solve [inversion H0].
        destruct t; try solve [inversion H0].
        destruct g; try solve [inversion H0].
        destruct p.
        destruct g; try solve [inversion H0].
        right. right. intros.
        destruct v; try solve [inversion H0].
          destruct (Mem.ptr2int Mem2' b 0); inv H0; intro J; inversion J.
          inv H0; intro J; inversion J.

      SSCase "cast.1.2".
        destruct t1; try solve [inversion H0].
        destruct t; try solve [inversion H0].
        destruct g; try solve [inversion H0].
        destruct p.
        destruct g; try solve [inversion H0].
        destruct v; try solve [inversion H0].
        remember (Mem.int2ptr Mem2' (Int.signed wz i0)) as R1.
        destruct R1; try solve [inversion H0].
          destruct p. inv H0.
          remember (Mem.int2ptr Mem2 (Int.signed wz i0)) as R2.
          destruct R2.
            destruct p.
            left.
            admit. (* b0 z0 must equal to b z *)

            right. left.
            admit. (* b must be mb2 *)

          inv H0.
          left. admit. (* Mem.int2ptr Mem2 (Int.signed wz i0) must be None *)

    SCase "cast.2".
      unfold mcast, ptr2GV, val2GV, GV2val in H0. 
      destruct c; try solve [
        inversion H0 |
        destruct t1; try solve [
          inversion H0 |
          destruct t; inv H0;
            right; left; unfold ptr2GV, val2GV; exists i2; auto
          ]
        ].

        destruct t1; try solve [inversion H0].
          destruct t; try solve [inversion H0].
          right. right. intros.
          destruct (Mem.ptr2int Mem2' mb2 0); inv H0; intro J; inversion J.

    SCase "cast.3".
      admit.

Case "gep". admit.
Case "select". admit. 
Case "icmp". admit. 
Case "fcmp". admit. 
Case "extractvalue". admit. 
Case "insertvalue". admit. 
Case "bop". admit. 
Case "fbop". admit. 
Qed.

Lemma alloc_getOperandValue_inv : forall Mem2 lo hi Mem2' mb2 TD v lc2 gl gv,
  Mem.alloc Mem2 lo hi = (Mem2', mb2) ->
  getOperandValue TD Mem2' v lc2 gl = Some gv ->
  getOperandValue TD Mem2 v lc2 gl = Some gv \/
  (exists i2, gv = ptr2GV TD (Vptr mb2 i2)) \/
  (forall b2 i2, gv <> ptr2GV TD (Vptr b2 i2)).
Proof.
  intros Mem2 lo hi Mem2' mb2 TD v lc2 gl gv Halloc Hget'.
  destruct v as [vid | ]; simpl in *; auto.
    unfold const2GV in *.
    remember (_const2GV TD Mem2' gl c) as R.
    destruct R; inv Hget'.
    destruct p. inv H0.
Admitted. 

Lemma gv_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  gv_inject f1 v v' ->
  gv_inject f2 v v'.
Proof.
  intros. 
  unfold gv_inject in *.
  destruct (split v).
  destruct (split v').
  destruct H0.
  split; eauto using val_list_inject_incr.
Qed.

Lemma mem_simulation__malloc : forall mi TD MM Mem Mem2 tsz gn align0 Mem' mb,
  mem_simulation mi TD MM Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists mi', exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    mem_simulation mi' TD MM Mem' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb = Some (mb', 0) /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros mi TD MM Mem Mem2 tsz gn align0 Mem' mb Hmsim Halloc.
  destruct Hmsim as [H1 [H2 H3]].
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists (fun b => if zeq b mb then Some (mb2,0%Z) else mi b).
  exists Mem2'. exists mb2.
  split; auto.
  assert (inject_incr mi (fun b : Z => if zeq b mb then ret (mb2, 0) else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b mb); subst; auto.
      admit. (* mi mb must be None. *)
  split; auto.
  Case "msim".
    split.    
    SCase "msim1".
      clear H2 H3.
      destruct H1.
      apply Mem.mk_mem_inj.
      SSCase "mi_access".
        intros b1 b2 d c ofs p J1 J2.
        destruct (zeq b1 mb); subst; inv J1.
        SSSCase "b1=mb".
          symmetry in HeqR1.
          symmetry in HeqR2.
          destruct J2 as [J21 J22].
          assert (0 <= ofs /\ ofs + size_chunk c <= Size.to_Z tsz * z) as EQ.
            destruct (Z_le_dec 0 ofs).
              destruct (Z_le_dec (ofs + size_chunk c) (Size.to_Z tsz * z)); auto.
                apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in 
                  HeqR1; auto with zarith.
                unfold Mem.range_perm in J21.
                assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
                  assert (J':=@Memdata.size_chunk_pos c).
                  auto with zarith.
                apply J21 in J.           
                contradict J; auto. 
              apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in HeqR1; 
                auto with zarith.
              unfold Mem.range_perm in J21.
              assert (ofs <= ofs < ofs + size_chunk c) as J.
                assert (J':=@Memdata.size_chunk_pos c).
                auto with zarith.
              apply J21 in J.           
              contradict J; auto. 

          apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in HeqR2;
            auto with zarith.
            eapply Mem.valid_access_implies; eauto using perm_F_any.

        SSSCase "b1<>mb".
          eapply Mem.valid_access_alloc_other; eauto.
          eapply Mem.valid_access_alloc_inv with (b:=mb)(lo:=0)
            (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
          destruct (eq_block); subst; try solve [eauto | contradict n; auto].

      SSCase "mi_memval".
Transparent Mem.alloc.
        intros b1 ofs b2 d J1 J2.
        injection HeqR1. intros NEXT MEM.
        injection HeqR2. intros NEXT2 MEM2.
        destruct Mem2. destruct Mem2'. destruct Mem. destruct Mem'. 
        inv MEM.
        inv MEM2. clear HeqR1 HeqR2.
        simpl in *.
        unfold Mem.perm in *. simpl in *.
        clear maxaddress_pos0 conversion_props0 maxaddress_pos2 
              conversion_props2.
        unfold update.     
        destruct (zeq b1 nextblock1); subst; inv J1.
        SSSCase "b1=nextblock1".
          destruct (zeq b2 b2) as [e | n]; 
            try solve [contradict n; auto].
          apply memval_inject_undef.

        SSSCase "b1<>mb".
          destruct (zeq b2 nextblock); subst.
            admit. (* mi b1 cannot be Some nextblock if b1 <> nextblock1 *)

            apply Memdata.memval_inject_incr with (f:=mi); auto.
              apply mi_memval; auto.
                clear - J2 n.
                unfold update in J2.
                destruct (zeq b1 nextblock1); subst; 
                  try solve [auto | contradict n; auto].

Global Opaque Mem.alloc.

    split.    
    SCase "msim2".
      clear H1 H3.
      intros lc2 gl pgv bgv egv als addrb0 addre0 bid0 eid0 v pgv' J1 J2 J3.
      eapply alloc_getOperandValue_inv in J3; eauto.
      destruct J3 as [J3 | [[i2 J3] | J3]]; subst.
      SSCase "from Mem2".
        assert (gv_inject mi pgv pgv') as W.
          admit. (* from J3 HeqR2 J2 *)
        apply H2 with (lc2:=lc2)(gl:=gl)(als:=als)(addrb:=addrb0)(addre:=addre0)
          (bid0:=bid0)(eid0:=eid0)(v:=v)(pgv':=pgv') in J1; eauto.
        destruct J1 as 
          [bgv' [egv' [Mem21 [J37 [J33 [J34 J35]]]]]].
        clear H2.
        assert (exists Mem21', 
          dbCmds TD gl lc2 als Mem2'
             (insn_call fake_id true false typ_void get_mmetadata_fn
                ((p8, v)
                 :: (p8, value_id addrb0) :: (p8, value_id addre0) :: nil)
              :: insn_load bid0 p8 (value_id addrb0) Align.Zero
                 :: insn_load eid0 p8 (value_id addre0) Align.Zero :: nil)
             (updateAddAL GenericValue
               (updateAddAL GenericValue lc2 bid0 bgv') eid0 egv') 
             als Mem21' trace_nil /\
          Mem.mem_inj inject_id Mem2' Mem21') as J'.
          admit. (* get_mmetadata_fn's axiom *)
        destruct J' as [Mem21' [J1' J2']].
        exists bgv'. exists egv'. exists Mem21'.
        split; auto.
        split; eauto using gv_inject_incr.

      SSCase "from new mem".       
        unfold gv_inject, ptr2GV, val2GV in J2. simpl in J2.
        case_eq (split pgv). intros l0 l1 Heq1. rewrite Heq1 in J2.
        destruct J2 as [J21 J22].
        inversion J21; subst.
        inversion H3; subst.
          destruct (zeq b1 mb); subst.
            admit . (* J1 Heq1, wf MM should map mb i1 to None. *)
            admit.  (* H5, wf mi should not map b1 (<>mb) to mb2 *)
          admit. (* J1 Heq1, wf MM should map undef to None. *)
      
      SSCase "nptr".       
        (* We should only consider the case where pgv' is a ptr. In the proof,
           we only need gv's with pointer types. And we should prove that a 
           value with ptr type is always like vptrs. If so, the current case
           is impossible.
        *)
        admit. 

    SCase "msim3".
      admit.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.

    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

Definition veq Mem (v1 v2:val) : bool :=
match v1, v2 with
| Vundef, Vundef => true
| Vundef, _ => false
| _, Vundef => false
| Vint wz1 i1, Vint wz2 i2 => zeq (Int.unsigned wz1 i1) (Int.unsigned wz2 i2)
| Vint wz1 i1, Vfloat f2 => 
    zeq (Int.unsigned wz1 i1) (Int.unsigned 31 (Floats.Float.intuoffloat f2))
| Vfloat f1, Vint wz2 i2 => 
    zeq (Int.unsigned 31 (Floats.Float.intuoffloat f1)) (Int.unsigned wz2 i2)
| Vfloat f1, Vfloat f2 => match (Floats.Float.eq_dec f1 f2) with
                          | left _ => true
                          | right _ => false
                          end
| Vptr b1 o1, Vptr b2 o2 => eq_block b1 b2 && 
                            zeq (Int.unsigned 31 o1) (Int.unsigned 31 o2)
| Vinttoptr i1, Vinttoptr i2 => 
    (* FIXME: Should we compare Vinttoptr and Vptr? *)
    zeq (Int.unsigned 31 i1) (Int.unsigned 31 i2)
| Vptr b1 o1, Vinttoptr i2 =>
    match Mem.ptr2int Mem b1 0 with
    | ret z => zeq (z + Int.signed 31 o1) (Int.unsigned 31 i2)
    | merror => false
    end
| Vinttoptr i1, Vptr b2 o2 =>
    match Mem.ptr2int Mem b2 0 with
    | ret z => zeq (z + Int.signed 31 o2) (Int.unsigned 31 i1)
    | merror => false
    end
| _, _ => false
end.

Fixpoint gveq Mem (gv1 gv2:GenericValue) : bool :=
match gv1, gv2 with
| nil, nil => true
| (v1,c1)::gv1', (v2,c2)::gv2' => veq Mem v1 v2 && 
                                  AST.memory_chunk_eq c1 c2 && 
                                  gveq Mem gv1' gv2'
| _, _ => false
end.

Lemma veq_refl : forall M v, veq M v v = true.
Proof.
  destruct v; simpl; auto.
Admitted.

Lemma gveq_refl : forall M gv, gveq M gv gv = true.
Admitted.

Require Import symexe_tactic.

Lemma gveq__GV2val__veq : forall M gv1 gv2 TD v1, 
  gveq M gv1 gv2 = true ->
  GV2val TD gv1 = Some v1 ->
  exists v2, GV2val TD gv2 = Some v2 /\ veq M v1 v2.
Proof.
  intros M gv1 gv2 TD v1 H1 H2.
  unfold GV2val in H2.
  destruct gv1; inv H2.
  destruct p.
  destruct gv1; inv H0.
  simpl in H1.
  destruct gv2; inv H1.
  destruct p.
  bdestruct3 H0 as H1 H2 H3.
  destruct gv2.
    exists v. simpl. auto.
    inversion H3.
Qed.

Lemma alloc_ptr2int : forall Mem0 b0 ofs0 lo hi Mem' b,
  Mem.alloc Mem0 lo hi = (Mem', b) ->
  Mem.ptr2int Mem0 b0 ofs0 = Mem.ptr2int Mem' b0 ofs0.
(* 
  This is true if b0 and ofs0 are less then mem.nextblock. 
  alloc_ptr2int is used in alloc__const2GV, so the b0 and ofs0 must be from
    1) null
    2) globals
    3) inttoptr (disallowed by SB)
  So this should be correct.
*)
Admitted.

Lemma alloc__const2GV : forall lo hi Mem' b TD Mem gl c gv t, 
  _const2GV TD Mem gl c = ret (gv,t) ->
  Mem.alloc Mem lo hi = (Mem', b) ->
  exists gv', _const2GV TD Mem' gl c = ret (gv',t) /\ gveq Mem' gv gv' = true.
Proof.
  induction c; intros; simpl in *.
  
  exists gv. auto using gveq_refl.
    
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.

(*
  remember (_const2GV TD Mem0 gl c) as R.
  destruct R as [[gv1 t1]|]; try solve [inversion H].
    erewrite IHc; eauto.
    simpl; auto.
*)
  remember (_const2GV TD Mem0 gl c0) as R.
  destruct R as [[gv1 t1]|]; try solve [inversion H].
    assert (J:=H0).
    eapply IHc in J; eauto.
    destruct J as [gv' [J1 J2]].
    rewrite J1.
    unfold mcast in *.
    destruct c.
(*
      destruct t1; try solve [inversion H].
        destruct t; try solve [inversion H]; auto.
        destruct t; try solve [inversion H]; auto.
*)
      admit.
      admit.
      admit.
      admit.

Case "cast".
      destruct t1; try solve [inversion H].
      destruct t; try solve [inversion H].
      remember (GV2val TD gv1) as R.
      destruct R; try solve [inversion H].
      eapply gveq__GV2val__veq in J2; eauto.          
      destruct J2 as [v2 [J21 J22]].
      rewrite J21.
      destruct v; try solve [inversion H].
        unfold veq in J22.
        unfold is_true in J22.
        destruct v2; try solve [inversion J22].
            bdestruct J22 as J2 J3.
            destruct (eq_block b0 b1); subst; try solve [inversion J2].
              erewrite <- alloc_ptr2int; eauto.
              exists gv.
              split; auto using gveq_refl.
                destruct (Mem.ptr2int Mem0 b1 0); inv H; auto.
                  admit. (* zarith *)

            erewrite <- alloc_ptr2int in J22; eauto.
            destruct (Mem.ptr2int Mem0 b0 0); try solve [inversion J22].
            inv H.
            exists (val2GV TD (Vint s (Int.repr s (Int.unsigned 31 i1))) (AST.Mint s)).
            split; auto.
              unfold val2GV.
              simpl. bsplit; auto with zarith.
                admit. (* zarith *)

        inv H.
        unfold veq in J22.
        unfold is_true in J22.
        destruct v2; try solve [inversion J22].
            remember (Mem.ptr2int Mem' b0 0) as R'.
            destruct R'; inv J22.
              exists (val2GV TD (Vint s (Int.repr s (z + Int.signed 31 i1))) (AST.Mint s)).
              split; auto.
                  unfold val2GV.
                  simpl.
                    admit. (* zarith *)

            exists (val2GV TD (Vint s (Int.repr s (Int.unsigned 31 i1))) (AST.Mint s)).
            split; auto.
                unfold val2GV.
                simpl. 
                  admit. (* zarith *)

Case "gep".

Admitted.

Lemma alloc_const2GV : forall TD Mem gl c gv lo hi Mem' b, 
  const2GV TD Mem gl c = ret gv ->
  Mem.alloc Mem lo hi = (Mem', b) ->
  exists gv', const2GV TD Mem' gl c = ret gv' /\ gveq Mem' gv gv' = true.
Proof.
  intros.
  unfold const2GV in *.
  remember (_const2GV TD Mem0 gl c) as R. 
  destruct R; inv H.
  destruct p; inv H2.
  eapply alloc__const2GV in H0; eauto.
  destruct H0 as [gv' [H01 H02]].
  exists gv'. rewrite H01. auto.
Qed.

Lemma malloc_getOperandValue_inv : 
  forall Mem2 tsz gn a0 Mem2' TD v lc2 gl gv mb2,
  malloc TD Mem2 tsz gn a0 = Some (Mem2', mb2) ->
  getOperandValue TD Mem2 v lc2 gl = Some gv ->
  exists gv', 
    getOperandValue TD Mem2' v lc2 gl = Some gv' /\ gveq Mem2' gv gv' = true.
Proof.
  intros Mem2 tsz gn a0 Mem2' TD v lc2 gl gv mb2 Hmalloc Hget.
  unfold malloc in Hmalloc.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; inv Hmalloc.
  case_eq (Mem.alloc Mem2 0 (Size.to_Z tsz * z)).
  intros m b Halloc.
  destruct v as [vid |]; simpl in *; auto.
    exists gv. split; auto using gveq_refl.
    eapply alloc_const2GV; eauto.
Qed.

Lemma simulation__eq__GV2int : forall mi gn gn' TD,
  gv_inject mi gn gn' ->
  GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn'.
Admitted.

Lemma simulation__mload : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2,
  mem_simulation mi TD MM Mem0 Mem2 ->
  mload TD Mem0 gvp t align0 = ret gv ->
  gv_inject mi gvp gvp2 ->
  exists gv2, mload TD Mem2 gvp2 t align0 = ret gv2 /\ gv_inject mi gv gv2.
Proof.
  intros mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 Hmsim Hmload Hginject.
  unfold mload in *.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion Hmload].
  destruct v; try solve [inversion Hmload].
  remember (typ2memory_chunk t) as R'.
  destruct R'; try solve [inversion Hmload].
  remember (Mem.load m Mem0 b (Int.signed 31 i0)) as R1.
  destruct R1; try solve [inversion Hmload].
  unfold GV2ptr in *.
  destruct gvp; inv HeqR.
  destruct p.
  destruct v0; inv H0.
  destruct gvp; inv H1.
  unfold gv_inject in *.
  simpl in Hginject.
  remember (split gvp2) as R2.
  destruct R2; simpl in Hginject.
  destruct Hginject as [J1 J2].
  inversion J1; subst.
  inversion H3; subst.
  inversion H1; subst.
  destruct gvp2; try solve [inversion HeqR2].
  destruct p. simpl in HeqR2.
  remember (split gvp2) as R3.
  destruct R3; inv HeqR2.
  destruct gvp2.
    inv Hmload.
    symmetry in HeqR1.
    destruct Hmsim as [Hmsim _].
    eapply Mem.load_inj in HeqR1; eauto.
    destruct HeqR1 as [v2 [J2 J3]].
    exists (val2GV TD v2 m).
    split.
      admit. (* J2 *)

      unfold val2GV. simpl. 
      split; auto.


    destruct p. simpl in HeqR3. destruct (split gvp2). inversion HeqR3.
Qed.

Lemma gveq__eq__GV2int : forall Mem gn gn' TD,
  gveq Mem gn gn' ->
  GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn'.
Proof.
  intros.
  unfold GV2int.
  destruct gn.
    destruct gn'; auto.
      simpl in H. unfold is_true in H. inv H.
    destruct gn'.
      simpl in H. destruct p. unfold is_true in H. inv H.
      simpl in H. destruct p. destruct p0.
      bdestruct3 H as H1 H2 H3.
      destruct v; destruct v0; try solve [auto | inversion H1].
        destruct gn; destruct gn'; try solve [auto | inversion H3].
          admit.    
          simpl in H3. destruct p. inversion H3.
        admit. (* H1 shoule be false *)
        admit. (* H1 shoule be false *)
Qed.

Lemma trans_cmd__is__correct__dbMalloc : forall 
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : atom)
  (t : typ)
  (v : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_malloc id0 t v align0))
  (Hnotin : getCmdID (insn_malloc id0 t v align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_malloc id0 t v align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : AssocList SoftBound.metadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (gn : GenericValue)
  (als : list mblock)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVMap)
  (rm' : SoftBound.rmetadata)
  (n : Z)
  (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD Mem0 v lc gl = ret gn)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : SoftBound.prop_reg_metadata lc rm id0 (blk2GV TD mb)
         {|
         SoftBound.md_base := SoftBound.base2GV TD mb;
         SoftBound.md_bound := SoftBound.bound2GV TD mb tsz n |} = 
       (lc', rm')),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' TD gl rm' rm2 Mem' Mem2' lc' lc2' /\
         mem_simulation mi' TD MM Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1; try solve [inversion Htrans].
  destruct p as [bid eid].
  remember (mk_tmp ex_ids) as R2.
  destruct R2 as [tmp ex_ids''].
  inv Htrans.
  invert_prop_reg_metadata.
  apply mem_simulation__malloc with (MM:=MM)(Mem2:=Mem2)(mi:=mi) in H1; auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H12 [H13 [H14 H15]]]]]]].
  exists 
    (updateAddAL _ 
      (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb'))
        tmp (SoftBound.bound2GV TD mb' tsz n))
      eid (SoftBound.bound2GV TD mb' tsz n)).
  exists Mem2'. exists mi'.
  split.
  SCase "dbCmds".
    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))(als2:=als)
      (Mem2:=Mem2'); auto.
      eapply simulation__getOperandValue in H0; eauto.
      destruct H0 as [gn' [H00 H01]].
      unfold malloc in H11.
      erewrite simulation__eq__GV2int in H11; eauto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
              bid (SoftBound.base2GV TD mb')
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl.
        rewrite lookupAL_updateAddAL_eq.
        auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
                 bid (SoftBound.base2GV TD mb'))
               tmp (SoftBound.bound2GV TD mb' tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.

      assert (exists gn', getOperandValue TD Mem2' v lc2 gl = ret gn' /\
              GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn') as H4.
        eapply simulation__getOperandValue with (MM:=MM)(Mem2:=Mem2) in H0
          ; eauto.
        destruct H0 as [gv' [H00 H01]].
        apply malloc_getOperandValue_inv with (tsz:=tsz)(gn:=gn)(a0:=align0)
         (Mem2':=Mem2')(mb2:=mb') in H00; auto.
        destruct H00 as [gv'' [H0a H0b]].
        exists gv''. split; auto.
          rewrite simulation__eq__GV2int with (mi:=mi)(gn':=gv'); eauto.
          eapply gveq__eq__GV2int; eauto.
      destruct H4 as [gn' [H41 H42]].
      apply SimpleSE.dbGEP with (mp:=blk2GV TD mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.
          admit. (*id0 <> bid*)

        simpl.
        assert(getOperandValue TD Mem2' v
          (updateAddAL _ (updateAddAL _ lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb')) gl = 
          getOperandValue TD Mem2' v lc2 gl) as EQ'.
          admit. (* id0 and bid are not in v *)
        rewrite EQ'. clear EQ'.
        rewrite H41. auto.

        unfold SoftBound.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        rewrite <- H42. rewrite H2.
        unfold mgetoffset. destruct TD.
        unfold typ2utyp. simpl.
        assert (exists ut, typ2utyp_aux (gen_utyp_maps (rev n0)) t = Some ut)
          as H5.       
          admit. (* wft *)
        destruct H5 as [ut H5]. 
        rewrite H5. simpl.
        assert (getTypeAllocSize (l0, n0) t = 
          getTypeAllocSize (l0, n0) (utyp2typ ut)) as H6.
          admit. (* ?! *)
        rewrite <- H6.
        rewrite H. simpl.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL _
                  (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
                   bid (SoftBound.base2GV TD mb'))
                 tmp (SoftBound.bound2GV TD mb' tsz n))
               eid (SoftBound.bound2GV TD mb' tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

  split; auto.
  SCase "rsim".
    clear - Hrsim H13 H14 H15 subcase.
    split.
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
      SSCase "id0 = i0".
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists (blk2GV TD mb').
        split.
          admit. (* i0 <> bid eid tmp *)
 
          unfold gv_inject, blk2GV, ptr2GV, val2GV.
          simpl.
          split; eauto.
           
      SSCase "id0 <> i0".
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        destruct Hrsim as [J1 _].
        apply J1 in J.
        destruct J as [gv2 [J J2]].
        exists gv2.
        split.
          admit. (* i0 <> bid eid tmp *)

          eapply gv_inject_incr; eauto.

      admit. (* lets see if the proofs need this direction. *)
Qed.

Lemma trans_cmd__is__correct__dbLoad_nptr__case : forall b0 i1 TD s t
  b b1 i0 i2,
  ret Vptr b0 i1 = GV2ptr TD (getPointerSize TD) null ->
  ret Vptr b1 i2 = GV2ptr TD (getPointerSize TD) null  ->
  ret s = getTypeAllocSize TD t ->
  zeq b b0 && zeq b0 b1 && zle (Int.signed 31 i1) (Int.signed 31 i0) &&
  zle (Int.signed 31 i0 + Size.to_Z s) (Int.signed 31 i2) ->
  False.
Proof.  
  intros.
  simpl in *.
  inv H. inv H0.
  (* H2 is false since Size.to_Z s is pos. *)
Admitted.  

Definition id_fresh_in_value v1 i2 : Prop :=
match v1 with
| value_id i1 => i1 <> i2
| _ => False
end.

Lemma getOperandValue_eq_fresh_id : forall tmp TD Mem2 v lc2 gl gvp2,
  id_fresh_in_value v tmp ->
  getOperandValue TD Mem2 v lc2 gl = 
    getOperandValue TD Mem2 v (updateAddAL GenericValue lc2 tmp gvp2) gl.
Proof.
  intros.
  destruct v; simpl; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma trans_cmd__is__correct__dbLoad_nptr : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_load id0 t vp align0))
  (Hnotin : getCmdID (insn_load id0 t vp align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_load id0 t vp align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (gv : GenericValue)
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = Some md)
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : SoftBound.assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : ~ isPointerTyp t),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' TD gl rm rm2 Mem0 Mem2' 
           (updateAddAL GenericValue lc id0 gv) lc2' /\
         mem_simulation mi' TD MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    contradict H3; auto.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H1).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].

  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
       (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2)
        id0 gv2).
  exists Mem2. exists mi.
  split.
    SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR5 HeqR6.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2) id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
          auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)

  split; auto.
    SSCase "rsim".

    clear - Hrsim1 H22 subcase subsubcase.
    split.
      SSSCase "rsim1".
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> btmp etmp ptmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

      SSSCase "rsim2".
        admit. (* lets see if the proofs need this direction. *)    
Qed.

Lemma trans_cmd__is__correct__dbLoad_ptr: forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (addrb : id)
  (addre : id)
  (mi : meminj)
  (id0 : atom)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_load id0 t vp align0))
  (Hnotin : getCmdID (insn_load id0 t vp align0) `notin` codom rm2)
  (mt : typ)
  (bv : value)
  (ev : value)
  (HeqR : ret (mt, bv, ev) = get_reg_metadata rm2 vp)
  (ptmp : id)
  (ex_ids2 : ids)
  (HeqR1 : (ptmp, ex_ids2) = mk_tmp ex_ids)
  (btmp : id)
  (ex_ids3 : ids)
  (HeqR2 : (btmp, ex_ids3) = mk_tmp ex_ids2)
  (etmp : id)
  (HeqR4 : true = isPointerTypB t)
  (bid0 : id)
  (eid0 : id)
  (HeqR5 : ret (bid0, eid0) = lookupAL (id * id) rm2 id0)
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : Values.block -> int32 -> monad SoftBound.metadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (gv : GenericValue)
  (lc' : GVMap)
  (rm' : SoftBound.rmetadata)
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = ret md)
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : SoftBound.assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : isPointerTyp t)
  (HeqR3 : (etmp, ex_ids') = mk_tmp ex_ids3)
  (H5 : SoftBound.prop_reg_metadata lc rm id0 gv
         (SoftBound.get_mem_metadata TD MM gvp) = (lc', rm')),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2
           (insn_cast ptmp castop_bitcast (typ_pointer t) vp p8
            :: insn_cast btmp castop_bitcast mt bv p8
               :: insn_cast etmp castop_bitcast mt ev p8
                  :: insn_call fake_id true false typ_void assert_mptr_fn
                       ((p8, value_id ptmp)
                        :: (p8, value_id btmp)
                           :: (p8, value_id etmp)
                              :: (i32, type_size t) :: (i32, vint1) :: nil)
                     :: insn_load id0 t vp align0
                        :: insn_call fake_id true false typ_void
                             get_mmetadata_fn
                             ((p8, value_id ptmp)
                              :: (pp8, value_id addrb)
                                 :: (pp8, value_id addre)
                                    :: (p8, vnullp8)
                                       :: (i32, vint1)
                                          :: (p32, vnullp32) :: nil)
                           :: insn_load bid0 p8 (value_id addrb) Align.Zero
                              :: insn_load eid0 p8 
                                   (value_id addre) Align.Zero :: nil) lc2'
           als Mem2' trace_nil /\
         reg_simulation mi' TD gl rm' rm2 Mem0 Mem2' lc' lc2' /\
         mem_simulation mi' TD MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  assert (J:=H1).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  unfold SoftBound.get_reg_metadata in H.
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].
  case_eq (SoftBound.get_mem_metadata TD MM gvp).
  intros mb_base0 md_bound0 JJ.
  assert (Hmsim':=Hmsim).
  destruct Hmsim' as [Hmsim1 [Hmsim2 Hmsim3]].
  eapply Hmsim2 with (als:=als)(addrb:=addrb)(addre:=addre)(bid0:=bid0)
    (eid0:=eid0) in JJ; eauto.
  destruct JJ as [bgv' [egv' [Mem2' [JJ1 [JJ2 [JJ3 [JJ4 JJ5]]]]]]].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
       (updateAddAL _ 
        (updateAddAL _ 
         (updateAddAL _ 
          (updateAddAL _ 
            (updateAddAL _ 
             (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp bgv2)
             etmp egv2)
            id0 gv2)
           bid0 bgv')
          eid0 egv').
  exists Mem2. exists mi.
  split.
  SCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR5 HeqR6.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2) id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
          auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)
    clear - JJ1.
    admit. (* axiom of get_mmetadata_fn *)

  split; auto.
  SCase "rsim".

    clear - Hrsim1 H5 H22.
    unfold SoftBound.get_mem_metadata, SoftBound.prop_reg_metadata in H5.  
    inv H5.
    split.
    SSCase "rsim1".
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> btmp etmp ptmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

    SSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)
Qed.

Lemma int2ptr__mstore : forall Mem chk b ofs v Mem' z,
  Mem.store chk Mem b ofs v = Some Mem' ->
  Mem.int2ptr Mem z = Mem.int2ptr Mem' z. 
Admitted.

Lemma ptr2int__mstore : forall Mem chk b ofs v Mem' b' z',
  Mem.store chk Mem b ofs v = Some Mem' ->
  Mem.ptr2int Mem b' z' = Mem.ptr2int Mem' b' z'.
Admitted.

Lemma const2GV__mstore' : forall TD Mem chk b ofs v Mem' gl c,
  Mem.store chk Mem b ofs v = Some Mem' ->
  _const2GV TD Mem gl c = _const2GV TD Mem' gl c.
Proof.
  intros TD Mem chk b ofs v Mem' gl c Hstore.
  induction c; simpl in *; try solve 
    [ auto | rewrite IHc; auto | 
      rewrite IHc1; rewrite IHc2; auto |
      rewrite IHc1; rewrite IHc2; rewrite IHc3; auto ].
    admit.
    admit.
    rewrite IHc.
    destruct (_const2GV TD Mem' gl c0); auto.
    destruct p.
    unfold mcast.
    destruct t0; auto.
      destruct c; auto.
        destruct t; auto.
          destruct (GV2val TD g); auto.
            destruct v0; auto.
              erewrite int2ptr__mstore; eauto.
      destruct c; auto.
        destruct t; auto.
          destruct (GV2val TD g); auto.
            destruct v0; auto.
              erewrite ptr2int__mstore; eauto.
Qed.  

Lemma const2GV__mstore : forall TD Mem gvp t gv align0 Mem' gl c,
  mstore TD Mem gvp t gv align0 = Some Mem' ->
  const2GV TD Mem gl c = const2GV TD Mem' gl c.
Proof.
  intros TD Mem gvp t gv align0 Mem' gl c Hmstore. unfold const2GV.
  unfold mstore in Hmstore.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion Hmstore].  
  destruct v; try solve [inversion Hmstore].  
  remember (typ2memory_chunk t) as R1.
  destruct R1; try solve [inversion Hmstore].  
  remember (GV2val TD gv) as R2.
  destruct R2; try solve [inversion Hmstore].  
  erewrite const2GV__mstore'; eauto.
Qed.

Lemma getOperandValue__mstore : forall TD Mem gvp t gv align0 Mem' gl lc v,
  mstore TD Mem gvp t gv align0 = Some Mem' ->
  getOperandValue TD Mem v lc gl = getOperandValue TD Mem' v lc gl.
Proof.
  intros TD Mem gvp t gv align0 Mem' gl lc v Hmstore.
  destruct v as [vid |]; simpl; auto.
    erewrite const2GV__mstore; eauto.
Qed.

Lemma get_mmetadata_fn__prop : forall m Mem2 b2 ofs2 v1 Mem2' lc2 gl als addrb
    addre bid0 eid0 bgv' egv' Mem3 TD v,
  Mem.store m Mem2 b2 ofs2 v = ret Mem2' ->
  dbCmds TD gl lc2 als Mem2
         (insn_call fake_id true false typ_void get_mmetadata_fn
            ((p8, v1) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
          :: insn_load bid0 p8 (value_id addrb) Align.Zero
             :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
         (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
            eid0 egv') als Mem3 trace_nil ->
   exists Mem2'0 : mem,
     dbCmds TD gl lc2 als Mem2'
       (insn_call fake_id true false typ_void get_mmetadata_fn
          ((p8, v1) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
        :: insn_load bid0 p8 (value_id addrb) Align.Zero
           :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
       (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
          eid0 egv') als Mem2'0 trace_nil /\
     Mem.mem_inj inject_id Mem2' Mem2'0.
Admitted.

Lemma simulation__mstore : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 gv2
                                  Mem0',
  mem_simulation mi TD MM Mem0 Mem2 ->
  Mem.meminj_no_overlap mi Mem0 ->
  mstore TD Mem0 gvp t gv align0 = ret Mem0' ->
  gv_inject mi gvp gvp2 ->
  gv_inject mi gv gv2 ->
  exists Mem2', 
    mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' /\ 
    mem_simulation mi TD MM Mem0' Mem2'.
Proof.
  intros mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 gv2 Mem0' Hmsim Hnlap Hmstore 
    Hginject1 Hginject2.
  assert (Hmstore':=Hmstore).
  unfold mstore in Hmstore.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion Hmstore].
  destruct v; try solve [inversion Hmstore].
  remember (typ2memory_chunk t) as R'.
  destruct R'; try solve [inversion Hmstore].
  remember (GV2val TD gv) as R1.
  destruct R1; try solve [inversion Hmstore].
  unfold GV2ptr in *.
  destruct gvp; inv HeqR.
  destruct p.
  destruct v0; inv H0.
  destruct gvp; inv H1.
  unfold gv_inject in *.
  simpl in Hginject1.
  remember (split gvp2) as R2.
  destruct R2; simpl in Hginject1.
  destruct Hginject1 as [J1 J2].
  inversion J1; subst.
  inversion H3; subst.
  inversion H1; subst.
  destruct gvp2; try solve [inversion HeqR2].
  destruct p. simpl in HeqR2.
  remember (split gvp2) as R3.
  destruct R3; inv HeqR2.
  destruct gvp2.
    unfold GV2val in *.
    destruct gv; inv HeqR1.
    destruct p.
    destruct gv; inv H0.
    simpl in Hginject2.    
    remember (split gv2) as R3.
    destruct R3; simpl in Hginject2.
    destruct Hginject2 as [J3 J4].
    inversion J3; subst. 
    inversion H6; subst.
    destruct gv2; try solve [inversion HeqR0].
    destruct p. simpl in HeqR0.
    remember (split gv2) as R4.
    destruct R4; inv HeqR0.
      inv Hmstore.
      destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
      eapply Mem.store_mapped_inj with (f:=mi)(m2:=Mem2) in H0; eauto.
      destruct H0 as [Mem2' [J2 J4]].
      exists Mem2'.
      destruct gv2.
        assert ( mstore TD Mem2
          ((Vptr b2 (Int.add 31 i1 (Int.repr 31 delta)), m1) :: nil) t
          ((v, m2) :: nil) align0 = ret Mem2') as J.
          unfold mstore. simpl. rewrite <- HeqR'.
          admit. (* J2 *)
        split; auto.
          split; auto.
          split.
            clear Hmsim1 Hmsim3.
            intros lc2 gl pgv bgv egv als addrb addre bid0 eid0 v1 pgv' G1 G2 G3.
            assert (G3':=G3).
            erewrite <- getOperandValue__mstore with (Mem:=Mem2)(t:=t)
            (gvp:=(Vptr b2 (Int.add 31 i1 (Int.repr 31 delta)), m1) :: nil)
            (gv:=(v, m2) :: nil)(align0:=align0) in G3'; eauto.
            apply Hmsim2 with (bgv:=bgv)(egv:=egv)(als:=als)(addrb:=addrb)
              (addre:=addre)(bid0:=bid0)(eid0:=eid0)(pgv:=pgv) in G3'; auto.
            destruct G3' as [bgv' [egv' [Mem3 [G4 [G5 [G6 G7]]]]]].
            exists bgv'. exists egv'.
            eapply get_mmetadata_fn__prop in G4; eauto.
            destruct G4 as [Mem3' [G41 G42]].
            exists Mem3'. split; auto.

            (* skip this direction for now. *)            
            admit.

      destruct p. simpl in HeqR4. destruct (split gv2). inversion HeqR4.
    destruct p. simpl in HeqR3. destruct (split gvp2). inversion HeqR3.
Qed.

Lemma trans_cmd__is__correct__dbStore_nptr: forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (sid : id)
  (t : typ)
  (v : value)
  (vp : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_store sid t v vp align0))
  (Hnotin : getCmdID (insn_store sid t v vp align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_store sid t v vp align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gv : GenericValue)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (Mem' : mem)
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = Some md)
  (H0 : getOperandValue TD Mem0 v lc gl = ret gv)
  (H1 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H2 : SoftBound.assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : ~ isPointerTyp t),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' TD gl rm rm2 Mem' Mem2' lc lc2' /\
         mem_simulation mi' TD MM Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    unfold isPointerTyp in H4.
    rewrite <- HeqR4 in H4.
    contradict H4; auto.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H2).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].

  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SoftBound.get_reg_metadata in H.
  assert (Mem.meminj_no_overlap mi Mem0) as W. admit.
  eapply simulation__mstore in H3; eauto.
  destruct H3 as [Mem2' [H31 H32]].
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2).
  exists Mem2'. exists mi.
  split.
  SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H10.
        rewrite H10. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR5 HeqR6.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL _ (updateAddAL _ 
      (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2'); auto.
      apply SimpleSE.dbStore with (mp2:=gvp2)(gv1:=gv2); auto.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
          auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)

        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
          auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)

  split; auto.
  SSCase "rsim".

    clear - Hrsim1 subcase subsubcase.
    split.
    SSSCase "rsim1".
      intros i0 gv1 J.
      apply Hrsim1 in J.
      destruct J as [gv2' [J J2]].
      exists gv2'.
      split; auto.
        admit. (* i0 <> bid eid tmp *)

    SSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)
Qed.

Lemma set_mmetadata_fn__prop : forall TD gl lc2 als Mem2 ptmp pgv' bv0 ev0,
  lookupAL _ lc2 ptmp = Some pgv' ->
  exists Mem2',
    SimpleSE.dbCmd TD gl lc2 als Mem2
      (insn_call fake_id true false typ_void set_mmetadata_fn
        ((p8, value_id ptmp) :: (p8, bv0) :: (p8, ev0) :: (p8, vnullp8) :: 
         (i32, vint1) :: (i32, vint1) :: nil)) 
      lc2 als Mem2' trace_nil.
Admitted.

Lemma simulation__set_mmetadata_fn : forall lc2 gl pgv bgv egv als  
    pgv' bgv' egv' mi ptmp bv0 ev0 MM1 Mem1 Mem2 TD rm v,  
  mem_simulation mi TD MM1 Mem1 Mem2 ->
  SoftBound.get_reg_metadata TD Mem1 gl rm v = Some (SoftBound.mkMD bgv egv) -> 
  lookupAL _ lc2 ptmp = Some pgv' ->
  getOperandValue TD Mem2 bv0 lc2 gl = Some bgv' ->
  getOperandValue TD Mem2 ev0 lc2 gl = Some egv' ->
  gv_inject mi pgv pgv' ->
  gv_inject mi bgv bgv' ->
  gv_inject mi egv egv' ->
  exists Mem2',
    SimpleSE.dbCmd TD gl lc2 als Mem2
      (insn_call fake_id true false typ_void set_mmetadata_fn
        ((p8, value_id ptmp) :: (p8, bv0) :: (p8, ev0) :: (p8, vnullp8) :: 
         (i32, vint1) :: (i32, vint1) :: nil)) 
      lc2 als Mem2' trace_nil /\
      mem_simulation mi TD 
        (SoftBound.set_mem_metadata TD MM1 pgv (SoftBound.mkMD bgv egv)) 
        Mem1 Mem2'.
Proof.
  intros lc2 gl pgv bgv egv als pgv' bgv' egv' mi ptmp bv0 ev0 MM1 Mem1 Mem2 TD 
    rm v Hmsim Hgetm Hlookup Hgetb Hgete Hinjp Hinjb Hinje.
  destruct (@set_mmetadata_fn__prop TD gl lc2 als Mem2 ptmp pgv' bv0 ev0 Hlookup)
    as [Mem2' J].
  exists Mem2'.
  split; auto.
  destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
  split. 
    clear Hmsim2 Hmsim3.
    admit.
  split. 
    clear Hmsim1 Hmsim3.
    intros lc0 gl0 pgv0 bgv0 egv0 als0 addrb addre bid0 eid0 v0 pgv'0 J1 J2 J3.
    
    assert (getOperandValue TD Mem2 v0 lc0 gl0 = ret pgv'0) as G.
      admit. (* set_mmetadata_fn does not change int2ptr and ptr2int *)
    unfold SoftBound.set_mem_metadata, SoftBound.get_mem_metadata in J1.
    assert (exists b, exists ofs', 
      GV2ptr TD (getPointerSize TD) pgv0 = Some (Vptr b ofs')) as R.
      admit. (* Lets only consider the case when pgv0 is a pointer *)
    assert (exists b2, exists ofs2, 
      GV2ptr TD (getPointerSize TD) pgv = Some (Vptr b2 ofs2)) as R'.
      admit. (* ditto *)
    destruct R as [b1 [ofs1 R]]. 
    destruct R' as [b2 [ofs2 R']].
    rewrite R in J1. rewrite R' in J1.
    destruct (zeq b1 b2); subst; simpl in J1.
      destruct (Int.eq_dec 31 ofs2 ofs1); subst; simpl in J1.
        inv J1.      
        exists bgv'. exists egv'.
        admit. (* set_mmetadata_fn__prop *) 
        
        apply Hmsim2 with (pgv:=pgv0)(bgv:=bgv0)(egv:=egv0)(als:=als0)
          (addrb:=addrb)(addre:=addre)(bid0:=bid0)(eid0:=eid0) in G; auto.
        
          destruct G as [bgv0' [egv0' [Mem3' [G1 [G2 [G3 G4]]]]]]. 
          exists bgv0'.  exists egv0'.
            clear - G1 J G2 G3 G4.
            admit. (* get_mmetadata_fn__prop1 *) 

          unfold SoftBound.get_mem_metadata.
          rewrite R; auto.

      apply Hmsim2 with (pgv:=pgv0)(bgv:=bgv0)(egv:=egv0)(als:=als0)
        (addrb:=addrb)(addre:=addre)(bid0:=bid0)(eid0:=eid0) in G; auto.
        
        destruct G as [bgv0' [egv0' [Mem3' [G1 [G2 [G3 G4]]]]]]. 
        exists bgv0'.  exists egv0'.
          clear - G1 J G2 G3 G4.
          admit. (* get_mmetadata_fn__prop1 *) 

        unfold SoftBound.get_mem_metadata.
        rewrite R; auto.

    (* ignore this direction *)
    admit.
Qed.

Lemma trans_cmd__is__correct__dbStore_ptr : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (sid : id)
  (t : typ)
  (v : value)
  (vp : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_store sid t v vp align0))
  (Hnotin : getCmdID (insn_store sid t v vp align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_store sid t v vp align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gv : GenericValue)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (Mem' : mem)
  (md' : SoftBound.metadata)
  (MM' : SoftBound.mmetadata)
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = ret md)
  (H0 : getOperandValue TD Mem0 v lc gl = ret gv)
  (H1 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H2 : SoftBound.assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : isPointerTyp t)
  (H5 : SoftBound.get_reg_metadata TD Mem0 gl rm v = ret md')
  (H6 : SoftBound.set_mem_metadata TD MM gvp md' = MM'),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' TD gl rm rm2 Mem' Mem2' lc lc2' /\
         mem_simulation mi' TD MM' Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids2].
  remember (mk_tmp ex_ids2) as R2. 
  destruct R2 as [btmp ex_ids3].
  remember (mk_tmp ex_ids3) as R3. 
  destruct R3 as [etmp ex_ids4].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    remember (get_reg_metadata rm2 v) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [[mt0 bv0] ev0].
    inv Htrans.

  assert (J:=H2).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SoftBound.get_reg_metadata in H.
  assert (H3':=H3).
  assert (Mem.meminj_no_overlap mi Mem0) as G. admit.
  eapply simulation__mstore in H3'; eauto.
  destruct H3' as [Mem2' [H31 H32]].
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].

  destruct md' as [md_base' md_bound'].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  assert (H5':=H5).      
  apply Hrsim2 in H5'.
  destruct H5' as [t2' [bv2' [ev2' [bgv2' [egv2' [J1' [J2' [J3' [J4' J5']]]]]]]]].
  simpl in HeqR5.
  rewrite J1' in HeqR5.
  inv HeqR5.

  assert (exists Mem2'',
    SimpleSE.dbCmd TD gl 
      (updateAddAL _ (updateAddAL _ (updateAddAL GenericValue lc2 ptmp gvp2)
        btmp bgv2) etmp egv2)
      als Mem2'
      (insn_call fake_id true false typ_void set_mmetadata_fn
        ((p8, value_id ptmp) :: 
         (p8, bv2') :: 
         (p8, ev2') :: (p8, vnullp8) :: 
         (i32, vint1) :: (i32, vint1) :: nil)) 
      (updateAddAL _ (updateAddAL _ (updateAddAL GenericValue lc2 ptmp gvp2)
        btmp bgv2) etmp egv2)
      als Mem2'' trace_nil /\
      mem_simulation mi TD 
        (SoftBound.set_mem_metadata TD MM gvp 
          (SoftBound.mkMD md_base' md_bound')) 
        Mem' Mem2'') as W.
    apply simulation__set_mmetadata_fn with (pgv':=gvp2)(bgv':=bgv2')
      (egv':=egv2')(rm:=rm)(v:=v); simpl; auto.
      clear - H5 H3.
      destruct v; simpl in *; auto.
        destruct (SoftBound.get_const_metadata c); try solve [inv H5; auto].
        destruct p.
        remember (const2GV TD Mem0 gl c0) as R.
        destruct R; try solve [inv H5; auto].
        remember (const2GV TD Mem0 gl c2) as R'.
        destruct R'; try solve [inv H5; auto].
        simpl in *.
        inv H5.
        erewrite <- const2GV__mstore with (Mem:=Mem0); eauto.
        rewrite <- HeqR'.
        erewrite <- const2GV__mstore with (Mem:=Mem0); eauto.
        rewrite <- HeqR.
        simpl. auto.
          
      rewrite <- lookupAL_updateAddAL_neq.
      rewrite <- lookupAL_updateAddAL_neq.
      rewrite lookupAL_updateAddAL_eq; auto.
      admit. (* ptmp is fresh *)
      admit. (* ptmp is fresh *)

      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
        clear - J2' H31.
        erewrite <- getOperandValue__mstore; eauto.
        admit. (* fresh *)
        admit. (* fresh *)
        admit. (* fresh *)

      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
        clear - J3' H31.
        erewrite <- getOperandValue__mstore; eauto.
        admit. (* fresh *)
        admit. (* fresh *)
        admit. (* fresh *)

  destruct W as [Mem2'' [W1 W2]].

  exists 
          (updateAddAL _ 
            (updateAddAL _ 
             (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp bgv2)
             etmp egv2).
  exists Mem2''. exists mi.
  split.
    SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H10.
        rewrite H10. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR6.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)(als2:=als)(Mem2:=Mem2'); auto.
      apply SimpleSE.dbStore with (mp2:=gvp2)(gv1:=gv2); auto.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
          auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)

        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
          auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)(als2:=als)(Mem2:=Mem2''); auto.

  split; auto.
    SSCase "rsim".

    clear - Hrsim1 subcase subsubcase.
    split.
      SSSSCase "rsim1".
      intros i0 gv1 J.
      apply Hrsim1 in J.
      destruct J as [gv2' [J J2]].
      exists gv2'.
      split; auto.
        admit. (* i0 <> bid eid tmp *)

      SSSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)

  SCase "t isnt ptr".
    unfold isPointerTyp in H4.
    rewrite H4 in HeqR4.
    inversion HeqR4.
Qed.

Lemma trans_cmd__is__correct__dbLoad_abort : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_load id0 t vp align0))
  (Hnotin : getCmdID (insn_load id0 t vp align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_load id0 t vp align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = ret md)
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : ~ SoftBound.assert_mptr TD t gvp md),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' TD gl rm rm2 Mem0 Mem2' lc lc2' /\
         mem_simulation mi' TD MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    admit.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H1).
  destruct md as [md_base md_bound].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].
  unfold SoftBound.get_reg_metadata in H.
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2).
  exists Mem2. exists mi.
  split.
    SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01.
       admit. (* assert_mptr_fn' axiom. *)
    admit. (* unreachable, if dbCmds support abort. *)

  split; auto.
    SSCase "rsim".

    clear - Hrsim1 subcase subsubcase.
    split.
      SSSCase "rsim1".
      intros i0 gv1 J.
      apply Hrsim1 in J.
      destruct J as [gv2' [J J2]].
      exists gv2'.
      split; auto.
        admit. (* i0 <> bid eid tmp *)

      SSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)
Qed.

Lemma trans_cmd__is__correct : forall c TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs ex_ids tmps ex_ids' tmps' r
    optaddrb optaddre optaddrb' optaddre' mi,  
  non_temporal_cmd c ->
  getCmdID c `notin` codom rm2 ->
  trans_cmd ex_ids tmps optaddrb optaddre rm2 c = 
    Some (ex_ids', tmps', cs, optaddrb', optaddre') ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmd TD gl lc1 rm1 als Mem1 MM1 c lc1' rm1' als' Mem1' MM1' tr r ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs lc2' als' Mem2' tr /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
Proof.
  intros c TD lc1 rm1 als gl Mem1 MM1 lc1' als' Mem1' MM1' tr lc2 Mem2 rm2 rm1' 
    cs ex_ids tmps ex_ids' tmps' r optaddrb optaddre optaddrb' optaddre' mi
    Hnontemp Hnotin Htrans Hrsim Hmsim HdbCmd.
  (sb_dbCmd_cases (destruct HdbCmd) Case); try solve [inversion Hnontemp].

Case "dbBop".
  inv Htrans.
  eapply simulation__BOP in H; eauto.
  destruct H as [gv3' [H1 H2]].
  exists (updateAddAL GenericValue lc2 id0 gv3'). exists Mem2. exists mi.
  split.
   assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
   rewrite EQ.
   eapply SimpleSE.dbCmds_cons; eauto.
     apply SimpleSE.dbBop; auto.
  split; auto.
    apply reg_simulation__updateAddAL; auto.

admit. admit. admit.

Case "dbMalloc".
  eapply trans_cmd__is__correct__dbMalloc; eauto.

Case "dbMalloc_error".
  admit.    

Case "dbAlloca".
  admit. 

Case "dbAlloca_error".
  admit. 

Case "dbLoad_nptr".
  eapply trans_cmd__is__correct__dbLoad_nptr; eauto.

Case "dbLoad_ptr".
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids2].
  remember (mk_tmp ex_ids2) as R2. 
  destruct R2 as [btmp ex_ids3].
  remember (mk_tmp ex_ids3) as R3. 
  destruct R3 as [etmp ex_ids4].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    remember (lookupAL (id * id) rm2 id0) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bid0 eid0].
    destruct optaddrb as [addrb | ].
      destruct optaddre as [addre | ]; inv Htrans.
        eapply trans_cmd__is__correct__dbLoad_ptr; eauto.

      destruct optaddre as [addre | ]; inv Htrans.
        remember (mk_tmp ex_ids4) as W0.
        destruct W0 as [addrb ex_ids0].
        remember (mk_tmp ex_ids0) as W1.
        destruct W1 as [addre ex_ids1].
        inv H7.
        eapply trans_cmd__is__correct__dbLoad_ptr; eauto.

  SCase "t isnt ptr".
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    inversion H3.

Case "dbLoad_error1".
admit. 

Case "dbLoad_error2".
admit. 

Case "dbLoad_error3".
admit.

Case "dbLoad_abort".
  eapply trans_cmd__is__correct__dbLoad_abort; eauto.

Case "dbStore_nptr".
  eapply trans_cmd__is__correct__dbStore_nptr; eauto.

Case "dbStore_ptr".
  eapply trans_cmd__is__correct__dbStore_ptr; eauto.

Case "dbStore_error1".
  admit. 
  
Case "dbStore_error2".
  admit.
 
Case "dbStore_error3".
  admit.

Case "dbStore_abort".
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
    remember (get_reg_metadata rm2 v) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bv0 ev0].
    inv Htrans.
    admit.

    inv Htrans.
    admit.

Case "dbGEP".

Admitted.

Fixpoint getCmdsIDs (cs:list cmd) : atoms :=
match cs with
| nil => empty
| c::cs' => singleton (getCmdID c) `union` getCmdsIDs cs'
end.

Lemma trans_cmds__is__correct : forall cs TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs' ex_ids tmps ex_ids' tmps' r
    optaddrb optaddre optaddrb' optaddre' mi, 
  non_temporal_cmds cs ->
  AtomSetImpl.inter (getCmdsIDs cs) (codom rm2) [<=] empty ->
  trans_cmds ex_ids tmps optaddrb optaddre rm2 cs = 
    Some (ex_ids', tmps', cs', optaddrb', optaddre') ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmds TD gl lc1 rm1 als Mem1 MM1 cs lc1' rm1' als' Mem1' MM1' tr r 
    ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs' lc2' als' Mem2' tr /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
Admitted.

End SBpass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
