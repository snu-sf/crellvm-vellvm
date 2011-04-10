Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import Metatheory.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_tactic.
Require Import assoclist.
Require Import eq_tv_dec.
Require Import sub_tv_dec.
Require Import Coq.Bool.Sumbool.
Require Import monad.

Export SimpleSE.

Definition eq_value (v v':value) := sumbool2bool _ _ (value_dec v v').
Definition tv_typ (t t':typ) := sumbool2bool _ _ (typ_dec t t').
Definition tv_align (a a':align) := sumbool2bool _ _ (Align.dec a a').
Definition eq_sterm (st st':sterm) := sumbool2bool _ _ (sterm_dec st st').
Definition eq_smem (sm sm':smem) := sumbool2bool _ _ (smem_dec sm sm').
Definition eq_id (i i':id) := sumbool2bool _ _ (id_dec i i').
Definition eq_const (c c':const) := sumbool2bool _ _ (const_dec c c').
Definition eq_l (l1 l2:l) := sumbool2bool _ _ (l_dec l1 l2).

(* This is the tricky part. How can we know sm2 includes sm1 ?
 * So far, we only consider the memory effects of Softbound. 
 *
 * The axiom assumes the memory behavior of a lib call. This should
 * be admissible in terms of other axioms.
*)
Axiom smem_lib_sub : id -> bool.

(* true <-> id == @__hashLoadBaseBound *)
Axiom is_hashLoadBaseBound : id -> bool.

(* true <-> id == @__loadDereferenceCheck or @__storeDereferenceCheck 

declare void @__loadDereferenceCheck(
  i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe
  )
*)
Axiom is_dereferenceCheck : id -> bool.

(* true <-> id == @__hashStoreBaseBound *)
Axiom is_hashStoreBaseBound : id -> bool.

Inductive onat :=
| Ozero : onat
| Osucc : onat -> onat.

Definition beps := list (id * id * id).
(*
   We assign indices for phi, subblocks and appendent cmds inside a block, like 
   phi_n+1 s_n s_n-1 ... s_2 s_1 c_0

   At the (l_of_arg tt) block there is one subblock --- the 0th.
 *)
Definition nbeps := list (nat * beps).
Definition lnbeps := list (l * nbeps).
Definition flnbeps := list (id * lnbeps).

(* We assume there is a way to know the mapping between
     function id, block, base, bound and ptr *)
Axiom get_metadata : unit -> list (id * l* nat * id * id * id).

(* We assume there is a way to know the mapping between
     function id, addr_of_base, and addr_of_bound used by __hashLoadBaseBound
*)
Axiom get_addrof_be : unit -> list (id * id * id).

(* The label of arg. *)
Axiom l_of_arg : unit -> l.

(* We need to know if an INT is one . *)
Axiom INT_is_one : INT -> bool.

(* Realized to check if two function names are matched. For example,
 * in Softbound, 'test' in the original program matches 'softbound_test'.
*)
Axiom rename_fid : id -> id.

(* From a name in an output program to its original name in the input program. *)
Axiom rename_fid_inv : id -> option id.

Axiom rename_fid_prop1 : forall fid,
  rename_fid_inv (rename_fid fid) = Some fid.

Axiom rename_fid_prop2 : forall fid1 fid2,
  rename_fid_inv fid1 = Some fid2 ->
  rename_fid fid2 = fid1.

(* In function f1, i1 is renamed to be (rename_id f1 i1) *)
Axiom rename_id : id -> id -> id.

(* cast does not change value. We can prove they have the same operational
 * semantics. *)
Fixpoint remove_cast_const (c:const) : const :=
match c with
| const_castop _ c1 _ => remove_cast_const c1
| const_select c0 c1 c2 => 
    const_select c0 (remove_cast_const c1)(remove_cast_const c2) 
| _ => c
end.

Fixpoint remove_cast (st:sterm) : sterm :=
match st with
| sterm_cast _ _ st1 _ => remove_cast st1
| sterm_select st0 t st1 st2 => 
    sterm_select st0 t (remove_cast st1)(remove_cast st2) 
| sterm_val (value_const c) => sterm_val (value_const (remove_cast_const c))
| _ => st
end.

(*
  return the object pointer, e.g.

  %2 = getelementptr i32* %ptr.05, i32 %i.04
  %bcast_ld_dref_bound = bitcast i32* %2 to i8*   

  We return %ptr.05.
*)
Fixpoint get_ptr_object_const (c:const) : const :=
match c with
| const_castop _ c1 _ => get_ptr_object_const c1
| const_gep _ c1 _ => get_ptr_object_const c1
| const_select c0 c1 c2 => 
    const_select c0 (remove_cast_const c1)(remove_cast_const c2) 
| _ => c
end.

Fixpoint get_ptr_object (st:sterm) : sterm :=
match st with
| sterm_cast _ _ st1 _ => get_ptr_object st1
| sterm_gep _ _ st1 _ => get_ptr_object st1
| sterm_select st0 t st1 st2 => 
    sterm_select st0 t (get_ptr_object st1)(get_ptr_object st2) 
| sterm_val (value_const c) => sterm_val (value_const (get_ptr_object_const c))
| _ => st
end.

Definition eq_sterm_upto_cast (st1 st2:sterm) : bool :=
eq_sterm (remove_cast st1) (remove_cast st2).

(***************************************************************)
(** LLVM.syntax -> Symexe.syntax 
 * 
   If a function returns a pointer, e.g.
     define i32* @test(i32 %mm) nounwind
   Softbound translates it to be
     define void @softbound_test({ i32*, i8*, i8* }* %shadow_ret, i32 %mm)

   %shadow_ret is a returned pointer with its base and bound.

   At callsite,
     %3 = tail call i32* @test(i32 %2) nounwind
   is translated to be

     call void @softbound_test({ i32*, i8*, i8* }* %ret_tmp, i32 %2)
     %3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 0
     %4 = load i32** %3          
     %_base3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 1
     %call_repl_base = load i8** %_base3       
     %_bound4 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 2
     %call_repl_bound = load i8** %_bound4   

   The idea is defining an abstract call
     {%3, %call_repl_base, %call_repl_bound} = 
       call void @softbound_test({ i32*, i8*, i8* }* %ret_tmp, i32 %2)
   that equals to the above seven instructions.

*)

Inductive icall : Set :=
 | icall_nptr : id -> noret -> tailc -> typ -> value -> params -> icall
 | icall_ptr : id -> id -> id -> typ -> value -> id -> params -> icall.

Record isubblock := mkiSB
{
  iNBs : list nbranch;
  icall_cmd : icall
}.

Lemma isCall_inv : forall (c:cmd), isCall c = true -> 
  id * noret * tailc * typ * value * params.
Proof.
  destruct c; intros H; try solve [inversion H].
  split; auto.
Defined. 

(*
     %3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 0
     %4 = load i32** %3          
     %_base3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 1
     %call_repl_base = load i8** %_base3       
     %_bound4 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 2
     %call_repl_bound = load i8** %_bound4    
*)
Definition gen_icall (v:value) (pa0:params) (c1 c2 c3 c4 c5 c6:cmd) 
  : option icall :=
match c1 with
|insn_gep id11 _ t1 (value_id id12)
   (Cons_list_value (value_const (const_int _ i11 as c11)) 
     (Cons_list_value (value_const (const_int _ i12 as c12)) 
      Nil_list_value)) =>
  match c2 with
  |insn_load id21 t2 (value_id id22) _ =>
    match c3 with 
    |insn_gep id31 _ t3 (value_id id32) 
       (Cons_list_value (value_const (const_int _ i31 as c31)) 
         (Cons_list_value (value_const (const_int _ i32 as c32)) 
         Nil_list_value)) =>
      match c4 with
      |insn_load id41 t4 (value_id id42) _ =>
        match c5 with
        |insn_gep id51 _ t5 (value_id id52)
           (Cons_list_value (value_const (const_int _ i51 as c51)) 
           (Cons_list_value (value_const (const_int _ i52 as c52)) 
              Nil_list_value)) =>
           match c6 with
           |insn_load id61 t6 (value_id id62) _ =>
              match pa0 with
              | (
                 typ_pointer t0,
(*
   FIXME: This can also be a namedt that equals to typ_struct...  
   We should formalize the type equivalence algorithm.

                 typ_pointer (typ_struct 
                  (Cons_list_typ (typ_pointer _ as t01) 
                  (Cons_list_typ (typ_pointer _ as t02)
                  (Cons_list_typ (typ_pointer _ as t03) Nil_list_typ))) as t0),
*)
                 value_id id0)::pa0' =>
                if (tv_typ t1 t3 && tv_typ t3 t5 && tv_typ t5 t0 &&
(*
                    tv_typ t2 t01 && tv_typ t4 t02 && tv_typ t6 t03 &&
                    tv_typ t02 t03 && 
*)
                    eq_id id0 id12 && eq_id id0 id32 && eq_id id0 id52 &&
                    eq_id id11 id22 && eq_id id31 id42 && eq_id id51 id62 &&
                    eq_const c11 c12 && eq_const c11 c31 && eq_const c11 c51
                   ) 
                then 
                  Some (icall_ptr id21 id41 id61 t2 v id0 pa0')
                else None
              | _ => None
              end
           | _ => None
           end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end
| _ => None
end.

(* e.g. calloc -> softbound_calloc *)
Axiom syscall_returns_pointer : id -> bool.

(* Ps is from the input program. *)
Definition function_returns_pointer Ps1 fid2 : bool :=
match (rename_fid_inv fid2) with
| Some fid1 =>
    match lookupFdefViaIDFromProducts Ps1 fid1 with      
    | Some (fdef_intro (fheader_intro (typ_pointer _ as tp) _ _) _) => true
    | _ => syscall_returns_pointer fid1
    end
| None => false
end.

Fixpoint cmds2isbs (Ps1:products) (cs:cmds) : (list isubblock*list nbranch) :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCall_dec c) with
  | left isnotcall => 
    match (cmds2isbs Ps1 cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkiSB nbs call0::sbs', nbs0) => 
      (mkiSB (mkNB c isnotcall::nbs) call0::sbs', nbs0) 
    end
  | right iscall => 
    let '(id1, nr1, tc1, t1, v1, pa1) := isCall_inv c iscall in
    let '(sbs, nbs0, ic) :=
(*
    Do not check if the called function returns ptr. The problem is
    v1 can be a value that represents a function pointer. Statically, we 
    need more work to identidy it.

    We check this property at tv_call.

    match v1 with
    | value_const (const_gid _ fid2) => 
      if (function_returns_pointer Ps1 fid2) then
*)
        match cs' with
        | c1::c2::c3::c4::c5::c6::cs'' =>
          match (gen_icall v1 pa1 c1 c2 c3 c4 c5 c6) with
          | Some ic => (cmds2isbs Ps1 cs'', ic)
          | None => (cmds2isbs Ps1 cs', icall_nptr id1 nr1 tc1 t1 v1 pa1)
          end
        | _ => (cmds2isbs Ps1 cs', icall_nptr id1 nr1 tc1 t1 v1 pa1)
        end
(* 
      else (cmds2isbs Ps1 cs', icall_nptr id1 nr1 tc1 t1 v1 pa1)
    | _ => (cmds2isbs Ps1 cs', icall_nptr id1 nr1 tc1 t1 v1 pa1)
    end 
*)
    in (mkiSB nil ic::sbs, nbs0) 
  end
end.

Inductive wf_inbranchs : list nbranch -> Prop :=
| wf_inbranchs_intro : forall Ps cs nbs, 
  cmds2isbs Ps cs = (nil, nbs) ->
  NoDup (getCmdsIDs cs) ->
  wf_inbranchs nbs.

Inductive wf_isubblock : isubblock -> Prop :=
| wf_isubblock_intro : forall nbs call0, 
  wf_inbranchs nbs ->
  wf_isubblock (mkiSB nbs call0).

Inductive wf_isubblocks : list isubblock -> Prop :=
| wf_isubblocks_nil : wf_isubblocks nil
| wf_isubblocks_cons : forall sb sbs,
  wf_isubblock sb ->
  wf_isubblocks sbs ->
  wf_isubblocks (sb::sbs).

Inductive wf_iblock : block -> Prop :=
| wf_iblock_intro : forall Ps l ps cs sbs nbs tmn, 
  cmds2isbs Ps cs = (sbs,nbs) ->
  wf_isubblocks sbs ->
  wf_inbranchs nbs ->
  wf_iblock (block_intro l ps cs tmn).

Hint Constructors wf_isubblocks.

(************************************************************)
(* Generating metadata *) 

(* add b e p if they are not in md *)
Fixpoint add_bep (md:beps) (b e p:id) : beps :=
match md with
| nil => [(b,e,p)]
| (b',e',p')::md' => 
    if (eq_id b b' && eq_id e e' && eq_id p p') then md
    else (b',e',p')::add_bep md' b e p
end.

Fixpoint add_beps (accum bep:beps): beps :=
match bep with
| nil => accum
| (b,e,p)::bep' =>
  add_beps (add_bep accum b e p) bep'
end.

(* update if exists, add it otherwise *)
Fixpoint updateAdd_nbeps (m:nbeps) (i:nat) (gv:beps) : nbeps :=
match m with
| nil => (i, gv)::nil
| (i', gv')::m' =>
  if (beq_nat i i')
  then (i', gv)::m'
  else (i', gv')::updateAdd_nbeps m' i gv
end.

(* update only if exists, do nothing otherwise *)
Fixpoint update_nbeps (m:nbeps) (i:nat) (gv:beps) : nbeps :=
match m with
| nil => nil
| (i', gv')::m' =>
  if (beq_nat i i')
  then (i', gv)::m'
  else (i', gv')::update_nbeps m' i gv
end.

Fixpoint lookup_nbeps (m:nbeps) (i:nat) : option beps :=
match m with
| nil => None
| (i', gv')::m' =>
  if (beq_nat i i')
  then Some gv'
  else lookup_nbeps m' i
end.

(* If assert(b<=e<p), and b e p are defined wrt open variables,
   add those open variables.

   Assumption:
   1) Used within a subblock
   2) b e p must be created all together
   3) Within a subblock, b e can only be bitcasted or selected, 
      p can only be gep-ed or selected. 
*)
Fixpoint metadata_from_bep_aux (base bound ptr:sterm) (accum:beps) : beps :=
match (base, bound, ptr) with
| (sterm_val (value_id b), sterm_val (value_id e), sterm_val (value_id p)) => 
    add_bep accum b e p
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22, 
   sterm_select st30 _ st31 st32) =>
    if (eq_sterm st10 st20 && eq_sterm st20 st30) then
      metadata_from_bep_aux st11 st21 st31 
        (metadata_from_bep_aux st12 st22 st32 accum)
    else accum
| _ => accum
end.

Definition metadata_from_bep (base bound ptr:sterm) (accum:beps) : beps :=
  metadata_from_bep_aux (remove_cast base) (remove_cast bound) 
    (get_ptr_object ptr) accum.

Fixpoint metadata_from_smem (sm:smem) (accum:beps) : beps :=
match sm with
| smem_init => accum
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _ 
| smem_store sm1 _ _ _ _ => metadata_from_smem sm1 accum
| smem_lib sm1 lid1 sts1 =>
    metadata_from_smem sm1
    (if (is_dereferenceCheck lid1) then
      match sts1 with
      |  Cons_list_sterm base 
        (Cons_list_sterm bound
        (Cons_list_sterm ptr
        (Cons_list_sterm _
        (Cons_list_sterm _ Nil_list_sterm)))) => 
          metadata_from_bep base bound ptr accum
      | _ => accum
      end
    else accum)
end.

(* The propagation case
   sm: symbolic results of a subblock
   md: the bep we found so far
   accum: it must be md initially

   We consider 3 cases:
   1) b e p are copied
   2) b e are copied
   3) p is copied

   All the other cases are conservatively ignored.
*) 
Fixpoint metadata_from_sterms_aux (sm:smap) (accum md:beps) : beps :=
match md with
| nil => accum
| (b,e,p)::md' =>
    metadata_from_sterms_aux sm
      (match (lookupAL _ sm b, lookupAL _ sm e, lookupAL _ sm p) with
      | (Some sb, Some se, Some sp) =>
          metadata_from_bep sb se sp accum
      | (Some sb, Some se, None) =>
          match (remove_cast sb, remove_cast se) with
          | (sterm_val (value_id b'), sterm_val (value_id e')) => 
              add_bep accum b' e' p
          | _ => accum
          end
      | (None, None, Some sp) =>
          match (get_ptr_object sp) with
          | sterm_val (value_id p') => add_bep accum b e p'
          | _ => accum
          end
      |  _ => accum
      end) md'
end.

Fixpoint metadata_from_sterms (sm:smap) (accum:beps) : beps :=
  metadata_from_sterms_aux sm accum accum.

(* For correctness it does not matter whether metadata_from_smem is called
 * before metadata_from_sterms. But hopefully callling metadata_from_smem 
 * first can reduce some steps towards fixpoint, because it adds more bep
 * for metadata_from_sterms to propagate.
 *)
Definition metadata_from_cmds (nbs2 : list nbranch) (accum:beps) : beps :=
let st2 := se_cmds sstate_init nbs2 in 
let accum' := metadata_from_smem st2.(SMem) accum in
metadata_from_sterms st2.(STerms) accum'.

(* Parameters at callsite are some other resources of metadata. If a function
   has a pointer input, the pointer also has its base/bound as additional 
   inputs.
*)

(* We assume that the orders of ars and sars are matched. The function finds
   the corresponding sterm to arg with id i. 

  define fid2 (ars2) { ... }

  define fid ... {
    ...
  l1:
    call fid2 sars2
  }  
*)
Fixpoint lookupSarg (ars2:list (typ*id)) (sars2:list (typ*sterm)) (i:id) :
  option sterm :=
match (ars2, sars2) with
| (nil, nil) => None
| ((_,i')::ars2', (_,s')::sars2') =>
    if (eq_id i i') then Some s' else lookupSarg ars2' sars2' i
| _ => None
end.

(* ar_bep are base/bound in the arguments of function fid
   fid's arguments i args2
   sars2 is parameters supplied to fid at its callsite
*)
Fixpoint metadata_from_params (ar_bep:list (id*id*id)) ars2 sars2 
  (accum:beps) : beps :=
match ar_bep with
| nil => accum
| (b,e,p)::ar_bep' => metadata_from_params ar_bep' ars2 sars2 
    (match (lookupSarg ars2 sars2 b, lookupSarg ars2 sars2 e, 
      lookupSarg ars2 sars2 p) with
    | (Some sb, Some se, Some sp) => metadata_from_bep sb se sp accum
    | _ => accum
    end)
end.

Definition get_arg_metadata (md:flnbeps) fid : beps :=
match lookupAL _ md fid with
| None => nil
| Some lnbeps => 
  match lookupAL _ lnbeps (l_of_arg tt) with
  | None => nil
  | Some nbeps => 
    match lookup_nbeps nbeps O with
    | None => nil
    | Some beps => beps
    end
  end
end.

Inductive sicall : Set :=
| stmn_icall_nptr : 
    id -> noret -> tailc -> typ -> sterm -> list (typ*sterm) -> sicall
| stmn_icall_ptr : 
    id -> id -> id -> typ -> sterm -> sterm -> list (typ*sterm) -> sicall
.

Definition se_icall (st:sstate) (i:icall) : sicall :=
match i with
| icall_nptr id0 nr tc t0 v0 p0 =>
    stmn_icall_nptr id0 nr tc t0 (value2Sterm st.(STerms) v0) 
      (list_param__list_typ_subst_sterm p0 st.(STerms))
| icall_ptr id0 id1 id2 t0 v0 id4 p0 =>
    stmn_icall_ptr id0 id1 id2 t0 (value2Sterm st.(STerms) v0) 
      (lookupSmap st.(STerms) id4)
      (list_param__list_typ_subst_sterm p0 st.(STerms))
end.

Definition metadata_from_iscall Ps2 (flnbep0:flnbeps) (accum:beps) (c2:sicall) 
  : beps :=
match c2 with
| stmn_icall_nptr _ _ _ _ t2 tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then accum
      else
        match (lookupFdefViaIDFromProducts Ps2 fid2) with
        | None => accum
        | Some (fdef_intro (fheader_intro _ _ args2) _) =>
           metadata_from_params (get_arg_metadata flnbep0 fid2) args2 tsts2 accum
        end
  | _ => accum
  end
| stmn_icall_ptr _ _ _ _ t2 _ tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then accum
      else
        match (lookupFdefViaIDFromProducts Ps2 fid2) with
        | Some (fdef_intro (fheader_intro _ _ (_::args2)) _) =>
           metadata_from_params (get_arg_metadata flnbep0 fid2) args2 tsts2 accum
        | _ => accum
        end
  | _ => accum
  end
end.

Definition metadata_from_isubblock Ps2 flnbep (sb2:isubblock)
  (accum:beps) : beps :=
match sb2 with
| mkiSB nbs2 call2 => 
  let st2 := se_cmds sstate_init nbs2 in 
  let cl2 := se_icall st2 call2 in
  let accum' := metadata_from_iscall Ps2 flnbep accum cl2 in
  let accum'' := metadata_from_sterms st2.(STerms) accum' in
  metadata_from_smem st2.(SMem) accum''
end.

(* Find beps not in cs2 *)
Fixpoint metadata_diff_cmds (md:beps) (cs2:cmds) : beps :=
match md with
| nil => md
| (b,e,p)::md' => 
    match lookupBindingViaIDFromCmds cs2 p with
    | id_binding_cmd _ => metadata_diff_cmds md' cs2
    | _ => (b,e,p)::metadata_diff_cmds md' cs2
    end
end.

Definition update_pred_subblock (accum:nbeps) nth bep : nbeps :=
 let bep_nth := 
   match lookup_nbeps accum (S nth) with
   | None => nil
   | Some bep_nth => bep_nth
   end in
 updateAdd_nbeps accum (S nth) (add_beps bep_nth bep).

(* The indices of subblocks are [1 .. len]. Subblocks are visited in a 
   reversed order. *)
Fixpoint metadata_from_isubblocks_aux Ps2 flnbep len (sbs2:list isubblock) 
  (accum:nbeps) : nbeps :=
match sbs2 with
| nil => accum
| sb2::sbs2' => 
    let nth := List.length sbs2' in
    let bep :=
      match lookup_nbeps accum nth with
      | Some bep => bep 
      | None => nil
      end in
    let bep' := metadata_from_isubblock Ps2 flnbep sb2 bep in
    let accum' := update_nbeps accum (len - nth) bep' in
    let accum'' := update_pred_subblock accum' nth 
      (metadata_diff_cmds bep' (nbranchs2cmds sb2.(iNBs))) in
    metadata_from_isubblocks_aux Ps2 flnbep len sbs2' accum''
end.

Definition metadata_from_isubblocks Ps2 flnbep (sbs2:list isubblock) 
  (accum:nbeps) : nbeps :=
metadata_from_isubblocks_aux Ps2 flnbep (List.length sbs2) (List.rev sbs2) accum.

(* from phinodes 
    b = phi b1 b2 ...
    e = phi e1 e2 ...
    p = phi p1 p2 ...
  We only consider the case where all b e p are from phinodes. Because
  the phinodes of b e are generated by Softbound if their corresponding p
  is a phinode.
*)
Fixpoint lookupPhinode (phs:phinodes) (i:id) :=
match phs with
| nil => None
| (insn_phi i' t vs)::phs' =>
    if (eq_dec i i') then Some (insn_phi i' t vs)
    else lookupPhinode phs' i
end.

(* adding md0 into the last subblock of block l1 *)
Definition update_block_metadata (accum:lnbeps) (l1:l) (md0:beps) : lnbeps :=
let nbep :=
  match lookupAL _ accum l1 with
  | None => nil
  | Some nbep => nbep
  end in
let bep :=
  match lookup_nbeps nbep 0 with
  | None => nil
  | Some bep => bep
  end in
let bep' := add_beps bep md0 in
let nbep' := updateAdd_nbeps nbep 0 bep' in
updateAL _ accum l1 nbep'.

Definition metadata_from_value l1 (bv ev pv:value) (accum:lnbeps) : lnbeps :=
match (bv, ev, pv) with
| (value_id bid, value_id eid, value_id pid) => 
    update_block_metadata accum l1 [(bid, eid, pid)]
| _ => accum
end.

Fixpoint metadata_from_list_value_l (bvls evls pvls:list_value_l) (accum:lnbeps) 
  : lnbeps :=
match bvls with
| Nil_list_value_l => accum
| Cons_list_value_l bv bl bvls' =>
    metadata_from_list_value_l bvls' evls pvls
      (match (getValueViaLabelFromValuels evls bl,
             getValueViaLabelFromValuels pvls bl) with
      | (Some ev, Some pv) => metadata_from_value bl bv ev pv accum
      | _ => accum
      end)
end.

Fixpoint metadata_from_phinodes (ps2:phinodes) (accum:lnbeps) (md:beps) 
  : lnbeps :=
match md with
| nil => accum
| (b,e,p)::md' =>
    metadata_from_phinodes ps2
      (match (lookupPhinode ps2 b, lookupPhinode ps2 e, lookupPhinode ps2 p) with
       | (None, None, None) => accum
       | (Some (insn_phi _ _ bvls), 
          Some (insn_phi _ _ evls), 
          Some (insn_phi _ _ pvls)) =>
            metadata_from_list_value_l bvls evls pvls accum 
       | _ => accum
       end) md'
end.

(* adding md0 into blocks ls *)
Fixpoint updatePredBlocks (ls:list l) (accum:lnbeps) (md0:beps) : lnbeps :=
match ls with
| nil => accum
| l1::ls' => updatePredBlocks ls' (update_block_metadata accum l1 md0) md0
end.

(* Find beps not in ps2 *)
Fixpoint metadata_diff_phinodes (md:beps) (ps2:phinodes) : beps :=
match md with
| nil => md
| (b,e,p)::md' => 
    match lookupPhinode ps2 b with
    | None => (b,e,p)::metadata_diff_phinodes md' ps2
    | _ => metadata_diff_phinodes md' ps2
    end
end.

(* The beps not in the current ps2 and cs2 are falled-through from
   previous blocks. *)
Definition falling_through_metadata (md:beps) (b2:block) : beps :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
    metadata_diff_cmds (metadata_diff_phinodes md ps2) cs2
end.

(* Reimplement usedef, the one in ssa_lib is WRONG!!!!!!!!!! *)
Definition usedef_block := list (l*list l).

Definition update_udb (udb:usedef_block) (lu ld:l) : usedef_block :=
let ls :=
  match lookupAL _ udb ld with
  | Some ls => ls
  | None => nil
  end in
match (in_dec l_dec lu ls) with
| left _ => udb
| right _ => updateAddAL _ udb ld (lu::ls) 
end.

Definition genBlockUseDef_block b (udb:usedef_block) : usedef_block :=
match b with
| block_intro l0 _ _ tmn2 =>
  match tmn2 with
  | insn_br _ _ l1 l2 => update_udb (update_udb udb l0 l2) l0 l1
  | insn_br_uncond _ l1 => update_udb udb l0 l1
  | _ => udb
  end
end.

Fixpoint genBlockUseDef_blocks bs (udb:usedef_block) : usedef_block :=
match bs with
| nil => udb
| b::bs' => genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)
end.

Definition genBlockUseDef_fdef f2 : usedef_block :=
match f2 with
| fdef_intro _ lb2 => genBlockUseDef_blocks lb2 nil
end.

Definition metadata_from_block Ps1 Ps2 flnbep (b2:block) (udb:usedef_block) 
  (lnbep:lnbeps) : lnbeps :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
  let (sbs2, nbs2) := cmds2isbs Ps1 cs2 in
  let nbep0 :=
    match lookupAL _ lnbep l2 with
    | None => nil
    | Some nbep => nbep
    end in
  let bep0 :=
    match lookup_nbeps nbep0 0 with
    | None => nil
    | Some bep => bep
    end in
  let bep1 := metadata_from_cmds nbs2 bep0 in
  let nbep1 := updateAdd_nbeps nbep0 0 bep1 in
  let nbep2 := update_pred_subblock nbep1 0 
    (metadata_diff_cmds bep1 (nbranchs2cmds nbs2)) in
  let nbep3 := metadata_from_isubblocks Ps2 flnbep sbs2 nbep2 in
  let lnbep' := updateAddAL _ lnbep l2 nbep3 in
  let bep_phi :=
    match lookup_nbeps nbep3 (List.length sbs2+1) with
    | None => nil
    | Some bep => bep
    end in
  let lnbep'' := metadata_from_phinodes ps2 lnbep' bep_phi in
  let preds := 
    match lookupAL _ udb l2 with
    | Some ls => ls
    | None => nil
    end in
  updatePredBlocks preds lnbep'' (metadata_diff_phinodes bep_phi ps2)
end.

Fixpoint metadata_from_blocks_aux Ps1 Ps2 flnbep (bs2:blocks) (udb:usedef_block) 
  (lnbep:lnbeps) : lnbeps :=
match bs2 with
| nil => lnbep
| b2::bs2' => metadata_from_blocks_aux Ps1 Ps2 flnbep bs2' udb 
    (metadata_from_block Ps1 Ps2 flnbep b2 udb lnbep)
end.

Fixpoint eq_nbeps (md1 md2:nbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((n1,bep1)::md1', (n2,bep2)::md2') =>
    beq_nat n1 n2 && beq_nat (List.length bep1) (List.length bep2) &&
    eq_nbeps md1' md2'
| _ => false
end.

Fixpoint eq_lnbeps (md1 md2:lnbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((l1,nbep1)::md1', (l2,nbep2)::md2') =>
    eq_l l1 l2 && eq_nbeps nbep1 nbep2 && eq_lnbeps md1' md2'
| _ => false
end.

Fixpoint metadata_from_blocks Ps1 Ps2 flbep (bs2:blocks) (udb:usedef_block) 
  (md:lnbeps) (bsteps:onat) : lnbeps :=
match bsteps with
| Ozero => md 
| Osucc bsteps' => 
  let md' := metadata_from_blocks_aux Ps1 Ps2 flbep bs2 udb md in
  if eq_lnbeps md md' then md'
  else metadata_from_blocks Ps1 Ps2 flbep bs2 udb md' bsteps'
end.

Fixpoint metadata_from_args (a:args) (md accum:beps) : beps :=
match md with
| nil => accum
| (b,e,p)::md' => 
    metadata_from_args a md'
      (match (lookupBindingViaIDFromArgs a b,
              lookupBindingViaIDFromArgs a e,
              lookupBindingViaIDFromArgs a p) with
       | (id_binding_arg _, id_binding_arg _, id_binding_arg _) =>
           add_bep accum b e p
       | _ => accum
       end)
end.

Definition metadata_from_fdef Ps1 Ps2 flbep (f2:fdef) (md:lnbeps) (bsteps:onat) 
  : lnbeps :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then md 
  else 
   let accum := 
      metadata_from_blocks Ps1 Ps2 flbep lb2 (genBlockUseDef_fdef f2) md bsteps 
    in 
      match getEntryBlock f2 with
       | None => accum
       | Some (block_intro l2 _ _ _) =>
           match lookupAL _ accum l2 with
           | Some nbep => 
             match lookup_nbeps nbep (List.length nbep - 1) with
             | Some bep =>
               updateAddAL _ accum (l_of_arg tt) 
                 [(0, metadata_from_args a2 bep nil)]
             | None => accum
             end
           | _ => accum
           end
       end
end.

Fixpoint metadata_from_products_aux (Ps10 Ps20 Ps2:products) (md:flnbeps) 
  (bsteps:onat) : flnbeps :=
match Ps2 with
| nil => md
| product_fdef f2::Ps2' => 
    let lnbep0 := match lookupAL _ md (getFdefID f2) with
      | Some md => md 
      | None => nil
      end in 
    let lnbep := metadata_from_fdef Ps10 Ps20 md f2 lnbep0 bsteps in
    let md' := updateAddAL _ md (getFdefID f2) lnbep in
    metadata_from_products_aux Ps10 Ps20 Ps2' md' bsteps
| _::Ps2' => metadata_from_products_aux Ps10 Ps20 Ps2' md bsteps
end.

Fixpoint eq_flnbeps (md1 md2:flnbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((f1,lnbeps1)::md1', (f2,lnbeps2)::md2') =>
    eq_id f1 f2 && eq_lnbeps lnbeps1 lnbeps2 && eq_flnbeps md1' md2'
| _ => false
end.

Fixpoint metadata_from_products (Ps1 Ps2:products) (md:flnbeps) (bsteps:onat)
  (psteps:onat) : flnbeps :=
match psteps with
| Ozero => md 
| Osucc psteps' => 
  let md' := metadata_from_products_aux Ps1 Ps2 Ps2 md bsteps in
  if eq_flnbeps md md' then md'
  else metadata_from_products Ps1 Ps2 md' bsteps psteps'
end.

Definition metadata_from_module (m1 m2:module) (bsteps psteps:onat) :=
match (m1, m2) with
| (module_intro _ _ Ps1, module_intro _ _ Ps2) => 
    metadata_from_products Ps1 Ps2 nil bsteps psteps
end.

(************************************************************)
(* Generating addrof base/bound *) 

Definition abes := list (id*id).

(* add addrof b e if they are not in *)
Fixpoint add_abes (md:abes) (ab ae:id) : abes :=
match md with
| nil => [(ab,ae)]
| (ab',ae')::md' => 
    if (eq_id ab ab' && eq_id ae ae') then md
    else (ab',ae')::add_abes md' ab ae
end.

Fixpoint addrofbe_from_smem (sm:smem) (accum:abes) : abes :=
match sm with
| smem_init => accum
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _ 
| smem_store sm1 _ _ _ _ => addrofbe_from_smem sm1 accum
| smem_lib sm1 lid1 sts1 =>
    addrofbe_from_smem sm1
    (if (is_hashLoadBaseBound lid1) then
      match sts1 with
      |  Cons_list_sterm _ 
        (Cons_list_sterm addr_of_base
        (Cons_list_sterm addr_of_bound
        (Cons_list_sterm _
        (Cons_list_sterm _
        (Cons_list_sterm _ Nil_list_sterm))))) =>
          match (addr_of_base, addr_of_bound) with
          | (sterm_val (value_id ab), sterm_val (value_id ae)) =>
              add_abes accum ab ae
          | _ => accum
          end
      | _ => accum
      end
    else accum)
end.
 
Definition addrofbe_from_cmds (nbs2 : list nbranch) (md:abes) : abes :=
let st2 := se_cmds sstate_init nbs2 in 
addrofbe_from_smem st2.(SMem) md.

Definition addrofbe_from_subblock (sb2:subblock) (md:abes) : abes :=
match sb2 with
| mkSB nbs2 _ _ => addrofbe_from_cmds nbs2 md
end.

Fixpoint addrofbe_from_subblocks (sbs2:list subblock) (md:abes) : abes :=
match sbs2 with
| nil => md
| sb2::sbs2' => addrofbe_from_subblocks sbs2' (addrofbe_from_subblock sb2 md)
end.

Definition addrofbe_from_block (b2:block) (md:abes) : abes :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
  let (sbs2, nbs2) := cmds2sbs cs2 in
  let accum1 := addrofbe_from_cmds nbs2 md in
  addrofbe_from_subblocks sbs2 accum1
end.

Fixpoint addrofbe_from_blocks (bs2:blocks) (md:abes) : abes :=
match bs2 with
| nil => md
| b2::bs2' => addrofbe_from_blocks bs2' (addrofbe_from_block b2 md)
end.

Definition addrofbe_from_fdef (f2:fdef) (md:abes) : abes :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then md 
  else addrofbe_from_blocks lb2 nil
end.

Definition fabes := list (id*abes).

Fixpoint addrofbe_from_products (Ps2:products) (md:fabes) : fabes :=
match Ps2 with
| nil => md
| product_fdef f2::Ps2' => 
    let abes := addrofbe_from_fdef f2 nil in
    let md' := updateAddAL _ md (getFdefID f2) abes in
    addrofbe_from_products Ps2' md'
| _::Ps2' => addrofbe_from_products Ps2' md
end.

Definition addrofbe_from_module (m2:module) :=
match m2 with
| module_intro _ _ Ps2 => addrofbe_from_products Ps2 nil
end.

(***********************************************)
(* Sub TV *)

(*
declare weak void @__hashLoadBaseBound(
  i8* %addr_of_ptr, 
  i8** %addr_of_base, 
  i8** %addr_of_bound, 
  i8* %actual_ptr,    // useless 
  i32 %size_of_type,  // useless
  i32* %ptr_safe      // useless
  )

We assume 
  1) We have already checked that %addr_of_base, %addr_of_bound and %ptr_safe 
     are valid when being passed into @__hashLoadBaseBound. 
  2) __hashLoadBaseBound does not change %base, %bound and %ptr_safe.

So, %base, %bound and %ptr_safe are safe to load w/o memsafety checks.
*)
Fixpoint load_from_metadata (sm:smem) (st:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => load_from_metadata sm1 st
| smem_lib sm1 fid1 sts1 =>
  if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm _ 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm ptr_safe Nil_list_sterm))))) =>
      if (eq_sterm st addr_of_base || 
          eq_sterm st addr_of_bound || 
          eq_sterm st ptr_safe) 
      then true 
      else load_from_metadata sm1 st
    | _ => load_from_metadata sm1 st
    end
  else load_from_metadata sm1 st
end.

Definition tv_id fid (id1 id2:id) : bool :=
  eq_id (rename_id fid id1) id2.

Axiom tv_id_injective1 : forall fid id1 id2 id1' id2',
  id1 = id2 -> tv_id fid id1 id1' -> tv_id fid id2 id2' -> id1' = id2'.

Axiom tv_id_injective2 : forall fid id1 id2 id1' id2',
  id1 <> id2 -> tv_id fid id1 id1' -> tv_id fid id2 id2' -> id1' <> id2'.

Definition tv_fid (fid1 fid2:id) := 
  eq_id (rename_fid fid1) fid2.

Axiom tv_fid_injective1 : forall fid1 fid2 fid1' fid2',
  fid1 = fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' = fid2'.

Axiom tv_fid_injective2 : forall fid1 fid2 fid1' fid2',
  fid1 <> fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' <> fid2'.

Fixpoint tv_const fid (c c':const) : bool :=
match (c, c') with
| (const_zeroinitializer t0, const_zeroinitializer t0') => tv_typ t0 t0'
| (const_int _ _, const_int _ _) 
| (const_floatpoint _ _, const_floatpoint _ _)
| (const_undef _, const_undef _)
| (const_null _, const_null _) => eq_const c c'
| (const_arr t0 cs0, const_arr t0' cs0') => 
    tv_typ t0 t0' && tv_list_const fid cs0 cs0'
| (const_struct cs0, const_struct cs0') => tv_list_const fid cs0 cs0'
| (const_gid _ id0, const_gid _ id0') => 
    tv_fid id0 id0' || tv_id fid id0 id0'
| (const_truncop to0 c0 t0, const_truncop to0' c0' t0') =>
    sumbool2bool _ _ (truncop_dec to0 to0') && tv_const fid c0 c0' &&
    tv_typ t0 t0'
| (const_extop eo0 c0 t0, const_extop eo0' c0' t0') =>
    sumbool2bool _ _ (extop_dec eo0 eo0') && tv_const fid c0 c0' &&
    tv_typ t0 t0'
| (const_castop co0 c0 t0, const_castop co0' c0' t0') =>
    sumbool2bool _ _ (castop_dec co0 co0') && tv_const fid c0 c0' &&
    tv_typ t0 t0'
| (const_gep ib0 c0 cs0, const_gep ib0' c0' cs0') =>
    sumbool2bool _ _ (inbounds_dec ib0 ib0') && tv_const fid c0 c0' &&
    tv_list_const fid cs0 cs0' 
| (const_select c0 c1 c2, const_select c0' c1' c2') =>
    tv_const fid c0 c0' && tv_const fid c1 c1' && tv_const fid c2 c2'
| (const_icmp cd0 c0 c1, const_icmp cd0' c0' c1') =>
    sumbool2bool _ _ (cond_dec cd0 cd0') &&
    tv_const fid c0 c0' && tv_const fid c1 c1'
| (const_fcmp fd0 c0 c1, const_fcmp fd0' c0' c1') =>
    sumbool2bool _ _ (fcond_dec fd0 fd0') &&
    tv_const fid c0 c0' && tv_const fid c1 c1'
| (const_extractvalue c0 cs0, const_extractvalue c0' cs0') =>
    tv_const fid c0 c0' && tv_list_const fid cs0 cs0'
| (const_insertvalue c0 c1 cs0, const_insertvalue c0' c1' cs0') =>
    tv_const fid c0 c0' && tv_const fid c c1' && tv_list_const fid cs0 cs0'
| (const_bop b0 c0 c1, const_bop b0' c0' c1') =>
    sumbool2bool _ _ (bop_dec b0 b0') && 
    tv_const fid c0 c0' && tv_const fid c1 c1'
| (const_fbop f0 c0 c1, const_fbop f0' c0' c1') =>
    sumbool2bool _ _ (fbop_dec f0 f0') && 
    tv_const fid c0 c0' && tv_const fid c1 c1'
| _ => false
end
with tv_list_const fid (cs cs':list_const) : bool :=
match (cs, cs') with
| (Nil_list_const, Nil_list_const) => true
| (Cons_list_const c0 cs0, Cons_list_const c0' cs0') => 
    tv_const fid c0 c0' && tv_list_const fid cs0 cs0'
| _ => false
end.

Definition tv_value fid v1 v2 : bool :=
match (v1, v2) with
| (value_id id1, value_id id2) => tv_id fid id1 id2
| (value_const c1, value_const c2) => tv_const fid c1 c2
| _ => false
end.

Definition store_to_ret Ps1 Ps2 fid2 (ptr:sterm) : bool :=
if (function_returns_pointer Ps1 fid2) then
   match lookupFdefViaIDFromProducts Ps2 fid2 with      
   | Some (fdef_intro (fheader_intro _  _ ((_,re)::_)) _) =>
       eq_sterm (get_ptr_object ptr) (sterm_val (value_id re))
   | _ => false
   end
else false.

Fixpoint tv_sterm Ps1 Ps2 fid (st st':sterm) : bool :=
match (st, st') with
| (sterm_val v, sterm_val v') => tv_value fid v v'
| (sterm_bop b sz st1 st2, sterm_bop b' sz' st1' st2') =>
    sumbool2bool _ _ (bop_dec b b') && sumbool2bool _ _ (Size.dec sz sz') &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_fbop b f st1 st2, sterm_fbop b' f' st1' st2') =>
    sumbool2bool _ _ (fbop_dec b b') && 
    sumbool2bool _ _ (floating_point_dec f f') &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_extractvalue t st1 cs, sterm_extractvalue t' st1' cs') =>
    tv_typ t t' && tv_sterm Ps1 Ps2 fid st1 st1' &&
  sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_insertvalue t1 st1 t2 st2 cs, 
   sterm_insertvalue t1' st1' t2' st2' cs') =>
    tv_typ t1 t1' && tv_sterm Ps1 Ps2 fid st1 st1' && 
    tv_typ t2 t2' && tv_sterm Ps1 Ps2 fid st2 st2' &&
    sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_malloc sm t st1 a, sterm_malloc sm' t' st1' a') =>
    tv_smem Ps1 Ps2 fid sm sm' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_align a a'
| (sterm_alloca sm t st1 a, sterm_alloca sm' t' st1' a') =>
    tv_smem Ps1 Ps2 fid sm sm' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_align a a'
| (sterm_load sm t st1 a, sterm_load sm' t' st1' a') =>
    tv_smem Ps1 Ps2 fid sm sm' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_align a a'
| (sterm_gep i t st1 sts2, sterm_gep i' t' st1' sts2') =>
    sumbool2bool _ _ (bool_dec i i') && tv_typ t t' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_list_sterm Ps1 Ps2 fid sts2 sts2'
| (sterm_trunc top t1 st1 t2, sterm_trunc top' t1' st1' t2') =>
    sumbool2bool _ _ (truncop_dec top top') && tv_typ t1 t1' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t2 t2'
| (sterm_ext eo t1 st1 t2, sterm_ext eo' t1' st1' t2') =>
    sumbool2bool _ _ (extop_dec eo eo') && tv_typ t1 t1' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t2 t2' 
| (sterm_cast co t1 st1 t2, sterm_cast co' t1' st1' t2') =>
    sumbool2bool _ _ (castop_dec co co') && tv_typ t1 t1' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t2 t2' 
| (sterm_icmp c t st1 st2, sterm_icmp c' t' st1' st2') =>
    sumbool2bool _ _ (cond_dec c c') && tv_typ t t' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_fcmp c ft st1 st2, sterm_fcmp c' ft' st1' st2') =>
    sumbool2bool _ _ (fcond_dec c c') &&
    sumbool2bool _ _ (floating_point_dec ft ft') &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_phi t stls, sterm_phi t' stls') =>
    tv_typ t t' && tv_list_sterm_l Ps1 Ps2 fid stls stls'
| (sterm_select st1 t st2 st3, sterm_select st1' t' st2' st3') =>
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st2 st2' && tv_sterm Ps1 Ps2 fid st3 st3'
| (sterm_lib sm i sts, sterm_lib sm' i' sts') =>
    tv_smem Ps1 Ps2 fid sm sm' && eq_id i i' && 
    tv_list_sterm Ps1 Ps2 fid sts sts'
| _ => false
end
with tv_list_sterm Ps1 Ps2 fid (sts sts':list_sterm) : bool :=
match (sts, sts') with
| (Nil_list_sterm, Nil_list_sterm) => true
| (Cons_list_sterm st sts0, Cons_list_sterm st' sts0') =>
    tv_sterm Ps1 Ps2 fid st st' && tv_list_sterm Ps1 Ps2 fid sts0 sts0'
| _ => false
end
with tv_list_sterm_l Ps1 Ps2 fid (stls stls':list_sterm_l) : bool :=
match (stls, stls') with
| (Nil_list_sterm_l, Nil_list_sterm_l) => true
| (Cons_list_sterm_l st l stls0, Cons_list_sterm_l st' l' stls0') =>
    tv_sterm Ps1 Ps2 fid st st' && sumbool2bool _ _ (l_dec l l') && 
    tv_list_sterm_l Ps1 Ps2 fid stls0 stls0'
| _ => false
end
with tv_smem Ps1 Ps2 fid (sm1 sm2:smem) : bool :=
match (sm1, sm2) with
| (smem_init, _) => true
| (smem_malloc sm1 t1 st1 a1, smem_malloc sm2 t2 st2 a2) =>
    tv_smem Ps1 Ps2 fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2
| (smem_alloca sm1 t1 st1 a1, smem_alloca sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_alloca sm1 t1 st1 a1) sm2
| (smem_free sm1 t1 st1, smem_free sm2 t2 st2) =>
    tv_smem Ps1 Ps2 fid sm1 sm2 && tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2
| (smem_load sm1 t1 st1 a1, smem_load sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_load sm1 t1 st1 a1) sm2 &&
         load_from_metadata sm2 st2
| (smem_store sm1 t1 st11 st12 a1, smem_store sm2 t2 st21 st22 a2) =>
    if (tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st11 st21 &&
        tv_sterm Ps1 Ps2 fid st12 st22 && tv_align a1 a2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_store sm1 t1 st11 st12 a1) sm2 &&
         store_to_ret Ps1 Ps2 (rename_fid fid) st22
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    if (eq_id fid1 fid2 && tv_list_sterm Ps1 Ps2 fid sts1 sts2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_lib sm1 fid1 sts1) sm2
| (sm1, smem_lib sm2 lid sts) => smem_lib_sub lid && tv_smem Ps1 Ps2 fid sm1 sm2
| (sm1, smem_alloca sm2 t2 st2 a2) => tv_smem Ps1 Ps2 fid sm1 sm2
| (sm1, smem_load sm2 t2 st2 a2) => 
  (* We check load_from_metadata to ensure that the behavior of output programs 
   * preserves input's. If we did not check, the additional load may be stuck. 
   *)
    tv_smem Ps1 Ps2 fid sm1 sm2 && load_from_metadata sm2 st2
| (sm1, smem_store sm2 t2 st21 st22 a2) => 
  (* We check that the additional stores must be to shadow_ret. *)
    tv_smem Ps1 Ps2 fid sm1 sm2 && store_to_ret Ps1 Ps2 (rename_fid fid) st22
| _ => false
end.

Fixpoint tv_sframe Ps1 Ps2 fid (sf1 sf2:sframe) : bool :=
match (sf1, sf2) with
| (sframe_init, _) => true
| (sframe_alloca sm1 sf1 t1 st1 a1, sframe_alloca sm2 sf2 t2 st2 a2) =>
    if (tv_smem Ps1 Ps2 fid sm1 sm2 && tv_typ t1 t2 && 
        tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2)
    then tv_sframe Ps1 Ps2 fid sf1 sf2
    else tv_sframe Ps1 Ps2 fid (sframe_alloca sm1 sf1 t1 st1 a1) sf2
| _ => false
end.

Fixpoint tv_smap Ps1 Ps2 fid (sm1 sm2:smap) : bool :=
match sm1 with
| nil => true
| (id1,st1)::sm1' =>
  match lookupAL _ sm2 (rename_id fid id1) with
  | None => false
  | Some st2 => tv_sterm Ps1 Ps2 fid st1 st2 && tv_smap Ps1 Ps2 fid sm1' sm2
  end
end.

Definition sub_sstate Ps1 Ps2 fid s1 s2 := 
  tv_smap Ps1 Ps2 fid s1.(STerms) s2.(STerms) = true /\ 
  tv_smem Ps1 Ps2 fid s1.(SMem) s2.(SMem) = true /\
  tv_sframe Ps1 Ps2 fid s1.(SFrame) s2.(SFrame) = true /\ 
  s1.(SEffects) = s2.(SEffects).

Lemma sstate_sub_dec : forall Ps1 Ps2 fid (sts1 sts2:sstate), 
  uniq sts1.(STerms) -> 
  {sub_sstate Ps1 Ps2 fid sts1 sts2} + {~sub_sstate Ps1 Ps2 fid sts1 sts2}.
Proof.
Ltac done_right' := 
  right; intro J ; destruct J as [ J1 [J2 [J3 J4]]]; simpl in *; auto.

  intros Ps1 Ps2 fid sts1 sts2 Huniq.
  destruct sts1 as [st1 sm1 sf1 se1].
  destruct sts2 as [st2 sm2 sf2 se2].
  destruct (@sterms_dec se1 se2); subst; try solve [done_right'].
  unfold sub_sstate. simpl.
  destruct (tv_smap Ps1 Ps2 fid st1 st2); auto.
  destruct (tv_smem Ps1 Ps2 fid sm1 sm2); auto.
  destruct (tv_sframe Ps1 Ps2 fid sf1 sf2); auto.
    right. intro J ; destruct J as [ J1 [J2 [J3 J4]]]. inversion J3.
    right. intro J ; destruct J as [ J1 [J2 [J3 J4]]]. inversion J2.
    right. intro J ; destruct J as [ J1 [J2 [J3 J4]]]. inversion J1.
Qed.

Definition tv_cmds Ps1 Ps2 fid (nbs1 nbs2 : list nbranch) :=
sumbool2bool _ _ 
  (sstate_sub_dec Ps1 Ps2 fid 
    (se_cmds sstate_init nbs1) 
    (se_cmds sstate_init nbs2) 
    (se_cmds_init_uniq nbs1)).

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Fixpoint tv_params Ps1 Ps2 fid (tsts1 tsts2:list (typ*sterm)) : bool :=
match (tsts1, tsts2) with
| (nil, _) => true
| ((t1,st1)::tsts1', (t2,st2)::tsts2') => 
  tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2 && 
  tv_params Ps1 Ps2 fid tsts1' tsts2'
| _ => false
end.

(* Do not check if their tailc flags match. Softbound changes the flag for
 * system calls, say atoi from tailcall to non-tailcall.
 *)

Inductive scall : Set :=
| stmn_call : id -> noret -> tailc -> typ -> sterm -> list (typ*sterm) -> scall
.

Definition se_call : forall (st : sstate)(i:cmd)(iscall:isCall i = true), scall.
Proof.
  intros. unfold isCall in iscall.
  destruct i0; try solve [inversion iscall].
  apply (@stmn_call i0 n t t0 (value2Sterm st.(STerms) v) 
                      (list_param__list_typ_subst_sterm p st.(STerms))).
Defined.

Definition tv_scall Ps1 Ps2 fid (c1:scall) (c2:sicall) :=
  let '(stmn_call rid1 nr1 _ ty1 t1 tsts1) := c1 in
  match c2 with
  | stmn_icall_nptr rid2 nr2 _ ty2 t2 tsts2 =>
    tv_id fid rid1 rid2 &&
    (sumbool2bool _ _ (noret_dec nr1 nr2)) &&
    tv_typ ty1 ty2 && tv_params Ps1 Ps2 fid tsts1 tsts2 && 
    tv_sterm Ps1 Ps2 fid (remove_cast t1) (remove_cast t2)
  | stmn_icall_ptr rid2 _ _ ty2 t2 _ tsts2 =>
    tv_id fid rid1 rid2 &&
    tv_typ ty1 ty2 && tv_params Ps1 Ps2 fid tsts1 tsts2 && 
    match (remove_cast t1, remove_cast t2) with
    | (sterm_val (value_const (const_gid _ fid1)),
       sterm_val (value_const (const_gid _ fid2))) =>
      tv_fid fid1 fid2 && function_returns_pointer Ps1 fid2
    | (st1, st2) => tv_sterm Ps1 Ps2 fid st1 st2
    end
  end.

Definition tv_subblock Ps1 Ps2 fid (sb1:subblock) (sb2:isubblock) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkiSB nbs2 call2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_icall st2 call2 in
   (sumbool2bool _ _ 
     (sstate_sub_dec Ps1 Ps2 fid st1 st2 (se_cmds_init_uniq nbs1))) &&
   tv_scall Ps1 Ps2 fid cl1 cl2 
end.

Fixpoint tv_subblocks Ps1 Ps2 fid (sbs1:list subblock) (sbs2:list isubblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
    (tv_subblock Ps1 Ps2 fid sb1 sb2) && (tv_subblocks Ps1 Ps2 fid sbs1' sbs2')
| _ => false
end.

Fixpoint tv_list_value_l fid (vls1 vls2:list_value_l) : bool :=
match (vls1, vls2) with
| (Nil_list_value_l, Nil_list_value_l) => true
| (Cons_list_value_l v1 l1 vls1, Cons_list_value_l v2 l2 vls2) =>
    tv_value fid v1 v2 && eq_l l1 l2 && tv_list_value_l fid vls1 vls2
| _ => false
end.

Definition tv_phinode fid (p1 p2:phinode) : bool :=
match (p1, p2) with
| (insn_phi id1 t1 vls1, insn_phi id2 t2 vls2) =>
    tv_id fid id1 id2  && tv_typ t1 t2 && tv_list_value_l fid vls1 vls2
end.

Fixpoint tv_phinodes fid (ps1 ps2:phinodes) : bool :=
match ps1 with
| nil => true
| (insn_phi i1 _ _)as p1::ps1' =>
  match lookupPhinode ps2 (rename_id fid i1) with
  | None => false
  | Some p2 => tv_phinode fid p1 p2 && tv_phinodes fid ps1' ps2
  end
end.

(*
  For a function that returns a pointer, Softbound translates
         ret i32* %8                                                           
  into
         %.ptr = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 0
         %.base = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 1
         store i8* %bitcast, i8** %.base
         %.bound = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 2
         store i8* %bitcast4, i8** %.bound
         store i32* %8, i32** %.ptr
         ret void
 
  gen_iret returns %shadow_ret %.base %.base %.ptr i32* 
*)
Definition gen_iret t0 id0 (c1 c2 c3 c4 c5 c6:cmd) :=
match c1 with
|insn_gep id11 _ 
(*
   FIXME: This can also be a namedt...  We should formalize the type
   equivalence algorithm.

   (typ_struct 
     (Cons_list_typ (typ_pointer _ as t01) 
     (Cons_list_typ (typ_pointer _ as t02)
     (Cons_list_typ (typ_pointer _ as t03) Nil_list_typ))) as t1)
*)
   t1
   (value_id id12)
   (Cons_list_value (value_const (const_int _ i11 as c11)) 
     (Cons_list_value (value_const (const_int _ i12 as c12)) 
      Nil_list_value)) =>
  match c2 with 
  |insn_gep id21 _ t2 (value_id id22) 
     (Cons_list_value (value_const (const_int _ i21 as c21)) 
       (Cons_list_value (value_const (const_int _ i22 as c22)) 
       Nil_list_value)) =>
    match c3 with
    |insn_store id31 t3 v3 (value_id id32) _ =>
      match c4 with
      |insn_gep id41 _ t4 (value_id id42)
         (Cons_list_value (value_const (const_int _ i41 as c41)) 
         (Cons_list_value (value_const (const_int _ i42 as c42)) 
            Nil_list_value)) =>
        match c5 with
        |insn_store id51 t5 v5 (value_id id52) _ =>
           match c6 with
           |insn_store id61 t6 v6 (value_id id62) _ =>
              if (tv_typ t0 (typ_pointer t1) && tv_typ t1 t2 && tv_typ t2 t4 &&
(*
                  tv_typ t6 t01 && tv_typ t3 t02 && tv_typ t5 t03 &&
                  tv_typ t02 t03 &&
*)
                  eq_id id0 id12 && eq_id id12 id22 && eq_id id22 id42 &&
                  eq_id id11 id62 && eq_id id21 id32 && eq_id id41 id52 &&
                  eq_const c11 c12 && eq_const c11 c21 && eq_const c11 c41
                 ) 
              then 
                Some (id12, v3, v5, v6, t6)
              else None
           | _ => None
           end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end
| _ => None
end.

Definition tv_terminator fid (tmn1 tmn2:terminator) : bool :=
match (tmn1, tmn2) with
| (insn_return id1 t1 v1, insn_return id2 t2 v2) => 
    tv_id fid id1 id2 && tv_typ t1 t2 && tv_value fid v1 v2
| (insn_return_void id1, insn_return_void id2) => tv_id fid id1 id2
| (insn_br id1 v1 l11 l12, insn_br id2 v2 l21 l22) =>
    tv_id fid id1 id2 && tv_value fid v1 v2 && eq_l l11 l21 && eq_l l12 l22
| (insn_br_uncond id1 l1, insn_br_uncond id2 l2) =>
    tv_id fid id1 id2 && eq_l l1 l2
| (insn_unreachable id1, insn_unreachable id2) => tv_id fid id1 id2
| _ => false
end.

Definition get_last_six_insns (cs:cmds) :=
match (List.rev cs) with
| c6::c5::c4::c3::c2::c1::cs' => (List.rev cs', Some (c1, c2, c3, c4, c5, c6))
| _ => (cs, None)
end.

Definition tv_block Ps1 Ps2 fid (b1 b2:block) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  let '(cs2', op) :=
    match lookupFdefViaIDFromProducts Ps1 fid with      
    | Some (fdef_intro (fheader_intro (typ_pointer _ as tp) _ _) _) =>
      match lookupFdefViaIDFromProducts Ps2 (rename_fid fid) with 
      | Some (fdef_intro (fheader_intro _ _ ((t2,id2)::_)) _) =>
          let '(cs2', opcs6) := get_last_six_insns cs2 in
          match opcs6 with
          | Some (c1,c2,c3,c4,c5,c6) => 
             (* gen_iret returns %shadow_ret %.base %.base %.ptr i32 *)
             match gen_iret t2 id2 c1 c2 c3 c4 c5 c6 with
             | None => (cs2, None)
             | op => (cs2', op)
             end
          | None => (cs2, None)
          end
      | _ => (cs2, None)
      end
    | _ => (cs2, None)
    end in 
  match (cmds2sbs cs1, cmds2isbs Ps1 cs2') with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    eq_l l1 l2 && tv_phinodes fid ps1 ps2 && 
    tv_subblocks Ps1 Ps2 fid sbs1 sbs2 &&
    tv_cmds Ps1 Ps2 fid nbs1 nbs2 && 
    match op with 
    | Some (id20, v21, v22, v23, t20) =>
        match (tmn1, tmn2) with
        | (insn_return id1 t1 v1, insn_return_void _) => tv_value fid v1 v23
        | _ => tv_terminator fid tmn1 tmn2
        end
    | None => tv_terminator fid tmn1 tmn2
    end
  end 
end.

Fixpoint tv_blocks Ps1 Ps2 fid (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => 
    tv_block Ps1 Ps2 fid b1 b2 && tv_blocks Ps1 Ps2 fid bs1' bs2'
| _ => false
end.

Definition tv_fheader Ps1 (f1 f2:fheader) := 
  let '(fheader_intro t1 fid1 a1) := f1 in
  let '(fheader_intro t2 fid2 a2) := f2 in
  tv_fid fid1 fid2 &&
  if (function_returns_pointer Ps1 fid2) then
    if (syscall_returns_pointer fid1) then true
    else
      match a2 with
(*
    | (typ_pointer (typ_struct 
        (Cons_list_typ t21
        (Cons_list_typ _
        (Cons_list_typ _ Nil_list_typ)))),_)::a2' =>
      (sumbool2bool _ _ (typ_dec t1 t21)) &&
      (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2'))
*)
      | (typ_pointer _,_)::a2' =>
        (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2'))
      | _ => false
      end
  else
    (sumbool2bool _ _ (typ_dec t1 t2)) &&
    (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2)).

Definition tv_fdec Ps1 (f1 f2:fdec) :=
match (f1, f2) with
| (fdec_intro fh1, fdec_intro fh2) => tv_fheader Ps1 fh1 fh2
end.

Definition tv_fdef Ps1 Ps2 (f1 f2:fdef) :=
match (f1, f2) with
| (fdef_intro (fheader_intro _ fid1 _ as fh1) lb1, fdef_intro fh2 lb2) =>
  tv_fheader Ps1 fh1 fh2 && tv_blocks Ps1 Ps2 fid1 lb1 lb2
end.

Fixpoint lookupGvarViaIDFromProducts (lp:products) (i:id) : option gvar :=
match lp with
| nil => None
| (product_gvar gv)::lp' => 
    if (eq_dec (getGvarID gv) i) then Some gv
    else lookupGvarViaIDFromProducts lp' i
| _::lp' => lookupGvarViaIDFromProducts lp' i
end.

Fixpoint tv_products (Ps10 Ps1 Ps2:products) : bool :=
match Ps1 with
| nil => true
| product_gvar gv1::Ps1' =>
  match lookupGvarViaIDFromProducts Ps2 (getGvarID gv1) with
  | None => false
  | Some gv2 => sumbool2bool _ _ (gvar_dec gv1 gv2) && tv_products Ps10 Ps1' Ps2 
  end
| product_fdec f1::Ps1' =>
  match lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1)) with
  | None => false
  | Some f2 => tv_fdec Ps10 f1 f2 && tv_products Ps10 Ps1' Ps2 
  end
| product_fdef f1::Ps1' =>
  match lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1)) with
  | None => false
  | Some f2 => tv_fdef Ps10 Ps2 f1 f2 && tv_products Ps10 Ps1' Ps2 
  end
end.

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  tv_products Ps1 Ps1 Ps2
end.

Fixpoint tv_system (S1 S2:system) :=
match (S1, S2) with
| (nil, nil) => true
| (m1::S1', m2::S2') => tv_module m1 m2 && tv_system S1' S2'
| _ => false
end.

(***********************************************)
(* Sub TV (guessing renamings) *)

Fixpoint rtv_const (c c':const) : bool :=
match (c, c') with
| (const_zeroinitializer t0, const_zeroinitializer t0') => tv_typ t0 t0'
| (const_int _ _, const_int _ _) 
| (const_floatpoint _ _, const_floatpoint _ _)
| (const_undef _, const_undef _)
| (const_null _, const_null _) => eq_const c c'
| (const_arr t0 cs0, const_arr t0' cs0') => 
    tv_typ t0 t0' && rtv_list_const cs0 cs0'
| (const_struct cs0, const_struct cs0') => rtv_list_const cs0 cs0'
| (const_gid _ id0, const_gid _ id0') => 
    tv_fid id0 id0' || 
    eq_id id0 id0' (* assuming global variables are not renamed *)
| (const_truncop to0 c0 t0, const_truncop to0' c0' t0') =>
    sumbool2bool _ _ (truncop_dec to0 to0') && rtv_const c0 c0' &&
    tv_typ t0 t0'
| (const_extop eo0 c0 t0, const_extop eo0' c0' t0') =>
    sumbool2bool _ _ (extop_dec eo0 eo0') && rtv_const c0 c0' &&
    tv_typ t0 t0'
| (const_castop co0 c0 t0, const_castop co0' c0' t0') =>
    sumbool2bool _ _ (castop_dec co0 co0') && rtv_const c0 c0' &&
    tv_typ t0 t0'
| (const_gep ib0 c0 cs0, const_gep ib0' c0' cs0') =>
    sumbool2bool _ _ (inbounds_dec ib0 ib0') && rtv_const c0 c0' &&
    rtv_list_const cs0 cs0' 
| (const_select c0 c1 c2, const_select c0' c1' c2') =>
    rtv_const c0 c0' && rtv_const c1 c1' && rtv_const c2 c2'
| (const_icmp cd0 c0 c1, const_icmp cd0' c0' c1') =>
    sumbool2bool _ _ (cond_dec cd0 cd0') &&
    rtv_const c0 c0' && rtv_const c1 c1'
| (const_fcmp fd0 c0 c1, const_fcmp fd0' c0' c1') =>
    sumbool2bool _ _ (fcond_dec fd0 fd0') &&
    rtv_const c0 c0' && rtv_const c1 c1'
| (const_extractvalue c0 cs0, const_extractvalue c0' cs0') =>
    rtv_const c0 c0' && rtv_list_const cs0 cs0'
| (const_insertvalue c0 c1 cs0, const_insertvalue c0' c1' cs0') =>
    rtv_const c0 c0' && rtv_const c c1' && rtv_list_const cs0 cs0'
| (const_bop b0 c0 c1, const_bop b0' c0' c1') =>
    sumbool2bool _ _ (bop_dec b0 b0') && 
    rtv_const c0 c0' && rtv_const c1 c1'
| (const_fbop f0 c0 c1, const_fbop f0' c0' c1') =>
    sumbool2bool _ _ (fbop_dec f0 f0') && 
    rtv_const c0 c0' && rtv_const c1 c1'
| _ => false
end
with rtv_list_const (cs cs':list_const) : bool :=
match (cs, cs') with
| (Nil_list_const, Nil_list_const) => true
| (Cons_list_const c0 cs0, Cons_list_const c0' cs0') => 
    rtv_const c0 c0' && rtv_list_const cs0 cs0'
| _ => false
end.

(* mapping from an input local variable to its output local variable within
   a function. *)
Definition renaming := list (id * id).

(* Check if an id is a name of tmp var, e.g. %100 *)
Axiom is_tmp_var : id -> bool.

Definition lookup_renaming r i :=
if is_tmp_var i then
  match lookupAL _ r i with
  | Some i' => Some i'
  | None => None
  end
else Some i.

Definition rtv_id (r:renaming) id1 id2 :=
  match lookup_renaming r id1 with
  | None => eq_id id1 id2
  | Some id2' => eq_id id2 id2'
  end.

Definition rtv_value r v1 v2 : option renaming :=
match (v1, v2) with
| (value_id id1, value_id id2) => 
  match lookup_renaming r id1 with
  | None => Some ((id1,id2)::r)
  | Some id2' => if eq_id id2 id2' then Some r else None
  end
| (value_const c1, value_const c2) => if rtv_const c1 c2 then Some r else None
| _ => None
end.

Fixpoint rtv_sterm Ps1 Ps2 fid r (st st':sterm) : option renaming :=
match (st, st') with
| (sterm_val v, sterm_val v') => rtv_value r v v'
| (sterm_bop b sz st1 st2, sterm_bop b' sz' st1' st2') =>
    if sumbool2bool _ _ (bop_dec b b') && sumbool2bool _ _ (Size.dec sz sz') then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_fbop b f st1 st2, sterm_fbop b' f' st1' st2') =>
    if sumbool2bool _ _ (fbop_dec b b') && 
       sumbool2bool _ _ (floating_point_dec f f')
    then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_extractvalue t st1 cs, sterm_extractvalue t' st1' cs') =>
    if tv_typ t t' && sumbool2bool _ _ (list_const_dec cs cs') then
      rtv_sterm Ps1 Ps2 fid r st1 st1'
    else None
| (sterm_insertvalue t1 st1 t2 st2 cs, 
   sterm_insertvalue t1' st1' t2' st2' cs') =>
    if tv_typ t1 t1' && tv_typ t2 t2' && 
       sumbool2bool _ _ (list_const_dec cs cs') then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_malloc sm t st1 a, sterm_malloc sm' t' st1' a') =>
    if tv_typ t t' && tv_align a a' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st1 st1')
    else None
| (sterm_alloca sm t st1 a, sterm_alloca sm' t' st1' a') =>
    if tv_typ t t' && tv_align a a' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st1 st1')
    else None
| (sterm_load sm t st1 a, sterm_load sm' t' st1' a') =>
    if tv_typ t t' && tv_align a a' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st1 st1')
    else None
| (sterm_gep i t st1 sts2, sterm_gep i' t' st1' sts2') =>
    if sumbool2bool _ _ (bool_dec i i') && tv_typ t t' then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_list_sterm Ps1 Ps2 fid r sts2 sts2')
    else None
| (sterm_trunc top t1 st1 t2, sterm_trunc top' t1' st1' t2') =>
    if sumbool2bool _ _ (truncop_dec top top') && tv_typ t1 t1' && tv_typ t2 t2'
    then rtv_sterm Ps1 Ps2 fid r st1 st1'
    else None
| (sterm_ext eo t1 st1 t2, sterm_ext eo' t1' st1' t2') =>
    if sumbool2bool _ _ (extop_dec eo eo') && tv_typ t1 t1' && tv_typ t2 t2' 
    then rtv_sterm Ps1 Ps2 fid r st1 st1'
    else None
| (sterm_cast co t1 st1 t2, sterm_cast co' t1' st1' t2') =>
    if sumbool2bool _ _ (castop_dec co co') && tv_typ t1 t1' && tv_typ t2 t2' 
    then rtv_sterm Ps1 Ps2 fid r st1 st1' 
    else None
| (sterm_icmp c t st1 st2, sterm_icmp c' t' st1' st2') =>
    if sumbool2bool _ _ (cond_dec c c') && tv_typ t t' then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_fcmp c ft st1 st2, sterm_fcmp c' ft' st1' st2') =>
    if sumbool2bool _ _ (fcond_dec c c') &&
       sumbool2bool _ _ (floating_point_dec ft ft') then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_phi t stls, sterm_phi t' stls') =>
    if tv_typ t t' then rtv_list_sterm_l Ps1 Ps2 fid r stls stls' else None
| (sterm_select st1 t st2 st3, sterm_select st1' t' st2' st3') =>
    if tv_typ t t' then 
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>= 
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2') >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st3 st3')
    else None
| (sterm_lib sm i sts, sterm_lib sm' i' sts') =>
    if eq_id i i' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_list_sterm Ps1 Ps2 fid r sts sts')
    else None
| _ => None
end
with rtv_list_sterm Ps1 Ps2 fid r (sts sts':list_sterm) : option renaming :=
match (sts, sts') with
| (Nil_list_sterm, Nil_list_sterm) => Some r
| (Cons_list_sterm st sts0, Cons_list_sterm st' sts0') =>
    rtv_sterm Ps1 Ps2 fid r st st' >>=
    fun r => rtv_list_sterm Ps1 Ps2 fid r sts0 sts0'
| _ => None
end
with rtv_list_sterm_l Ps1 Ps2 fid r (stls stls':list_sterm_l) 
  : option renaming :=
match (stls, stls') with
| (Nil_list_sterm_l, Nil_list_sterm_l) => Some r
| (Cons_list_sterm_l st l stls0, Cons_list_sterm_l st' l' stls0') =>
    if sumbool2bool _ _ (l_dec l l') then
      rtv_sterm Ps1 Ps2 fid r st st' >>=
      fun r => rtv_list_sterm_l Ps1 Ps2 fid r stls0 stls0'
    else None
| _ => None
end
with rtv_smem Ps1 Ps2 fid r (sm1 sm2:smem) : option renaming :=
match (sm1, sm2) with
| (smem_init, _) => Some r
| (smem_malloc sm1 t1 st1 a1, smem_malloc sm2 t2 st2 a2) =>
    if tv_typ t1 t2 && tv_align a1 a2 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2 >>= 
      fun r => rtv_sterm Ps1 Ps2 fid r st1 st2 
    else None
| (smem_alloca sm1 t1 st1 a1, smem_alloca sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then 
      rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else rtv_smem Ps1 Ps2 fid r (smem_alloca sm1 t1 st1 a1) sm2
| (smem_free sm1 t1 st1, smem_free sm2 t2 st2) =>
    if tv_typ t1 t2 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2 >>= 
      fun r => rtv_sterm Ps1 Ps2 fid r st1 st2
    else None
| (smem_load sm1 t1 st1 a1, smem_load sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then
      rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else 
      if load_from_metadata sm2 st2 then
        rtv_smem Ps1 Ps2 fid r (smem_load sm1 t1 st1 a1) sm2
      else None
| (smem_store sm1 t1 st11 st12 a1, smem_store sm2 t2 st21 st22 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then 
      rtv_sterm Ps1 Ps2 fid r st11 st21 >>=
      fun r => rtv_sterm Ps1 Ps2 fid r st12 st22 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else 
      if store_to_ret Ps1 Ps2 (rename_fid fid) st22 then
        rtv_smem Ps1 Ps2 fid r (smem_store sm1 t1 st11 st12 a1) sm2
      else None
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    if (eq_id fid1 fid2)
    then 
      rtv_list_sterm Ps1 Ps2 fid r sts1 sts2 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else rtv_smem Ps1 Ps2 fid r (smem_lib sm1 fid1 sts1) sm2
| (sm1, smem_lib sm2 lid sts) => 
    if smem_lib_sub lid then rtv_smem Ps1 Ps2 fid r sm1 sm2 else None
| (sm1, smem_alloca sm2 t2 st2 a2) => rtv_smem Ps1 Ps2 fid r sm1 sm2
| (sm1, smem_load sm2 t2 st2 a2) => 
  (* We check load_from_metadata to ensure that the behavior of output programs 
   * preserves input's. If we did not check, the additional load may be stuck. 
   *)
    if load_from_metadata sm2 st2 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2
    else None
| (sm1, smem_store sm2 t2 st21 st22 a2) => 
  (* We check that the additional stores must be to shadow_ret. *)
    if store_to_ret Ps1 Ps2 (rename_fid fid) st22 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2
    else None
| _ => None
end.

Fixpoint rtv_sframe Ps1 Ps2 fid r (sf1 sf2:sframe) : option renaming :=
match (sf1, sf2) with
| (sframe_init, _) => Some r
| (sframe_alloca sm1 sf1 t1 st1 a1, sframe_alloca sm2 sf2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then 
      rtv_smem Ps1 Ps2 fid r sm1 sm2 >>=
      fun r => rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
      fun r => rtv_sframe Ps1 Ps2 fid r sf1 sf2
    else rtv_sframe Ps1 Ps2 fid r (sframe_alloca sm1 sf1 t1 st1 a1) sf2
| _ => None
end.

(* Find a (id2,st2) from sm2 where st1 = st2, then return id2 and the rest
   sm2'. *)
Fixpoint match_smap Ps1 Ps2 fid r id1 st1 sm2 : option (smap * renaming) :=
match sm2 with
| nil => None
| (id2,st2)::sm2' => 
    match rtv_sterm Ps1 Ps2 fid r st1 st2 with
    | Some r' => Some (sm2',(id1,id2)::r')
    | None => match_smap Ps1 Ps2 fid r id1 st1 sm2'
    end
end.

Fixpoint rtv_smap Ps1 Ps2 fid r (sm1 sm2:smap) : option renaming :=
match sm1 with
| nil => Some r
| (id1,st1)::sm1' =>
  match lookup_renaming r id1 with
  | Some id2 =>
    match lookupAL _ sm2 id2 with
    | None => None
    | Some st2 => 
        rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
        fun r => rtv_smap Ps1 Ps2 fid r sm1' sm2
    end
  | None => 
    match match_smap Ps1 Ps2 fid r id1 st1 sm2 with
    | None => None
    | Some (sm2',r') => rtv_smap Ps1 Ps2 fid r' sm1' sm2'
    end
  end
end.

Definition rsub_sstate Ps1 Ps2 fid r s1 s2 : option renaming := 
if sumbool2bool _ _ (sterms_dec s1.(SEffects) s2.(SEffects)) then
  rtv_smap Ps1 Ps2 fid r s1.(STerms) s2.(STerms) >>=
  fun r => rtv_smem Ps1 Ps2 fid r s1.(SMem) s2.(SMem) >>=
  fun r => rtv_sframe Ps1 Ps2 fid r s1.(SFrame) s2.(SFrame)
else None.

Definition rtv_cmds Ps1 Ps2 fid r (nbs1 nbs2 : list nbranch) :=
rsub_sstate Ps1 Ps2 fid r (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2).

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Fixpoint rtv_params Ps1 Ps2 fid r (tsts1 tsts2:list (typ*sterm)) : 
  option renaming :=
match (tsts1, tsts2) with
| (nil, _) => Some r
| ((t1,st1)::tsts1', (t2,st2)::tsts2') => 
  if tv_typ t1 t2 then
    rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
    fun r => rtv_params Ps1 Ps2 fid r tsts1' tsts2'
  else None
| _ => None
end.

Definition rtv_scall Ps1 Ps2 fid r (c1:scall) (c2:sicall) : option renaming :=
  let '(stmn_call rid1 nr1 _ ty1 t1 tsts1) := c1 in
  match c2 with
  | stmn_icall_nptr rid2 nr2 _ ty2 t2 tsts2 =>
    if ((sumbool2bool _ _ (noret_dec nr1 nr2)) && tv_typ ty1 ty2) then
      rtv_params Ps1 Ps2 fid r tsts1 tsts2 >>=
      fun r => rtv_sterm Ps1 Ps2 fid r (remove_cast t1) (remove_cast t2) >>=
      fun r => Some ((rid1,rid2)::r)
    else None
  | stmn_icall_ptr rid2 _ _ ty2 t2 _ tsts2 =>
    if (tv_typ ty1 ty2) then
      rtv_params Ps1 Ps2 fid r tsts1 tsts2 >>=
      fun r => 
        match (remove_cast t1, remove_cast t2) with
        | (sterm_val (value_const (const_gid _ fid1)),
           sterm_val (value_const (const_gid _ fid2))) =>
           if tv_fid fid1 fid2 && function_returns_pointer Ps1 fid2
           then Some ((rid1,rid2)::r) else None
        | (st1, st2) => 
            rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
            fun r => Some ((rid1,rid2)::r)
        end
    else None
  end.

Definition rtv_subblock Ps1 Ps2 fid r (sb1:subblock) (sb2:isubblock) : 
  option renaming :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkiSB nbs2 call2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_icall st2 call2 in
  rsub_sstate Ps1 Ps2 fid r st1 st2 >>=
  fun r => rtv_scall Ps1 Ps2 fid r cl1 cl2 
end.

Fixpoint rtv_subblocks Ps1 Ps2 fid r (sbs1:list subblock) (sbs2:list isubblock) :
  option renaming :=
match (sbs1, sbs2) with
| (nil, nil) => Some r
| (sb1::sbs1', sb2::sbs2') => 
    rtv_subblock Ps1 Ps2 fid r sb1 sb2 >>=
    fun r => rtv_subblocks Ps1 Ps2 fid r sbs1' sbs2'
| _ => None
end.

Fixpoint rtv_list_value_l r (vls1 vls2:list_value_l) : option renaming :=
match (vls1, vls2) with
| (Nil_list_value_l, Nil_list_value_l) => Some r
| (Cons_list_value_l v1 l1 vls1, Cons_list_value_l v2 l2 vls2) =>
    if eq_l l1 l2 then
      rtv_value r v1 v2 >>=
      fun r => rtv_list_value_l r vls1 vls2
    else None
| _ => None
end.

Definition rtv_phinode r t1 vls1 t2 vls2 : option renaming :=
if tv_typ t1 t2 then rtv_list_value_l r vls1 vls2 else None.

Fixpoint match_phinodes r i1 t1 vls1 ps2 : option (phinodes * renaming) :=
match ps2 with
| nil => None
| (insn_phi i2 t2 vls2)::ps2' => 
    if (is_tmp_var i2) then
      (* We assume phi tmp is always mapped to phi tmp *)
      match rtv_phinode r t1 vls1 t2 vls2 with
      | Some r' => Some (ps2',(i1,i2)::r')
      | None => match_phinodes r i1 t1 vls1 ps2'
      end
    else match_phinodes r i1 t1 vls1 ps2'
end.

Fixpoint rtv_phinodes r (ps1 ps2:phinodes) : option renaming :=
match ps1 with
| nil => Some r
| (insn_phi i1 t1 vls1)::ps1' =>
  match lookup_renaming r i1 with
  | Some i2 =>
    match lookupPhinode ps2 i2 with
    | None => None
    | Some (insn_phi _ t2 vls2) => 
      rtv_phinode r t1 vls1 t2 vls2 >>=
      fun r' => rtv_phinodes r ps1' ps2
    end
  | None =>
    match match_phinodes r i1 t1 vls1 ps2 with
    | None => None
    | Some (ps2',r') => rtv_phinodes r' ps1' ps2'
    end
  end
end.

Definition rtv_terminator r (tmn1 tmn2:terminator) : option renaming :=
match (tmn1, tmn2) with
| (insn_return id1 t1 v1, insn_return id2 t2 v2) => 
    if tv_typ t1 t2 then rtv_value r v1 v2 else None
| (insn_return_void id1, insn_return_void id2) => Some r
| (insn_br id1 v1 l11 l12, insn_br id2 v2 l21 l22) =>
    if eq_l l11 l21 && eq_l l12 l22 then rtv_value r v1 v2 else None
| (insn_br_uncond id1 l1, insn_br_uncond id2 l2) =>
    if eq_l l1 l2 then Some r else None
| (insn_unreachable id1, insn_unreachable id2) => Some r
| _ => None
end.

Definition rtv_block Ps1 Ps2 fid r (b1 b2:block) : option renaming :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  let '(cs2', op) :=
    match lookupFdefViaIDFromProducts Ps1 fid with      
    | Some (fdef_intro (fheader_intro (typ_pointer _ as tp) _ _) _) =>
      match lookupFdefViaIDFromProducts Ps2 (rename_fid fid) with 
      | Some (fdef_intro (fheader_intro _ _ ((t2,id2)::_)) _) =>
          let '(cs2', opcs6) := get_last_six_insns cs2 in
          match opcs6 with
          | Some (c1,c2,c3,c4,c5,c6) => 
             (* gen_iret returns %shadow_ret %.base %.base %.ptr i32 *)
             match gen_iret t2 id2 c1 c2 c3 c4 c5 c6 with
             | None => (cs2, None)
             | op => (cs2', op)
             end
          | None => (cs2, None)
          end
      | _ => (cs2, None)
      end
    | _ => (cs2, None)
    end in 
  match (cmds2sbs cs1, cmds2isbs Ps1 cs2') with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    if eq_l l1 l2 then
      rtv_phinodes r ps1 ps2 >>=
      fun r => rtv_subblocks Ps1 Ps2 fid r sbs1 sbs2 >>=
      fun r => rtv_cmds Ps1 Ps2 fid r nbs1 nbs2 >>=
      fun r => 
            match op with 
            | Some (id20, v21, v22, v23, t20) =>
              match (tmn1, tmn2) with
              | (insn_return id1 t1 v1, insn_return_void _) => 
                rtv_value r v1 v23
              | _ => rtv_terminator r tmn1 tmn2
              end
            | None => rtv_terminator r tmn1 tmn2
            end
    else None
  end 
end.

Fixpoint rtv_blocks Ps1 Ps2 fid r (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => Some r
| (b1::bs1', b2::bs2') => 
    rtv_block Ps1 Ps2 fid r b1 b2 >>=
    fun r => rtv_blocks Ps1 Ps2 fid r bs1' bs2'
| _ => None
end.

Definition rtv_fdef Ps1 Ps2 (f1 f2:fdef) :=
match (f1, f2) with
| (fdef_intro (fheader_intro _ fid1 _ as fh1) lb1, fdef_intro fh2 lb2) =>
  match rtv_blocks Ps1 Ps2 fid1 nil lb1 lb2 with
  | None => false
  | Some _ => tv_fheader Ps1 fh1 fh2 
  end
end.

Fixpoint rtv_products (Ps10 Ps1 Ps2:products) : bool :=
match Ps1 with
| nil => true
| product_gvar gv1::Ps1' =>
  match lookupGvarViaIDFromProducts Ps2 (getGvarID gv1) with
  | None => false
  | Some gv2 => sumbool2bool _ _ (gvar_dec gv1 gv2) && 
                rtv_products Ps10 Ps1' Ps2 
  end
| product_fdec f1::Ps1' =>
  match lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1)) with
  | None => false
  | Some f2 => tv_fdec Ps10 f1 f2 && rtv_products Ps10 Ps1' Ps2 
  end
| product_fdef f1::Ps1' =>
  match lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1)) with
  | None => false
  | Some f2 => rtv_fdef Ps10 Ps2 f1 f2 && rtv_products Ps10 Ps1' Ps2 
  end
end.

Definition rtv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  rtv_products Ps1 Ps1 Ps2
end.

(*************************************)
(* MTV *)

(* 
   ptr = load addr_of_ptr
   hashLoadBaseBound addr_of_ptr addr_of_b addr_of_e _ _ _
*)
Fixpoint deref_from_metadata (fid:id) (sm:smem) (addr_of_b addr_of_e ptr:sterm) 
  : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
| smem_free sm1 _ _ => false
| smem_load sm1 _ _ _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
| smem_store sm1 _ _ _ _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
| smem_lib sm1 fid1 sts1 =>
    if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm addr_of_ptr 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm _ Nil_list_sterm))))) =>
      if (eq_sterm_upto_cast addr_of_b addr_of_base &&
          eq_sterm_upto_cast addr_of_e addr_of_bound) then
        match (remove_cast addr_of_ptr, remove_cast ptr) with
        | (st1, sterm_load _ _ st2 _) => eq_sterm_upto_cast st1 st2
        | _ => false
        end
      else deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    end      
    else deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
end.

Fixpoint is_metadata_aux (ms:list (id*l*nat*id*id*id)) (fid:id) (l1:l) (i:nat)
  (b e p:id) : bool :=
match ms with
| nil => false
| (fid',l2,i',b',e',p')::ms' => 
    (eq_id fid fid' && eq_l l1 l2 && beq_nat i i' && eq_id b b' && eq_id e e' &&
     eq_id p p') ||
    is_metadata_aux ms' fid l1 i b e p
end.

Definition is_metadata (fid:id) (l1:l) (i:nat) (b e p:id) : bool :=
  is_metadata_aux (get_metadata tt) fid l1 i b e p.

Fixpoint check_metadata_aux Ps2 fid l1 i base bound ptr := 
match (base, bound, ptr) with
| (sterm_val (value_id idb), sterm_val (value_id ide), 
   sterm_val (value_id idp)) => 
    is_metadata fid l1 i idb ide idp
| (sterm_malloc _ _ st10 _ as st1, 
   sterm_gep _ _ st2 (Cons_list_sterm st20 Nil_list_sterm),  
   sterm_malloc _ _ _ _ as st3) =>
     eq_sterm_upto_cast st1 st2 && 
     eq_sterm_upto_cast st1 st3 && 
     eq_sterm st10 st20
| (sterm_alloca _ _ st10 _ as st1, 
   sterm_gep _ _ st2 (Cons_list_sterm st20 Nil_list_sterm),  
   sterm_alloca _ _ _ _ as st3) =>
     eq_sterm_upto_cast st1 st2 && 
     eq_sterm_upto_cast st1 st3 && 
     eq_sterm st10 st20
| (sterm_val (value_const (const_gid _ _ as c1)),
   sterm_val (value_const (const_gep _ (const_gid _ _ as c2)
     (Cons_list_const (const_int _ i2) Nil_list_const))),  
   sterm_val (value_const (const_gid _ _ as c3))) =>
     eq_const c1 c2 && eq_const c1 c3 && INT_is_one i2   
| (sterm_load sm1 _ st1 _, sterm_load sm2 _ st2 _, st3) =>
     deref_from_metadata fid sm1 st1 st2 st3
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22,
   sterm_select st30 _ st31 st32) =>
     eq_sterm st10 st20 && eq_sterm st20 st30 &&
     check_metadata_aux Ps2 fid l1 i st11 st21 st31 && 
     check_metadata_aux Ps2 fid l1 i st12 st22 st32
(*
  Assign external globals infinite base/bound.

  %bcast_ld_dref_base19 = bitcast i8* null to i8* 
  %16 = bitcast i8* inttoptr (i32 2147483647 to i8* ) to i8*
  %bcast_ld_dref_bound20 = bitcast %struct._IO_FILE** @stderr to i8* 
*)
| (sterm_val (value_const (const_null _)),
   sterm_val (value_const (const_int _ _)),
   sterm_val (value_const (const_gid (typ_pointer _) id))) =>
     match lookupBindingViaIDFromProducts Ps2 id with 
     | id_binding_gvar (gvar_external _ _ _) => true
     | _ => false
     end
| (sterm_val (value_const (const_null _)), 
   sterm_val (value_const (const_null _)),
   sterm_val (value_const (const_null _))) => true
| (sterm_val (value_const (const_undef _)),
   sterm_val (value_const (const_undef _)),
   sterm_val (value_const (const_undef _))) => true (* assumed by Softbound *)
| _ => false
end.

Definition check_metadata Ps2 fid l1 i base bound ptr := 
  check_metadata_aux Ps2 fid l1 i (remove_cast base) (remove_cast bound) 
    (get_ptr_object ptr).

Definition deref_check Ps2 fid l1 i lid sts : bool :=
  if (is_dereferenceCheck lid) then
    match sts with
    |  Cons_list_sterm base 
      (Cons_list_sterm bound
      (Cons_list_sterm ptr
      (Cons_list_sterm size_of_type
      (Cons_list_sterm _ Nil_list_sterm)))) => 
        check_metadata Ps2 fid l1 i base bound ptr
    | _ => false
    end
  else true.

Fixpoint find_stored_ptr sm addr_of_ptr : option sterm :=
match sm with
| smem_init => None
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_lib sm1 _ _ => find_stored_ptr sm1 addr_of_ptr
| smem_store sm1 _ st1 st2 _ =>
    if (eq_sterm_upto_cast st2 addr_of_ptr) then Some st1
    else find_stored_ptr sm1 addr_of_ptr
end.

(* 
   store ptr addr_of_ptr
   hashStoreBaseBound addr_of_ptr b e _ _ _
*)
Fixpoint store_to_metadata Ps2 fid l1 i sm (lid:id) sts : bool :=
if (is_hashLoadBaseBound lid) then
  match sts with
  |  Cons_list_sterm addr_of_ptr 
    (Cons_list_sterm base
    (Cons_list_sterm bound
    (Cons_list_sterm _
    (Cons_list_sterm _
    (Cons_list_sterm _ Nil_list_sterm))))) =>
      match (find_stored_ptr sm addr_of_ptr) with
      | None => false
      | Some ptr => check_metadata Ps2 fid l1 i base bound ptr
      end
  | _ => false
  end      
else true.

Fixpoint is_addrof_be_aux (abes:list (id*id*id)) (fid ab ae:id)
  : bool :=
match abes with
| nil => false
| (fid', ab', ae')::abes' => 
    if (eq_id fid fid' && eq_id ab ab' && eq_id ae ae') then true
    else is_addrof_be_aux abes' fid ab ae
end.

Definition is_addrof_be (fid:id) (sab sae:sterm) : bool :=
match (sab, sae) with
| (sterm_val (value_id ab), sterm_val (value_id ae)) =>
  is_addrof_be_aux (get_addrof_be tt) fid ab ae
| (sterm_alloca _ _ _ _, sterm_alloca _ _ _ _) => true
| _ => false
end.

(* ptr is safe to access if ptr is asserted by a deref check or
   from hasLoadBaseBound *)

Fixpoint safe_mem_access fid (sm:smem) t (ptr:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => safe_mem_access fid sm1 t ptr
| smem_lib sm1 fid1 sts1 =>
  if (is_dereferenceCheck fid1) then
    match sts1 with
    |  Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm actual_ptr
      (Cons_list_sterm
         (sterm_val 
           (value_const 
             (const_castop 
               castop_ptrtoint
               (const_gep false 
                 (const_null t) 
                   (Cons_list_const (const_int _ i0) Nil_list_const)
               )
              (typ_int sz)
             )
           )
         )
      (Cons_list_sterm _ Nil_list_sterm)))) =>
      if (eq_sterm (get_ptr_object ptr) (get_ptr_object actual_ptr) && 
         INT_is_one i0 && sumbool2bool _ _ (Size.dec sz Size.ThirtyTwo))
      then true else safe_mem_access fid sm1 t ptr
    | _ => safe_mem_access fid sm1 t ptr
    end
  else if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm _ 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm ptr_safe Nil_list_sterm))))) =>
      if (eq_sterm ptr addr_of_base || 
          eq_sterm ptr addr_of_bound || 
          eq_sterm ptr ptr_safe) 
      then is_addrof_be fid addr_of_base addr_of_bound  
      else safe_mem_access fid sm1 t ptr
    | _ => safe_mem_access fid sm1 t ptr
    end
  else safe_mem_access fid sm1 t ptr
end.

Fixpoint sterm_is_memsafe Ps1 Ps2 fid l i (st:sterm) : bool :=
match st with
| sterm_val v => true
| sterm_bop _ _ st1 st2 
| sterm_fbop _ _ st1 st2  
| sterm_icmp _ _ st1 st2 
| sterm_fcmp _ _ st1 st2 
| sterm_insertvalue _ st1 _ st2 _ => 
    sterm_is_memsafe Ps1 Ps2 fid l i st1 && sterm_is_memsafe Ps1 Ps2 fid l i st2 
| sterm_trunc _ _ st1 _
| sterm_ext _ _ st1 _ 
| sterm_cast _ _ st1 _ 
| sterm_extractvalue _ st1 _ => sterm_is_memsafe Ps1 Ps2 fid l i st1
| sterm_malloc sm _ st1 _
| sterm_alloca sm _ st1 _ => 
    smem_is_memsafe Ps1 Ps2 fid l i sm && sterm_is_memsafe Ps1 Ps2 fid l i st1
| sterm_load sm t st1 _ => 
   smem_is_memsafe Ps1 Ps2 fid l i sm && sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
   safe_mem_access fid sm t st1
| sterm_gep _ _ st1 sts2 => 
   sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
   list_sterm_is_memsafe Ps1 Ps2 fid l i sts2
| sterm_phi _ stls => list_sterm_l_is_memsafe Ps1 Ps2 fid l i stls
| sterm_select st1 _ st2 st3 => 
    sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st2 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st3
| sterm_lib sm lid sts => 
    smem_is_memsafe Ps1 Ps2 fid l i sm && 
    list_sterm_is_memsafe Ps1 Ps2 fid l i sts && 
    store_to_metadata Ps2 fid l i sm lid sts
end
with list_sterm_is_memsafe Ps1 Ps2 fid l i (sts:list_sterm) : bool :=
match sts with
| Nil_list_sterm => true
| Cons_list_sterm st sts0 => 
    sterm_is_memsafe Ps1 Ps2 fid l i st && 
    list_sterm_is_memsafe Ps1 Ps2 fid l i sts0
end
with list_sterm_l_is_memsafe Ps1 Ps2 fid l i (stls:list_sterm_l) : bool :=
match stls with
| Nil_list_sterm_l => true
| Cons_list_sterm_l st _ stls0 =>
    sterm_is_memsafe Ps1 Ps2 fid l i st && 
    list_sterm_l_is_memsafe Ps1 Ps2 fid l i stls0
end
with smem_is_memsafe Ps1 Ps2 fid l i (sm:smem) : bool :=
match sm with
| smem_init => true
| smem_malloc sm1 _ st1 _
| smem_alloca sm1 _ st1 _ => 
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && sterm_is_memsafe Ps1 Ps2 fid l i st1
| smem_free sm1 _ _ => false
| smem_load sm1 t st1 _ => 
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
    safe_mem_access fid sm1 t st1
| smem_store sm1 t st11 st12 _ =>
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st11 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st12 && 
    (store_to_ret Ps1 Ps2 fid st12 || 
     safe_mem_access fid sm1 (typ_pointer t) st12)
| smem_lib sm1 lid1 sts1 =>
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && 
    list_sterm_is_memsafe Ps1 Ps2 fid l i sts1 && 
    deref_check Ps2 fid l i lid1 sts1
end.

Fixpoint is_be_aux (ms:list (id*l*nat*id*id*id)) (fid:id) (l1:l) (i:nat) (b e:id)
  : bool :=
match ms with
| nil => false
| (fid',l2,i',b',e',_)::ms' => 
    (eq_id fid fid' && eq_l l1 l2 && beq_nat i i' && eq_id b b' && eq_id e e') ||
    is_be_aux ms' fid l1 i b e
end.

Definition is_be (fid:id) (l1:l) i (b e:id) : bool :=
  is_be_aux (get_metadata tt) fid l1 i b e.

Fixpoint deref_from_be (fid:id) (sm:smem) (addr_of_b addr_of_e:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _ => deref_from_be fid sm1 addr_of_b addr_of_e
| smem_free sm1 _ _ => false
| smem_load sm1 _ _ _ => deref_from_be fid sm1 addr_of_b addr_of_e
| smem_store sm1 _ _ _ _ => deref_from_be fid sm1 addr_of_b addr_of_e
| smem_lib sm1 fid1 sts1 =>
    if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm addr_of_ptr 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm _ Nil_list_sterm))))) =>
      if (eq_sterm_upto_cast addr_of_b addr_of_base &&
          eq_sterm_upto_cast addr_of_e addr_of_bound) then true
      else deref_from_be fid sm1 addr_of_b addr_of_e
    | _ => deref_from_be fid sm1 addr_of_b addr_of_e
    end      
    else deref_from_be fid sm1 addr_of_b addr_of_e
end.

Fixpoint check_be_aux (Ps2:products) fid l1 i base bound:= 
match (base, bound) with
| (sterm_val (value_id idb), sterm_val (value_id ide)) => 
    is_be fid l1 i idb ide
| (sterm_malloc _ _ st10 _ as st1, 
   sterm_gep _ _ st2 (Cons_list_sterm st20 Nil_list_sterm)) =>
     eq_sterm_upto_cast st1 st2
| (sterm_alloca _ _ st10 _ as st1, 
   sterm_gep _ _ st2 (Cons_list_sterm st20 Nil_list_sterm)) =>
     eq_sterm_upto_cast st1 st2
| (sterm_val (value_const (const_gid _ _ as c1)),
   sterm_val (value_const (const_gep _ (const_gid _ _ as c2)
     (Cons_list_const (const_int _ i2) Nil_list_const)))) =>
     eq_const c1 c2 && INT_is_one i2   
| (sterm_load sm1 _ st1 _, sterm_load sm2 _ st2 _) =>
     deref_from_be fid sm1 st1 st2
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22) =>
     eq_sterm st10 st20 &&
     check_be_aux Ps2 fid l1 i st11 st21 && 
     check_be_aux Ps2 fid l1 i st12 st22
(*
  Assign external globals infinite base/bound.

  %bcast_ld_dref_base19 = bitcast i8* null to i8* 
  %16 = bitcast i8* inttoptr (i32 2147483647 to i8* ) to i8*
  %bcast_ld_dref_bound20 = bitcast %struct._IO_FILE** @stderr to i8* 
*)
| (sterm_val (value_const (const_null _)),
   sterm_val (value_const (const_castop cast_inttoptr _ _))) => true
| (sterm_val (value_const (const_null _)), 
   sterm_val (value_const (const_null _))) => true
| (sterm_val (value_const (const_undef _)),
   sterm_val (value_const (const_undef _))) => true (* assumed by Softbound *)
| _ => false
end.

Definition check_be Ps2 fid l1 i base bound:= 
  check_be_aux Ps2 fid l1 i (remove_cast base) (remove_cast bound).

Fixpoint check_all_metadata_aux Ps2 fid l1 i1 (sm:smap) 
  (ms:list (id*l*nat*id*id*id)) : bool :=
match ms with
| nil => true
| (fid0,l2,i2,b,e,p)::ms' =>
    (if (eq_id fid0 fid && eq_l l1 l2 && beq_nat i1 i2) then
      match (lookupAL _ sm b, lookupAL _ sm e, lookupAL _ sm p) with
      | (Some sb, Some se, Some sp) => check_metadata Ps2 fid l1 i1 sb se sp
      | (Some sb, Some se, None) => 
          (*   b1 = bitcast b; e1 = bitcast e
               and p is falled-through or  *)
          check_metadata Ps2 fid l1 i1 sb se (sterm_val (value_id p))
      | (None, None, Some (sterm_gep _ _ _ _)) => 
          (*   b and e are falled-through  *)
          true
      | (None, None, None) => 
          (*   b, e and p are falled-through  *)
          true
      | _ => false
      end
    else true) &&
    check_all_metadata_aux Ps2 fid l1 i1 sm ms'
end.

Definition check_all_metadata Ps2 fid l i sm :=
  check_all_metadata_aux Ps2 fid l i sm (get_metadata tt).

Fixpoint check_addrof_be_aux fid (sm:smap) (abes:list (id*id*id))
  : bool :=
match abes with
| nil => true
| (fid0,ab,ae)::abes' =>
    (if (eq_id fid0 fid) then
      match (lookupAL _ sm ab, lookupAL _ sm ae) with
      | (None, None) => true
      | (Some (sterm_alloca _ _ _ _), Some (sterm_alloca _ _ _ _)) => true
      | _ => false
      end
    else true) &&
    check_addrof_be_aux fid sm abes'
end.

Definition check_addrof_be fid sm :=
  check_addrof_be_aux fid sm (get_addrof_be tt).

Definition mtv_cmds Ps1 Ps2 fid l (nbs2 : list nbranch) :=
let st2 := se_cmds sstate_init nbs2 in 
smem_is_memsafe Ps1 Ps2 fid l O st2.(SMem) &&
check_all_metadata Ps1 fid l O st2.(STerms) &&
check_addrof_be fid st2.(STerms).

Fixpoint mtv_func_metadata (ms:list (id*l*nat*id*id*id)) Ps2 fid l1 i1 fid2 ars2 
  sars2 : bool :=
match ms with
| nil => true
| (fid0,l2,i2,b,e,p)::ms' =>
    (if (eq_id fid0 fid2 && eq_l l2 (l_of_arg tt) && beq_nat i2 O) then
      match (lookupSarg ars2 sars2 b, lookupSarg ars2 sars2 e, 
        lookupSarg ars2 sars2 p) with
      | (Some sb, Some se, Some sp) => check_metadata Ps2 fid l1 i1 sb se sp
      | _ => false
      end
    else true) &&
    mtv_func_metadata ms' Ps2 fid l1 i1 fid2 ars2 sars2
end.

(*
  fid2 args2

  fid
  ...
    l1:
      call fid2 tsts2   
*)
Definition mtv_iscall Ps2 fid l1 i1 (c2:sicall) :=
match c2 with
| stmn_icall_nptr _ _ _ _ t2 tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then true
      else
        match (lookupFdefViaIDFromProducts Ps2 fid2) with
        | None => true
        | Some (fdef_intro (fheader_intro _ _ args2) _) =>
            mtv_func_metadata (get_metadata tt) Ps2 fid l1 i1 fid2 args2 tsts2
        end
  | _ => true
  end
| stmn_icall_ptr _ _ _ _ t2 _ tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then true
      else
        match (lookupFdefViaIDFromProducts Ps2 fid2) with
        | Some (fdef_intro (fheader_intro _ _ (_::args2)) _) =>
            mtv_func_metadata (get_metadata tt) Ps2 fid l1 i1 fid2 args2 tsts2
        | _ => true
        end
  | _ => true
  end
end.

Definition mtv_isubblock Ps1 Ps2 fid l nth (sb2:isubblock) :=
match sb2 with
| mkiSB nbs2 call2 =>
  let st2 := se_cmds sstate_init nbs2 in
  let cl2 := se_icall st2 call2 in
   smem_is_memsafe Ps1 Ps2 fid l nth st2.(SMem) &&
   check_all_metadata Ps2 fid l nth st2.(STerms) &&
   check_addrof_be fid st2.(STerms) &&
   mtv_iscall Ps2 fid l nth cl2
end.

Fixpoint mtv_isubblocks_aux Ps1 Ps2 fid l len (sbs2:list isubblock) :=
match sbs2 with
| nil => true
| sb2::sbs2' => 
    mtv_isubblock Ps1 Ps2 fid l (len - List.length sbs2') sb2 && 
    mtv_isubblocks_aux Ps1 Ps2 fid l len sbs2'
end.

Definition mtv_isubblocks Ps1 Ps2 fid l (sbs2:list isubblock) :=
  mtv_isubblocks_aux Ps1 Ps2 fid l (List.length sbs2) (List.rev sbs2).

(* Check
   1) i = phi l1 i1, l2 i2, ..., ln in
      if i is a metadata, then all i1 ... in should be metadata
   2) i = phi l1 i1, l2 i2, ..., ln in
      i' = phi l1' i1', l2' i2', ..., lm' im'
      if both i and i' are metadata, l1 ... ln should be a permutation of 
         l1' ... lm'
   3) either all of (b e p) are in phinodes, or none of them is...
   Not clear how to implement the checking in a way suitable to proofs.
*)
(* We don't need to check them, if the metadata are generated correctly
Definition mtv_bep_value fid l i (bv ev pv:value) : bool :=
match (bv, ev, pv) with
| (value_id bid, value_id eid, value_id pid) => is_metadata fid l i bid eid pid
| (value_const (const_null _), value_const (const_null _), 
     value_const (const_null _)) => true
| (value_const (const_undef _), value_const (const_undef _), 
     value_const (const_undef _)) => 
    (* I dont think this is safe, since undefined values can be
       arbitrary. But Softbound assumes the this is fine. *)
    true
| _ => false
end.
*)

Fixpoint mtv_list_value_l (bvls evls pvls:list_value_l) : bool :=
match bvls with
| Nil_list_value_l => true
| Cons_list_value_l bv bl bvls' =>
    match (getValueViaLabelFromValuels evls bl,
           getValueViaLabelFromValuels pvls bl) with
    | (Some ev, Some pv) => true
    | _ => false
    end && mtv_list_value_l bvls' evls pvls
end.

Fixpoint mtv_phinodes_aux fid l1 i1 (ms:list (id*l*nat*id*id*id)) (ps2:phinodes)
  : bool :=
match ms with
| nil => true
| (((((fid',l2),i2),b),e),p)::ms' =>
    (if (eq_id fid fid' && eq_l l1 l2 && beq_nat i1 i2) then
       match (lookupPhinode ps2 b, lookupPhinode ps2 e, lookupPhinode ps2 p) with
       | (None, None, None) => true
       | (Some (insn_phi _ _ bvls), Some (insn_phi _ _ evls), 
           Some (insn_phi _ _ pvls)) => mtv_list_value_l bvls evls pvls
       | _ => false
       end
     else true) && 
    mtv_phinodes_aux fid l1 i1 ms' ps2 
end.

Definition mtv_phinodes fid l i (ps2:phinodes) : bool :=
  mtv_phinodes_aux fid l i (get_metadata tt) ps2.

Definition mtv_block Ps1 Ps2 fid (b2:block) :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
  match cmds2isbs Ps1 cs2 with
  | (sbs2, nbs2) =>
    mtv_phinodes fid l2 (S (List.length sbs2)) ps2 &&
    mtv_isubblocks Ps1 Ps2 fid l2 sbs2 && mtv_cmds Ps1 Ps2 fid l2 nbs2
  end
end.

Fixpoint mtv_blocks Ps1 Ps2 fid (bs2:blocks):=
match bs2 with
| nil => true
| b2::bs2' => mtv_block Ps1 Ps2 fid b2 && mtv_blocks Ps1 Ps2 fid bs2'
end.

Definition mtv_fdef Ps1 Ps2 (f2:fdef) :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then true else mtv_blocks Ps1 Ps2 fid2 lb2
end.

Fixpoint mtv_products Ps1 (Ps20 Ps2:products) : bool :=
match Ps2 with
| nil => true
| product_fdef f2::Ps2' => mtv_fdef Ps1 Ps20 f2 && mtv_products Ps1 Ps20 Ps2'
| _::Ps2' => mtv_products Ps1 Ps20 Ps2'
end.

Definition mtv_module (m1:module) (m2:module) :=
match (m1, m2) with
| (module_intro _ _ Ps1, module_intro _ _ Ps2) => mtv_products Ps1 Ps2 Ps2
end.

(***********************************)
(* tactic *)
Ltac sumbool_simpl :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_value _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_typ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_align _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_sterm _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_smem _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_id _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_const _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_l _ _ = true |- _ ] => apply sumbool2bool_true in H
  end.

Ltac sumbool_subst :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_value _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:tv_typ _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:tv_align _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_sterm _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_smem _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_id _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_const _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_l _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  end.

Tactic Notation "sumbool_subst" "in" hyp(H) :=
  apply sumbool2bool_true in H.



(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
