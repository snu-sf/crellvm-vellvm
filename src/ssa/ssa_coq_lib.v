(* These libs are only used when typechecking ssa_coq_lib.v alone.
   They are not copied into the final ssa.v, otherwise the definitions in ssa_def,
   and ssa are conflict, since they define same syntax. For example, we may have
   ssa_def.insn and insn in ssa, but they are same. This is fixed if we dont copy
   the libs below into ssa_coq.ott.
*)
Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa_def.
Require Import Metatheory.

(*BEGINCOPY*)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Recdef.
Require Import Coq.Program.Wf.
Require Import Omega.

(**********************************)
(* LabelSet. *)

  Definition lempty_set := empty_set l.
  Definition lset_add (l1:l) (ls2:ls) := set_add eq_dec l1 ls2.
  Definition lset_union (ls1 ls2:ls) := set_union eq_dec ls1 ls2.
  Definition lset_inter (ls1 ls2:ls) := set_inter eq_dec ls1 ls2.
  Definition lset_eq (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => true
    | _ => false
    end.
  Definition lset_neq (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => false
    | _ => true
    end.
  Definition lset_single (l0:l) := lset_add l0 (lempty_set). 
  Definition lset_mem (l0:l) (ls0:ls) := set_mem eq_dec l0 ls0.

(**********************************)
(* Inversion. *)

  Definition getCmdID (i:cmd) : id :=
  match i with
  | insn_bop id _ sz v1 v2 => id
  (* | insn_extractelement id typ0 id0 c1 => id *)
  (* | insn_insertelement id typ0 id0 typ1 v1 c2 => id *)
  | insn_extractvalue id typs id0 c1 => id
  | insn_insertvalue id typs id0 typ1 v1 c2 => id 
  | insn_malloc id _ _ _ => id
  | insn_free id _ _ => id
  | insn_alloca id _ _ _ => id
  | insn_load id typ1 v1 => id
  | insn_store id typ1 v1 v2 => id
  | insn_gep id _ _ _ _ => id
  (* | insn_trunc id typ1 v1 typ2 => id *)
  | insn_ext id _ sz1 v1 sz2 => id
  (* | insn_fptrunc id typ1 v1 typ2 => id *)
  (* | insn_fptoui id typ1 v1 typ2 => id *)
  (* | insn_fptosi id typ1 v1 typ2 => id *)
  (* | insn_uitofp id typ1 v1 typ2 => id *)
  (* | insn_sitofp id typ1 v1 typ2 => id *)
  | insn_cast id _ typ1 v1 typ2 => id
  | insn_icmp id cond typ v1 v2 => id
  (* | insn_fcmp id cond typ v1 v2 => id *)
  | insn_select id v0 typ v1 v2 => id
  | insn_call id _ _ typ id0 paraml => id
  end.
 
  Definition getTerminatorID (i:terminator) : id :=
  match i with
  | insn_return id t v => id
  | insn_return_void id => id
  | insn_br id v l1 l2 => id
  | insn_br_uncond id l => id
  (* | insn_switch id t v l _ => id *)
  (* | insn_invoke id typ id0 paraml l1 l2 => id *)
  | insn_unreachable id => id
  end.

  Definition getPhiNodeID (i:phinode) : id :=
  match i with
  | insn_phi id _ _ => id
  end.

  Definition getValueID (v:value) : option id :=
  match v with
  | value_id id => Some id
  | value_const _ => None
  end.

  Definition getInsnID (i:insn) : id :=
  match i with
  | insn_phinode p => getPhiNodeID p
  | insn_cmd c => getCmdID c
  | insn_terminator t => getTerminatorID t
  end.

  Definition isPhiNodeB (i:insn) : bool :=
  match i with
  | insn_phinode p => true
  | insn_cmd c => false
  | insn_terminator t => false
  end.  

  Definition isPhiNode (i:insn) : Prop :=
  match i with
  | insn_phinode p => True
  | insn_cmd c => False
  | insn_terminator t => False
  end.  

(** Statically idx for struct must be int, and idx for arr can be
    anything without checking bounds. *)
Fixpoint getSubTypFromConstIdxs (idxs : list const) (t : typ) : option typ :=
match idxs with
| nil => Some t 
| idx::idxs' => 
  match t with
  | typ_array sz t' => getSubTypFromConstIdxs idxs' t'
  | typ_struct lt => 
    match idx with
    | (const_int sz i) =>
      match (nth_error lt i) with
      | Some t' => getSubTypFromConstIdxs idxs' t'
      | None => None
      end
    | _ => None
    end
  | _ => None
  end
end.

Fixpoint getSubTypFromValueIdxs (idxs : list value) (t : typ) : option typ :=
match idxs with
| nil => Some t 
| idx::idxs' => 
  match t with
  | typ_array sz t' => getSubTypFromValueIdxs idxs' t'
  | typ_struct lt => 
    match idx with
    | value_const (const_int sz i) =>
      match (nth_error lt i) with
      | Some t' => getSubTypFromValueIdxs idxs' t'
      | None => None
      end
    | _ => None
    end
  | _ => None
  end
end.

Definition getGEPTyp (idxs : list value) (t : typ) : option typ :=
match idxs with
| nil => None
| (idx::idxs') =>
     (* The input t is already an element of a pointer typ *)
     match (getSubTypFromValueIdxs idxs' t) with
     | Some t' => Some (typ_pointer t')
     | _ => None
     end
end.

Definition getLoadTyp (t:typ) : option typ :=
match t with
| typ_pointer t' => Some t'
| _ => None
end.

Definition getCmdTyp (i:cmd) : option typ :=
match i with
| insn_bop _ _ sz _ _ => Some (typ_int sz)
(*
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ *)
| insn_extractvalue _ typ _ idxs => getSubTypFromConstIdxs idxs typ
| insn_insertvalue _ typ _ _ _ _ => Some typ
| insn_malloc _ typ _ _ => Some (typ_pointer typ)
| insn_free _ typ _ => Some typ_void
| insn_alloca _ typ _ _ => Some (typ_pointer typ)
| insn_load _ typ _ => getLoadTyp typ
| insn_store _ _ _ _ => Some typ_void
| insn_gep _ _ typ _ idxs => getGEPTyp idxs typ
(* | insn_trunc _ _ _ typ => Some typ *)
| insn_ext _ _ _ _ typ2 => Some typ2
| insn_cast _ _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int 1)
(* | insn_fcmp _ _ _ _ _ => Some (typ_int 1) *)
| insn_select _ _ typ _ _ => Some typ
| insn_call _ true _ typ _ _ => Some typ_void
| insn_call _ false _ typ _ _ => Some typ
end.

Definition getTerminatorTyp (i:terminator) : typ :=
match i with
| insn_return _ typ _ => typ
| insn_return_void _ => typ_void
| insn_br _ _ _ _ => typ_void
| insn_br_uncond _ _ => typ_void
(* | insn_switch _ typ _ _ _ => typ_void *)
(* | insn_invoke _ typ _ _ _ _ => typ *)
| insn_unreachable _ => typ_void
end.

Definition getPhiNodeTyp (i:phinode) : typ :=
match i with
| insn_phi _ typ _ => typ
end.

Definition getInsnTyp (i:insn) : option typ :=
match i with
| insn_phinode p => Some (getPhiNodeTyp p)
| insn_cmd c => getCmdTyp c
| insn_terminator t => Some (getTerminatorTyp t)
end.

Definition getPointerEltTyp (t:typ) : option typ :=
match t with
| typ_pointer t' => Some t' 
| _ => None
end.

Definition getValueIDs (v:value) : ids :=
match (getValueID v) with
| None => nil
| Some id => id::nil
end.

Fixpoint getParamsOperand (lp:list_param) : ids :=
match lp with
| nil => nil
| (t, v)::lp' => (getValueIDs v) ++ (getParamsOperand lp')
end.

Fixpoint list_prj1 (X Y:Type) (ls : list (X*Y)) : list X :=
match ls with
| nil => nil
| (x, y)::ls' => x::list_prj1 X Y ls'
end.

Fixpoint list_prj2 (X Y:Type) (ls : list (X*Y)) : list Y :=
match ls with
| nil => nil
| (x, y)::ls' => y::list_prj2 X Y ls'
end.

Definition getCmdOperands (i:cmd) : ids :=
match i with
| insn_bop _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
(* | insn_extractelement _ _ v _ => getValueIDs v
| insn_insertelement _ _ v1 _ v2 _ => getValueIDs v1 ++ getValueIDs v2
*)
| insn_extractvalue _ _ v _ => getValueIDs v
| insn_insertvalue _ _ v1 _ v2 _ => getValueIDs v1 ++ getValueIDs v2
| insn_malloc _ _ _ _ => nil
| insn_free _ _ v => getValueIDs v
| insn_alloca _ _ _ _ => nil
| insn_load _ _ v => getValueIDs v
| insn_store _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
| insn_gep _ _ _ v  _ => getValueIDs v
(* | insn_trunc _ _ v _ => getValueIDs v *)
| insn_ext _ _ _ v1 typ2 => getValueIDs v1
| insn_cast _ _ _ v _ => getValueIDs v
| insn_icmp _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
(* | insn_fcmp _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2 *)
| insn_select _ v0 _ v1 v2 => getValueIDs v0 ++ getValueIDs v1 ++ getValueIDs v2
| insn_call _ _ _ _ _ lp => getParamsOperand lp
end.

Definition getTerminatorOperands (i:terminator) : ids :=
match i with
| insn_return _ _ v => getValueIDs v
| insn_return_void _ => nil
| insn_br _ v _ _ => getValueIDs v
| insn_br_uncond _ _ => nil
(* | insn_switch _ _ value _ _ => getValueIDs value *)
(* | insn_invoke _ _ _ lp _ _ => getParamsOperand lp *)
| insn_unreachable _ => nil
end.

Definition getPhiNodeOperands (i:phinode) : ids :=
match i with
| insn_phi _ _ ls => list_prj1 _ _ ls
end.

Definition getInsnOperands (i:insn) : ids :=
match i with
| insn_phinode p => getPhiNodeOperands p
| insn_cmd c => getCmdOperands c
| insn_terminator t => getTerminatorOperands t
end.

Definition getCmdLabels (i:cmd) : ls :=
match i with
| insn_bop _ _ _ _ _ => nil
(* | insn_extractelement _ _ _ _ => nil
| insn_insertelement _ _ _ _ _ _ => nil
*)
| insn_extractvalue _ _ _ _ => nil
| insn_insertvalue _ _ _ _ _ _ => nil
| insn_malloc _ _ _ _ => nil
| insn_free _ _ _ => nil
| insn_alloca _ _ _ _ => nil
| insn_load _ _ _ => nil
| insn_store _ _ _ _ => nil
| insn_gep _ _ _ v  _ => nil
(* | insn_trunc _ _ _ _ => nil *)
| insn_ext _ _ _ _ _ => nil
| insn_cast _ _ _ _ _ => nil
| insn_icmp _ _ _ _ _ => nil
(* | insn_fcmp _ _ _ _ _ => nil *)
| insn_select _ _ _ _ _ => nil
| insn_call _ _ _ _ _ _ => nil
end.

Definition getTerminatorLabels (i:terminator) : ls :=
match i with
| insn_return _ _ _ => nil
| insn_return_void _ => nil
| insn_br _ _ l1 l2 => l1::l2::nil
| insn_br_uncond _ l => l::nil
(* | insn_switch _ _ _ l ls => l::list_prj2 _ _ ls *)
(* | insn_invoke _ _ _ _ l1 l2 => l1::l2::nil *)
| insn_unreachable _ => nil
end.

Definition getPhiNodeLabels (i:phinode) : ls :=
match i with
| insn_phi _ _ ls => list_prj2 _ _ ls
end.

Definition getInsnLabels (i:insn) : ls :=
match i with
| insn_phinode p => getPhiNodeLabels p
| insn_cmd c => getCmdLabels c
| insn_terminator tmn => getTerminatorLabels tmn
end.

Fixpoint args2Typs (la:list_arg) : list_typ :=
match la with
| nil => nil
| (t, id)::la' => t::args2Typs la'
end.

Definition getFheaderTyp (fh:fheader) : typ :=
match fh with
| fheader_intro t _ la => typ_function t (args2Typs la)
end.

Definition getFdecTyp (fdec:fdec) : typ :=
match fdec with
| fdec_intro fheader => getFheaderTyp fheader
end.

Definition getFdefTyp (fdef:fdef) : typ :=
match fdef with
| fdef_intro fheader _ => getFheaderTyp fheader
end.

Definition getBindingTyp (ib:id_binding) : option typ :=
match ib with
| id_binding_cmd i => getCmdTyp i
| id_binding_terminator i => Some (getTerminatorTyp i)
| id_binding_phinode i => Some (getPhiNodeTyp i)
| id_binding_gvar (gvar_intro _ t _ _) => Some (typ_pointer t)
| id_binding_arg (t, id) => Some t
| id_binding_fdec fdec => Some (getFdecTyp fdec)
| id_binding_none => None
end.

Definition getCmdsFromBlock (b:block) : list_cmd :=
match b with
| block_intro l _ li _ => li
(* | block_without_label li => li *)
end.

Definition getPhiNodesFromBlock (b:block) : list_phinode :=
match b with
| block_intro l li _ _ => li
(* | block_without_label li => li *)
end.

Definition getTerminatorFromBlock (b:block) : terminator :=
match b with
| block_intro l _ _ t => t
(* | block_without_label li => li *)
end.

Definition getBindingFdec (ib:id_binding) : option fdec :=
match ib with
| id_binding_fdec fdec => Some fdec
| _ => None
end.

Definition getBindingArg (ib:id_binding) : option arg :=
match ib with
| id_binding_arg arg => Some arg
| _ => None
end.

Definition getBindingGvar (ib:id_binding) : option gvar :=
match ib with
| id_binding_gvar g => Some g
| _ => None
end.

Definition getBindingCmd (ib:id_binding) : option cmd :=
match ib with
| id_binding_cmd i => Some i
| _ => None
end.

Definition getBindingInsn (ib:id_binding) : option insn :=
match ib with
| id_binding_cmd c => Some (insn_cmd c)
| id_binding_phinode p => Some (insn_phinode p)
| id_binding_terminator tmn => Some (insn_terminator tmn)
| _ => None
end.


Definition getBindingPhiNode (ib:id_binding) : option phinode :=
match ib with
| id_binding_phinode i => Some i
| _ => None
end.

Definition getBindingTerminator (ib:id_binding) : option terminator :=
match ib with
| id_binding_terminator i => Some i
| _ => None
end.

Definition getFheaderID (fh:fheader) : id :=
match fh with
| fheader_intro _ id _ => id
end.

Definition getFdecID (fd:fdec) : id :=
match fd with
| fdec_intro fh => getFheaderID fh
end.

Definition getFdefID (fd:fdef) : id :=
match fd with
| fdef_intro fh _ => getFheaderID fh
end.

(*
Definition getNormalDestFromInvokeInsnC (i:insn) : option l :=
match i with
| insn_invoke _ _ _ _ l1 _ => Some l1
| _ => None
end.

Definition getUnwindDestFromInvokeInsnC (i:insn) : option l :=
match i with
| insn_invoke _ _ _ _ _ l2 => Some l2
| _ => None
end.
*)

Fixpoint getLabelViaIDFromList (ls:list (id*l)) (branch:id) : option l :=
match ls with
| nil => None
| (id, l)::ls' => 
  match (eq_dec id branch) with
  | left _ => Some l
  | right _ => getLabelViaIDFromList ls' branch
  end
end.

Definition getLabelViaIDFromPhiNode (phi:phinode) (branch:id) : option l :=
match phi with
| insn_phi _ _ ls => getLabelViaIDFromList ls branch
end.

Fixpoint getLabelsFromIdls (idls:list (id*l)) : ls :=
match idls with
| nil => lempty_set
| (_, l)::idls' => lset_add l (getLabelsFromIdls idls')
end.

Definition getLabelsFromPhiNode (phi:phinode) : ls :=
match phi with
| insn_phi _ _ ls => getLabelsFromIdls ls
end.

Fixpoint getLabelsFromPhiNodes (phis:list phinode) : ls :=
match phis with
| nil => lempty_set
| phi::phis' => lset_union (getLabelsFromPhiNode phi) (getLabelsFromPhiNodes phis')
end.


Definition getIDLabelsFromPhiNode p : id_labels :=
match p with
| insn_phi _ _ idls => idls
end.

Fixpoint getLabelViaIDFromIDLabels idls id : option l :=
match idls with
| nil => None
| (id0, l0)::idls' => if eq_dec id id0 then Some l0 else getLabelViaIDFromIDLabels idls' id
end.

Definition _getLabelViaIDPhiNode p id : option l :=
match p with
| insn_phi _ _ ls => getLabelViaIDFromIDLabels ls id
end.

Definition getLabelViaIDPhiNode (phi:insn) id : option l :=
match phi with
| insn_phinode p => _getLabelViaIDPhiNode p id
| _ => None
end.

Definition getReturnTyp fdef : typ :=
match fdef with
| fdef_intro (fheader_intro t _ _) _ => t
end.

Definition getGvarID g : id :=
match g with
| gvar_intro id _ _ _ => id
end.

Definition getCallName i : option id :=
match i with
| insn_cmd (insn_call _ _ _ _ id0 _) => Some id0
| _ => None
end.

(**********************************)
(* Lookup. *)

(* ID binding lookup *)

Definition lookupBindingViaIDFromCmd (i:cmd) (id:id) : id_binding :=
match (getCmdID i) with
| id' =>
  match (eq_dec id id') with
  | left _ => id_binding_cmd i
  | right _ => id_binding_none
  end
end.

Fixpoint lookupBindingViaIDFromCmds (li:list_cmd) (id:id) : id_binding :=
match li with
| nil => id_binding_none
| i::li' =>
  match (lookupBindingViaIDFromCmd i id) with
  | id_binding_cmd _ => id_binding_cmd i
  | _ => lookupBindingViaIDFromCmds li' id
  end
end.

Definition lookupBindingViaIDFromPhiNode (i:phinode) (id:id) : id_binding :=
match (getPhiNodeID i) with
| id' =>
  match (eq_dec id id') with
  | left _ => id_binding_phinode i
  | right _ => id_binding_none
  end
end.

Fixpoint lookupBindingViaIDFromPhiNodes (li:list_phinode) (id:id) : id_binding :=
match li with
| nil => id_binding_none
| i::li' =>
  match (lookupBindingViaIDFromPhiNode i id) with
  | id_binding_phinode _ => id_binding_phinode i
  | _ => lookupBindingViaIDFromPhiNodes li' id
  end
end.

Definition lookupBindingViaIDFromTerminator (i:terminator) (id:id) : id_binding :=
match (getTerminatorID i) with
| id' =>
  match (eq_dec id id') with
  | left _ => id_binding_terminator i
  | right _ => id_binding_none
  end
end.

Definition lookupBindingViaIDFromBlock (b:block) (id:id) : id_binding :=
match b with
| block_intro l ps cs t =>
  match (lookupBindingViaIDFromPhiNodes ps id) with
  | id_binding_none => 
    match (lookupBindingViaIDFromCmds cs id) with
    | id_binding_none => lookupBindingViaIDFromTerminator t id
    | re => re
    end
  | re => re    
  end
end.

Fixpoint lookupBindingViaIDFromBlocks (lb:list_block) (id:id) : id_binding :=
match lb with
| nil => id_binding_none
| b::lb' => 
  match (lookupBindingViaIDFromBlock b id) with
  | id_binding_none => lookupBindingViaIDFromBlocks lb' id
  | re => re
  end
end.

Definition lookupBindingViaIDFromArg (a:arg) (id:id) : id_binding :=
let (t, id') := a in
match (eq_dec id id') with
| left _ => id_binding_arg a
| right _ => id_binding_none
end.

Fixpoint lookupBindingViaIDFromArgs (la:list_arg) (id:id) : id_binding :=
match la with 
| nil => id_binding_none
| a::la' => 
  match (lookupBindingViaIDFromArg a id) with
  | id_binding_arg a' => id_binding_arg a'
  | _ => lookupBindingViaIDFromArgs la' id
  end
end.

Definition lookupBindingViaIDFromFdec (fd:fdec) (id:id) : id_binding :=
let '(fdec_intro (fheader_intro t id' la)) := fd in
match (eq_dec id id') with
| left _ => id_binding_fdec fd
| right _ => lookupBindingViaIDFromArgs la id
end.

Definition lookupBindingViaIDFromFdef (fd:fdef) (id:id) : id_binding :=
let '(fdef_intro fh lb) := fd in
lookupBindingViaIDFromBlocks lb id.

Definition lookupBindingViaIDFromProduct (p:product) (id:id) : id_binding :=
match p with
| product_gvar (gvar_intro id' t c a) =>
  match (eq_dec id id') with
  | left _ => id_binding_gvar (gvar_intro id' t c a)
  | right _ => id_binding_none
  end
| product_fdec fdec => lookupBindingViaIDFromFdec fdec id
(* | product_namedt _ => id_binding_none *)
| product_fdef fdef => lookupBindingViaIDFromFdef fdef id
end.  

Fixpoint lookupBindingViaIDFromProducts (lp:list_product) (id:id) : id_binding :=
match lp with
| nil => id_binding_none
| p::lp' => 
  match (lookupBindingViaIDFromProduct p id) with
  | id_binding_none => lookupBindingViaIDFromProducts lp' id
  | re => re
  end
end.
  
Definition lookupBindingViaIDFromModule (m:module) (id:id) : id_binding :=
  let (os, ps) := m in 
  lookupBindingViaIDFromProducts ps id.

Fixpoint lookupBindingViaIDFromModules (lm:list_module) (id:id) : id_binding :=
match lm with
| nil => id_binding_none
| m::lm' =>
  match (lookupBindingViaIDFromModule m id) with
  | id_binding_none => lookupBindingViaIDFromModules lm' id
  | re => re
  end
end.

Definition lookupBindingViaIDFromSystem (s:system) (id:id) : id_binding :=
lookupBindingViaIDFromModules s id.

(* Block lookup from ID *)

Definition isIDInBlockB (id:id) (b:block) : bool :=
match (lookupBindingViaIDFromBlock b id) with
| id_binding_none => false
| _ => true
end.

Fixpoint lookupBlockViaIDFromBlocks (lb:list_block) (id:id) : option block :=
match lb with
| nil => None  
| b::lb' => 
  match (isIDInBlockB id b) with
  | true => Some b
  | false => lookupBlockViaIDFromBlocks lb' id
  end
end.

Definition lookupBlockViaIDFromFdef (fd:fdef) (id:id) : option block :=
match fd with
| fdef_intro fh lb => lookupBlockViaIDFromBlocks lb id
end.

(* Fun lookup from ID *)

Definition lookupFdecViaIDFromProduct (p:product) (i:id) : option fdec :=
match p with
| (product_fdec fd) => if eq_dec (getFdecID fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdecViaIDFromProducts (lp:list_product) (i:id) : option fdec :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdecViaIDFromProduct p i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromProducts lp' i
  end
end.

Definition lookupFdecViaIDFromModule (m:module) (i:id) : option fdec :=
  let (os, ps) := m in 
  lookupFdecViaIDFromProducts ps i.

Fixpoint lookupFdecViaIDFromModules (lm:list_module) (i:id) : option fdec :=
match lm with
| nil => None
| m::lm' => 
  match (lookupFdecViaIDFromModule m i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromModules lm' i
  end
end.

Definition lookupFdecViaIDFromSystem (s:system) (i:id) : option fdec :=
lookupFdecViaIDFromModules s i.

Definition lookupFdefViaIDFromProduct (p:product) (i:id) : option fdef :=
match p with
| (product_fdef fd) => if eq_dec (getFdefID fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdefViaIDFromProducts (lp:list_product) (i:id) : option fdef :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdefViaIDFromProduct p i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromProducts lp' i
  end
end.

Definition lookupFdefViaIDFromModule (m:module) (i:id) : option fdef :=
  let (os, ps) := m in 
  lookupFdefViaIDFromProducts ps i.

Fixpoint lookupFdefViaIDFromModules (lm:list_module) (i:id) : option fdef :=
match lm with
| nil => None
| m::lm' => 
  match (lookupFdefViaIDFromModule m i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromModules lm' i
  end
end.

Definition lookupFdefViaIDFromSystem (s:system) (i:id) : option fdef :=
lookupFdefViaIDFromModules s i.

(*     ID type lookup                                    *)

Definition lookupTypViaIDFromCmd (i:cmd) (id0:id) : option typ :=
match (getCmdTyp i) with
| None => None
| Some t => 
  match (getCmdID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some t
    else None
  end
end.

Fixpoint lookupTypViaIDFromCmds (li:list_cmd) (id0:id) : option typ :=
match li with
| nil => None
| i::li' =>
  match (lookupTypViaIDFromCmd i id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromCmds li' id0
  end
end.
    
Definition lookupTypViaIDFromPhiNode (i:phinode) (id0:id) : option typ :=
match (getPhiNodeTyp i) with
| t => 
  match (getPhiNodeID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some t
    else None
  end
end.

Fixpoint lookupTypViaIDFromPhiNodes (li:list_phinode) (id0:id) : option typ :=
match li with
| nil => None
| i::li' =>
  match (lookupTypViaIDFromPhiNode i id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromPhiNodes li' id0
  end
end.

Definition lookupTypViaIDFromTerminator (i:terminator) (id0:id) : option typ :=
match (getTerminatorTyp i) with
| t => 
  match (getTerminatorID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some t
    else None
  end
end.

Definition lookupTypViaIDFromBlock (b:block) (id0:id) : option typ :=
match b with
| block_intro l ps cs t =>
  match (lookupTypViaIDFromPhiNodes ps id0) with
  | None => 
    match (lookupTypViaIDFromCmds cs id0) with
    | None => lookupTypViaIDFromTerminator t id0
    | re => re
    end
  | re => re    
  end
end.

Fixpoint lookupTypViaIDFromBlocks (lb:list_block) (id0:id) : option typ :=
match lb with
| nil => None
| b::lb' =>
  match (lookupTypViaIDFromBlock b id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromBlocks lb' id0
  end
end.

Definition lookupTypViaIDFromFdef (fd:fdef) (id0:id) : option typ :=
match fd with
| (fdef_intro _ lb) => lookupTypViaIDFromBlocks lb id0
end.

Definition lookupTypViaIDFromProduct (p:product) (id0:id) : option typ :=
match p with
| (product_fdef fd) => lookupTypViaIDFromFdef fd id0
| _ => None
end.

Fixpoint lookupTypViaIDFromProducts (lp:list_product) (id0:id) : option typ :=
match lp with
| nil => None
| p::lp' =>
  match (lookupTypViaIDFromProduct p id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromProducts lp' id0
  end
end.

Definition lookupTypViaIDFromModule (m:module) (id0:id) : option typ :=
  let (os, ps) := m in 
 lookupTypViaIDFromProducts ps id0.
     
Fixpoint lookupTypViaIDFromModules (lm:list_module) (id0:id) : option typ :=
match lm with
| nil => None
| m::lm' =>
  match (lookupTypViaIDFromModule m id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromModules lm' id0
  end
end.

Definition lookupTypViaIDFromSystem (s:system) (id0:id) : option typ :=
lookupTypViaIDFromModules s id0.

(**********************************)
(* SSA. *)

  Definition l2block := l -> option block.

  Definition mergel2block (lb1:l2block) (lb2:l2block) : l2block :=
  fun l0 =>
  match (lb1 l0, lb2 l0) with
  | (Some b1, _) => Some b1
  | (_, Some b2) => Some b2
  | (_, _) => None 
  end.

  Definition genLabel2Block_block (b:block) (f:fdef) : l2block :=
  match b with
  | block_intro l _ _ _ => fun l' => 
    if eq_dec l' l then Some b else None
  end.  

  Fixpoint genLabel2Block_blocks (bs:list_block) (f:fdef) : l2block :=
  match bs with 
  | nil => fun _ => None
  | b::bs' => mergel2block (genLabel2Block_blocks bs' f) (genLabel2Block_block b f)
  end.

  Definition genLabel2Block_fdef (f:fdef) : l2block := 
  match f with
  | fdef_intro fheader blocks => genLabel2Block_blocks blocks f
  end.

  Fixpoint genLabel2Block_product (p:product) : l2block :=
  match p with 
  | product_gvar g => fun _ => None
  | product_fdef f => (genLabel2Block_fdef f)
  | product_fdec f => fun _ => None 
  (*  | product_namedtype nt => fun _ => None *)
  end.

  Fixpoint genLabel2Block_products (ps:list_product) : l2block :=
  match ps with
  | nil => fun _ => None
  | p::ps' => mergel2block (genLabel2Block_products ps') (genLabel2Block_product p)
  end.

  Definition genLabel2Block (m: module) : l2block :=
  let (os, ps) := m in
  genLabel2Block_products ps.

  Definition getEntryOfFdef (f:fdef) : option block :=
  match f with
  | fdef_intro fheader blocks => 
    match blocks with
    | nil => None
    | b::blocks' => Some b
    end 
  end.  

  Definition getNonEntryOfFdef (f:fdef) : list_block :=
  match f with
  | fdef_intro fheader blocks => 
    match blocks with
    | nil => nil
    | b::blocks' => blocks'
    end 
  end.  

  Definition lookupBlockViaLabelFromFdef (f:fdef) (l0:l) : option block :=
  genLabel2Block_fdef f l0.  

  Definition lookupBlockViaLabelFromModule (m:module) (l0:l) : option block :=
  genLabel2Block m l0.  

  Fixpoint lookupBlockViaLabelFromSystem (s:system) (l0:l) : option block :=
  match s with 
  | nil => None
  | m::s' =>
    match (genLabel2Block m l0) with
    | Some b => Some b
    | None => lookupBlockViaLabelFromSystem s' l0
    end  
  end.

  Fixpoint getLabelsFromBlocks (lb:list_block) : ls :=
  match lb with
  | nil => lempty_set
  | (block_intro l0 _ _ _)::lb' => lset_add l0 (getLabelsFromBlocks lb')
  end.

(**********************************)
(* UseDef *)

  Definition mergeInsnUseDef (udi1:usedef_id) (udi2:usedef_id) : usedef_id :=
  fun i => (udi1 i) ++ (udi2 i).

  Definition mergeBlockUseDef (udb1:usedef_block) (udb2:usedef_block) : usedef_block :=
  fun b => (udb1 b) ++ (udb2 b).

  Infix "+++" := mergeInsnUseDef (right associativity, at level 60).
  Infix "++++" := mergeBlockUseDef (right associativity, at level 60).

  (* generate id use-def *)

  Definition genIdUseDef_id_uses_value (v:value) (id0:id): usedef_id :=
  fun id' => 
  match (getValueID v) with
  | Some id => if eq_dec id' id then id0::nil else nil
  | _ => nil
  end.     

  Definition genIdUseDef_id_uses_id (id0:id) (id1:id) : usedef_id :=
  fun id' => if eq_dec id' id0 then id1::nil else nil.

  Fixpoint genIdUseDef_id_uses_params (ps:list_param) (id0:id) : usedef_id :=
  match ps with
  | nil => fun _ => nil
  | (_, v)::ps' => (genIdUseDef_id_uses_value v id0)+++(genIdUseDef_id_uses_params ps' id0)
  end.

  Definition genIdUseDef_cmd_uses_value (v:value) (i:cmd) : usedef_id :=
  genIdUseDef_id_uses_value v (getCmdID i).

  Definition genIdUseDef_terminator_uses_value (v:value) (i:terminator) : usedef_id :=
  genIdUseDef_id_uses_value v (getTerminatorID i).

  Definition genIdUseDef_phinode_uses_value (v:value) (i:phinode) : usedef_id :=
  genIdUseDef_id_uses_value v (getPhiNodeID i).

  Definition genIdUseDef_cmd_uses_id (id0:id) (i:cmd) : usedef_id :=
  genIdUseDef_id_uses_id id0 (getCmdID i).

  Definition genIdUseDef_terminator_uses_id (id0:id) (i:terminator) : usedef_id :=
  genIdUseDef_id_uses_id id0 (getTerminatorID i).

  Definition genIdUseDef_phinode_uses_id (id0:id) (i:phinode) : usedef_id :=
  genIdUseDef_id_uses_id id0 (getPhiNodeID i).

  Definition genIdUseDef_cmd_uses_params (ps:list_param) (i:cmd) : usedef_id :=
  genIdUseDef_id_uses_params ps (getCmdID i).

  Definition genIdUseDef_terminator_uses_params (ps:list_param) (i:terminator) : usedef_id :=
  genIdUseDef_id_uses_params ps (getTerminatorID i).

  Definition genIdUseDef_phinode_uses_params (ps:list_param) (i:phinode) : usedef_id :=
  genIdUseDef_id_uses_params ps (getPhiNodeID i).

  Definition genIdUseDef_cmd (i:cmd): usedef_id :=
  match i with
  | insn_bop id _ sz v1 v2 => (genIdUseDef_id_uses_value v1 id)+++
                              (genIdUseDef_id_uses_value v2 id)
  (* | insn_extractelement id typ0 value0 c1 =>  *)
  (*   (genIdUseDef_id_uses_value value0 id) *)
  (* | insn_insertelement id typ0 value0 typ1 v1 c2 =>  *)
  (*   (genIdUseDef_od_uses_value value0 id)+++(genIdUseDef_id_uses_value v1 id) *)
  | insn_extractvalue id typ0 value0 _ => (genIdUseDef_id_uses_value value0 id)
  | insn_insertvalue id typs v0 typ1 v1 c2 => 
    (genIdUseDef_cmd_uses_value v0 i)+++(genIdUseDef_id_uses_value v1 id)
  | insn_malloc id typ _ _ => fun _ => nil
  | insn_free id typ v => genIdUseDef_id_uses_value v id
  | insn_alloca id typ _ _ => fun _ => nil
  | insn_load id typ1 v1 => genIdUseDef_id_uses_value v1 id
  | insn_store id typ1 v1 v2 => (genIdUseDef_id_uses_value v1 id)+++
                               (genIdUseDef_id_uses_value v2 id)
  | insn_gep id _ typ0 value0 _ => (genIdUseDef_id_uses_value value0 id)
  (* | insn_trunc id typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)			 *)
  | insn_ext id _ sz1 v1 sz2 => (genIdUseDef_id_uses_value v1 id)			 
  (* | insn_fptrunc id typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)          	 *)
  (* | insn_fptoui id typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)			 *)
  (* | insn_fptosi id typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)			 *)
  (* | insn_uitofp id typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)			 *)
  (* | insn_sitofp id typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)			 *)
  | insn_cast id _ typ1 v1 typ2 => (genIdUseDef_id_uses_value v1 id)			 
  | insn_icmp id cond typ v1 v2 => (genIdUseDef_id_uses_value v1 id)+++
                                   (genIdUseDef_id_uses_value v2 id)
  (* | insn_fcmp id cond typ v1 v2 => (genIdUseDef_id_uses_value v1 id)+++(genIdUseDef_id_uses_value v2 id)  *)
  | insn_select id v0 typ v1 v2 => (genIdUseDef_id_uses_value v0 id)+++
                                   (genIdUseDef_id_uses_value v1 id)+++
                                   (genIdUseDef_id_uses_value v2 id)
  | insn_call id _ _ typ id0 paraml => (genIdUseDef_id_uses_id id0 id)+++
                                       (genIdUseDef_id_uses_params paraml id)
  end.
 
  Definition genIdUseDef_terminator (i:terminator) : usedef_id :=
  match i with
  | insn_return id t v => genIdUseDef_id_uses_value v id
  | insn_return_void  _ => fun _ => nil
  | insn_br id v l1 l2 => genIdUseDef_id_uses_value v id
  | insn_br_uncond _ l => fun _ => nil
  (* | insn_switch id t v l _ => genIdUseDef_id_uses_value v id *)
  (* | insn_invoke id typ id0 paraml l1 l2 => (genIdUseDef_id_uses_id id0 id)+++ *)
  (*                                          (genIdUseDef_id_uses_params paraml id) *)
  | insn_unreachable _ => fun _ => nil
  end.

  Fixpoint genIdUseDef_id_uses_idls (idls:id_labels) (id0:id) : usedef_id :=
  match idls with
  | nil => fun _ => nil
  | (id1, _)::idls' => (genIdUseDef_id_uses_id id1 id0)+++
                       (genIdUseDef_id_uses_idls idls' id0)
  end.

  Definition genIdUseDef_phinode (i:phinode) : usedef_id :=
  match i with
  | insn_phi id typ idls => genIdUseDef_id_uses_idls idls id
  end.

  Fixpoint genIdUseDef_cmds (is:list_cmd) : usedef_id :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genIdUseDef_cmd i)+++(genIdUseDef_cmds is')
  end.  

  Fixpoint genIdUseDef_phinodes (is:list_phinode) : usedef_id :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genIdUseDef_phinode i)+++(genIdUseDef_phinodes is')
  end.  

  Definition genIdUseDef_block (b:block) : usedef_id :=
  match b with
  | block_intro l ps cs t => (genIdUseDef_phinodes ps)+++
                             (genIdUseDef_cmds cs)+++
                             (genIdUseDef_terminator t)
  end.  

  Fixpoint genIdUseDef_blocks (bs:list_block) : usedef_id :=
  match bs with 
  | nil => fun _ => nil
  | b::bs' => (genIdUseDef_blocks bs')+++(genIdUseDef_block b)
  end.

  Definition genIdUseDef_fdef (f:fdef) : usedef_id := 
  match f with
  | fdef_intro fheader blocks => genIdUseDef_blocks blocks 
  end.

  Definition genIdUseDef_product (p:product) : usedef_id :=
  match p with 
  | product_gvar (gvar_intro id t v a) => genIdUseDef_id_uses_value v id
  | product_fdef f => (genIdUseDef_fdef f)
  | product_fdec f => fun _ => nil
  (* | product_namedtype nt => fun _ => nil *)
  end.

  Fixpoint genIdUseDef_products (ps:list_product) : usedef_id :=
  match ps with
  | nil => fun _ => nil
  | p::ps' => (genIdUseDef_products ps') +++ (genIdUseDef_product p) 
  end.

  Definition genIdUseDef (m: module) : usedef_id :=
  let (os, ps) := m in 
  genIdUseDef_products ps.

  Definition getIdUseDef (udi:usedef_id) (i:id) : list id :=
  udi i. 

  (* generate block use-def *)

  Definition getBlockLabel (b:block) : l :=
  match b with
  | block_intro l _ _ _ => l
  end.

  Definition genBlockUseDef_label (l0:l) (b:block) : usedef_block :=
  fun b' => if eq_dec (getBlockLabel b') l0 then b::nil else nil.

  Fixpoint genBlockUseDef_switch_cases (cs:list (const * l)) (b:block) : usedef_block :=
  match cs with
  | nil => fun _ => nil
  | (_, l0)::cs' => (genBlockUseDef_label l0 b)++++(genBlockUseDef_switch_cases cs' b)
  end.

  Fixpoint genBlockUseDef_phi_cases (ps:list (id * l)) (b:block) : usedef_block :=
  match ps with
  | nil => fun _ => nil
  | (_, l0)::ps' => (genBlockUseDef_label l0 b)++++(genBlockUseDef_phi_cases ps' b)
  end.

  Definition genBlockUseDef_cmd (i:cmd) (b:block) : usedef_block :=
  match i with
  | insn_bop id _ sz v1 v2 => fun _ => nil 
  (* | insn_extractelement id typ0 v0 c1 => fun _ => nil *)
  (* | insn_insertelement id typ0 v0 typ1 v1 c2 => fun _ => nil *)
  | insn_extractvalue id typ0 v0 c1 => fun _ => nil 
  | insn_insertvalue id typ0 v0 typ1 v1 c2 => fun _ => nil 
  | insn_malloc id typ _ _ => fun _ => nil 
  | insn_free _ typ _ => fun _ => nil 
  | insn_alloca id typ _ _ => fun _ => nil 
  | insn_load id typ1 v1 => fun _ => nil 
  | insn_store _ typ1 v1 v2 => fun _ => nil 
  | insn_gep id _ typ0 v0 c1 => fun _ => nil 
  (* | insn_trunc id typ1 v1 typ2 => fun _ => nil *)
  | insn_ext id _ sz1 v1 sz2 => fun _ => nil
  | insn_cast id _ typ1 v1 typ2 => fun _ => nil 
  | insn_icmp id cond typ v1 v2 => fun _ => nil
  (* | insn_fcmp id cond typ v1 v2 => fun _ => nil *)
  | insn_select id v0 t v1 v2 => fun _ => nil
  | insn_call _ _ _ typ id0 paraml => fun _ => nil 
  end.
 
  Definition genBlockUseDef_terminator (i:terminator) (b:block) : usedef_block :=
  match i with
  | insn_return _ t v => fun _ => nil
  | insn_return_void _ => fun _ => nil
  | insn_br _ v l1 l2 => genBlockUseDef_label l1 b ++++ genBlockUseDef_label l2 b
  | insn_br_uncond _ l => genBlockUseDef_label l b
  (* | insn_switch _ t v l ls => genBlockUseDef_label l b ++++ genBlockUseDef_switch_cases ls b*)
  (* | insn_invoke id typ id0 paraml l1 l2 => (genBlockUseDef_label l1 b)++++(genBlockUseDef_label l2 b) *)
  | insn_unreachable _ => fun _ => nil 
  end.

  Definition genBlockUseDef_phinode (i:phinode) (b:block) : usedef_block :=
  match i with
  | insn_phi id typ idls => genBlockUseDef_phi_cases idls b
  end.

  Fixpoint genBlockUseDef_cmds (is:list_cmd) (b:block) : usedef_block :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genBlockUseDef_cmd i b)++++(genBlockUseDef_cmds is' b)
  end.  

  Fixpoint genBlockUseDef_phinodes (is:list_phinode) (b:block) : usedef_block :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genBlockUseDef_phinode i b)++++(genBlockUseDef_phinodes is' b)
  end.  

  Definition genBlockUseDef_block (b:block) : usedef_block :=
  match b with
  | block_intro l ps cs t => genBlockUseDef_phinodes ps b++++
                             genBlockUseDef_cmds cs b++++
                             genBlockUseDef_terminator t b
  end.  

  Fixpoint genBlockUseDef_blocks (bs:list_block) : usedef_block :=
  match bs with 
  | nil => fun _ => nil
  | b::bs' => (genBlockUseDef_blocks bs')++++(genBlockUseDef_block b)
  end.

  Definition genBlockUseDef_fdef (f:fdef) : usedef_block := 
  match f with
  | fdef_intro fheader blocks => genBlockUseDef_blocks blocks
  end.

  Fixpoint genBlockUseDef_product (p:product) : usedef_block :=
  match p with 
  | product_gvar g => fun _ => nil
  | product_fdef f => (genBlockUseDef_fdef f)
  | product_fdec f => fun _ => nil
  (* | product_namedtype nt => fun _ => nil *)
  end.

  Fixpoint genBlockUseDef_products (ps:list_product) : usedef_block :=
  match ps with
  | nil => fun _ => nil
  | p::ps' => (genBlockUseDef_products ps') ++++ (genBlockUseDef_product p) 
  end.

  Definition genBlockUseDef (m: module) : usedef_block :=
  let (os, ps) := m in 
  genBlockUseDef_products ps.

  Definition getBlockUseDef (udb:usedef_block) (b:block) : list block :=
  udb b. 

(**********************************)
(* CFG. *)

  Definition getTerminator (b:block) : terminator := 
  match b with
  | block_intro l _ _ t => t
  end. 

  Fixpoint getLabelsFromSwitchCases (cs:list (const*l)) : ls :=
  match cs with
  | nil => lempty_set 
  | (_, l0)::cs' => lset_add l0 (getLabelsFromSwitchCases cs')
  end.

  Definition getLabelsFromTerminator (i:terminator) : ls := 
  match i with
  | insn_br _ v l1 l2 => lset_add l1 (lset_add l2 lempty_set)
  | insn_br_uncond _ l0 => lset_add l0 lempty_set 
  (* | insn_switch _ t v l0 cls => lset_add l0 (getLabelsFromSwitchCases cls) *)
  (* | insn_invoke id typ id0 ps l1 l2 => lset_add l1 (lset_add l2 lempty_set) *)
  | _ => empty_set l
  end.

  Fixpoint getBlocksFromLabels (ls0:ls) (l2b:l2block): list_block :=
  match ls0 with
  | nil => nil
  | l0::ls0' => 
    match (l2b l0) with
    | None => getBlocksFromLabels ls0' l2b
    | Some b => b::getBlocksFromLabels ls0' l2b
    end
  end.

  Definition succOfBlock (b:block) (m:module) : list_block :=
  match (getTerminator b) with
  | i => getBlocksFromLabels (getLabelsFromTerminator i) (genLabel2Block m)
  end.
  
  Definition predOfBlock (b:block) (udb:usedef_block) : list_block :=
  udb b.

  Definition hasSinglePredecessor (b:block) (udb:usedef_block) : bool :=
  match (eq_nat_dec (length (predOfBlock b udb)) 1) with
  | left _ => true
  | right _ => false
  end.

(**********************************)
(* Dominator. *)

  Parameter genLabelsFromFdef : fdef -> ls.

  Fixpoint inputFromPred (bs:list_block) (output:dt) : ls :=
  match bs with
  | nil => lempty_set
  | (block_intro l0 _ _ _)::bs' => lset_union (output l0) (inputFromPred bs' output)
  end.

  Definition outputFromInput (b:block) (input:ls) : ls :=
  match b with
  | block_intro l0 _ _ _=> lset_add l0 input
  end.

  Definition update_dt (d1:dt) (l0:l) (ls0:ls) : dt :=
  fun l1 => if eq_dec l1 l0 then ls0 else d1 l1.

  Definition inter_dt (d1 d2:dt) : dt :=
  fun l0 => lset_inter (d1 l0) (d2 l0).

  Fixpoint genDominatorTree_blocks_innerloop (bs:list_block) (udb:usedef_block) (output:dt) : dt :=
  match bs with 
  | nil => output
  | (block_intro l ps cs t)::bs' => 
    match (outputFromInput (block_intro l ps cs t) (inputFromPred (predOfBlock (block_intro l ps cs t) udb) output)) with 
    | ls' => genDominatorTree_blocks_innerloop bs' udb (update_dt output l ls') 
    end
(*  | (block_without_label is)::bs' => 
    genDominatorTree_blocks_innerloop bs' udb output  *)
  end.  

  (*
    Check if the two dominator tress are equal w.r.t the domain (blocks of the current function)
  *)
  Fixpoint eq_dt (d0 d1:dt) (bs:list_block) : bool :=
  match bs with
  | nil => true
  | (block_intro l0 _ _ _)::bs' =>
    match (lset_eq (d0 l0) (d1 l0)) with
    | true => eq_dt d0 d1 bs'
    | false => false
    end
(*  | _::bs' => eq_dt d0 d1 bs' *)
  end.

  Fixpoint sizeOfDT (bs:list_block) (output:dt) : nat :=
  match bs with
  | nil => 0
  | (block_intro l0 _ _ _)::bs' => length (output l0) + sizeOfDT bs' output
(*  | _::bs'=> sizeOfDT bs' output *)
  end.

  Definition size (arg:(list_block*dt)) : nat :=
  match arg with
  | (bs, output) => sizeOfDT bs output
  end.

  Function genDominatorTree_blocks (arg:list_block*dt) (udb:usedef_block) {measure size arg} : dt :=
  match arg with
  | (bs, output) => 
    match (genDominatorTree_blocks_innerloop bs udb output) with
    | output' =>
      match (eq_dt output output' bs) with
      | true => output'
      | false => genDominatorTree_blocks (bs, output') udb
      end
    end
  end.
  intros.
  Admitted.

  Fixpoint initialize_genDominatorTree_blocks (bs:list_block) (U:ls) (d0:dt) : dt :=
  match bs with
  | nil => d0
  | (block_intro l0 _ _ _)::bs' => initialize_genDominatorTree_blocks bs' U (update_dt d0 l0 U)
(*  | _::bs' => initialize_genDominatorTree_blocks bs' U d0 *)
  end.

  Definition genEmptyDT : dt := fun _ => nil. 

  Definition initialize_genDominatorTree_entry (f:fdef) : dt :=
  match (getEntryOfFdef f) with
  | None => genEmptyDT
  | Some (block_intro l0 _ _ _) => update_dt genEmptyDT l0 (lset_single l0)
(*  | Some  _ => genEmptyDT *)
  end.

  Definition initialize_genDominatorTree (f:fdef) (U:ls) : dt :=
  initialize_genDominatorTree_blocks (getNonEntryOfFdef f) U (initialize_genDominatorTree_entry f).  

  Definition genDominatorTree (f:fdef) (m:module) : dt :=
  match f with
  | fdef_intro fheader blocks => 
    genDominatorTree_blocks (blocks, (initialize_genDominatorTree f (genLabelsFromFdef f))) (genBlockUseDef m)  
  end.

  Definition blockDominates (d:dt) (b1 b2: block) : Prop :=
  match b1 with
  | block_intro l1 _ _ _=>
    match (d l1) with
    | ls1 => 
      match b2 with
      | block_intro l2 _ _ _=> 
        match (lset_mem l2 ls1) with
        | true => True
        | false => False
        end
(*      | _ => False *)
      end
    end 
(*  | _ => False *)
  end.

  Definition blockDominatesB (d:dt) (b1 b2: block) : bool :=
  match b1 with
  | block_intro l1 _ _ _=>
    match (d l1) with
    | ls1 => 
      match b2 with
      | block_intro l2 _ _ _ => 
        match (lset_mem l2 ls1) with
        | true => true
        | false => false
        end
(*      | _ => false *)
      end
    end 
(*  | _ => false *)
  end.

  Definition insnDominates (i1 i2:insn) (b:block) : Prop :=
  match b with 
  | (block_intro l5 ps cs tmn) =>
    match (i1, i2) with
    | (insn_cmd _, insn_terminator _) => True  
    | (insn_phinode _, insn_terminator _) => True
    | (insn_phinode _, insn_cmd _) => True
    | (insn_cmd c1, insn_cmd c2) => 
      (exists cs1, exists cs2, exists cs3, cs = cs1++(c1::cs2)++(c2::cs3))
    | (insn_phinode p1, insn_phinode p2) => 
      (exists ps1, exists ps2, exists ps3, ps = ps1++(p1::ps2)++(p2::ps3))
    | _ => False
    end
  end.

  Definition isReachableFromEntry (fi:fdef_info) (b:block) : Prop :=
  let (f, d) := fi in   
  match (getEntryOfFdef f) with
  | None => False
  | Some be => blockDominates d be b
  end.
 
  Definition isReachableFromEntryB (fi:fdef_info) (b:block) : bool :=
  let (f, d) := fi in   
  match (getEntryOfFdef f) with
  | None => false
  | Some be => blockDominatesB d be b
  end.

(**********************************)
(* Classes. *)

Definition isPointerTypB (t:typ) : bool :=
match t with
| typ_pointer _ => true
| _ => false
end.

Definition isArrayTypB (t:typ) : bool :=
match t with
| typ_array _ _ => true
| _ => false
end.

(*
Definition isInvokeInsnB (i:insn) : bool :=
match i with
| insn_invoke _ _ _ _ _ _ => true
| _ => false
end.
*)

Definition isReturnInsnB (i:terminator) : bool :=
match i with
| insn_return _ _ _ => true
| insn_return_void _ => true
| _ => false
end.

Definition _isCallInsnB (i:cmd) : bool :=
match i with
| insn_call _ _ _ _ _ _ => true
| _ => false
end.

Definition isCallInsnB (i:insn) : bool :=
match i with
| insn_cmd c => _isCallInsnB c
| _ => false
end.

Definition isNotValidReturnTypB (t:typ) : bool :=
match t with
| typ_label => true
| typ_metadata => true
| _ => false
end.

Definition isValidReturnTypB (t:typ) : bool :=
negb (isNotValidReturnTypB t).

Definition isNotFirstClassTypB (t:typ) : bool :=
match t with
| typ_void => true
(* | typ_opaque => true *)
| typ_function _ _ => true
| _ => false
end.

Definition isFirstClassTypB (t:typ) : bool :=
negb (isNotFirstClassTypB t).

Definition isValidArgumentTypB (t:typ) : bool :=
match t with
(*| typ_opaque => true *)
| _ => isFirstClassTypB t
end.

Definition isNotValidElementTypB (t:typ) : bool :=
match t with
| typ_void => true
| typ_label => true
| typ_metadata => true
| typ_function _ _ => true
| _ => false
end.

Definition isValidElementTypB (t:typ) : bool :=
negb (isNotValidElementTypB t).

Definition isBindingFdecB (ib:id_binding) : bool :=
match ib with
| id_binding_fdec fdec => true
| _ => false
end.

Definition isBindingGvarB (ib:id_binding) : bool :=
match ib with
| id_binding_gvar _ => true
| _ => false
end.

Definition isBindingArgB (ib:id_binding) : bool :=
match ib with
| id_binding_arg arg => true
| _ => false
end.

Definition isBindingCmdB (ib:id_binding) : bool :=
match ib with
| id_binding_cmd _ => true
| _ => false
end.

Definition isBindingTerminatorB (ib:id_binding) : bool :=
match ib with
| id_binding_terminator _ => true
| _ => false
end.

Definition isBindingPhiNodeB (ib:id_binding) : bool :=
match ib with
| id_binding_phinode _ => true
| _ => false
end.

Definition isBindingInsnB (ib:id_binding) : bool :=
isBindingCmdB ib || isBindingTerminatorB ib || isBindingPhiNodeB ib.

Definition isPointerTyp typ := isPointerTypB typ = true.

(* Definition isInvokeInsn insn := isInvokeInsnB insn = true. *)

Definition isReturnTerminator tmn := isReturnInsnB tmn = true.

Definition isNotValidReturnTyp typ := isNotValidReturnTypB typ = true.
      
Definition isValidReturnTyp typ := isValidReturnTypB typ = true.

Definition isNotFirstClassTyp typ := isNotFirstClassTypB typ = true.

Definition isFirstClassTyp typ := isFirstClassTypB typ = true.

Definition isValidArgumentTyp typ := isValidArgumentTypB typ = true.

Definition isNotValidElementTyp typ := isNotValidElementTypB typ = true.

Definition isValidElementTyp typ := isValidElementTypB typ = true.

Definition isBindingFdec ib : option fdec :=
match ib with
| id_binding_fdec f => Some f
| _ => None
end.

Definition isBindingArg ib : option arg :=
match ib with
| id_binding_arg a => Some a
| _ => None
end.

Definition isBindingGvar ib : option gvar :=
match ib with
| id_binding_gvar g => Some g
| _ => None
end.

Definition isBindingCmd ib : option cmd :=
match ib with
| id_binding_cmd c => Some c
| _ => None
end.

Definition isBindingPhiNode ib : option phinode :=
match ib with
| id_binding_phinode p => Some p
| _ => None
end.

Definition isBindingTerminator ib : option terminator :=
match ib with
| id_binding_terminator tmn => Some tmn
| _ => None
end.

Definition isBindingInsn ib : option insn :=
match ib with
| id_binding_cmd c => Some (insn_cmd c)
| id_binding_phinode p => Some (insn_phinode p)
| id_binding_terminator tmn => Some (insn_terminator tmn)
| _ => None
end.

Definition isAggregateTyp t := 
match t with
| typ_struct _ => True
| typ_array _ _ => True 
| _ => False
end.

(*************************************************)
(*         Uniq                                  *)

Fixpoint getCmdsIDs (cs:list cmd) : ids :=
match cs with
| nil => nil
| c::cs' => getCmdID c::getCmdsIDs cs'
end.

Fixpoint getPhiNodesIDs (ps:list phinode) : ids :=
match ps with
| nil => nil
| p::ps' => getPhiNodeID p::getPhiNodesIDs ps'
end.

Definition getBlockIDs b : ids :=
match b with
| block_intro l ps cs t =>
  getPhiNodesIDs ps++getCmdsIDs cs++(getTerminatorID t::nil)
end.

Fixpoint getBlocksIDs bs : ids :=
match bs with
| nil => nil
| b::bs' => getBlockIDs b++getBlocksIDs bs'
end.

Fixpoint getBlocksLabels bs : ls :=
match bs with
| nil => nil
| (block_intro l _ _ _)::bs' => l::getBlocksLabels bs'
end.

Definition uniqBlocks bs : Prop :=
let ls := getBlocksLabels bs in
let ids := getBlocksIDs bs in
NoDup ls /\ NoDup ids.


Definition uniqFdef fdef : Prop :=
match fdef with
| (fdef_intro _ bs) => uniqBlocks bs
end.

Definition getProductID product : id :=
match product with
| product_gvar g => getGvarID g
| product_fdec f => getFdecID f
| product_fdef f => getFdefID f
end.

Fixpoint getProductsIDs ps : ids :=
match ps with
| nil => nil
| p::ps' => getProductID p::getProductsIDs ps'
end.
   
Definition uniqProduct product : Prop :=
match product with
| product_gvar g => True
| product_fdec f => True
| product_fdef f => uniqFdef f
end.

Definition uniqProducts ps : Prop :=
NoDup (getProductsIDs ps).

Definition uniqModule m : Prop :=
match m with
| module_intro _ ps => uniqProducts ps
end.

Fixpoint uniqModules ms : Prop :=
match ms with
| nil => True
| m::ms' => uniqModule m /\ uniqModules ms'
end.

Definition uniqSystem s : Prop := uniqModules s.

(**********************************)
(* Eq. *)

Fixpoint typ_size (t:typ) : nat :=
  match t with
  | typ_int n => 1
  | typ_metadata => 1
  | typ_function t1 lt2 => 1+ typ_size t1 + fold_left plus (map typ_size lt2) 0
  | typ_void => 1
  | typ_label => 1
  | typ_array _ t' => 1 + typ_size t'
  | typ_pointer t' => 1 + typ_size t'
  | typ_struct lt1 => 1 + fold_left plus (map typ_size lt1) 0
  end.

Definition typ2_size (txy:typ*typ) : nat :=
  let (tx, ty) := txy in
  typ_size tx + typ_size ty.

Lemma list_typ_size__inc : forall lt n n',
  n <= n' ->
  n <= fold_left plus (map typ_size lt) n'.
Proof.
  induction lt; intros; simpl; auto.
    apply IHlt; auto.
      omega.
Qed.

Lemma typ_size__ge__zero : forall t,
  typ_size t >= 0.
Proof.
  induction t as [ | | | | | t H l0 | l0 | ]; simpl; auto.
    assert (J:=@list_typ_size__inc l0 0 0).
    omega.

    assert (J:=@list_typ_size__inc l0 0 0).
    omega.
Qed.

Lemma list_typ_size__ge__typ_size : forall lt t n,
  In t lt ->
  typ_size t <= fold_left plus (map typ_size lt) n.
Proof.
  induction lt; intros; simpl.
    inversion H.

    simpl in H. inversion H.
      subst. apply list_typ_size__inc. omega.
      apply IHlt; auto.
Qed.

Lemma flist_typ2_size__gt__typ2_size : forall t1 lt1 t1' lt1' t2 t2',
  In t2 lt1 ->
  In t2' lt1' ->
  typ2_size (t2, t2') < typ2_size (typ_function t1 lt1, typ_function t1' lt1').
Proof.
  intros.
  simpl.
  assert (J:=@list_typ_size__ge__typ_size lt1 t2 0 H).
  assert (J':=@list_typ_size__ge__typ_size lt1' t2' 0 H0).
  omega.
Qed. 

Definition create_felt tt t1 lt1 t1' lt1' t2 t2'
                (H1:In t2 lt1)
                (H2:In t2' lt1') 
                (H:(typ_function t1 lt1, typ_function t1' lt1') = tt):
  { t | typ2_size t < typ2_size tt }.
Proof.
  intros. subst.
  exists (t2, t2'). 
  apply flist_typ2_size__gt__typ2_size; auto.
Qed.

Lemma head_in_incl : forall A (x:A) (l1' l1 l2:list A),
  l1 = x::l1'->
  incl l1 l2 ->
  In x l2.
Proof.
  intros A x l1' l1 l2 H1 H2.
  apply H2. subst. simpl. auto.
Qed.

Lemma prod_eq_inv : forall A (x y:A) (lt1' lt1 lt2' lt2:list A),
  (lt1, lt2) = (x::lt1', y::lt2') ->
  lt1 = x::lt1' /\ lt2 = y::lt2'.
Proof.
  intros A x y lt1' lt1 lt2' lt2 H.
  inversion H; subst. auto.
Qed.

Lemma tail_incl_incl : forall A (x:A) (l1' l1 l2:list A),
  l1 = x::l1'->
  incl l1 l2 ->
  incl l1' l2.
Proof.
  intros A x l1' l1 l2 H1 H2. subst.
  apply incl_tran with (m:=x::l1'); auto.
  assert ((x::nil)++l1'=x::l1') as Eq. simpl. auto.
  rewrite <- Eq.
  apply incl_appr; auto.
  apply incl_refl.
Qed.  

Fixpoint create_felts tt t1 lt1 t2 lt2 ltl ltr 
              (Hl:incl lt1 ltl) 
              (Hr:incl lt2 ltr)
              (H:(typ_function t1 ltl, typ_function t2 ltr) = tt ) 
              {struct lt1} :
  list {t: typ*typ | typ2_size t < typ2_size tt } := 
(match (lt1,lt2) as r return ((lt1, lt2) = r -> _) with
| (x::lt1', y::lt2') => 
  fun Ha:(lt1,lt2) = (x::lt1', y::lt2') =>
  match (prod_eq_inv typ x y lt1' lt1 lt2' lt2 Ha) with
  | conj Hal Har  =>
    (create_felt tt t1 ltl t2 ltr x y 
          (head_in_incl typ x lt1' lt1 ltl Hal Hl) 
          (head_in_incl typ y lt2' lt2 ltr Har Hr)  
          H)::
    (create_felts tt t1 lt1' t2 lt2' ltl ltr 
           (tail_incl_incl typ x lt1' lt1 ltl Hal Hl) 
           (tail_incl_incl typ y lt2' lt2 ltr Har Hr) 
           H)
  end
| (_, _) => 
  fun _ =>
  nil
end) (refl_equal (lt1, lt2)).

Definition fcombine_with_measure tt t1 lt1 t1' lt1' (H:(typ_function t1 lt1, typ_function t1' lt1') = tt ) :
  list {t: typ*typ | typ2_size t < typ2_size tt } := 
  create_felts tt t1 lt1 t1' lt1' lt1 lt1' (incl_refl lt1) (incl_refl lt1') H.

Lemma slist_typ2_size__gt__typ2_size : forall lt1 lt1' t2 t2',
  In t2 lt1 ->
  In t2' lt1' ->
  typ2_size (t2, t2') < typ2_size (typ_struct lt1, typ_struct lt1').
Proof.
  intros.
  simpl.
  assert (J:=@list_typ_size__ge__typ_size lt1 t2 0 H).
  assert (J':=@list_typ_size__ge__typ_size lt1' t2' 0 H0).
  omega.
Qed. 

Definition create_selt tt lt1 lt1' t2 t2'
                (H1:In t2 lt1)
                (H2:In t2' lt1') 
                (H:(typ_struct lt1, typ_struct lt1') = tt):
  { t | typ2_size t < typ2_size tt }.
Proof.
  intros. subst.
  exists (t2, t2'). 
  apply slist_typ2_size__gt__typ2_size; auto.
Qed.

Fixpoint create_selts tt lt1 lt2 ltl ltr 
              (Hl:incl lt1 ltl) 
              (Hr:incl lt2 ltr)
              (H:(typ_struct ltl, typ_struct ltr) = tt ) 
              {struct lt1} :
  list {t: typ*typ | typ2_size t < typ2_size tt } := 
(match (lt1,lt2) as r return ((lt1, lt2) = r -> _) with
| (x::lt1', y::lt2') => 
  fun Ha:(lt1,lt2) = (x::lt1', y::lt2') =>
  match (prod_eq_inv typ x y lt1' lt1 lt2' lt2 Ha) with
  | conj Hal Har  =>
    (create_selt tt ltl ltr x y 
          (head_in_incl typ x lt1' lt1 ltl Hal Hl) 
          (head_in_incl typ y lt2' lt2 ltr Har Hr)  
          H)::
    (create_selts tt lt1' lt2' ltl ltr 
           (tail_incl_incl typ x lt1' lt1 ltl Hal Hl) 
           (tail_incl_incl typ y lt2' lt2 ltr Har Hr) 
           H)
  end
| (_, _) => 
  fun _ =>
  nil
end) (refl_equal (lt1, lt2)).

Definition scombine_with_measure tt lt1 lt1' (H:(typ_struct lt1, typ_struct lt1') = tt ) :
  list {t: typ*typ | typ2_size t < typ2_size tt } := 
  create_selts tt lt1 lt1' lt1 lt1' (incl_refl lt1) (incl_refl lt1') H.

Program Fixpoint _typEqB (tt:typ*typ) {measure typ2_size} : bool :=
(match tt as r return (tt = r -> _) with 
| (typ_int n, typ_int n') => 
  fun _ =>
  match (eq_nat_dec n n') with
  | left _ => true 
  | right _ => false
  end 
| (typ_metadata, typ_metadata) => fun _ => true
| (typ_void, typ_void) => fun _ => true
| (typ_label, typ_label) => fun _ => true
| (typ_pointer t1, typ_pointer t1') => fun _ => _typEqB (t1, t1')
| (typ_array n t1, typ_array n' t1') => fun _ =>
  match (eq_nat_dec n n') with
  | left _ => _typEqB (t1, t1')
  | right _ => false
  end
| (typ_function t1 lt1, typ_function t1' lt1') =>
  fun Ha:(tt = (typ_function t1 lt1, typ_function t1' lt1')) =>
  match (eq_nat_dec (length lt1) (length lt1')) with
  | left _ => 
    _typEqB (t1, t1') &&
    fold_left andb (map _typEqB (fcombine_with_measure tt t1 lt1 t1' lt1' Ha)) true 
  | right _ => false
  end
| (typ_struct lt1, typ_struct lt1') =>
  fun Ha:(tt = (typ_struct lt1, typ_struct lt1')) =>
  match (eq_nat_dec (length lt1) (length lt1')) with
  | left _ => 
    fold_left andb (map _typEqB (scombine_with_measure tt lt1 lt1' Ha)) true 
  | right _ => false
  end
| (_, _) => fun _ => false
end) (refl_equal tt).
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.


Definition typEqB (t t':typ) : bool := _typEqB (t, t').

Fixpoint const_size (c:const) : nat :=
  match c with
  | const_int _ n => 1
  | const_undef _ => 1
  | const_null _ => 1
  | const_arr lc => 1 + fold_left plus (map const_size lc) 0
  | const_struct lc => 1 + fold_left plus (map const_size lc) 0
  end.

Definition const2_size (cxy:const*const) : nat :=
  let (cx, cy) := cxy in
  const_size cx + const_size cy.

Lemma list_const_size__inc : forall lc n n',
  n <= n' ->
  n <= fold_left plus (map const_size lc) n'.
Proof.
  induction lc; intros; simpl; auto.
    apply IHlc; auto.
      omega.
Qed.

Lemma const_size__ge__zero : forall c,
  const_size c >= 0.
Proof.
  induction c as [ | | | l0 | l0 ]; simpl; auto.
    assert (J:=@list_const_size__inc l0 0 0).
    omega.

    assert (J:=@list_const_size__inc l0 0 0).
    omega.
Qed.

Lemma list_const_size__ge__const_size : forall lc c n,
  In c lc ->
  const_size c <= fold_left plus (map const_size lc) n.
Proof.
  induction lc; intros; simpl.
    inversion H.

    simpl in H. inversion H.
      subst. apply list_const_size__inc. omega.
      apply IHlc; auto.
Qed.

Lemma alist_const2_size__gt__const2_size : forall lc1 lc1' c2 c2',
  In c2 lc1 ->
  In c2' lc1' ->
  const2_size (c2, c2') < const2_size (const_arr lc1, const_arr lc1').
Proof.
  intros.
  simpl.
  assert (J:=@list_const_size__ge__const_size lc1 c2 0 H).
  assert (J':=@list_const_size__ge__const_size lc1' c2' 0 H0).
  omega.
Qed. 

Definition create_ca_elt cc lc1 lc1' c2 c2'
                (H1:In c2 lc1)
                (H2:In c2' lc1') 
                (H:(const_arr lc1, const_arr lc1') = cc):
  { c | const2_size c < const2_size cc }.
Proof.
  intros. subst.
  exists (c2, c2'). 
  apply alist_const2_size__gt__const2_size; auto.
Qed.

Fixpoint create_ca_elts cc lc1 lc2 lcl lcr 
              (Hl:incl lc1 lcl) 
              (Hr:incl lc2 lcr)
              (H:(const_arr lcl, const_arr lcr) = cc ) 
              {struct lc1} :
  list {c: const*const | const2_size c < const2_size cc } := 
(match (lc1,lc2) as r return ((lc1, lc2) = r -> _) with
| (x::lc1', y::lc2') => 
  fun Ha:(lc1,lc2) = (x::lc1', y::lc2') =>
  match (prod_eq_inv const x y lc1' lc1 lc2' lc2 Ha) with
  | conj Hal Har  =>
    (create_ca_elt cc lcl lcr x y 
          (head_in_incl const x lc1' lc1 lcl Hal Hl) 
          (head_in_incl const y lc2' lc2 lcr Har Hr)  
          H)::
    (create_ca_elts cc lc1' lc2' lcl lcr 
           (tail_incl_incl const x lc1' lc1 lcl Hal Hl) 
           (tail_incl_incl const y lc2' lc2 lcr Har Hr) 
           H)
  end
| (_, _) => 
  fun _ =>
  nil
end) (refl_equal (lc1, lc2)).

Definition ca_combine_with_measure cc lc1 lc1' (H:(const_arr lc1, const_arr lc1') = cc ) :
  list {c: const*const | const2_size c < const2_size cc } := 
  create_ca_elts cc lc1 lc1' lc1 lc1' (incl_refl lc1) (incl_refl lc1') H.

Lemma slist_const2_size__gt__const2_size : forall lc1 lc1' c2 c2',
  In c2 lc1 ->
  In c2' lc1' ->
  const2_size (c2, c2') < const2_size (const_struct lc1, const_struct lc1').
Proof.
  intros.
  simpl.
  assert (J:=@list_const_size__ge__const_size lc1 c2 0 H).
  assert (J':=@list_const_size__ge__const_size lc1' c2' 0 H0).
  omega.
Qed. 

Definition create_cs_elt cc lc1 lc1' c2 c2'
                (H1:In c2 lc1)
                (H2:In c2' lc1') 
                (H:(const_struct lc1, const_struct lc1') = cc):
  { c | const2_size c < const2_size cc }.
Proof.
  intros. subst.
  exists (c2, c2'). 
  apply slist_const2_size__gt__const2_size; auto.
Qed.

Fixpoint create_cs_elts cc lc1 lc2 lcl lcr 
              (Hl:incl lc1 lcl) 
              (Hr:incl lc2 lcr)
              (H:(const_struct lcl, const_struct lcr) = cc ) 
              {struct lc1} :
  list {c: const*const | const2_size c < const2_size cc } := 
(match (lc1,lc2) as r return ((lc1, lc2) = r -> _) with
| (x::lc1', y::lc2') => 
  fun Ha:(lc1,lc2) = (x::lc1', y::lc2') =>
  match (prod_eq_inv const x y lc1' lc1 lc2' lc2 Ha) with
  | conj Hal Har  =>
    (create_cs_elt cc lcl lcr x y 
          (head_in_incl const x lc1' lc1 lcl Hal Hl) 
          (head_in_incl const y lc2' lc2 lcr Har Hr)  
          H)::
    (create_cs_elts cc lc1' lc2' lcl lcr 
           (tail_incl_incl const x lc1' lc1 lcl Hal Hl) 
           (tail_incl_incl const y lc2' lc2 lcr Har Hr) 
           H)
  end
| (_, _) => 
  fun _ =>
  nil
end) (refl_equal (lc1, lc2)).

Definition cs_combine_with_measure cc lc1 lc1' (H:(const_struct lc1, const_struct lc1') = cc ) :
  list {c: const*const | const2_size c < const2_size cc } := 
  create_cs_elts cc lc1 lc1' lc1 lc1' (incl_refl lc1) (incl_refl lc1') H.

Program Fixpoint _constEqB (cc:const*const) {measure const2_size} : bool :=
(match cc as r return (cc = r -> _) with 
| (const_int sz n, const_int sz' n') => 
  fun _ => beq_nat n n' && beq_nat sz sz'
| (const_null t, const_null t') => fun _ => typEqB t t'
| (const_undef t, const_undef t') => fun _ => typEqB t t'
| (const_struct lc1, const_struct lc1') =>
  fun Ha:(cc = (const_struct lc1, const_struct lc1')) =>
  match (eq_nat_dec (length lc1) (length lc1')) with
  | left _ => 
    fold_left andb (map _constEqB (cs_combine_with_measure cc lc1 lc1' Ha)) true 
  | right _ => false
  end
| (const_arr lc1, const_arr lc1') =>
  fun Ha:(cc = (const_arr lc1, const_arr lc1')) =>
  match (eq_nat_dec (length lc1) (length lc1')) with
  | left _ => 
    fold_left andb (map _constEqB (ca_combine_with_measure cc lc1 lc1' Ha)) true 
  | right _ => false
  end
| (_, _) => fun _ => false
end) (refl_equal cc).

Definition constEqB (c c':const) : bool := _constEqB (c, c').

Definition idEqB (i i':id) : bool := if i == i' then true else false.

Definition valueEqB (v v':value) : bool :=
match (v, v') with
| (value_id i, value_id i') =>idEqB i i'
| (value_const c, value_const c') => constEqB c c'
| (_, _) => false
end.

Fixpoint _list_param_EqB (lp lp':list_param) {struct lp} : bool :=
match (lp, lp') with
| ((t,v)::lp0, (t',v')::lp0') =>
  typEqB t t' && valueEqB v v' &&
  _list_param_EqB lp0 lp0'
| (_, _) => true
end.

Definition list_param_EqB (lp lp':list_param) :=
  _list_param_EqB lp lp' && beq_nat (length lp) (length lp').

Definition lEqB (i i':l) : bool := if i == i' then true else false.

Fixpoint _id_labels_EqB (idls idls':id_labels) {struct idls} : bool :=
match (idls, idls') with
| ((id,l)::idls0, (id',l')::idls0') =>
  idEqB id id' && lEqB l l' &&
  _id_labels_EqB idls0 idls0'
| (_, _) => true
end.

Definition id_labels_EqB (idls idls':id_labels) :=
  _id_labels_EqB idls idls' && beq_nat (length idls) (length idls').

Fixpoint _idxs_EqB (idxs idxs':list value) {struct idxs} : bool :=
match (idxs, idxs') with
| (idx::idxs, idx'::idxs') =>
  valueEqB idx idx' && 
  _idxs_EqB idxs idxs'
| (_, _) => true
end.

Definition idxs_EqB (idxs idxs' : list value) :=
  _idxs_EqB idxs idxs' && beq_nat (length idxs) (length idxs').

Fixpoint _cidxs_EqB (cidxs cidxs':list const) {struct cidxs} : bool :=
match (cidxs, cidxs') with
| (cidx::cidxs, cidx'::cidxs') =>
  constEqB cidx cidx' && 
  _cidxs_EqB cidxs cidxs'
| (_, _) => true
end.

Definition cidxs_EqB (cidxs cidxs' : list const) :=
  _cidxs_EqB cidxs cidxs' && beq_nat (length cidxs) (length cidxs').

Definition bopEqB (op op':bop) : bool :=
match (op, op') with
| (bop_add, bop_add) => true
| (bop_lshr, bop_lshr) => true
| (bop_and, bop_and) => true
| (bop_or, bop_or) => true
| _ => false
end.

Definition extopEqB (op op':extop) : bool :=
match (op, op') with
| (extop_z, extop_z) => true
| (extop_s, extop_s) => true
| _ => false
end.

Definition condEqB (c c':cond) : bool :=
match (c, c') with
| (cond_eq, cond_eq) => true
| (cond_ne, cond_ne) => true
| (cond_ugt, cond_ugt) => true
| (cond_uge, cond_uge) => true
| (cond_ult, cond_ult) => true
| (cond_ule, cond_ule) => true
| (cond_sgt, cond_sgt) => true
| (cond_sge, cond_sge) => true
| (cond_slt, cond_slt) => true
| (cond_sle, cond_sle) => true
| _ => false
end.

Definition castopEqB (c c':castop) : bool :=
match (c, c') with
| (castop_fptoui, castop_fptoui) => true
| (castop_fptosi, castop_fptosi) => true
| (castop_uitofp, castop_uitofp) => true
| (castop_sitofp, castop_sitofp) => true
| (castop_ptrtoint, castop_ptrtoint) => true
| (castop_inttoptr, castop_inttoptr) => true
| (castop_bitcast, castop_bitcast) => true
| _ => false
end.

Definition cmdEqB (i i':cmd) : bool :=
match (i, i') with
| (insn_bop id op sz v1 v2,
   insn_bop id' op' sz' v1' v2') =>
  idEqB id id' &&
  bopEqB op op' &&
  beq_nat sz sz' &&
  valueEqB v1 v1' &&
  valueEqB v2 v2'
| (insn_extractvalue id typ0 v0 cidxs, insn_extractvalue id' typ0' v0' cidxs') => 
  idEqB id id' &&
  typEqB typ0 typ0' &&
  valueEqB v0 v0' &&
  cidxs_EqB cidxs cidxs'  
| (insn_insertvalue id typ0 v0 typ1 v1 cidxs, 
   insn_insertvalue id' typ0' v0' typ1' v1' cidxs') =>
  idEqB id id' &&
  typEqB typ0 typ0' &&
  valueEqB v0 v0' &&
  typEqB typ1 typ1' &&
  valueEqB v1 v1' &&
  cidxs_EqB cidxs cidxs'  
| (insn_malloc id typ sz align, insn_malloc id' typ' sz' align') =>
  idEqB id id' &&
  typEqB typ typ' &&
  beq_nat sz sz' &&
  beq_nat align align' 
| (insn_free id typ v, insn_free id' typ' v') =>
  idEqB id id' &&
  typEqB typ typ' &&
  valueEqB v v'
| (insn_alloca id typ sz align, insn_alloca id' typ' sz' align') =>
  idEqB id id' &&
  typEqB typ typ' &&
  beq_nat sz sz' &&
  beq_nat align align' 
| (insn_load id typ v, insn_load id' typ' v') =>
  idEqB id id' &&
  typEqB typ typ' &&
  valueEqB v v'
| (insn_store id typ0 v0 v1, insn_store id' typ0' v0' v1') =>
  idEqB id id' &&
  typEqB typ0 typ0' &&
  valueEqB v0 v0' &&
  valueEqB v1 v1'
| (insn_gep id inbounds typ v idxs, insn_gep id' inbounds' typ' v' idxs') =>
  idEqB id id' &&
  eqb inbounds inbounds' &&
  typEqB typ typ' &&
  valueEqB v v' &&
  idxs_EqB idxs idxs'  
| (insn_ext id op t1 v1 t2,
   insn_ext id' op' t1' v1' t2') =>
  idEqB id id' &&
  extopEqB op op' &&
  typEqB t1 t1' &&
  valueEqB v1 v1' &&
  typEqB t2 t2'
| (insn_cast id op t1 v1 t2,
   insn_cast id' op' t1' v1' t2') =>
  idEqB id id' &&
  castopEqB op op' &&
  typEqB t1 t1' &&
  valueEqB v1 v1' &&
  typEqB t2 t2'
| (insn_icmp id c typ v1 v2,
   insn_icmp id' c' typ' v1' v2') =>
  idEqB id id' &&
  condEqB c c' &&
  typEqB typ typ' &&
  valueEqB v1 v1' &&
  valueEqB v2 v2'
| (insn_select id v0 typ v1 v2,
   insn_select id' v0' typ' v1' v2') =>
  idEqB id id' &&
  valueEqB v0 v0' &&
  typEqB typ typ' &&
  valueEqB v1 v1' &&
  valueEqB v2 v2'
| (insn_call id r tail typ id0 paraml,
   insn_call id' r' tail' typ' id0' paraml') =>
  idEqB id id' &&
  eqb r r' &&
  eqb tail tail' &&
  typEqB typ typ' &&
  idEqB id0 id0' &&
  list_param_EqB paraml paraml'
| (_, _) => false
end.

Definition terminatorEqB (i i':terminator) : bool :=
match (i, i') with
| (insn_return id t v, insn_return id' t' v') =>
  idEqB id id' && typEqB t t' && valueEqB v v'
| (insn_return_void id, insn_return_void id') => idEqB id id'
| (insn_br id v l1 l2, insn_br id' v' l1' l2') =>
  idEqB id id' && 
  valueEqB v v' &&
  lEqB l1 l1' && lEqB l2 l2'
| (insn_br_uncond id l, insn_br_uncond id' l') =>
  idEqB id id' && 
  lEqB l l'
(*
| (insn_invoke id typ id0 paraml l1 l2,
   insn_invoke id' typ' id0' paraml' l1' l2') =>
  idEqB id id' &&
  typEqB typ typ' &&
  idEqB id0 id0' &&
  list_param_EqB paraml paraml' &&
  beq_nat l1 l1' &&
  beq_nat l2 l2'
*)
| (insn_unreachable id, insn_unreachable id') =>
  idEqB id id'
| (_, _) => false
end.

Definition phinodeEqB (i i':phinode) : bool :=
match (i, i') with
| (insn_phi id typ idls,
   insn_phi id' typ' idls') =>
  idEqB id id' &&
  typEqB typ typ' &&
  id_labels_EqB idls idls'
end.

Definition blockEqB (b1 b2:block) : bool :=
match (eq_dec (getBlockLabel b1) (getBlockLabel b2)) with
| left _ => true
| right _ => false
end.

Fixpoint _list_arg_EqB (la la':list_arg) {struct la} : bool :=
match (la, la') with
| ((t,id)::la0, (t',id')::la0') =>
  typEqB t t' && idEqB id id' &&
  _list_arg_EqB la0 la0'
| (_, _) => true
end.

Definition list_arg_EqB (la la':list_arg) :=
  _list_arg_EqB la la' && beq_nat (length la) (length la').

Definition fheaderEqB (fh fh' : fheader) : bool :=
match (fh, fh') with
| (fheader_intro t id la, fheader_intro t' id' la') =>
  typEqB t t' && idEqB id id' && list_arg_EqB la la'
end.

Fixpoint _blocksEqB (lb lb':list_block) {struct lb} : bool :=
match (lb, lb') with
| (b::lb0, b'::lb0') =>
  blockEqB b b' &&
  _blocksEqB lb0 lb0'
| (_, _) => true
end.

Definition blocksEqB (lb lb':list_block) :=
  _blocksEqB lb lb' && beq_nat (length lb) (length lb').

Definition fdecEqB (fd fd' : fdec) : bool :=
match (fd, fd') with
| (fdec_intro fh, fdec_intro fh') => fheaderEqB fh fh'
end.

Definition fdefEqB (fd fd' : fdef) : bool :=
match (fd, fd') with
| (fdef_intro fh lb, fdef_intro fh' lb') => 
  fheaderEqB fh fh' && blocksEqB lb lb'
end.

Definition gvarEqB (gv gv' : gvar) : bool :=
match (gv, gv') with
| (gvar_intro id t v a, gvar_intro id' t' v' a') =>
  idEqB id id' && typEqB t t' && valueEqB v v' && beq_nat a a'
end.

Definition productEqB (p p' : product) : bool :=
match (p, p') with
| (product_fdec fd, product_fdec fd') => fdecEqB fd fd'  
| (product_fdef fd, product_fdef fd') => fdefEqB fd fd'
| (product_gvar gv, product_gvar gv') => gvarEqB gv gv'
| (_, _) => false
end.

Fixpoint _productsEqB (lp lp':list_product) {struct lp} : bool :=
match (lp, lp') with
| (p::lp0, p'::lp0') =>
  productEqB p p' &&
  _productsEqB lp0 lp0'
| (_, _) => true
end.

Definition productsEqB (lp lp':list_product) :=
  _productsEqB lp lp' && beq_nat (length lp) (length lp').

Fixpoint layoutEqB (o o' : layout) : bool :=
match (o, o') with
| (layout_be, layout_be) => true
| (layout_le, layout_le) => true
| (layout_ptr sz align0 align1, layout_ptr sz' align0' align1') =>
  beq_nat sz sz' && beq_nat align0 align0' && beq_nat align1 align1'
| (layout_int sz align0 align1, layout_int sz' align0' align1') =>
  beq_nat sz sz' && beq_nat align0 align0' && beq_nat align1 align1'
| (layout_aggr sz align0 align1, layout_aggr sz' align0' align1') =>
  beq_nat sz sz' && beq_nat align0 align0' && beq_nat align1 align1'
| (layout_stack sz align0 align1, layout_stack sz' align0' align1') =>
  beq_nat sz sz' && beq_nat align0 align0' && beq_nat align1 align1'
| (_, _) => false
end.

Fixpoint _layoutsEqB (lo lo':list_layout) {struct lo} : bool :=
match (lo, lo') with
| (o::lo0, o'::lo0') =>
  layoutEqB o o' &&
  _layoutsEqB lo0 lo0'
| (_, _) => true
end.

Definition layoutsEqB (lo lo':list_layout) :=
  _layoutsEqB lo lo' && beq_nat (length lo) (length lo').

Definition moduleEqB (m m':module) := 
  let (os, ps) := m in 
  let (os', ps') := m' in 
  productsEqB ps ps' &&
  layoutsEqB os os'.

Fixpoint _modulesEqB (lm lm':list_module) {struct lm} : bool :=
match (lm, lm') with
| (m::lm0, m'::lm0') =>
  moduleEqB m m' &&
  _modulesEqB lm0 lm0'
| (_, _) => true
end.

Definition modulesEqB (lm lm':list_module) :=
  _modulesEqB lm lm' && beq_nat (length lm) (length lm').

Definition systemEqB (s s':system) := modulesEqB s s'.

(**********************************)
(* Inclusion. *)

Fixpoint InCmdsB (i:cmd) (li:list_cmd) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => cmdEqB i i' || InCmdsB i li'
end.

Fixpoint InPhiNodesB (i:phinode) (li:list_phinode) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => phinodeEqB i i' || InPhiNodesB i li'
end.

Definition cmdInBlockB (i:cmd) (b:block) : bool :=
match b with
| block_intro l _ cmds _ => InCmdsB i cmds
end.

Definition phinodeInBlockB (i:phinode) (b:block) : bool :=
match b with
| block_intro l ps _ _ => InPhiNodesB i ps
end.

Definition terminatorInBlockB (i:terminator) (b:block) : bool :=
match b with
| block_intro l _ _ t => terminatorEqB i t
end.

Fixpoint InArgsB (a:arg) (la:list_arg) {struct la} : bool :=
match la with
| nil => false
| a' :: la' => 
  match (a, a') with
  | ((t, id), (t', id')) => typEqB t t' && idEqB id id'
  end ||
  InArgsB a la'
end.

Definition argInFheaderB (a:arg) (fh:fheader) : bool :=
match fh with
| (fheader_intro t id la) => InArgsB a la
end.

Definition argInFdecB (a:arg) (fd:fdec) : bool :=
match fd with
| (fdec_intro fh) => argInFheaderB a fh
end.

Definition argInFdefB (a:arg) (fd:fdef) : bool :=
match fd with
| (fdef_intro fh lb) => argInFheaderB a fh
end.

Fixpoint InBlocksB (b:block) (lb:list_block) {struct lb} : bool :=
match lb with
| nil => false
| b' :: lb' => blockEqB b b' || InBlocksB b lb'
end.

Definition blockInFdefB (b:block) (fd:fdef) : bool :=
match fd with
| (fdef_intro fh lb) => InBlocksB b lb
end.

Fixpoint InProductsB (p:product) (lp:list_product) {struct lp} : bool :=
match lp with
| nil => false
| p' :: lp' => productEqB p p' || InProductsB p lp'
end.

Definition productInModuleB (p:product) (m:module) : bool :=
let (os, ps) := m in
InProductsB p ps.

Fixpoint InModulesB (m:module) (lm:list_module) {struct lm} : bool :=
match lm with
| nil => false
| m' :: lm' => moduleEqB m m' || InModulesB m lm'
end.

Definition moduleInSystemB (m:module) (s:system) : bool :=
InModulesB m s.

Definition productInSystemModuleB (p:product) (s:system) (mi:module_info) : bool :=
match mi with
| (m, (ui, ub)) =>
  moduleInSystemB m s && productInModuleB p m
end.

Definition blockInSystemModuleFdefB (b:block) (s:system) (mi:module_info) (fi:fdef_info) : bool :=
match fi with
| (fd, dt) =>
  blockInFdefB b fd && productInSystemModuleB (product_fdef fd) s mi
end.

Definition cmdInSystemModuleFdefBlockB 
  (i:cmd) (s:system) (mi:module_info) (fi:fdef_info) (b:block) : bool :=
cmdInBlockB i b && blockInSystemModuleFdefB b s mi fi.

Definition phinodeInSystemModuleFdefBlockB 
  (i:phinode) (s:system) (mi:module_info) (fi:fdef_info) (b:block) : bool :=
phinodeInBlockB i b && blockInSystemModuleFdefB b s mi fi.

Definition terminatorInSystemModuleFdefBlockB 
  (i:terminator) (s:system) (mi:module_info) (fi:fdef_info) (b:block) : bool :=
terminatorInBlockB i b && blockInSystemModuleFdefB b s mi fi.

Definition insnInSystemModuleFdefBlockB 
  (i:insn) (s:system) (mi:module_info) (fi:fdef_info) (b:block) : bool :=
match i with
| insn_phinode p => phinodeInSystemModuleFdefBlockB p s mi fi b
| insn_cmd c => cmdInSystemModuleFdefBlockB c s mi fi b
| insn_terminator t => terminatorInSystemModuleFdefBlockB t s mi fi b
end.

(**********************************)
(* parent *)

(* matching (cmdInBlockB i b) in getParentOfCmdFromBlocksC directly makes
   the compilation very slow, so we define this dec lemma first... *)
Lemma cmdInBlockB_dec : forall i b,
  {cmdInBlockB i b = true} + {cmdInBlockB i b = false}.
Proof.
  intros i0 b. destruct (cmdInBlockB i0 b); auto.
Qed.

Lemma phinodeInBlockB_dec : forall i b,
  {phinodeInBlockB i b = true} + {phinodeInBlockB i b = false}.
Proof.
  intros i0 b. destruct (phinodeInBlockB i0 b); auto.
Qed.

Lemma terminatorInBlockB_dec : forall i b,
  {terminatorInBlockB i b = true} + {terminatorInBlockB i b = false}.
Proof.
  intros i0 b. destruct (terminatorInBlockB i0 b); auto.
Qed.

Fixpoint getParentOfCmdFromBlocks (i:cmd) (lb:list_block) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  match (cmdInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfCmdFromBlocks i lb'
  end
end.

Definition getParentOfCmdFromFdef (i:cmd) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfCmdFromBlocks i lb
end.

Definition getParentOfCmdFromProduct (i:cmd) (p:product) : option block :=
match p with
| (product_fdef fd) => getParentOfCmdFromFdef i fd
| _ => None
end.

Fixpoint getParentOfCmdFromProducts (i:cmd) (lp:list_product) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfCmdFromProduct i p) with
  | Some b => Some b
  | None => getParentOfCmdFromProducts i lp'
  end
end.

Definition getParentOfCmdFromModule (i:cmd) (m:module) : option block := 
  let (os, ps) := m in
  getParentOfCmdFromProducts i ps.

Fixpoint getParentOfCmdFromModules (i:cmd) (lm:list_module) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfCmdFromModule i m) with
  | Some b => Some b
  | None => getParentOfCmdFromModules i lm'
  end
end.

Definition getParentOfCmdFromSystem (i:cmd) (s:system) : option block := 
  getParentOfCmdFromModules i s.

Definition cmdHasParent (i:cmd) (s:system) : bool :=
match (getParentOfCmdFromSystem i s) with
| Some _ => true
| None => false
end.

Fixpoint getParentOfPhiNodeFromBlocks (i:phinode) (lb:list_block) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  match (phinodeInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfPhiNodeFromBlocks i lb'
  end
end.

Definition getParentOfPhiNodeFromFdef (i:phinode) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfPhiNodeFromBlocks i lb
end.

Definition getParentOfPhiNodeFromProduct (i:phinode) (p:product) : option block :=
match p with
| (product_fdef fd) => getParentOfPhiNodeFromFdef i fd
| _ => None
end.

Fixpoint getParentOfPhiNodeFromProducts (i:phinode) (lp:list_product) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfPhiNodeFromProduct i p) with
  | Some b => Some b
  | None => getParentOfPhiNodeFromProducts i lp'
  end
end.

Definition getParentOfPhiNodeFromModule (i:phinode) (m:module) : option block := 
  let (os, ps) := m in
  getParentOfPhiNodeFromProducts i ps.

Fixpoint getParentOfPhiNodeFromModules (i:phinode) (lm:list_module) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfPhiNodeFromModule i m) with
  | Some b => Some b
  | None => getParentOfPhiNodeFromModules i lm'
  end
end.

Definition getParentOfPhiNodeFromSystem (i:phinode) (s:system) : option block := 
  getParentOfPhiNodeFromModules i s.

Definition phinodeHasParent (i:phinode) (s:system) : bool :=
match (getParentOfPhiNodeFromSystem i s) with
| Some _ => true
| None => false
end.

Fixpoint getParentOfTerminatorFromBlocks (i:terminator) (lb:list_block) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  match (terminatorInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfTerminatorFromBlocks i lb'
  end
end.

Definition getParentOfTerminatorFromFdef (i:terminator) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfTerminatorFromBlocks i lb
end.

Definition getParentOfTerminatorFromProduct (i:terminator) (p:product) : option block :=
match p with
| (product_fdef fd) => getParentOfTerminatorFromFdef i fd
| _ => None
end.

Fixpoint getParentOfTerminatorFromProducts (i:terminator) (lp:list_product) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfTerminatorFromProduct i p) with
  | Some b => Some b
  | None => getParentOfTerminatorFromProducts i lp'
  end
end.

Definition getParentOfTerminatorFromModule (i:terminator) (m:module) : option block := 
  let (os, ps) := m in
  getParentOfTerminatorFromProducts i ps.

Fixpoint getParentOfTerminatorFromModules (i:terminator) (lm:list_module) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfTerminatorFromModule i m) with
  | Some b => Some b
  | None => getParentOfTerminatorFromModules i lm'
  end
end.

Definition getParentOfTerminatorFromSystem (i:terminator) (s:system) : option block := 
  getParentOfTerminatorFromModules i s.

Definition terminatoreHasParent (i:terminator) (s:system) : bool :=
match (getParentOfTerminatorFromSystem i s) with
| Some _ => true
| None => false
end.

Lemma productInModuleB_dec : forall b m,
  {productInModuleB b m = true} + {productInModuleB b m = false}.
Proof.
  intros b m. destruct (productInModuleB b m); auto.
Qed.

Fixpoint getParentOfFdefFromModules (fd:fdef) (lm:list_module) {struct lm} : option module :=
match lm with
| nil => None
| m::lm' => 
  match (productInModuleB_dec (product_fdef fd) m) with
  | left _ => Some m
  | right _ => getParentOfFdefFromModules fd lm'
  end
end.

Definition getParentOfFdefFromSystem (fd:fdef) (s:system) : option module := 
  getParentOfFdefFromModules fd s.

Notation "t =t= t' " := (typEqB t t') (at level 50).
Notation "n =n= n'" := (beq_nat n n') (at level 50).
Notation "b =b= b'" := (blockEqB b b') (at level 50).
Notation "i =cmd= i'" := (cmdEqB i i') (at level 50).
Notation "i =phi= i'" := (phinodeEqB i i') (at level 50).
Notation "i =tmn= i'" := (terminatorEqB i i') (at level 50).

(**********************************)
(* Check to make sure that if there is more than one entry for a
   particular basic block in this PHI node, that the incoming values 
   are all identical. *)
Fixpoint lookupIdsViaLabelFromIdls (idls:list (id*l)) (l0:l) : list id :=
match idls with
| nil => nil
| (id1,l1)::idls' =>
  if (eq_dec l0 l1) 
  then set_add eq_dec id1 (lookupIdsViaLabelFromIdls idls' l0)
  else (lookupIdsViaLabelFromIdls idls' l0)
end.

Fixpoint _checkIdenticalIncomingValues (idls idls0:list (id*l)) : Prop :=
match idls with
| nil => True
| (id, l)::idls' => 
  (length (lookupIdsViaLabelFromIdls idls0 l) <= 1) /\
  (_checkIdenticalIncomingValues idls' idls0)
end.

Definition checkIdenticalIncomingValues (PN:phinode) : Prop :=
match PN with
| insn_phi _ _ idls => _checkIdenticalIncomingValues idls idls
end.

(**********************************)
(* Instruction Signature *)

Module Type SigValue.

 Parameter getNumOperands : insn -> nat.

End SigValue.

Module Type SigUser. 
 Include Type SigValue.

End SigUser.

Module Type SigConstant.
 Include Type SigValue.

 Parameter getTyp : const -> typ.

End SigConstant.

Module Type SigGlobalValue.
 Include Type SigConstant.

End SigGlobalValue.

Module Type SigFunction.
 Include Type SigGlobalValue.

 Parameter getDefReturnType : fdef -> typ.
 Parameter getDefFunctionType : fdef -> typ.
 Parameter def_arg_size : fdef -> nat.
 
 Parameter getDecReturnType : fdec -> typ.
 Parameter getDecFunctionType : fdec -> typ.
 Parameter dec_arg_size : fdec -> nat.

End SigFunction.

Module Type SigInstruction.
 Include Type SigUser.

(* Parameter isInvokeInst : insn -> bool. *)
 Parameter isCallInst : cmd -> bool.

End SigInstruction.

Module Type SigReturnInst.
 Include Type SigInstruction.

 Parameter hasReturnType : terminator -> bool.
 Parameter getReturnType : terminator -> option typ.

End SigReturnInst.

Module Type SigCallSite.
 Parameter getCalledFunction : cmd -> system -> option fdef.
 Parameter getFdefTyp : fdef -> typ.
 Parameter arg_size : fdef -> nat.
 Parameter getArgument : fdef -> nat -> option arg.
 Parameter getArgumentType : fdef -> nat -> option typ.

End SigCallSite.

Module Type SigCallInst.
 Include Type SigInstruction.

End SigCallInst.

(*
Module Type SigInvokeInst.
 Include Type SigInstruction.

 Parameter getNormalDest : system -> insn -> option block.

End SigInvokeInst.
*)

Module Type SigBinaryOperator.
 Include Type SigInstruction.

 Parameter getFirstOperandType : system -> cmd -> option typ.
 Parameter getSecondOperandType : system -> cmd -> option typ.
 Parameter getResultType : cmd -> option typ.

End SigBinaryOperator.

Module Type SigPHINode.
 Include Type SigInstruction.

 Parameter getNumIncomingValues : phinode -> nat.
 Parameter getIncomingValueType : system  -> phinode -> i -> option typ.
End SigPHINode.

(* Type Signature *)

Module Type SigType.
 Parameter isIntOrIntVector : typ -> bool.
 Parameter isInteger : typ -> bool.
 Parameter isSized : typ -> bool.
 Parameter getPrimitiveSizeInBits : typ -> nat.
End SigType.

Module Type SigDerivedType.
 Include Type SigType.
End SigDerivedType.

Module Type SigFunctionType.
 Include Type SigDerivedType.

 Parameter getNumParams : typ -> option nat.
 Parameter isVarArg : typ -> bool.
 Parameter getParamType : typ -> nat -> option typ.
End SigFunctionType.

Module Type SigCompositeType.
 Include Type SigDerivedType.
End SigCompositeType.

Module Type SigSequentialType.
 Include Type SigCompositeType.

 Parameter hasElementType : typ -> bool.
 Parameter getElementType : typ -> option typ.

End SigSequentialType.

Module Type SigArrayType.
 Include Type SigSequentialType.

 Parameter getNumElements : typ -> nat.

End SigArrayType.

(* Instruction Instantiation *)

Module Value <: SigValue.

 Definition getNumOperands (i:insn) : nat := 
   length (getInsnOperands i).  

End Value.

Module User <: SigUser. Include Value.

End User.

Module Constant <: SigConstant.
 Include Value.

 Fixpoint getTyp (c:const) : typ :=
 match c with
 | const_int sz _ => typ_int sz
 | const_undef t => t
 | const_null t => typ_pointer t
 | const_arr lc => 
   match lc with
   | nil => typ_array 0 (typ_int 0)
   | c'::lc' => typ_array (length lc) (getTyp c')
   end
 | const_struct lc => typ_struct (map getTyp lc)
 end.

End Constant.

Module GlobalValue <: SigGlobalValue.
 Include Constant.

End GlobalValue.

Module Function <: SigFunction.
 Include GlobalValue.

 Definition getDefReturnType (fd:fdef) : typ :=
 match fd with
 | fdef_intro (fheader_intro t _ _) _ => t
 end.

 Definition getDefFunctionType (fd:fdef) : typ := getFdefTyp fd.

 Definition def_arg_size (fd:fdef) : nat :=
 match fd with
 | (fdef_intro (fheader_intro _ _ la) _) => length la
 end.

 Definition getDecReturnType (fd:fdec) : typ :=
 match fd with
 | fdec_intro (fheader_intro t _ _) => t
 end.

 Definition getDecFunctionType (fd:fdec) : typ := getFdecTyp fd.

 Definition dec_arg_size (fd:fdec) : nat :=
 match fd with
 | (fdec_intro (fheader_intro _ _ la)) => length la
 end.

End Function.

Module Instruction <: SigInstruction.
 Include User.

(* Definition isInvokeInst (i:insn) : bool := isInvokeInsnB i. *)
 Definition isCallInst (i:cmd) : bool := _isCallInsnB i.

End Instruction.

Module ReturnInst <: SigReturnInst.
 Include Instruction.

 Definition hasReturnType (i:terminator) : bool :=
 match i with
 | insn_return _ t v => true
 | _ => false
 end.

 Definition getReturnType (i:terminator) : option typ :=
 match i with
 | insn_return _ t v => Some t
 | _ => None
 end.

End ReturnInst.

Module CallSite <: SigCallSite.

 Definition getCalledFunction (i:cmd) (s:system) : option fdef :=
 match i with 
 (* | insn_invoke _ _ fid _ _ _ => lookupFdefViaIDFromSystemC s fid *)
 | insn_call _ _ _ _ fid _ => lookupFdefViaIDFromSystem s fid
 | _ => None
 end.

 Definition getFdefTyp (fd:fdef) : typ := getFdefTyp fd.

 Definition arg_size (fd:fdef) : nat :=
 match fd with
 | (fdef_intro (fheader_intro _ _ la) _) => length la
 end.

 Definition getArgument (fd:fdef) (i:nat) : option arg :=
 match fd with
 | (fdef_intro (fheader_intro _ _ la) _) => 
    match (nth_error la i) with
    | Some a => Some a
    | None => None
    end
 end. 

 Definition getArgumentType (fd:fdef) (i:nat) : option typ :=
 match (getArgument fd i) with
 | Some (t, _) => Some t
 | None => None
 end.

End CallSite.

Module CallInst <: SigCallInst.
 Include Instruction.

End CallInst.

(*
Module InvokeInst <: SigInvokeInst.
 Include Instruction.

 Definition getNormalDest (s:system) (i:insn) : option block :=
 match (getNormalDestFromInvokeInsnC i) with
 | None => None
 | Some l => lookupBlockViaLabelFromSystem s l
 end.

End InvokeInst.
*)

Module BinaryOperator <: SigBinaryOperator.
 Include Instruction.

 Definition getFirstOperandType (s:system) (i:cmd) : option typ := 
 match i with
 | insn_bop _ _ _ v1 _ => 
   match v1 with
   | value_id id1 => lookupTypViaIDFromSystem s id1
   | value_const c => Some (Constant.getTyp c)
   end
 | _ => None
 end.

 Definition getSecondOperandType (s:system) (i:cmd) : option typ := 
 match i with
 | insn_bop _ _ _ _ v2 => 
   match v2 with
   | value_id id2 => lookupTypViaIDFromSystem s id2
   | value_const c => Some (Constant.getTyp c)
   end
 | _ => None
 end.

 Definition getResultType (i:cmd) : option typ := getCmdTyp i.

End BinaryOperator.

Module PHINode <: SigPHINode.
 Include Instruction.

 Definition getNumIncomingValues (i:phinode) : nat :=
 match i with
 | (insn_phi _ _ ln) => (length ln)
 end.

 Definition getIncomingValueType (s:system) (i:phinode) (n:nat) : option typ :=
 match i with
 | (insn_phi _ _ ln) => 
    match (nth_error ln n) with
    | Some (id, _) => lookupTypViaIDFromSystem s id
    | None => None
    end
 end.

End PHINode.

(* Type Instantiation *)

Module Typ <: SigType.
 Definition isIntOrIntVector (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | _ => false
 end.

 Definition isInteger (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | _ => false
 end.

 (* isSizedDerivedType - Derived types like structures and arrays are sized
    iff all of the members of the type are sized as well.  Since asking for
    their size is relatively uncommon, move this operation out of line. 

    isSized - Return true if it makes sense to take the size of this type.  To
    get the actual size for a particular target, it is reasonable to use the
    TargetData subsystem to do this. *)
 Fixpoint isSized (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | typ_array _ t' => isSized t'
 | typ_struct lt => fold_left andb (map isSized lt) true 
 | _ => false
 end.

  Definition getPrimitiveSizeInBits (t:typ) : nat :=
  match t with
  | typ_int sz => sz
  | _ => 0
  end.

End Typ.

Module DerivedType <: SigDerivedType.
 Include Typ.
End DerivedType.

Module FunctionType <: SigFunctionType.
 Include DerivedType.

 Definition getNumParams (t:typ) : option nat :=
 match t with
 | (typ_function _ lt) => Some (length lt)
 | _ => None
 end.

 Definition isVarArg (t:typ) : bool := false.

 Definition getParamType (t:typ) (i:nat) : option typ :=
 match t with
 | (typ_function _ lt) => 
    match (nth_error lt i) with
    | Some t => Some t
    | None => None
    end
 | _ => None
 end.

End FunctionType.

Module CompositeType <: SigCompositeType.
 Include DerivedType.
End CompositeType.

Module SequentialType <: SigSequentialType.
 Include CompositeType.

 Definition hasElementType (t:typ) : bool :=
 match t with
 | typ_array _ t' => true
 | _ => false
 end.

 Definition getElementType (t:typ) : option typ :=
 match t with
 | typ_array _ t' => Some t'
 | _ => None
 end.

End SequentialType.

Module ArrayType <: SigArrayType.
 Include SequentialType.

 Definition getNumElements (t:typ) : nat :=
 match t with
 | typ_array N _ => N
 | _ => 0
 end.

End ArrayType.

(**********************************)
(* reflect *)

Require Import Decidable.

Section Decidable.

Lemma dec_blockDominates : forall (d:dt) (b1 b2: block),
  decidable (blockDominates d b1 b2).
Proof.
  intros d b1 b2.
  unfold decidable. unfold blockDominates.
  destruct b1 as [l1 insns1].
  destruct b2 as [l2 insns2].
  remember (lset_mem l2 (d l1)) as c.
  destruct c; auto.
Qed.

End Decidable.

Coercion is_true (b:bool) := b = true.

Inductive reflect (P:Prop) : bool -> Set :=
| ReflectT : P -> reflect P true
| ReflectF : ~P -> reflect P false
.

Section Reflect.

Lemma reflect_blockDominates : forall d b1 b2,
  reflect (blockDominates d b1 b2) (blockDominatesB d b1 b2).
Proof.
  intros d b1 b2.
  unfold blockDominates. unfold blockDominatesB.
  destruct b1 as [l1 insns1].
  destruct b2 as [l2 insns2].
  remember (lset_mem l2 (d l1)) as c.
  destruct c; auto.
    apply ReflectT; auto.
    apply ReflectF; auto.
Qed.

Require Import monad.

Definition ifP d b1 b2 (X:Type) (t f : monad X) :=
match (reflect_blockDominates d b1 b2) with
| ReflectT _ => t
| ReflectF _ => f
end.

End Reflect.

(*ENDCOPY*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./ott" "-I" "./monads") ***
*** End: ***
 *)


