
Require Import ssa_def.

(*BEGINCOPY*)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Recdef.

Section LabelSet.

  Definition lempty_set := empty_set l.
  Definition lset_add (l1:l) (ls2:ls) := set_add eq_nat_dec l1 ls2.
  Definition lset_union (ls1 ls2:ls) := set_union eq_nat_dec ls1 ls2.
  Definition lset_inter (ls1 ls2:ls) := set_inter eq_nat_dec ls1 ls2.
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
  Definition lset_mem (l0:l) (ls0:ls) := set_mem eq_nat_dec l0 ls0.

End LabelSet.

Section SSA.

  Definition l2block := l -> option block.

  Definition mergel2block (lb1:l2block) (lb2:l2block) : l2block :=
  fun l0 =>
  match (lb1 l0, lb2 l0) with
  | (Some b1, _) => Some b1
  | (_, Some b2) => Some b2
  | (_, _) => None 
  end.

  Definition genLabel2Block_block (b:block) (f:fdef) (m:module) : l2block :=
  match b with
  | block_intro l _ => fun l' => 
    match lt_eq_lt_dec l' l with 
    | inleft (right _) => Some b
    | _ => None
    end 
  end.  

  Fixpoint genLabel2Block_blocks (bs:list_block) (f:fdef) (m:module) : l2block :=
  match bs with 
  | nil => fun _ => None
  | b::bs' => mergel2block (genLabel2Block_blocks bs' f m) (genLabel2Block_block b f m)
  end.

  Definition genLabel2Block_fdef (f:fdef) (m:module) : l2block := 
  match f with
  | fdef_intro fheader blocks => genLabel2Block_blocks blocks f m 
  end.

  Fixpoint genLabel2Block_product (p:product) (m: module) : l2block :=
  match p with 
  (*  | product_global_var g => fun _ => None *)
  | product_function_def f => (genLabel2Block_fdef f m)
  | product_function_dec f => fun _ => None 
  (*  | product_namedtype nt => fun _ => None *)
  end.

  Fixpoint genLabel2Block_products (ps:list_product) (m:module) : l2block :=
  match ps with
  | nil => fun _ => None
  | p::ps' => mergel2block (genLabel2Block_products ps' m) (genLabel2Block_product p m)
  end.

  Definition genLabel2Block (m: module) : l2block :=
  genLabel2Block_products m m.

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

End SSA.

Section UseDef.

  Definition mergeInsnUseDef (udi1:usedef_insn) (udi2:usedef_insn) : usedef_insn :=
  fun i => (udi1 i) ++ (udi2 i).

  Definition mergeBlockUseDef (udb1:usedef_block) (udb2:usedef_block) : usedef_block :=
  fun b => (udb1 b) ++ (udb2 b).

  Infix "+++" := mergeInsnUseDef (right associativity, at level 60).
  Infix "++++" := mergeBlockUseDef (right associativity, at level 60).

  Definition getInsnID (i:insn) : option id :=
  match i with
  | insn_return t v => None
  | insn_return_void  => None
  | insn_br t v l1 l2 => None
  | insn_br_uncond l => None
  (* | insn_switch t v l _ => None *)
  | insn_invoke id typ id0 paraml l1 l2 => Some id
  | insn_call id typ id0 paraml => Some id
  | insn_unreachable => None
  | insn_add id typ v1 v2 => Some id
  (* | insn_fadd id typ v1 v2 => Some id *)
  (* | insn_udiv id typ v1 v2 => Some id *)
  (* | insn_fdiv id typ v1 v2 => Some id *)
  (* | insn_or id typ v1 v2 => Some id *)
  (* | insn_and id typ v1 v2 =>Some id *)
  (* | insn_extractelement id typ0 id0 c1 => Some id *)
  (* | insn_insertelement id typ0 id0 typ1 v1 c2 => Some id *)
  (* | insn_extractvalue id typs id0 c1 => Some id *)
  (* | insn_insertvalue id typs id0 typ1 v1 c2 => Some id *)
  (* | insn_alloca id typ N => None *)
  (* | insn_load id typ1 id1 => Some id *)
  (* | insn_store typ1 v1 typ2 id2 => None *)
  (* | insn_trunc id typ1 v1 typ2 => Some id *)
  (* | insn_fptrunc id typ1 v1 typ2 =>Some id *)
  (* | insn_fptoui id typ1 v1 typ2 => Some id *)
  (* | insn_fptosi id typ1 v1 typ2 =>Some id *)
  (* | insn_uitofp id typ1 v1 typ2 =>Some id *)
  (* | insn_sitofp id typ1 v1 typ2 =>Some id *)
  (* | insn_ptrtoint id typ1 v1 typ2 => Some id *)
  (* | insn_inttoptr id typ1 v1 typ2 => Some id *)
  (* | insn_bitcast id typ1 v1 typ2 => Some id *)
  (* | insn_icmp id cond typ v1 v2 => Some id *)
  (* | insn_fcmp id cond typ v1 v2 => Some id *)
  | insn_phi id typ idls => None
  end.
 
  Definition getValueID (v:value) : option id :=
  match v with
  | value_id id => Some id
  | value_constant _ => None
  end.

  (* generate insn use-def *)

  Definition genInsnUseDef_value (v:value) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  fun i' => 
  match (getInsnID i', getValueID v) with
  | (Some id', Some id) => 
    match lt_eq_lt_dec id' id with 
    | inleft (right _) => i::nil
    | _ => nil
    end 
  |( _, _) => nil
  end.     

  Definition genInsnUseDef_id (id0:id) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  fun i' => 
  match (getInsnID i') with
  | Some id' => 
    match lt_eq_lt_dec id' id0 with 
    | inleft (right _) => i::nil
    | _ => nil
    end 
  | _ => nil
  end.     

  Fixpoint genInsnUseDef_params (ps:list_param) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match ps with
  | nil => fun _ => nil
  | (_, v)::ps' => (genInsnUseDef_value v i b f m)+++(genInsnUseDef_params ps' i b f m)
  end.

  Definition genInsnUseDef_insn (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match i with
  | insn_return t v => genInsnUseDef_value v i b f m
  | insn_return_void  => fun _ => nil 
  | insn_br t v l1 l2 => genInsnUseDef_value v i b f m        
  | insn_br_uncond l => fun _ => nil
  (* | insn_switch t v l _ => genInsnUseDef_value v i b f m *)
  | insn_invoke id typ id0 paraml l1 l2 => (genInsnUseDef_id id0 i b f m)+++(genInsnUseDef_params paraml i b f m)
  | insn_call id typ id0 paraml => fun _ => nil
  | insn_unreachable => fun _ => nil
  | insn_add id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)
  (* | insn_fadd id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 	 *)
  (* | insn_udiv id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_fdiv id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_or id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_and id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_extractelement id typ0 value0 c1 =>  *)
  (*   (genInsnUseDef_value value0 i b f m) *)
  (* | insn_insertelement id typ0 value0 typ1 v1 c2 =>  *)
  (*   (genInsnUseDef_value value0 i b f m)+++(genInsnUseDef_value v1 i b f m) *)
  (* | insn_extractvalue id typ0 value0 c1 =>  *)
  (*   (genInsnUseDef_value value0 i b f m) *)
  (* | insn_insertvalue id typs value0 typ1 v1 c2 =>  *)
  (*   (genInsnUseDef_value value0 i b f m)+++(genInsnUseDef_value v1 i b f m) *)
  (* | insn_alloca id typ N => fun _ => nil *)
  (* | insn_load id typ1 v1 => genInsnUseDef_value v1 i b f m *)
  (* | insn_store typ1 v1 typ2 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)	  *)
  (* | insn_trunc id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_fptrunc id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_fptoui id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_fptosi id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_uitofp id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_sitofp id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_ptrtoint id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_inttoptr id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_bitcast id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_icmp id cond typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_fcmp id cond typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  | insn_phi id typ idls => fun _ => nil
  end.
 
  Fixpoint genInsnUseDef_insns (is:list_insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genInsnUseDef_insn i b f m)+++(genInsnUseDef_insns is' b f m)
  end.  

  Definition genInsnUseDef_block (b:block) (f:fdef) (m:module) : usedef_insn :=
  match b with
  | block_intro l is => genInsnUseDef_insns is b f m
  end.  

  Fixpoint genInsnUseDef_blocks (bs:list_block) (f:fdef) (m:module) : usedef_insn :=
  match bs with 
  | nil => fun _ => nil
  | b::bs' => (genInsnUseDef_blocks bs' f m)+++(genInsnUseDef_block b f m)
  end.

  Definition genInsnUseDef_fdef (f:fdef) (m:module) : usedef_insn := 
  match f with
  | fdef_intro fheader blocks => genInsnUseDef_blocks blocks f m 
  end.

  Fixpoint genInsnUseDef_product (p:product) (m: module) : usedef_insn :=
  match p with 
  (* | product_global_var g => fun _ => nil *)
  | product_function_def f => (genInsnUseDef_fdef f m)
  | product_function_dec f => fun _ => nil
  (* | product_namedtype nt => fun _ => nil *)
  end.

  Fixpoint genInsnUseDef_products (ps:list_product) (m:module) : usedef_insn :=
  match ps with
  | nil => fun _ => nil
  | p::ps' => (genInsnUseDef_products ps' m) +++ (genInsnUseDef_product p m) 
  end.

  Definition genInsnUseDef (m: module) : usedef_insn :=
  genInsnUseDef_products m m.

  Definition getInsnUseDef (udi:usedef_insn) (i:insn) : list_insn :=
  udi i. 

  (* generate block use-def *)

  Definition getBlockLabel (b:block) : l :=
  match b with
  | block_intro l b => l
  end.

  Definition genBlockUseDef_label (l0:l) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  fun b' => 
  match lt_eq_lt_dec (getBlockLabel b') l0 with 
  | inleft (right _) => b::nil
  | _ => nil
  end.

  Fixpoint genBlockUseDef_switch_cases (cs:list (const * l)) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match cs with
  | nil => fun _ => nil
  | (_, l0)::cs' => (genBlockUseDef_label l0 i b f m)++++(genBlockUseDef_switch_cases cs' i b f m)
  end.

  Fixpoint genBlockUseDef_phi_cases (ps:list (id * l)) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match ps with
  | nil => fun _ => nil
  | (_, l0)::ps' => (genBlockUseDef_label l0 i b f m)++++(genBlockUseDef_phi_cases ps' i b f m)
  end.

  Definition genBlockUseDef_insn (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match i with
  | insn_return t v => fun _ => nil
  | insn_return_void  => fun _ => nil 
  | insn_br t v l1 l2 => genBlockUseDef_label l1 i b f m ++++ genBlockUseDef_label l2 i b f m       
  | insn_br_uncond l => genBlockUseDef_label l i b f m
  (* | insn_switch t v l ls => genBlockUseDef_label l i b f m ++++ genBlockUseDef_switch_cases ls i b f m *)
  | insn_invoke id typ id0 paraml l1 l2 => (genBlockUseDef_label l1 i b f m)++++(genBlockUseDef_label l2 i b f m)
  | insn_call id typ id0 paraml => fun _ => nil
  | insn_unreachable => fun _ => nil 
  | insn_add id typ v1 v2 => fun _ => nil 
  (* | insn_fadd id typ v1 v2 => fun _ => nil *)
  (* | insn_udiv id typ v1 v2 => fun _ => nil *)
  (* | insn_fdiv id typ v1 v2 => fun _ => nil *)
  (* | insn_or id typ v1 v2 => fun _ => nil *)
  (* | insn_and id typ v1 v2 => fun _ => nil *)
  (* | insn_extractelement id typ0 v0 c1 => fun _ => nil *)
  (* | insn_insertelement id typ0 v0 typ1 v1 c2 => fun _ => nil *)
  (* | insn_extractvalue id typ0 v0 c1 => fun _ => nil *)
  (* | insn_insertvalue id typ0 v0 typ1 v1 c2 => fun _ => nil *)
  (* | insn_alloca id typ N => fun _ => nil *)
  (* | insn_load id typ1 v1 => fun _ => nil *)
  (* | insn_store typ1 v1 typ2 v2 => fun _ => nil *)
  (* | insn_trunc id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_fptrunc id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_fptoui id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_fptosi id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_uitofp id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_sitofp id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_ptrtoint id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_inttoptr id typ1 v1 typ2 =>fun _ => nil *)
  (* | insn_bitcast id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_icmp id cond typ v1 v2 => fun _ => nil *)
  (* | insn_fcmp id cond typ v1 v2 => fun _ => nil *)
  | insn_phi id typ idls => genBlockUseDef_phi_cases idls i b f m
  end.
 
  Fixpoint genBlockUseDef_insns (is:list_insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genBlockUseDef_insn i b f m)++++(genBlockUseDef_insns is' b f m)
  end.  

  Definition genBlockUseDef_block (b:block) (f:fdef) (m:module) : usedef_block :=
  match b with
  | block_intro l is => genBlockUseDef_insns is b f m
  end.  

  Fixpoint genBlockUseDef_blocks (bs:list_block) (f:fdef) (m:module) : usedef_block :=
  match bs with 
  | nil => fun _ => nil
  | b::bs' => (genBlockUseDef_blocks bs' f m)++++(genBlockUseDef_block b f m)
  end.

  Definition genBlockUseDef_fdef (f:fdef) (m:module) : usedef_block := 
  match f with
  | fdef_intro fheader blocks => genBlockUseDef_blocks blocks f m 
  end.

  Fixpoint genBlockUseDef_product (p:product) (m: module) : usedef_block :=
  match p with 
  (* | product_global_var g => fun _ => nil *)
  | product_function_def f => (genBlockUseDef_fdef f m)
  | product_function_dec f => fun _ => nil
  (* | product_namedtype nt => fun _ => nil *)
  end.

  Fixpoint genBlockUseDef_products (ps:list_product) (m:module) : usedef_block :=
  match ps with
  | nil => fun _ => nil
  | p::ps' => (genBlockUseDef_products ps' m) ++++ (genBlockUseDef_product p m) 
  end.

  Definition genBlockUseDef (m: module) : usedef_block :=
  genBlockUseDef_products m m.

  Definition getBlockUseDef (udb:usedef_block) (b:block) : list_block :=
  udb b. 

End UseDef.

Section CFG.

  Definition getTerminator (b:block) : option insn := 
  match b with
  | block_intro l is => last_opt insn is
  end. 

  Fixpoint getLabelsFromSwitchCases (cs:list (const*l)) : ls :=
  match cs with
  | nil => lempty_set 
  | (_, l0)::cs' => lset_add l0 (getLabelsFromSwitchCases cs')
  end.

  Definition getLabelsFromTerminator (i:insn) : ls := 
  match i with
  | insn_br t v l1 l2 => lset_add l1 (lset_add l2 lempty_set)
  | insn_br_uncond l0 => lset_add l0 lempty_set 
  (* | insn_switch t v l0 cls => lset_add l0 (getLabelsFromSwitchCases cls) *)
  | insn_invoke id typ id0 ps l1 l2 => lset_add l1 (lset_add l2 lempty_set)
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
  | None => nil
  | Some i => getBlocksFromLabels (getLabelsFromTerminator i) (genLabel2Block m)
  end.
  
  Fixpoint predOfBlock_rec (ls:list block) : list_block :=
  match ls with
  | nil => nil
  | b::ls' => b::predOfBlock_rec ls'
  end.

  Definition predOfBlock (b:block) (udb:usedef_block) : list_block :=
  predOfBlock_rec (udb b).

End CFG.

Section Dominator.

  Parameter genLabelsFromFdef : fdef -> ls.

  Fixpoint inputFromPred (bs:list_block) (output:dt) : ls :=
  match bs with
  | nil => lempty_set
  | (block_intro l0 _)::bs' => lset_union (output l0) (inputFromPred bs' output)
  end.

  Definition outputFromInput (b:block) (input:ls) : ls :=
  match b with
  | block_intro l0 _ => lset_add l0 input
  end.

  Definition update_dt (d1:dt) (l0:l) (ls0:ls) : dt :=
  fun l1 =>
  match lt_eq_lt_dec l1 l0 with 
  | inleft (right _) => ls0
  | _ => d1 l1
  end. 

  Definition inter_dt (d1 d2:dt) : dt :=
  fun l0 => lset_inter (d1 l0) (d2 l0).

  Fixpoint genDominatorTree_blocks_innerloop (bs:list_block) (udb:usedef_block) (output:dt) : dt :=
  match bs with 
  | nil => output
  | (block_intro l is)::bs' => 
    match (outputFromInput (block_intro l is) (inputFromPred (predOfBlock (block_intro l is) udb) output)) with 
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
  | (block_intro l0 _)::bs' =>
    match (lset_eq (d0 l0) (d1 l0)) with
    | true => eq_dt d0 d1 bs'
    | false => false
    end
(*  | _::bs' => eq_dt d0 d1 bs' *)
  end.

  Fixpoint sizeOfDT (bs:list_block) (output:dt) : nat :=
  match bs with
  | nil => 0
  | (block_intro l0 _)::bs' => length (output l0) + sizeOfDT bs' output
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
  | (block_intro l0 _)::bs' => initialize_genDominatorTree_blocks bs' U (update_dt d0 l0 U)
(*  | _::bs' => initialize_genDominatorTree_blocks bs' U d0 *)
  end.

  Definition genEmptyDT : dt := fun _ => nil. 

  Definition initialize_genDominatorTree_entry (f:fdef) : dt :=
  match (getEntryOfFdef f) with
  | None => genEmptyDT
  | Some (block_intro l0 _) => update_dt genEmptyDT l0 (lset_single l0)
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
  | block_intro l1 _ =>
    match (d l1) with
    | ls1 => 
      match b2 with
      | block_intro l2 _ => 
        match (lset_mem l2 ls1) with
        | true => True
        | false => False
        end
(*      | _ => False *)
      end
    end 
(*  | _ => False *)
  end.

  Definition insnDominates (i1 i2:insn) : Prop :=
  match (getInsnID i1, getInsnID i2) with
  | (Some id1, Some id2) =>
    match (le_lt_dec id1 id2) with
    | left _ => (*id1 <= id2*) True
    | right _ => (*id2 < id2*) False
    end
  | _ => False
  end.

  Definition isReachableFromEntry (fi:fdef_info) (b:block) : Prop :=
  let (f, d) := fi in   
  match (getEntryOfFdef f) with
  | None => False
  | Some be => blockDominates d be b
  end.

End Dominator.

Section Classes.

Definition isPointerTypB (t:typ) : bool :=
match t with
| typ_pointer _ => true
| _ => false
end.

Definition isInvokeInsnB (i:insn) : bool :=
match i with
| insn_invoke _ _ _ _ _ _ => true
| _ => false
end.

Definition isCallInsnB (i:insn) : bool :=
match i with
| insn_call _ _ _ _ => true
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

Definition isPhiNodeB (i:insn) : bool :=
match i with
| insn_phi _ _ _ => true
| _ => false
end.

Definition isTerminatorInsnB (i:insn) : bool :=
match i with
| insn_return _ _ => true
| insn_return_void => true
| insn_br _ _ _ _ => true
| insn_br_uncond _ => true
(* | insn_switch _ _ _ => true *)
| insn_invoke _ _ _ _ _ _ => true
| insn_unreachable => true
| _ => false
end.

Definition isBindingFdecB (ib:id_binding) : bool :=
match ib with
| id_binding_fdec fdec => true
| _ => false
end.

Definition isBindingArgB (ib:id_binding) : bool :=
match ib with
| id_binding_arg arg => true
| _ => false
end.

Definition isBindingInsnB (ib:id_binding) : bool :=
match ib with
| id_binding_insn _ => true
| _ => false
end.

End Classes.

Section Inversion.

Definition getInsnTypC (i:insn) : option typ :=
match i with
| insn_return typ _ => Some typ
| insn_return_void => None
| insn_br typ _ _ _ => None 
| insn_br_uncond _ => None
(* | insn_switch typ _ _ _ => None *)
| insn_invoke _ typ _ _ _ _ => Some typ
| insn_call _ typ _ _ => Some typ
| insn_unreachable => None
| insn_add _ typ _ _ => Some typ
(*| insn_fadd _ typ _ _ => Some typ
| insn_udiv _ typ _ _ => Some typ
| insn_fdiv _ typ _ _ => Some typ
| insn_or _ typ _ _ => Some typ
| insn_and _ typ _ _ => Some typ
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ
| insn_extractvalue _ typ _ const1 => getFieldTyp typ const1
| insn_insertvalue _ typ _ _ _ _ => typ
| insn_alloca _ typ _ => Some (typ_pointer typ)
| insn_load _ typ _ => getLoadTyp typ
| insn_store _ _ _ _ => None
| insn_trunc _ _ _ typ => Some typ
| insn_fptrunc _ _ _ typ => Some typ
| insn_fptoui _ _ _ typ => Some typ
| insn_fptosi _ _ _ typ => Some typ
| insn_uitofp _ _ _ typ => Some typ
| insn_sitofp _ _ _ typ => Some typ
| insn_ptrtoint _ _ _ typ => Some typ
| insn_inttoptr _ _ _ typ => Some typ
| insn_bitcase _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int 1)
| insn_fcmp _ _ _ _ _ => Some (typ_int 1) *)
| insn_phi _ typ _ => Some typ
end.

Definition getPointerEltTypC (t:typ) : option typ :=
match t with
| typ_pointer t' => Some t' 
| _ => None
end.

Definition getValueIDsC (v:value) : ids :=
match (getValueID v) with
| None => nil
| Some id => id::nil
end.

Fixpoint getParamsOperandC (lp:list_param) : ids :=
match lp with
| nil => nil
| (t, v)::lp' => (getValueIDsC v) ++ (getParamsOperandC lp')
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

Definition getInsnOperandsC (i:insn) : ids :=
match i with
| insn_return _ v => getValueIDsC v
| insn_return_void => nil
| insn_br _ v _ _ => getValueIDsC v
| insn_br_uncond _ => nil
(* | insn_switch _ value _ _ => getValueIDs value *)
| insn_invoke _ _ _ lp _ _ => getParamsOperandC lp
| insn_call _ _ _ lp => getParamsOperandC lp
| insn_unreachable => nil
| insn_add _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
(*| insn_fadd _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_udiv _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_fdiv _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_or _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_and _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_extractelement _ _ v _ => getValueIDsC v
| insn_insertelement _ _ v1 _ v2 _ => getValueIDsC v1 ++ getValueIDsC v2
| insn_extractvalue _ _ v _ => getValueIDsC v
| insn_insertvalue _ _ v1 _ v2 _ => getValueIDsC v1 ++ getValueIDsC v2
| insn_alloca _ _ _ => nil
| insn_load _ _ v => getValueIDsC v
| insn_store _ v1 _ v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_trunc _ _ v _ => getValueIDsC v
| insn_fptrunc _ _ v _ => getValueIDsC v
| insn_fptoui _ _ v _ => getValueIDsC v
| insn_fptosi _ _ v _ => getValueIDsC v
| insn_uitofp _ _ v _ => getValueIDsC v
| insn_sitofp _ _ v _ => getValueIDsC v
| insn_ptrtoint _ _ v _ => getValueIDsC v
| insn_inttoptr _ _ v _ => getValueIDsC v
| insn_bitcase _ _ v _ => getValueIDsC v
| insn_icmp _ _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_fcmp _ _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2 *)
| insn_phi _ _ ls => list_prj1 _ _ ls
end.

Definition getInsnLabelsC (i:insn) : ls :=
match i with
| insn_return _ _ => nil
| insn_return_void => nil
| insn_br _ _ l1 l2 => l1::l2::nil
| insn_br_uncond l => l::nil
(* | insn_switch _ _ l ls => l::list_prj2 _ _ ls *)
| insn_invoke _ _ _ _ l1 l2 => l1::l2::nil
| insn_call _ _ _ _ => nil
| insn_unreachable => nil
| insn_add _ _ _ _ => nil
(*| insn_fadd _ _ _ _ => nil
| insn_udiv _ _ _ _ => nil
| insn_fdiv _ _ _ _ => nil
| insn_or _ _ _ _ => nil
| insn_and _ _ _ _ => nil
| insn_extractelement _ _ _ _ => nil
| insn_insertelement _ _ _ _ _ _ => nil
| insn_extractvalue _ _ _ _ => nil
| insn_insertvalue _ _ _ _ _ _ => nil
| insn_alloca _ _ _ => nil
| insn_load _ _ _ => nil
| insn_store _ _ _ _ => nil
| insn_trunc _ _ _ _ => nil
| insn_fptrunc _ _ _ _ => nil
| insn_fptoui _ _ _ _ => nil
| insn_fptosi _ _ _ _ => nil
| insn_uitofp _ _ _ _ => nil
| insn_sitofp _ _ _ _ => nil
| insn_ptrtoint _ _ _ _ => nil
| insn_inttoptr _ _ _ _ => nil
| insn_bitcase _ _ _ _ => nil
| insn_icmp _ _ _ _ _ => nil
| insn_fcmp _ _ _ _ _ => nil *)
| insn_phi _ _ ls => list_prj2 _ _ ls
end.

Fixpoint args2TypsC (la:list_arg) : list_typ :=
match la with
| nil => nil
| (t, id)::la' => t::args2TypsC la'
end.

Definition getFheaderTypC (fh:fheader) : typ :=
match fh with
| fheader_intro t _ la => typ_function t (args2TypsC la)
end.

Definition getFdecTypC (fdec:fdec) : typ :=
match fdec with
| fdec_intro fheader => getFheaderTypC fheader
end.

Definition getFdefTypC (fdef:fdef) : typ :=
match fdef with
| fdef_intro fheader _ => getFheaderTypC fheader
end.

Definition getBindingTypC (ib:id_binding) : option typ :=
match ib with
| id_binding_insn i => getInsnTypC i
(* | id_binding_g _ t _ => Some t *)
| id_binding_arg (t, id) => Some t
| id_binding_fdec fdec => Some (getFdecTypC fdec)
| id_binding_none => None
end.

Definition getInsnsFromBlockC (b:block) : list_insn :=
match b with
| block_intro l li => li
(* | block_without_label li => li *)
end.

Definition getBindingFdecC (ib:id_binding) : option fdec :=
match ib with
| id_binding_fdec fdec => Some fdec
| _ => None
end.

Definition getBindingArgC (ib:id_binding) : option arg :=
match ib with
| id_binding_arg arg => Some arg
| _ => None
end.

(*
Definition getBindingGC (ib:id_binding) : option g :=
match ib with
| id_binding_g g => Some g
| _ => None
end.
*)

Definition getBindingInsnC (ib:id_binding) : option insn :=
match ib with
| id_binding_insn i => Some i
| _ => None
end.

Definition getFheaderIDC (fh:fheader) : id :=
match fh with
| fheader_intro _ id _ => id
end.

Definition getFdecIDC (fd:fdec) : id :=
match fd with
| fdec_intro fh => getFheaderIDC fh
end.

Definition getFdefIDC (fd:fdef) : id :=
match fd with
| fdef_intro fh _ => getFheaderIDC fh
end.

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

Fixpoint getLabelViaIDFromList (ls:list (id*l)) (branch:id) : option l :=
match ls with
| nil => None
| (id, l)::ls' => 
  match (eq_nat_dec id branch) with
  | left _ => Some l
  | right _ => getLabelViaIDFromList ls' branch
  end
end.

Definition getLabelViaIDFromPhiNode (phi:insn) (branch:id) : option l :=
match phi with
| insn_phi _ _ ls => getLabelViaIDFromList ls branch
| _ => None
end.

End Inversion.

Section Lookup.

(* ID binding lookup *)

Definition lookupBindingViaIDFromInsnC (i:insn) (id:id) : id_binding :=
match (getInsnID i) with
| None => id_binding_none
| Some id' =>
  match (eq_nat_dec id id') with
  | left _ => id_binding_insn i
  | right _ => id_binding_none
  end
end.

Fixpoint lookupBindingViaIDFromInsnsC (li:list_insn) (id:id) : id_binding :=
match li with
| nil => id_binding_none
| i::li' =>
  match (lookupBindingViaIDFromInsnC i id) with
  | id_binding_insn _ => id_binding_insn i
  | _ => lookupBindingViaIDFromInsnsC li' id
  end
end.

Definition lookupBindingViaIDFromBlockC (b:block) (id:id) : id_binding :=
let list_insn := getInsnsFromBlockC b in
lookupBindingViaIDFromInsnsC list_insn id.

Fixpoint lookupBindingViaIDFromBlocksC (lb:list_block) (id:id) : id_binding :=
match lb with
| nil => id_binding_none
| b::lb' => 
  match (lookupBindingViaIDFromBlockC b id) with
  | id_binding_insn i => id_binding_insn i
  | _ => lookupBindingViaIDFromBlocksC lb' id
  end
end.

Definition lookupBindingViaIDFromArgC (a:arg) (id:id) : id_binding :=
let (t, id') := a in
match (eq_nat_dec id id') with
| left _ => id_binding_arg a
| right _ => id_binding_none
end.

Fixpoint lookupBindingViaIDFromArgsC (la:list_arg) (id:id) : id_binding :=
match la with 
| nil => id_binding_none
| a::la' => 
  match (lookupBindingViaIDFromArgC a id) with
  | id_binding_arg a' => id_binding_arg a'
  | _ => lookupBindingViaIDFromArgsC la' id
  end
end.

Definition lookupBindingViaIDFromFdecC (fd:fdec) (id:id) : id_binding :=
let '(fdec_intro (fheader_intro t id' la)) := fd in
match (eq_nat_dec id id') with
| left _ => id_binding_fdec fd
| right _ => lookupBindingViaIDFromArgsC la id
end.

Definition lookupBindingViaIDFromFdefC (fd:fdef) (id:id) : id_binding :=
let '(fdef_intro fh lb) := fd in
lookupBindingViaIDFromBlocksC lb id.

Definition lookupBindingViaIDFromProductC (p:product) (id:id) : id_binding :=
match p with
(*
| product_global id' t c =>
  match (eq_nat_dec id id') with
  | left _ => id_binding_global id' t c
  | right _ => id_binding_none
  end
*)
| product_function_dec fdec => lookupBindingViaIDFromFdecC fdec id
(* | product_namedt _ => id_binding_none *)
| product_function_def fdef => lookupBindingViaIDFromFdefC fdef id
end.  

Fixpoint lookupBindingViaIDFromProductsC (lp:list_product) (id:id) : id_binding :=
match lp with
| nil => id_binding_none
| p::lp' => 
  match (lookupBindingViaIDFromProductC p id) with
  | id_binding_insn i => id_binding_insn i
  | id_binding_fdec f => id_binding_fdec f
  (* | id_binding_global g => id_binding_global g *)
  | _ => lookupBindingViaIDFromProductsC lp' id
  end
end.
  
Definition lookupBindingViaIDFromModuleC (m:module) (id:id) : id_binding :=
lookupBindingViaIDFromProductsC m id.

Fixpoint lookupBindingViaIDFromModulesC (lm:list_module) (id:id) : id_binding :=
match lm with
| nil => id_binding_none
| m::lm' =>
  match (lookupBindingViaIDFromModuleC m id) with
  | id_binding_insn i => id_binding_insn i
  | id_binding_fdec f => id_binding_fdec f
  (* | id_binding_global g => id_binding_global g *)
  | _ => lookupBindingViaIDFromModulesC lm' id
  end
end.

Definition lookupBindingViaIDFromSystemC (s:system) (id:id) : id_binding :=
lookupBindingViaIDFromModulesC s id.

(* Block lookup from ID *)

Definition isIDInBlockB (id:id) (b:block) : bool :=
match (lookupBindingViaIDFromBlockC b id) with
| id_binding_insn i => true
| _ => false
end.

Fixpoint lookupBlockViaIDFromBlocksC (lb:list_block) (id:id) : option block :=
match lb with
| nil => None  
| b::lb' => 
  match (isIDInBlockB id b) with
  | true => Some b
  | false => lookupBlockViaIDFromBlocksC lb' id
  end
end.

Definition lookupBlockViaIDFromFdefC (fd:fdef) (id:id) : option block :=
match fd with
| fdef_intro fh lb => lookupBlockViaIDFromBlocksC lb id
end.

End Lookup.

Section Eq.

Definition blockEq (b1 b2:block) : bool :=
match (eq_nat_dec (getBlockLabel b1) (getBlockLabel b2)) with
| left _ => true
| right _ => false
end.

End Eq.

(*ENDCOPY*)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./ott") ***
*** End: ***
 *)