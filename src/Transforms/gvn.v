Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import dtree.
Require Import primitives.

Definition cmds_from_block (f:fdef) (lbl:l) : option cmds :=
  match lookupBlockViaLabelFromFdef f lbl with
  | None => None
  | Some (block_intro _ _ cs _) => 
      Some (List.filter (fun c => 
                         match (getCmdID c) with
                         | Some _ => true
                         | None => false
                         end) cs)
  end.

Inductive rhs : Set :=
    rhs_bop : bop -> sz -> value -> value -> rhs
  | rhs_fbop : fbop -> floating_point -> value -> value -> rhs
  | rhs_extractvalue : typ -> value -> list_const -> rhs
  | rhs_insertvalue : typ -> value -> typ -> value -> list_const -> rhs
  | rhs_malloc : typ -> value -> align -> rhs
  | rhs_free : typ -> value -> rhs
  | rhs_alloca : typ -> value -> align -> rhs
  | rhs_load : typ -> value -> align -> rhs
  | rhs_store : typ -> value -> value -> align -> rhs
  | rhs_gep : inbounds -> typ -> value -> list_value -> rhs
  | rhs_trunc : truncop -> typ -> value -> typ -> rhs
  | rhs_ext : extop -> typ -> value -> typ -> rhs
  | rhs_cast : castop -> typ -> value -> typ -> rhs
  | rhs_icmp : cond -> typ -> value -> value -> rhs
  | rhs_fcmp : fcond -> floating_point -> value -> value -> rhs
  | rhs_select : value -> typ -> value -> value -> rhs
  | rhs_call : noret -> clattrs -> typ -> value -> params -> rhs
.

Tactic Notation "rhs_cases" tactic(first) tactic(c) :=
  first;
  [ c "rhs_bop" | c "rhs_fbop" |
    c "rhs_extractvalue" | c "rhs_insertvalue" |
    c "rhs_malloc" | c "rhs_free" |
    c "rhs_alloca" | c "rhs_load" | c "rhs_store" | c "rhs_gep" |
    c "rhs_trunc" | c "rhs_ext" | c "rhs_cast" | 
    c "rhs_icmp" | c "rhs_fcmp" | c "rhs_select" |
    c "rhs_call" ].

Definition rhs_of_cmd (c: cmd) : rhs :=
match c with
| insn_bop _ bop0 sz v1 v2 => rhs_bop bop0 sz v1 v2
| insn_fbop _ fbop0 fp0 v1 v2 => rhs_fbop fbop0 fp0 v1 v2
| insn_extractvalue _ t v cnts => rhs_extractvalue t v cnts
| insn_insertvalue _ t1 v1 t2 v2 cnts => rhs_insertvalue t1 v1 t2 v2 cnts
| insn_malloc _ t v al => rhs_malloc t v al
| insn_free _ t v => rhs_free t v
| insn_alloca _ t v al => rhs_alloca t v al
| insn_load _ t v al => rhs_load t v al
| insn_store _ t1 v1 v2 al => rhs_store t1 v1 v2 al
| insn_gep _ ib0 t v vs => rhs_gep ib0 t v vs
| insn_trunc _ top0 t1 v1 t2 => rhs_trunc top0 t1 v1 t2
| insn_ext _ eop0 t1 v1 t2 => rhs_ext eop0 t1 v1 t2
| insn_cast _ cop0 t1 v1 t2 => rhs_cast cop0 t1 v1 t2
| insn_icmp _ t0 cnd0 v1 v2 => rhs_icmp t0 cnd0 v1 v2
| insn_fcmp _ fcond0 fp0 v1 v2 => rhs_fcmp fcond0 fp0 v1 v2
| insn_select _ v0 t0 v1 v2 => rhs_select v0 t0 v1 v2
| insn_call _ noret0 cl0 t1 v1 ps => rhs_call noret0 cl0 t1 v1 ps
end.

Lemma rhs_dec : forall (r1 r2:rhs), {r1=r2}+{~r1=r2}.
Proof.
  (rhs_cases (destruct r1) Case); destruct r2; try solve [done_right | auto].
  Case "rhs_bop".
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "rhs_fbop".
    destruct (@fbop_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "rhs_extractvalue".
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "rhs_insertvalue".
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "rhs_malloc".    
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "rhs_free".    
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "rhs_alloca".    
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (Align.dec a a0); subst; try solve [auto | done_right].
  Case "rhs_load".    
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "rhs_store".    
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v1); try solve [auto | done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "rhs_gep".    
    destruct (@inbounds_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); try solve [auto | done_right].
    destruct (@list_value_dec l0 l1); subst; try solve [auto | done_right].
  Case "rhs_trunc".
    destruct (@truncop_dec t t2); subst; try solve [done_right].
    destruct (@typ_dec t0 t3); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t1 t4); subst; try solve [auto | done_right].
  Case "rhs_ext".
    destruct (@extop_dec e e0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "rhs_cast".
    destruct (@castop_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "rhs_icmp".
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "rhs_fcmp".
    destruct (@fcond_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "rhs_select".
    destruct (@value_dec v v2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v0 v3); subst; try solve [done_right].
    destruct (@value_dec v1 v4); subst; try solve [auto | done_right].
  Case "rhs_call".
    destruct (@value_dec v v0); subst; try solve [done_right]. 
    destruct (@noret_dec n n0); subst; try solve [done_right].
    destruct c. destruct c0.
    destruct (@tailc_dec t1 t2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@callconv_dec c c0); subst; try solve [done_right]. 
    destruct (@attributes_dec a a1); subst; try solve [done_right]. 
    destruct (@attributes_dec a0 a2); subst; try solve [done_right]. 
    destruct (@params_dec p p0); subst; try solve [auto | done_right].
Qed.

Definition pure_cmd (c:cmd) : bool :=
match c with
| insn_bop _ _ _ _ _ 
| insn_fbop _ _ _ _ _ 
| insn_extractvalue _ _ _ _
| insn_insertvalue _ _ _ _ _ _
| insn_gep _ _ _ _ _
| insn_trunc _ _ _ _ _
| insn_ext _ _ _ _ _
| insn_cast _ _ _ _ _
| insn_icmp _ _ _ _ _ 
| insn_fcmp _ _ _ _ _
| insn_select _ _ _ _ _ => true
| _ => false
end.

Fixpoint const_list_value (vs: list_value) : option list_const :=
match vs with
| Nil_list_value => Some Nil_list_const
| Cons_list_value (value_const c) vs' => 
    match const_list_value vs' with
    | Some cs' => Some (Cons_list_const c cs')
    | None => None
    end
| _ => None
end.

Definition const_cmd (c:cmd) : option const :=
match c with
| insn_bop _ bop0 _ (value_const c1) (value_const c2) => 
    Some (const_bop bop0 c1 c2)
| insn_fbop _ fbop0 _ (value_const c1) (value_const c2) =>
    Some (const_fbop fbop0 c1 c2)
| insn_extractvalue _ _ (value_const c0) cnts =>
    Some (const_extractvalue c0 cnts)
| insn_insertvalue _ _ (value_const c1) _ (value_const c2) cnts =>
    Some (const_insertvalue c1 c2 cnts)
| insn_malloc _ _ _ _ => None
| insn_free _ _ _ => None
| insn_alloca _ _ _ _ => None
| insn_load _ _ _ _ => None
| insn_store _ _ _ _ _ => None
| insn_gep _ ib0 _ (value_const c) vs => 
    match const_list_value vs with
    | None => None
    | Some cnts => Some (const_gep ib0 c cnts)
    end
| insn_trunc _ top0 _ (value_const c1) t1 => Some (const_truncop top0 c1 t1)   
| insn_ext _ eop0 _ (value_const c1) t1 => Some (const_extop eop0 c1 t1)   
| insn_cast _ cop0 _ (value_const c1) t1 => Some (const_castop cop0 c1 t1)   
| insn_icmp _ cond0 _ (value_const c1) (value_const c2) =>
    Some (const_icmp cond0 c1 c2)   
| insn_fcmp _ fcond0 _ (value_const c1) (value_const c2) => 
    Some (const_fcmp fcond0 c1 c2)
| insn_select _ (value_const c0) _ (value_const c1) (value_const c2) =>
    Some (const_select c0 c1 c2)
| insn_call _ _ _ _ _ _ => None
| _ => None
end.

Fixpoint const_in_list_value_l (cst0:const) (vls:list_value_l) : bool :=
match vls with
| Nil_list_value_l => true
| Cons_list_value_l (value_const cst) _ vls' => 
    const_dec cst cst0 && const_in_list_value_l cst0 vls'
| _ => false
end.

Definition const_phinode (p:phinode) : option const :=
match p with
| insn_phi _ _ (Cons_list_value_l (value_const cnt) _ vls) =>
    if (const_in_list_value_l cnt vls) then Some cnt else None
| _ => None
end.

Definition lcmds := list (l*cmd).

Fixpoint lookup_redundant_exp (inscope: lcmds) (r:rhs) : option id :=
match inscope with
| nil => None
| (_,c)::inscope' =>
    match (getCmdID c) with
    | None => lookup_redundant_exp inscope' r
    | Some id0 => 
        if (rhs_dec r (rhs_of_cmd c)) then Some id0
        else lookup_redundant_exp inscope' r
    end
end.

Definition mem_effect (c:cmd) : option (value * typ) :=
match c with
| insn_malloc pid t _ _ => Some (value_id pid, t)
| insn_free _ t pv => Some (pv, t)
| insn_alloca pid t _ _ => Some (value_id pid, t)
| insn_store _ t _ pv _ => Some (pv, t)
| _ => None
end.

Definition is_aliasing (pv1:value) (t1:typ) (pv2:value) (t2:typ) : bool := true.

Definition kill_aliased_loadstores (inscope: lcmds) (pv1:value) (t1:typ) 
 : lcmds :=
 List.filter (fun data => 
              match data with
              | (_, insn_load _ t2 pv2 _) => negb (is_aliasing pv1 t1 pv2 t2)
              | (_, insn_store _ t2 _ pv2 _) => negb (is_aliasing pv1 t1 pv2 t2)
              | (_, _) => true
              end) inscope.

Fixpoint lookup_redundant_load (inscope: lcmds) t1 pv1 al1 
  : option (l * id * value) :=
match inscope with
| nil => None
| (l0,c)::inscope' =>
    if (rhs_dec (rhs_load t1 pv1 al1) (rhs_of_cmd c)) 
    then Some (l0, getCmdLoc c, value_id (getCmdLoc c))
    else 
      match c with
      | insn_store id0 t1' v0' pv1' _ => 
          if (t1 =t= t1') && valueEqB pv1 pv1' then Some (l0, id0, v0')
          else lookup_redundant_load inscope' t1 pv1 al1
      | _ => lookup_redundant_load inscope' t1 pv1 al1
      end
end.

Definition block_doesnt_kill (b: block) (pv1:value) (t1:typ) : bool :=
let '(block_intro _ _ cs _) := b in
List.fold_left 
  (fun (acc:bool) c =>
   if acc then
     match (mem_effect c) with
     | Some (pv2, t2) => negb (is_aliasing pv1 t1 pv2 t2)
     | None => true
     end
   else acc) cs true.

Fixpoint split_cmds (cs:cmds) (id1:id) : cmds :=
match cs with
| c::cs' => 
    if (id_dec id1 (getCmdLoc c)) then cs'
    else split_cmds cs' id1
| _ => nil
end.

Definition cmds_doesnt_kill (b: block) (id1:id) (pv1:value) (t1:typ) : bool :=
let '(block_intro _ _ cs _) := b in
List.fold_left 
  (fun (acc:bool) c =>
   if acc then
     match (mem_effect c) with
     | Some (pv2, t2) => negb (is_aliasing pv1 t1 pv2 t2)
     | None => true
     end
   else acc) (split_cmds cs id1) true.

Program Fixpoint fdef_doesnt_kill_aux (f:fdef) (preds : ATree.t ls) 
  (nvisited:list l) (src curr target:l) (id1:id) (pv1:value) (t1:typ)
  {measure (List.length nvisited)} : bool :=
let init :=
  if l_dec curr src then true
  else
    if l_dec curr target then
      match lookupBlockViaLabelFromFdef f curr with
      | None => false
      | Some b => cmds_doesnt_kill b id1 pv1 t1
      end
    else 
      match lookupBlockViaLabelFromFdef f curr with
      | None => false
      | Some b => block_doesnt_kill b pv1 t1
      end in
match (ATree.get curr preds) with
| None => init
| Some nexts => 
    fold_left 
      (fun acc next =>
       if acc then
         if (in_dec eq_atom_dec next nvisited) then 
           fdef_doesnt_kill_aux f preds 
             (List.remove eq_atom_dec next nvisited) src next target id1 pv1 t1
         else acc
       else acc)
      nexts init
end.
Next Obligation. 
  apply remove_in_length; auto.
Qed.

Definition fdef_doesnt_kill (f:fdef) (src target:l) (id1:id) (pv1:value) 
  (t1:typ) : bool :=
fdef_doesnt_kill_aux f (make_predecessors (successors f)) (bound_fdef f)
  src target target id1 pv1 t1.

Definition kill_loadstores (inscope: lcmds) : lcmds :=
 List.filter (fun data => 
              match data with
              | (_, insn_load _ _ _ _) => false
              | (_, insn_store _ _ _ _ _) => false
              | (_, _) => true
              end) inscope.

Definition gvn_cmd (st:fdef*bool*lcmds) (l1:l) (c:cmd) : fdef*bool*lcmds :=
let '(f, changed, inscope) := st in
if (pure_cmd c) then
  match (getCmdID c) with
  | None => (f, changed, inscope)
  | Some id0 =>
      match const_cmd c with
      | None =>
          match lookup_redundant_exp inscope (rhs_of_cmd c) with
          | None => (f, changed, (l1,c)::inscope)
          | Some id1 => 
              (remove_fdef id0 (isubst_fdef id0 id1 f), true, inscope)
          end
      | Some cst0 => 
          (remove_fdef id0 (csubst_fdef id0 cst0 f), true, inscope)
      end
  end 
else 
  match c with 
  | insn_load id1 t1 pv1 al1 =>
    match lookup_redundant_load inscope t1 pv1 al1 with
    | None => (f, changed, (l1,c)::inscope)
    | Some (l0, id0, v0) => 
        if fdef_doesnt_kill f l0 l1 id1 pv1 t1 then
          (remove_fdef id1 (subst_fdef id1 v0 f), true, inscope)
        else (f, changed, (l1,c)::inscope)
    end
  | _ =>
    match (mem_effect c) with
    | Some (pv, t) => 
        match c with 
        | insn_store _ _ _ _ _ => 
               (f, changed, (l1,c)::kill_aliased_loadstores inscope pv t)
        | _ => (f, changed, kill_aliased_loadstores inscope pv t)
        end
    | _ => 
       match c with
       | insn_call _ _ _ _ _ _ => (f, changed, kill_loadstores inscope)
       | _ => (f, changed, inscope)
       end
    end
  end
.

Fixpoint gvn_cmds (st:fdef*bool*lcmds) (l1:l) (n: nat) : fdef * bool * lcmds :=
let '(f, changed, inscope) := st in
match lookupBlockViaLabelFromFdef f l1 with
| None => st
| Some (block_intro _ _ cs _) =>
    match List.nth_error (List.rev cs) n with
    | Some c => 
        let st' := gvn_cmd st l1 c in
        match n with
        | S n' => gvn_cmds st' l1 n'
        | _ => st'
        end
    | None => st
    end
end.

Fixpoint gvn_phis (f:fdef) (changed : bool) (ps: phinodes): fdef * bool :=
match ps with
| nil => (f, changed)
| p::ps' =>
    let id0 := getPhiNodeID p in
    let '(f', changed') := 
      match const_phinode p with
      | None => (f, false) 
      | Some cst0 => (remove_fdef id0 (csubst_fdef id0 cst0 f), true)
      end in
    gvn_phis f' (changed || changed') ps' 
end.

Fixpoint gvn_fdef_dtree (f:fdef) (changed: bool) (inscope: lcmds) (dt: DTree)
  : fdef * bool :=
match dt with
| DT_node l0 dts => 
    match lookupBlockViaLabelFromFdef f l0 with
    | None => (f, changed)
    | Some (block_intro _ ps cs _) =>
        let '(f2, changed2, inscope2) := 
          gvn_cmds (gvn_phis f changed ps, inscope) l0 (List.length cs - 1) in
        gvn_fdef_dtrees f2 changed2 inscope2 dts 
    end
end
with gvn_fdef_dtrees (f:fdef) (changed: bool) (inscope: lcmds) (dts: DTrees)
  : fdef * bool :=
match dts with
| DT_nil => (f, changed)
| DT_cons dt dts' => 
    let '(f', changed') := gvn_fdef_dtree f changed inscope dt in
    gvn_fdef_dtrees f' changed' inscope dts' 
end.

Variable TNAME: Type.
Parameter init_expected_name : unit -> TNAME.
Parameter check_bname : l -> TNAME -> option (l * TNAME).
Parameter check_vname : id -> TNAME -> option (id * TNAME).

Definition renamel_block (l1 l2:l) (b:block) : block := 
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro (rename_id l1 l2 l0) ps0 cs0 tmn0
end.

Definition renamel_fdef (l1 l2:l) (f:fdef) : fdef := 
match f with
| fdef_intro fh bs => 
    fdef_intro fh (List.map (renamel_block l1 l2) bs) 
end.

Definition fix_temporary_block (f:fdef) (b:block) (eid:TNAME) 
  : option (fdef * TNAME) := 
let '(block_intro l0 ps cs _) := b in
match check_bname l0 eid with
| Some (l0', eid5) =>
  let st :=
  fold_left 
    (fun st p => 
     match st with
     | Some (f0, eid0) =>
         let 'pid := getPhiNodeID p in
         match check_vname pid eid0 with
         | None => None
         | Some (pid', eid') =>
             if (id_dec pid pid') then Some (f0, eid')
             else Some (rename_fdef pid pid' f0, eid')
         end
     | _ => None
     end) ps (Some ((renamel_fdef l0 l0' f), eid5)) in
  fold_left 
    (fun st c => 
     match st with
     | Some (f0, eid0) =>
         match getCmdID c with
         | None => Some (f0, eid0)
         | Some cid =>
           match check_vname cid eid0 with
           | None => None
           | Some (cid', eid') =>
               if (id_dec cid cid') then Some (f0, eid')
               else Some (rename_fdef cid cid' f0, eid')
           end
         end
     | _ => None
     end) cs st
| None => None
end.

Definition fix_temporary_fdef (f:fdef) : option fdef :=
let eid := init_expected_name tt in
let '(fdef_intro fh bs) := f in
match fold_left 
  (fun st b => 
   match st with
   | Some (f0, eid0) =>
       match fix_temporary_block f0 b eid0 with
       | Some (f1, eid1) => Some (f1, eid1)
       | None => None
       end
   | _ => None
   end) bs (Some (f, eid)) with
| Some (f', _) => Some f'
| None => None
end.

Fixpoint lookup_predundant_exp_from_cmds (cs: cmds) (r:rhs) : option cmd :=
match cs with
| nil => None
| c::cs' =>
    match (getCmdID c) with
    | None => lookup_predundant_exp_from_cmds cs' r
    | Some _ => 
        if (rhs_dec r (rhs_of_cmd c)) then Some c
        else lookup_predundant_exp_from_cmds cs' r
    end
end.

(* 
   ndom = bound_fdef f - res [l1] - l1
   id1 = r in l1 
*)
Fixpoint lookup_predundant_exp_for_id (f:fdef) (ndom: list l) 
  (res: AMap.t (set l)) (l1:l) (r:rhs) : option (l * cmd) :=
match ndom with
| nil => None
| l0::ndom' =>
    match (AMap.get l0 res) with
    | dts0 =>
      if (in_dec eq_atom_dec l1 dts0) then
        lookup_predundant_exp_for_id f ndom' res l1 r
      else
        match lookupBlockViaLabelFromFdef f l0 with
        | None => None
        | Some (block_intro _ _ cs _) =>
            match lookup_predundant_exp_from_cmds cs r with
            | None => lookup_predundant_exp_for_id f ndom' res l1 r
            | Some c0 => Some (l0, c0)
            end
        end
    end
end.

Fixpoint lookup_predundant_exp (f:fdef) (res: AMap.t (set l)) (rd0 rd:list l) 
  : option (l * id * l * cmd) :=
match rd with
| nil => None
| l1::rd' =>
    match lookupBlockViaLabelFromFdef f l1 with
    | None => None
    | Some (block_intro _ _ cs _) =>
        match (AMap.get l1 res) with
        | dts1 =>
           let ndom := 
             ListSet.set_diff id_dec 
               (ListSet.set_inter id_dec rd0 (bound_fdef f)) (l1::dts1) in
           match 
             fold_left (fun acc c =>
                        match acc with
                        | None =>
                          match getCmdID c with 
                          | Some id1 =>
                              if pure_cmd c then
                                match 
                                  lookup_predundant_exp_for_id f ndom res l1  
                                    (rhs_of_cmd c) with
                                | Some (l0, c0) => Some (l1, id1, l0, c0)
                                | None => None
                                end
                              else None
                          | None => None
                          end
                        | _ => acc
                        end) cs None with
           | None => lookup_predundant_exp f res rd0 rd'
           | Some re => Some re
           end
        end
    end
end.

Definition find_gcd_dom (res: AMap.t (set l)) (l1 l2:l) : option l :=
match AMap.get l1 res, AMap.get l2 res with
| dts1, dts2 =>
  match ListSet.set_inter id_dec dts1 dts2 with
  | l0::dts0 => find_idom_aux res l0 dts0
  | _ => None
  end
end.

Definition pre_fdef (f:fdef) (res: AMap.t (set l)) (rd:list l) : fdef * bool :=
match lookup_predundant_exp f res rd rd with
| Some (l1, id1, l0, c0) =>
    match find_gcd_dom res l1 l0 with
    | Some l2 =>
        match lookupBlockViaLabelFromFdef f l2 with
        | None => (f, false)
        | Some (block_intro _ _ cs _) => 
            (remove_fdef id1 
              (isubst_fdef id1 (getCmdLoc c0) 
                (motion_fdef l2 (List.length cs+1) c0 f)), true)
        end
    | None => (f, false)
    end
| None => (f, false)
end.

Definition opt_step (dt:DTree) (res: AMap.t (set l)) (rd:list l) (f: fdef)
  : fdef + fdef :=
let '(f1, changed1) := gvn_fdef_dtree f false nil dt in
if changed1 then inr _ f1 
else 
  let '(f2, changed2) := pre_fdef f1 res rd in
  if changed2 then inr _ f2 else inl _ f2.

Parameter print_reachablity : list l -> bool.
Parameter print_dominators : list l -> AMap.t (set l) -> bool.
Parameter print_dtree : DTree -> bool.

Definition dce_block (f:fdef) (b:block) : fdef :=
let '(block_intro _ ps cs _) := b in
fold_left 
  (fun f3 c => 
     match getCmdID c with
     | Some id0 => 
         if pure_cmd c then
           if (used_in_fdef id0 f3) then f3 
           else remove_fdef id0 f3
         else f3
     | _ => f3
     end) cs
  (fold_left 
    (fun f2 p => 
     let id0 := getPhiNodeID p in
     if (used_in_fdef id0 f2) then f2
     else remove_fdef id0 f2) ps f).

Definition dce_fdef (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
fold_left (fun f1 b => dce_block f1 b) bs f.

Definition opt_fdef (f:fdef) : fdef :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ _ _), Some rd =>
    let b := bound_fdef f in
    let dts := dep_doms__nondep_doms b (dom_analyze f) in
    match create_dtree_aux dts root 
      (List.remove eq_atom_dec root rd) with
    | Some dt => 
        if print_reachablity rd && print_dominators b dts && print_dtree dt then
          match fix_temporary_fdef 
                  (SafePrimIter.iterate _ (opt_step dt dts rd) (dce_fdef f)) with
          | Some f' => f'
          | _ => f
          end
        else f
    | None => f
    end
| _, _ => f
end.

Definition opt (m:module) : module :=
let '(module_intro los nts ps) := m in
module_intro los nts 
  (List.rev (fold_left (fun acc p =>
                        match p with
                        | product_fdef f => product_fdef (opt_fdef f)
                        | _ => p
                        end::acc) ps nil)).

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
