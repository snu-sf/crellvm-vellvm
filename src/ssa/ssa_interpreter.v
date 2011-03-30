Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
(* Add LoadPath "../../../theory/metatheory". *)

Require Import ssa_dynamic.
Require Import trace.
Require Import Metatheory.
Require Import assoclist.
Require Import monad.
Require Import genericvalues.
Require Import ssa_mem.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import ssa_props.

Export LLVMopsem.

Definition interInsn (state:State) : option (State*trace) :=
(* Check if the stack is empty. *) 
match state with
| mkState Sys TD Ps nil gl fs Mem0 => None
| mkState Sys TD Ps ((mkEC F B cs tmn lc arg0 als)::EC) gl fs Mem0 =>
  (* If cs is nil, we check tmn, 
     otherwise, we check the first cmd in cs *)
  match cs with
  | nil => (* terminator *)
    match tmn with
    | insn_return rid RetTy Result =>
      (* the suspended stacks cannot be empty, and
          there must be a caller of the current function. *)
      match EC with
      | nil => None
      | (mkEC F' B' nil tmn' lc' arg' als')::EC'' => None
      | (mkEC F' B' (c'::cs') tmn' lc' arg' als')::EC'' =>
        (* there must be a caller of the current function. *)
        if (Instruction.isCallInst c') 
        then 
          do Mem' <- free_allocas TD Mem0 als;
             ret ((mkState Sys TD Ps ((mkEC F' B' cs' tmn' (returnUpdateLocals TD c' RetTy Result lc lc' gl) arg' als')::EC'') gl fs Mem'),
                  trace_nil)
        else None
      end
    | insn_return_void rid =>
      (* the suspended stacks cannot be empty, and
          there must be a caller of the current function. *)
      match EC with
      | nil => None
      | (mkEC F' B' nil tmn' lc' arg' als')::EC'' => None
      | (mkEC F' B' (c'::cs') tmn' lc' arg' als')::EC'' =>
        (* there must be a caller of the current function. *)
        if (Instruction.isCallInst c')
        then
          do Mem' <- free_allocas TD Mem0 als;
             ret ((mkState Sys TD Ps ((mkEC F' B' cs' tmn' lc' arg' als')::EC'') gl fs Mem'),
                  trace_nil)
        else None
      end
    | insn_br bid Cond l1 l2 =>
      (* read the value of Cond *)
      do cond0 <- (getOperandValue TD Cond lc gl);
      (* look up the target block *)
        match (if isGVZero TD cond0
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) with
        | None => None
        | Some (block_intro l' ps' cs' tmn') =>
            Some ((mkState Sys TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' 
                     (switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc) arg0 als)::EC) gl fs Mem0),
                  trace_nil)
        end
    | insn_br_uncond bid l0 =>
      (* look up the target block *)
      match (lookupBlockViaLabelFromFdef F l0) with
      | None => None
      | Some (block_intro l' ps' cs' tmn') =>
          Some ((mkState Sys TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' 
                        (switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc) arg0 als)::EC) gl fs Mem0),
               trace_nil)
      end
    | insn_unreachable _ => None
    end

  | c::cs => (* non-terminator *)
    match c with
    | insn_bop id0 bop0 sz0 v1 v2 => 
      do gv3 <- BOP TD lc gl bop0 sz0 v1 v2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) arg0 als)::EC) gl fs Mem0),
              trace_nil)         
    | insn_fbop id0 fbop0 fp0 v1 v2 => 
      do gv3 <- FBOP TD lc gl fbop0 fp0 v1 v2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) arg0 als)::EC) gl fs Mem0),
              trace_nil)         
    | insn_extractvalue id0 t v idxs =>
      do gv <- getOperandValue TD v lc gl;
      do gv' <- extractGenericValue TD t gv idxs;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv') arg0 als)::EC) gl fs Mem0),
              trace_nil)
    | insn_insertvalue id0 t v t' v' idxs =>
      do gv <- getOperandValue TD v lc gl;
      do gv' <- getOperandValue TD v' lc gl;
      do gv'' <- insertGenericValue TD t gv idxs t' gv';
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv'') arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_malloc id0 t v0 align0 =>
      do tsz <- getTypeAllocSize TD t;
      do gn <- getOperandValue TD v0 lc gl;
      match (malloc TD Mem0 tsz gn align0) with
      | None => None
      | Some (Mem', mb) =>
        ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 (blk2GV TD mb)) arg0 als)::EC) gl fs Mem'),
            trace_nil)
      end
    | insn_free fid t v =>
      do mptr <- getOperandValue TD v lc gl;
      do Mem' <- free TD Mem0 mptr;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn lc arg0 als)::EC) gl fs Mem'), trace_nil)
    | insn_alloca id0 t v0 align0 =>
      do tsz <- getTypeAllocSize TD t;
      do gn <- getOperandValue TD v0 lc gl;
      match (malloc TD Mem0 tsz gn align0) with
      | None => None
      | Some (Mem', mb) =>
          ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 (blk2GV TD mb)) arg0 (mb::als))::EC) gl fs Mem'),
              trace_nil)
      end
    | insn_load id0 t v align0 =>
      do mp <- getOperandValue TD v lc gl;
      do gv <- mload TD Mem0 mp t align0;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv) arg0 als)::EC) gl fs Mem0),
              trace_nil)
    | insn_store sid t v1 v2 align0 =>
      do gv1 <- getOperandValue TD v1 lc gl;
      do mp2 <- getOperandValue TD v2 lc gl;
      do Mem' <- mstore TD Mem0 mp2 t gv1 align0;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn lc arg0 als)::EC) gl fs Mem'),
             trace_nil)
    | insn_gep id0 inbounds0 t v idxs =>
      do mp <- getOperandValue TD v lc gl;
      do vidxs <- values2GVs TD idxs lc gl;
      do mp' <- GEP TD t mp vidxs inbounds0;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 mp') arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_trunc id0 truncop0 t1 v1 t2 =>
      do gv2 <- TRUNC TD lc gl truncop0 t1 v1 t2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2) arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_ext id0 extop0 t1 v1 t2 =>
      do gv2 <- EXT TD lc gl extop0 t1 v1 t2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2) arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_cast id0 castop0 t1 v1 t2 =>
      do gv2 <- CAST TD lc gl castop0 t1 v1 t2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2) arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_icmp id0 cond0 t v1 v2 =>
      do gv3 <- ICMP TD lc gl cond0 t v1 v2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_fcmp id0 fcond0 fp v1 v2 =>
      do gv3 <- FCMP TD lc gl fcond0 fp v1 v2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) arg0 als)::EC) gl fs Mem0),
             trace_nil)
    | insn_select id0 v0 t v1 v2 =>
      do cond0 <- getOperandValue TD v0 lc gl;
      do gv1 <- getOperandValue TD v1 lc gl;
      do gv2 <- getOperandValue TD v2 lc gl;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (if isGVZero TD cond0 then updateAddAL _ lc id0 gv2 else updateAddAL _ lc id0 gv1) arg0 als)::EC) gl fs Mem0),
             trace_nil)  
    | insn_call rid noret0 tailc0 rt fv lp =>
      (* only look up the current module for the time being, 
         do not support linkage. *)
      do fptr <- getOperandValue TD fv lc gl;
      do fid <- lookupFdefViaGVFromFunTable fs fptr;
      match (lookupFdefViaIDFromProducts Ps fid) with
      | None => 
        match (lookupFdecViaIDFromProducts Ps fid) with
        | None => None
        | Some (fdec_intro (fheader_intro rt' fid' la)) =>
          if id_dec fid fid' then
            if typ_dec rt rt' then
              match (callExternalFunction Mem0 fid (params2GVs TD lp lc gl)) with
              | (oresult, Mem1) =>
                ret ((mkState Sys TD Ps 
                      ((mkEC F B cs tmn 
                         (exCallUpdateLocals noret0 rid rt oresult
                            lc) arg0 als)::EC) 
                       gl fs Mem1),
                     trace_nil)
              end
            else None
          else None
        end
      | Some (fdef_intro (fheader_intro rt' fid' la) lb) =>
        if id_dec fid fid' then
          if typ_dec rt rt' then
            match (getEntryBlock (fdef_intro (fheader_intro rt fid la) lb)) with
            | None => None
            | Some (block_intro l' ps' cs' tmn') =>
                ret ((mkState Sys TD Ps ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                                          (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl)) 
                                          (params2GVs TD lp lc gl) nil)::
                                        (mkEC F B ((insn_call rid noret0 tailc0 rt fv lp)::cs) tmn lc arg0 als)::EC) gl fs Mem0),
                    trace_nil)
            end
          else None
        else None
      end
    end
  end
end.

Lemma dsInsn__implies__interInsn : forall state state' tr,
  dsInsn state state' tr ->
  interInsn state = Some (state', tr).
Proof. 
  intros state state' tr HdsInsn.
  Opaque malloc. 
  (dsInsn_cases (destruct HdsInsn) Case); simpl;
    try solve [rewrite H; simpl; rewrite H0; simpl; rewrite H1; simpl; auto |
               rewrite H; simpl; rewrite H0; simpl; auto |
               rewrite H; simpl; auto ].
  Case "dsBranch".
    simpl. rewrite H. simpl. rewrite <- H0. simpl. auto.
  Case "dsBranch_uncond".
    simpl. rewrite <- H. simpl. auto.
  Case "dsCall".
    unfold lookupFdefViaGV in H.
    destruct (getOperandValue TD fv lc gl); try solve [inversion H]. simpl.
    destruct (lookupFdefViaGVFromFunTable fs g); try solve [inversion H]. simpl.
    rewrite H. simpl in H0. rewrite H0. 
    apply lookupFdefViaIDFromProducts_ideq in H; subst.
    destruct (id_dec fid fid); auto.
      destruct (typ_dec rt rt); auto.
        contradict n; auto.
      contradict n; auto.
  Case "dsExCall".
    unfold lookupExFdecViaGV in H.
    destruct (getOperandValue TD fv lc gl); try solve [inversion H]. simpl.
    destruct (lookupFdefViaGVFromFunTable fs g); try solve [inversion H]. simpl.
    destruct (lookupFdefViaIDFromProducts Ps i0); try solve [inversion H].
    rewrite H.
    apply lookupFdecViaIDFromProducts_ideq in H; subst.
    rewrite H0. 
    destruct (id_dec fid fid); auto.
      destruct (typ_dec rt rt); auto.        
        contradict n; auto.
      contradict n; auto.
Qed.

Lemma interInsn__implies__dsInsn : forall state state' tr,
  interInsn state = Some (state', tr) ->
  dsInsn state state' tr.
Proof.
  intros state state' tr HinterInsn.
  destruct state.
  destruct ECS0; simpl in HinterInsn;
    try solve [inversion HinterInsn].

    destruct e as [F B cs tmn lc arg0 als].
    destruct cs.
      destruct tmn.
      Case "insn_return".
        destruct ECS0;
          try solve [inversion HinterInsn].
          
          destruct e as [F' B' cs' tmn' lc' arg' als'].
          destruct cs';
            try solve [inversion HinterInsn].

            remember (Instruction.isCallInst c) as R1.
            remember (free_allocas CurTargetData0 Mem0 als) as R2.
            destruct R1; try solve [inversion HinterInsn].
            destruct R2; inversion HinterInsn; subst; eauto.

      Case "insn_return_void".
        destruct ECS0;
          try solve [inversion HinterInsn].
          
          destruct e as [F' B' cs' tmn' lc' arg' als'].
          destruct cs';
            try solve [inversion HinterInsn].

            remember (Instruction.isCallInst c) as R1.
            remember (free_allocas CurTargetData0 Mem0 als) as R2.
            destruct R1; try solve [inversion HinterInsn].
            destruct R2; inversion HinterInsn; subst; eauto.

      Case "insn_br".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; try solve [inversion HinterInsn].
          simpl in HinterInsn.
          remember (isGVZero CurTargetData0 g) as R3.
          destruct R3.
            remember (lookupBlockViaLabelFromFdef F l1) as R2.
            destruct R2; inversion HinterInsn; subst.
              destruct b.
              inversion HinterInsn; subst.
              eapply dsBranch; eauto.
                rewrite <- HeqR3. auto.
        
            remember (lookupBlockViaLabelFromFdef F l0) as R2.
            destruct R2; inversion HinterInsn; subst.
              destruct b.
              inversion HinterInsn; subst.
              eapply dsBranch; eauto.    
                rewrite <- HeqR3. auto.

      Case "insn_br_uncond".
        remember (lookupBlockViaLabelFromFdef F l0) as R2.
        destruct R2; inversion HinterInsn; subst.
          destruct b.
          inversion HinterInsn; subst; eauto.

      Case "insn_unreachable".
        inversion HinterInsn.
                    
      destruct c.
      Case "insn_bop".
        remember (BOP CurTargetData0 lc Globals0 b s v v0) as R1.
        destruct R1; 
          simpl in HinterInsn;
          inversion HinterInsn; subst; eauto.
          
      Case "insn_fbop".
        remember (FBOP CurTargetData0 lc Globals0 f f0 v v0) as R1.
        destruct R1; 
          simpl in HinterInsn;
          inversion HinterInsn; subst; eauto.

      Case "insn_extractvalue".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (extractGenericValue CurTargetData0 t g l0) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_insertvalue".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (insertGenericValue CurTargetData0 t g l0 t0 g0) as R3.
        destruct R3; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_malloc".
        remember (getTypeAllocSize CurTargetData0 t) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn]. 
        remember (getOperandValue CurTargetData0 v lc Globals0) as R3.
        destruct R3; simpl in HinterInsn;
          try solve [inversion HinterInsn].         
        remember (malloc CurTargetData0 Mem0 s g a) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        destruct p; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_free".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (free CurTargetData0 Mem0 g) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_alloca".
        remember (getTypeAllocSize CurTargetData0 t) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v lc Globals0) as R3.
        destruct R3; simpl in HinterInsn;
          try solve [inversion HinterInsn].         
        remember (malloc CurTargetData0 Mem0 s g a) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        destruct p; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_load".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (mload CurTargetData0 Mem0 g t a) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_store".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (mstore CurTargetData0 Mem0 g0 t g a) as R3.
        destruct R3; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_gep".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (values2GVs CurTargetData0 l0 lc Globals0) as R3.
        destruct R3; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (GEP CurTargetData0 t g l1 i1) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_trunc".
        remember (TRUNC CurTargetData0 lc Globals0 t t0 v t1) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_ext".
        remember (EXT CurTargetData0 lc Globals0 e t v t0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_cast".
        remember (CAST CurTargetData0 lc Globals0 c t v t0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_icmp".
        remember (ICMP CurTargetData0 lc Globals0 c t v v0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_fcmp".
        remember (FCMP CurTargetData0 lc Globals0 f f0 v v0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_select".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v1 lc Globals0) as R3.
        destruct R3; simpl in HinterInsn; 
          try solve [inversion HinterInsn].
        inversion HinterInsn; subst; eauto.

      Case "insn_call".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R0.
        destruct R0; try solve [inversion HinterInsn]. simpl in HinterInsn.
        remember (lookupFdefViaGVFromFunTable FunTable0 g) as R4.
        destruct R4; try solve [inversion HinterInsn]. simpl in HinterInsn.
        remember (lookupFdefViaIDFromProducts CurProducts0 i1) as R1.
        destruct R1; simpl in HinterInsn.
          destruct f. destruct f.
          destruct (id_dec i1 i2); try solve [inversion HinterInsn]; subst.
          destruct (typ_dec t0 t1); try solve [inversion HinterInsn]; subst.
          destruct b; try solve [inversion HinterInsn].
          destruct b.
          inversion HinterInsn; subst.
          eapply dsCall; eauto.
            unfold lookupFdefViaGV.
            rewrite <- HeqR0.
            rewrite <- HeqR4.
            rewrite <- HeqR1. auto.
        
          remember (lookupFdecViaIDFromProducts CurProducts0 i1) as R2.
          destruct R2; simpl in HinterInsn;
            try solve [inversion HinterInsn].
            destruct f. destruct f.
            destruct (id_dec i1 i2); try solve [inversion HinterInsn]; subst.
            destruct (typ_dec t0 t1); try solve [inversion HinterInsn]; subst.
            remember (callExternalFunction Mem0 i2 (params2GVs CurTargetData0 p lc Globals0)) as R3.
            destruct R3.
            inversion HinterInsn; subst.
            eapply dsExCall; eauto.
              unfold lookupExFdecViaGV.
              rewrite <- HeqR0.
              rewrite <- HeqR4.
              rewrite <- HeqR1. eauto.
Qed.


