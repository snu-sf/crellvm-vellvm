Require Import ssa_lib.
Require Import List.
Require Import ListSet.
Require Import monad.
Require Import Logic_Type.
Require Import reflect.
Require Import vmcore.
Require Import Arith.

(* defns Jwf_typ *)
Inductive wf_typ : typ -> Prop :=    (* defn wf_typ *)
 | wf_typ_int : forall (N5:INT),
     wf_typ (typ_int N5)
 | wf_typ_metadate : 
     wf_typ typ_metadata
 | wf_typ_function : forall (typ_list:list typ) (typ_5:typ),
     isValidReturnTyp typ_5 ->
     wf_typ typ_5 ->
     (forall typ_, In typ_ typ_list -> (isValidArgumentTyp typ_)) ->
     (forall typ_, In typ_ typ_list -> (wf_typ typ_)) ->
     wf_typ (typ_function typ_5 typ_list).

(* defns Jwf_operand_insn *)
Definition wf_operand_insn (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)
                           (insn5 insn':insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  {{
  do id' <- (getInsnID  insn');
  do OpBlock <- (lookupBlockViaIDFromFdefC fdef5 id');

  (* Check that a definition dominates all of its uses *)
     If (isInvokeInsnB insn')
     then 
     (* Invoke results are only usable in the normal destination, not in the
        exceptional destination. *)
     do ln <- getNormalDestFromInvokeInsnC insn';
     do NormalDest <- lookupBlockViaLabelFromSystem system5 ln;
     do lu <- getUnwindDestFromInvokeInsnC insn';
     do UnwindDest <- lookupBlockViaLabelFromSystem system5 lu;
     do Assert (not (NormalDest = UnwindDest));

     (* PHI nodes differ from other nodes because they actually "use" the
        value in the predecessor basic blocks they correspond to. *)
     do UseBlock <- 
        If (isPhiNodeB insn5) 
        then 
        do l <- getLabelViaIDFromPhiNode insn5 id';
           lookupBlockViaLabelFromSystem system5 l
        else
           ret block5
        endif;

        If (isPhiNodeB insn5 && (UseBlock =b= OpBlock))
        then
        (* Special case of a phi node in the normal destination or the unwind
           destination *)
           Assert (block5 = NormalDest /\ isReachableFromEntry fdef_info5 UseBlock)
        else
        (* Invoke result does dominate all uses! *)
        do Assert (blockDominates dt5 NormalDest UseBlock \/ 
                ~ (isReachableFromEntry fdef_info5 UseBlock));

        (* If the normal successor of an invoke instruction has multiple
           predecessors, then the normal edge from the invoke is critical,
           so the invoke value can only be live if the destination block
           dominates all of it's predecessors (other than the invoke). *)
           If (negb (hasSinglePredecessor NormalDest usedef_block5) &&
               (isReachableFromEntryB fdef_info5 UseBlock)
              )
           then
           (* If it is used by something non-phi, then the other case is that
              'NormalDest' dominates all of its predecessors other than the
              invoke.  In this case, the invoke value can still be used. *)
             for PI in (predOfBlock NormalDest usedef_block5) do
               (* Invoke result must dominate all uses! *)
               If (insnHasParent insn' system5)
               then
               do parentOfInsn' <- getParentOfInsnFromSystemC insn' system5;
                  If (negb (blockDominatesB dt5 NormalDest PI) && 
                      isReachableFromEntryB fdef_info5 PI)
                  then ret False
                  endif
               endif
             endfor
           endif
        endif
     elseif (isPhiNodeB insn5)
     then
     (* PHI nodes are more difficult than other nodes because they actually
        "use" the value in the predecessor basic blocks they correspond to. *)
     do predl <- getLabelViaIDFromPhiNode insn5 id';
     do PredBB <- lookupBlockViaLabelFromSystem system5 predl;
        (* Instruction must dominate all uses! *) 
        Assert (blockDominates dt5 OpBlock PredBB \/ ~ isReachableFromEntry fdef_info5 PredBB)
     else       
     do If (OpBlock =b= block5)
        then
          (* If they are in the same basic block, make sure that the definition
             comes before the use. *)
          Assert (insnDominates insn' insn5 \/ ~ isReachableFromEntry fdef_info5 block5)
        endif;
        (* Definition must dominate use unless use is unreachable! *)
        Assert (insnDominates insn' insn5 \/ ~ isReachableFromEntry fdef_info5 block5)
        (* !! FIXME
          Assert2(InstsInThisBlock.count(Op) || DT->dominates(Op, &I) ||
                  !DT->isReachableFromEntry(BB),
                  "Instruction does not dominate all uses!", Op, &I);
          *)
     endif
  }}.

(* defns Jwf_operand *)
Definition wf_operand (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef_info5:fdef_info)
                            (block5:block)
                            (insn5:insn) 
                            (id':id): Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  {{
  do ret (insnInSystemModuleFdefBlock 
            insn5 
            system5  
            ( module5 , ( usedef_insn5 ,  usedef_block5 )) 
            ( fdef5 ,  dt5 )   
            block5);
  do ids5 <- ret (getInsnOperandsC insn5);
  do ret ( set_In  id' ids5 );

  do id_binding' <- ret (lookupBindingViaIDFromSystemC system5 id');
  (* Check to make sure that only first-class-values are operands to instructions. *)
  do typ' <- (getBindingTypC id_binding');
  do Assert (isFirstClassTyp typ');
  
  (* Valid use of metadata pointer. *)
  do If (isPointerTypB typ')
     then 
     do typ'' <- (getPointerEltTypC typ');
        Assert (not (typEq typ'' typ_metadata))
     endif;

  do If (isBindingFdecB id_binding')
     then
     do fdec5 <- (getBindingFdecC id_binding');
     (* Check to make sure that the "address of" an intrinsic function is never
        taken *)
     do id0 <- ret (getFdecIDC fdec5);
     do Assert (( ~ set_In id0 intrinsic_funs5) \/  getCallName insn5 id0);

     (* Referencing function exists in current module *)
        Assert (In  (product_function_dec fdec5) module5)
     endif;

  do If (isBindingArgB id_binding')
     then 
     do arg <- getBindingArgC id_binding';
     (* Referring to an argument in the current function *)
        ret (argInFdef arg fdef5)
     endif;
(*
  do If (isBindingGB id_binding')
     then 
     (* Referencing global in the current module *)
     do g <- getBindingGC id_binding';
        ret True
     endif
*)        
     
  do If (isBindingInsnB id_binding')
     then 
     (*  Check when id_binding' is insn *)
     do insn' <- getBindingInsnC id_binding';
        ret (wf_operand_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 insn')
     endif;

     ret True
  }}.
  
(* defns Jwf_label *)
Inductive wf_label : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> l -> Prop :=    (* defn wf_label *)
 | wf_label_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef5:fdef) (dt5:dt) (block5:block) (insn5:insn) (l5:l) (ls5:ls),
     insnInSystemModuleFdefBlock insn5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 ->
     getInsnLabels insn5 ls5 ->
      ( set_In  l5   ls5 )  ->
      (lookupBlockViaLabelFromSystem  system5   l5  =   (Some  block5 )  )  ->
     blockInFdef block5 fdef5 ->
     wf_label intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 insn5 l5.

(* defns JvisitInstruction *)
Definition visitInstruction (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef_info5:fdef_info)
                            (block5:block)
                            (insn5:insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  {{
  (* Instruction must be embedded in basic block! *)
  do ret (insnInSystemModuleFdefBlock 
            insn5   
            system5   
            ( module5 , ( usedef_insn5 ,  usedef_block5 ))     
            ( fdef5 ,  dt5 )   
            block5);

  (* Check that non-phi nodes are not self referential *)
  do If (isPhiNodeB insn5)
     then 
       for insn in (getInsnUseDef usedef_insn5 insn5) do
         Assert ((not (getInsnID insn5 = getInsnID insn)) \/ 
                 (not (isReachableFromEntry (fdef5, dt5) block5)))
       endfor
     endif;

  (* Verify that if this is a terminator that it is at the end of the block. *)
  do If (isTerminatorInsnB insn5)
     then 
     do insn' <- (getTerminator block5);
        Assert (getInsnID insn5 = getInsnID insn')
     endif;

  (* Check that void typed values don't have names 
     We dont need to check this in Coq. *)

  (* Check that the return value of the instruction is either void or a legal
     value type. *)
  do typ5 <- (getInsnTypC insn5);
  do Assert (typEq typ5 typ_void  \/  isFirstClassTyp typ5);

  (* Check that the instruction doesn't produce metadata or metadata*. Calls
     all already checked against the callee type. *)
  do Assert ((not (typEq typ5 typ_metadata ))   \/  
             isInvokeInsn insn5   \/  
             isCallInsn insn5 );

  (* Instructions may not produce pointer to metadata *)
  do If (isPointerTypB typ5 )
     then  
     do typ' <- (getPointerEltTypC typ5);
        Assert (not (typEq typ' typ_metadata ))
     endif;

  (* Check that all uses of the instruction, if they are instructions
     themselves, actually have parent basic blocks.  If the use is not an
     instruction, it is an error!
     We should prove a lemma for this later *)
  
  (* Check operands *)
  do for insn in (getInsnOperandsC insn5) do
     (* Check to make sure that only first-class-values are operands to
        instructions. *)
       ret (wf_operand intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 insn)
     endfor;

  (* Check labels *)
     for l in (getInsnLabelsC insn5) do
       ret (wf_label intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 l)
     endfor
  }}.

(* defns JvisittTerminatorInst *)
Definition visitTerminatorInst (intrinsic_funs5:intrinsic_funs) 
                               (system5:system)
                               (module_info5:module_info)
                               (fdef_info5:fdef_info)
                               (block5:block)
                               (insn5:insn) : Prop :=
  (* Ensure that terminators only exist at the end of the basic block. *)
  {{
  do tI <- getTerminator block5;
  do Assert (insn5 =i= tI);
     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5)
  }}.

Definition visitReturnInst (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)                              
                           (RI:insn)                              (* ReturnInst *)
                           : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (F, dt5) := fdef_info5 in 
  {{
  do N <- ret (ReturnInst.getNumOperands RI);
  do If ((Function.getReturnType F) =t= typ_void)
     then
     (* return instr that returns non-void in Function cannot be of void return type! *)
       Assert (N =n= 0)
     elseif ((N =n= 1) && (ReturnInst.hasReturnType RI))
     then
     do rt <- ReturnInst.getReturnType RI;
     (* Exactly one return value and it matches the return type. Good. *)
        Assert ((Function.getReturnType F) =t= rt)
     elseif (false)
     then
     (*
       else if (const StructType *STy = dyn_cast<StructType>(F->getReturnType())) {
       // The return type is a struct; check for multiple return values.
       Assert2(STy->getNumElements() == N,
               "Incorrect number of return values in ret instruction!",
                &RI, F->getReturnType());
       for (unsigned i = 0; i != N; ++i)
         Assert2(STy->getElementType(i) == RI.getOperand(i)->getType(),
                 "Function return type does not match operand "
                 "type of return inst!", &RI, F->getReturnType());
     *)
       ret True
     elseif (isArrayTypB (Function.getReturnType F))
     then
     do ATy <- ret (Function.getReturnType F);
     (* The return type is an array; check for multiple return values. *)
     do Assert ((ArrayType.getNumElements ATy) =n= N);
        for i from 0 to N do
        (* Function return type matches operand type of return inst! *)
        do et <- (ArrayType.getElementType ATy);
        do rt <- (ReturnInst.getReturnType RI); 
        (* !! FIXME: RI.getOperand(i)->getType() *)
           Assert (et =t= rt)
        endfor
     else
     (* Function return type does not match operand type of return inst! *)
        ret False
     endif;

  (* Check to make sure that the return value has necessary properties for
     terminators... *)
     ret (visitTerminatorInst intrinsic_funs5 system5 module_info5 fdef_info5 block5 RI)
  }}.

Definition verifyCallSite (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)                              
                           (CS:insn)                              (* CallSite *)
                           : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (F, dt5) := fdef_info5 in 
  {{
  do I <- ret CS;
  (* LLVM checks that 
       "Called function must be a pointer!"
       "Called function is not pointer to function type!"
     We don't need to check this, but only ensure Call and FTy are valid
     *)
  do Call <- CallSite.getCalledFunction CS system5;
  do FTy <- ret CallSite.getFdefTyp Call;

  (* Verify that the correct number of arguments are being passed *)
  do If (FunctionType.isVarArg FTy)
     then 
     (* Called function requires less parameters. *)
     do numParams <- (FunctionType.getNumParams FTy);
        Assert(CallSite.arg_size Call >= numParams)
     else
     (* Correct number of arguments passed to called function! *)
     do numParams <- (FunctionType.getNumParams FTy);     
        Assert(CallSite.arg_size Call =n= numParams)   
     endif;

  (* Verify that all arguments to the call match the function type... *)
  do numParams <- (FunctionType.getNumParams FTy);
  do for i from 0 to numParams do
     (* Call parameter type should match function signature. *)
       do argt <- CallSite.getArgumentType Call i;
       do part <- FunctionType.getParamType FTy i;
          Assert (argt =t= part)
     endfor;

  (* Will Verify call attributes later... *)

  (* Verify that there's no metadata unless it's a direct call to an intrinsic. 
     Open soooon... *)

     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef_info5 block5 CS)
  }}.  


Definition visitCallInst (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)                              
                           (CI:insn)                              (* CallInst *)
                           : Prop :=
(*
  if (Function *F = CI.getCalledFunction())
    if (Intrinsic::ID ID = (Intrinsic::ID)F->getIntrinsicID())
      visitIntrinsicFunctionCall(ID, CI);
*)
  verifyCallSite intrinsic_funs5 system5 module_info5 fdef_info5 block5 CI.


Definition visitInvokeInst (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)                              
                           (II:insn)                              (* InvokeInst *)
                           : Prop :=
  verifyCallSite intrinsic_funs5 system5 module_info5 fdef_info5 block5 II.

Definition visitBinaryOperator (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)                              
                           (B:insn)                              (* BinaryOperator *)
                           : Prop :=
  {{
  (* "Both operands to a binary operator are of the same type" *)
  do firstT <- BinaryOperator.getFirstOperandType B;
  do secondT <- BinaryOperator.getSecondOperandType B;
  do Assert (firstT =t= secondT);

  (* Check that integer arithmetic operators are only used with
     integral operands. *)
  do rT <- BinaryOperator.getResultType B;
  (* Integer arithmetic operators only work with integral types *)
  do Assert (Typ.isIntOrIntVector rT);
  (* Integer arithmetic operators must have same type for operands and result *)
  do Assert (rT =t= firstT);

     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef_info5 block5 B)
  }}.  

Definition visitPHINode (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)                              
                           (PN:insn)                              (* PHINode *)
                           : Prop :=
  {{
  (* Ensure that the PHI nodes are all grouped together at the top of the block.
     This can be tested by checking whether the instruction before this is
     either nonexistent (because this is begin()) or is a PHI node.  If not,
     then there is some other instruction before a PHI. *)

  (*
    Assert2(&PN == &PN.getParent()->front() ||
            isa<PHINode>(--BasicBlock::iterator(&PN)),
            "PHI nodes not grouped at top of basic block!",
            &PN, PN.getParent());
  *)
  do Assert (blockStartsWithPhiNode block5);

  (* Check that all of the operands of the PHI node have the same type as the
     result. *)
  do nIncomingValues <- PHINode.getNumIncomingValues PN;
  do for i from 0 to nIncomingValues do
     do rT <- getInsnTypC PN;
     do iT <- PHINode.getIncomingValueType system5 PN i;
        Assert (rT =t= iT)
     endfor;

  (* All other PHI node constraints are checked in the visitBasicBlock method. *)
     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef_info5 block5 PN)
  }}.

(* defns Jwf_insn *)
Inductive wf_insn : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> Prop :=    (* defn wf_insn *)
 | wf_insn_return : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block) (typ5:typ) (value5:value),
     visitReturnInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_return typ5 value5) ->
     wf_insn intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_return typ5 value5)
 | wf_insn_return_void : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block),
     visitReturnInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 insn_return_void ->
     wf_insn intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 insn_return_void
 | wf_insn_br : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (typ5:typ) (value5:value) (l1 l2:l) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitTerminatorInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_br typ5 value5 l1 l2) ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_br typ5 value5 l1 l2)
 | wf_insn_br_uncond : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (l5:l) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitTerminatorInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_br_uncond l5) ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_br_uncond l5)
 | wf_insn_invoke : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (id_5:id) (typ0:typ) (id0:id) (list_param5:list_param) (l1 l2:l) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitInvokeInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_invoke id_5 typ0 id0 list_param5 l1 l2) ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_invoke id_5 typ0 id0 list_param5 l1 l2)
 | wf_insn_call : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (id_5:id) (typ0:typ) (id0:id) (list_param5:list_param) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitCallInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_call id_5 typ0 id0 list_param5) ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_call id_5 typ0 id0 list_param5)
 | wf_insn_unreachable : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitTerminatorInst intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 insn_unreachable ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 insn_unreachable
 | wf_insn_add : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (id5:id) (typ5:typ) (value1 value2:value) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitBinaryOperator intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_add id5 typ5 value1 value2) ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_add id5 typ5 value1 value2)
 | wf_insn_phi : forall (id_l_list:list (id*l)) (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (id_5:id) (typ5:typ) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitPHINode intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_phi id_5 typ5 id_l_list) ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_phi id_5 typ5 id_l_list)
 .

(* defns Jwf_list_insn *)
Inductive wf_list_insn : intrinsic_funs -> system -> module_info -> fdef_info -> block -> list_insn -> Prop :=    (* defn wf_list_insn *)
 | wf_list_insn_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (block5:block),
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5  nil 
 | wf_list_insn_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (block5:block) (list_insn5:list_insn) (insn5:insn),
     wf_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 ->
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 list_insn5 ->
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5  ( insn5 :: list_insn5 ) .

(* defns Jwf_block *)
Inductive wf_block : intrinsic_funs -> system -> module_info -> fdef_info -> block -> Prop :=    (* defn wf_block *)
 | wf_block_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (block5:block) (l5:l) (list_insn5:list_insn),
     blockInSystemModuleFdef  (block_intro l5 list_insn5)  system5 module_info5 fdef_info5 ->
     getInsnsFromBlock block5 list_insn5 ->
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 list_insn5 ->
     insnsChecksTerminatorInsn list_insn5 ->
     insnsStartsWithPhiNode list_insn5 ->
     wf_block intrinsic_funs5 system5 module_info5 fdef_info5 block5.

(* defns Jwf_list_block *)
Inductive wf_list_block : intrinsic_funs -> system -> module_info -> fdef_info -> list_block -> Prop :=    (* defn wf_list_block *)
 | wf_list_block_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info),
     wf_list_block intrinsic_funs5 system5 module_info5 fdef_info5  nil 
 | wf_list_block_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (list_block5:list_block) (block5:block),
     wf_block intrinsic_funs5 system5 module_info5 fdef_info5 block5 ->
     wf_list_block intrinsic_funs5 system5 module_info5 fdef_info5 list_block5 ->
     wf_list_block intrinsic_funs5 system5 module_info5 fdef_info5  ( block5 :: list_block5 ) .

(* defns Jwf_fdef *)
Inductive wf_fdef : intrinsic_funs -> system -> module_info -> fdef -> Prop :=    (* defn wf_fdef *)
 | wf_fdef_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fheader5:fheader) (list_block5:list_block) (dt5:dt),
     productInSystemModule (product_function_def  (fdef_intro fheader5 list_block5) ) system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   ->
     genDominatorTree (fdef_intro fheader5 list_block5) module5 = dt5  ->
     wf_list_block intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( (fdef_intro fheader5 list_block5) ,  dt5 )   list_block5 ->
     wf_fdef intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   (fdef_intro fheader5 list_block5).

(* defns Jwf_prod *)
Inductive wf_prod : intrinsic_funs -> system -> module_info -> product -> Prop :=    (* defn wf_prod *)
 | wf_prod_function_dec : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdec5:fdec),
     wf_prod intrinsic_funs5 system5 module_info5 (product_function_dec fdec5)
 | wf_prod_function_def : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef),
     wf_fdef intrinsic_funs5 system5 module_info5 fdef5 ->
     wf_prod intrinsic_funs5 system5 module_info5 (product_function_def fdef5).

(* defns Jwf_prods *)
Inductive wf_prods : intrinsic_funs -> system -> module_info -> list_product -> Prop :=    (* defn wf_prods *)
 | wf_prods_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info),
     wf_prods intrinsic_funs5 system5 module_info5  nil 
 | wf_prods_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (list_product5:list_product) (product5:product),
     wf_prods intrinsic_funs5 system5 module_info5 list_product5 ->
     wf_prod intrinsic_funs5 system5 module_info5 product5 ->
     wf_prods intrinsic_funs5 system5 module_info5  ( product5 :: list_product5 ) .

(* defns Jwf_module *)
Inductive wf_module : intrinsic_funs -> system -> module -> Prop :=    (* defn wf_module *)
 | wf_module_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (list_product5:list_product) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block),
      In   list_product5    system5  ->
     genInsnUseDef  list_product5  = usedef_insn5  ->
     genBlockUseDef  list_product5  = usedef_block5  ->
     wf_prods intrinsic_funs5 system5   (  list_product5  , ( usedef_insn5 ,  usedef_block5 ))   list_product5 ->
     wf_module intrinsic_funs5 system5  list_product5 .

(* defns Jwf_list_module *)
Inductive wf_list_module : intrinsic_funs -> system -> list_module -> Prop :=    (* defn wf_list_module *)
 | wf_list_module_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system),
     wf_list_module intrinsic_funs5 system5  nil 
 | wf_list_module_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (list_module5:list_module) (module5:module),
     wf_module intrinsic_funs5 system5 module5 ->
     wf_list_module intrinsic_funs5 system5 list_module5 ->
     wf_list_module intrinsic_funs5 system5  ( module5 :: list_module5 ) .

(* defns Jwf_system *)
Inductive wf_system : intrinsic_funs -> system -> Prop :=    (* defn wf_system *)
 | wf_system_intro : forall (intrinsic_funs5:intrinsic_funs) (list_module5:list_module),
     wf_list_module intrinsic_funs5  list_module5  list_module5 ->
     uniqSystem  list_module5  ->
     wf_system intrinsic_funs5  list_module5 .

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./monads" "-I" "./ott") ***
*** End: ***
 *)

