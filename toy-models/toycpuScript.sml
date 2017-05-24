open HolKernel Parse boolLib bossLib;

open wordsLib intLib

val _ = new_theory "toycpu";
val _ = ParseExtras.tight_equality()

val _ = type_abbrev("regcount", ``:4``)
val _ = type_abbrev("regwd", ``:bool[2]``)
val _ = type_abbrev("addr", ``:word64``)
val _ = type_abbrev("inst_addr", ``:num``)
val _ = type_abbrev("value", ``:word64``)

val _ = Datatype`arithop = ADD | SUB | MUL`
val _ = Datatype`flag = ZF | SF`

val flag_norm = Q.store_thm(
  "flag_norm[compute]",
  `(SF =+ v1) ((ZF =+ v2) f) = (ZF =+ v2) ((SF =+ v1) f) ∧
   (SF =+ v1) ((SF =+ v2) f) = (SF =+ v1) f ∧
   (ZF =+ v1) ((ZF =+ v2) f) = (ZF =+ v1) f`,
  simp[FUN_EQ_THM, combinTheory.UPDATE_def] >> Cases >> simp[]);

val _ = Datatype`regc = REG regwd | CNST value`
val _ = Datatype`runstate = HALTED | ERRORED | RUNNING`
val _ = Datatype`fence_type = ACQ | REL`

val _ = Datatype`
  instruction =
    BINOP arithop regwd regc regc  (* destination, arg1, arg2 *)
  | LOAD regwd addr                (* load value from memory addr into reg *)
  | ILOAD regwd regwd              (* load value from addr in reg2 into reg *)
  | MOV regwd regc                 (* move value into reg *)
  | STORE regwd addr               (* store contents of reg to address word64 *)
  | FENCE fence_type             (* perform either acquire or release fence *)
  | ISTORE regwd regwd           (* store contents of reg1 to address in reg2 *)
  | BRR flag int                 (* pc-relative branch on flag *)
  | BRA flag inst_addr           (* absolute branch on flag *)
  | JMPR int                     (* pc-relative branch *)
  | JMPA inst_addr               (* absolute jump *)
`

val _ = Datatype`
  memory = <| context : α ;
              mload : addr -> α -> (value # α) option ;
              mstore : addr -> value -> α -> α option ;
              mfence_acquire : α -> α ;
              mfence_release : α -> α
           |>
`;

val memload_def = Define‘
  memload m a =
    case m.mload a m.context of
      SOME (v,c) => SOME(v, m with context := c)
    | NONE => NONE
’;

val memstore_def = Define‘
  memstore m a v =
    OPTION_MAP (λc. m with context := c) (m.mstore a v m.context)
’;

val memfence_def = Define‘
  memfence m flavour =
    case flavour of
        ACQ => m with context updated_by m.mfence_acquire
      | REL => m with context updated_by m.mfence_release
’;

val _ = Datatype`
  cpustate = <|
    runstate : runstate ;
    pc : inst_addr ;
    instructions : instruction list ;
    memory : α memory ;  (* memory; other CPUs etc *)
    registers : value[regcount] ;
    flags : flag -> bool  (* flags are set by loads and binops *)
  |>
`;

val eval_regc_def = Define`
  eval_regc s (REG i) = s.registers ' (w2n i) ∧
  eval_regc s (CNST v) = v
`;

val evalop_def = Define`
  evalop ADD = words$word_add ∧
  evalop SUB = words$word_sub ∧
  evalop MUL = words$word_mul
`;

val flag_update_def = Define`
  flag_update v = (ZF =+ (v = 0w)) o (SF =+ word_msb v)
`;

val step_def = Define`
  step s =
    if s.runstate <> RUNNING then s
    else if LENGTH s.instructions = s.pc then s with runstate := HALTED
    else if LENGTH s.instructions < s.pc then s with runstate := ERRORED
    else
      let i = EL s.pc s.instructions
      in
        case i of
        | BINOP opn tgt arg1 arg2 =>
            let result = evalop opn (eval_regc s arg1) (eval_regc s arg2)
            in
              s with <| registers updated_by (w2n tgt :+ result) ;
                        flags updated_by (flag_update result) ;
                        pc updated_by SUC
                     |>
        | JMPA ia => s with pc := ia
        | JMPR off => let tgt = &s.pc + off
                      in
                        if tgt < 0 then s with runstate := ERRORED
                        else s with pc := Num tgt
        | BRA f ia => if s.flags f then s with pc := ia
                      else s with pc updated_by SUC
        | BRR f off => let tgt = &s.pc + off
                       in
                         if s.flags f then
                           if tgt < 0 then s with runstate := ERRORED
                           else s with pc := Num tgt
                         else s with pc updated_by SUC
        | MOV tgt rc =>
            let value = eval_regc s rc
            in
              s with <| registers updated_by (w2n tgt :+ value) ;
                        flags updated_by (flag_update value) ;
                        pc updated_by SUC |>
        | LOAD tgt a =>
            (case memload s.memory a of
                NONE => s with runstate := ERRORED
              | SOME (v,m) =>
                  s with <| registers updated_by (w2n tgt :+ v) ;
                            pc updated_by SUC ;
                            flags updated_by (flag_update v) ;
                            memory := m |>)
        | ILOAD tgt areg =>
            (case memload s.memory (s.registers ' (w2n areg)) of
                NONE => s with runstate := ERRORED
              | SOME (v,m) =>
                  s with <| registers updated_by (w2n tgt :+ v) ;
                            pc updated_by SUC ;
                            flags updated_by (flag_update v) ;
                            memory := m
                         |>)
        | STORE src a =>
            (case memstore s.memory a (s.registers ' (w2n src)) of
                NONE => s with runstate := ERRORED
              | SOME m => s with <| pc updated_by SUC ; memory := m |>)
        | ISTORE src dest =>
            (case memstore s.memory
                           (s.registers ' (w2n dest))
                           (s.registers ' (w2n src))
             of
                NONE => s with runstate := ERRORED
              | SOME m => s with <| pc updated_by SUC ; memory := m |>)
`;

val state0_def = Define`
  state0 m instrs = <|
    memory := m;
    instructions := instrs;
    registers := FCP c. 0w;
    pc := 0 ;
    flags := K F ;
    runstate := RUNNING
  |>
`;

val addprog_def = Define`
  addprog = [LOAD 0w 0w; LOAD 1w 1w; BINOP ADD 0w (REG 0w) (REG 1w);
             STORE 0w 0w]
`;

val factprog_def = Define`
  factprog = [MOV 1w (CNST 1w); LOAD 0w 0w;
              BRR ZF 5; (* loop body *)
              BINOP MUL 1w (REG 1w) (REG 0w);
              BINOP SUB 0w (REG 0w) (CNST 1w);
              BRR ZF 2; JMPR (-3); STORE 1w 1w]
`;

val trivM_def = Define‘
  trivM m = <| context := m ;
               mfence_acquire := I ;
               mfence_release := I ;
               mload := (λa m. SOME (m a, m)) ;
               mstore := (λa v m. SOME ((a =+ v) m))
            |>
’;

val fcp_norm = Q.store_thm(
  "fcp_norm[compute]",
  ‘(1 :+ v1) ((0 :+ v2) f) = (0 :+ v2) ((1 :+ v1) f) ∧
   (x :+ v1) ((x :+ v2) f) = (x :+ v1) f’,
  simp[fcpTheory.FCP_UPDATE_COMMUTES, fcpTheory.FCP_UPDATE_EQ]);

val fact50 = save_thm(
  "fact50",
  EVAL “FUNPOW step
              50
              (state0 (trivM ((0w =+ 10w) (K 0w))) factprog)”);

(* 10! is indeed 0x375F00 *)

val _ = export_theory();
