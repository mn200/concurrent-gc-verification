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
val _ = Datatype`flag = ZF | POSF`
val _ = Datatype`regc = REG regwd | CNST value`
val _ = Datatype`runstate = HALTED | ERRORED | RUNNING`

val _ = Datatype`
  instruction =
    BINOP arithop regwd regc regc  (* destination, arg1, arg2 *)
  | LOAD regwd addr                (* load value from memory addr into reg *)
  | ILOAD regwd regwd              (* load value from addr in reg2 into reg *)
  | LOADV regwd regc               (* load/copy value into reg *)
  | STORE regwd addr               (* store contents of reg to address word64 *)
  | ISTORE regwd regwd           (* store contents of reg1 to address in reg2 *)
  | BRR flag int                 (* pc-relative branch on flag *)
  | BRA flag inst_addr           (* absolute branch on flag *)
  | JMPR int                     (* pc-relative branch *)
  | JMPA inst_addr               (* absolute jump *)
`

val _ = Datatype`
  cpustate = <|
    runstate : runstate ;
    pc : inst_addr ;
    instructions : instruction list ;
    context : α ;  (* memory; other CPUs etc *)
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
  flag_update v = (ZF =+ (v = 0w)) o (POSF =+ (1w ≤ v))
`;

val step_def = Define`
  step mload mstore s =
    if s.runstate <> RUNNING then s
    else if LENGTH s.instructions = s.pc then s with runstate := HALTED
    else if LENGTH s.instructions < s.pc then s with runstate := ERRORED
    else
      let i = EL s.pc s.instructions
      in
        case i of
        | BINOP opn tgt arg1 arg2 =>
            let result = evalop opn (eval_regc s arg1) (eval_regc s arg2) in
            let zf' = (result = 0w) in
            let pf' = (result >= 0w)
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
        | LOADV tgt rc =>
            let value = eval_regc s rc
            in
              s with <| registers updated_by (w2n tgt :+ value) ;
                        flags updated_by (flag_update value) ;
                        pc updated_by SUC |>
        | LOAD tgt a =>
            (case mload a s.context of
                NONE => s with runstate := ERRORED
              | SOME (v,ctxt') =>
                  s with <| registers updated_by (w2n tgt :+ v) ;
                            pc updated_by SUC ;
                            flags updated_by (flag_update v) ;
                            context := ctxt' |>)
        | ILOAD tgt areg =>
            (case mload (s.registers ' (w2n areg)) s.context of
                NONE => s with runstate := ERRORED
              | SOME (v,ctxt') =>
                  s with <| registers updated_by (w2n tgt :+ v) ;
                            pc updated_by SUC ;
                            flags updated_by (flag_update v) ;
                            context := ctxt' |>)
        | STORE src a =>
            (case mstore a (s.registers ' (w2n src)) s.context of
                NONE => s with runstate := ERRORED
              | SOME ctxt' => s with <| pc updated_by SUC ;
                                        context := ctxt' |>)
        | ISTORE src dest =>
            (case mstore (s.registers ' (w2n dest))
                         (s.registers ' (w2n src))
                         s.context
             of
                NONE => s with runstate := ERRORED
              | SOME ctxt' => s with <| pc updated_by SUC ;
                                        context := ctxt' |>)
`;

val state0_def = Define`
  state0 c instrs = <| context := c;
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
  factprog = [LOADV 1w (CNST 1w); LOAD 0w 0w;
              BRR ZF 4; (* loop body *)
              BINOP MUL 1w (REG 1w) (REG 0w);
              BINOP SUB 0w (REG 0w) (CNST 1w);
              BRR POSF (-2)]
`;

val trivMload_def = Define`
  trivMload a mem = SOME (mem a, mem)
`;

val trivMstore_def = Define`
  trivMstore v addr mem = SOME ((v =+ addr) mem)
`;

(* e.g.,

val flag_norm = Q.store_thm(
  "flag_norm[compute]",
  `(POSF =+ v1) ((ZF =+ v2) f) = (ZF =+ v2) ((POSF =+ v1) f) ∧
   (POSF =+ v1) ((POSF =+ v2) f) = (POSF =+ v1) f ∧
   (ZF =+ v1) ((ZF =+ v2) f) = (ZF =+ v1) f`,
  simp[FUN_EQ_THM, combinTheory.UPDATE_def] >> Cases >> simp[]);

val fcp_norm = Q.store_thm(
  "fcp_norm[compute]",
  `(1 :+ v1) ((0 :+ v2) f) = (0 :+ v2) ((1 :+ v1) f) ∧
   (x :+ v1) ((x :+ v2) f) = (x :+ v1) f`,
  simp[fcpTheory.FCP_UPDATE_COMMUTES, fcpTheory.FCP_UPDATE_EQ]);

EVAL ``FUNPOW (step trivMload trivMstore)
              50
              (state0 ((0w =+ 10w) (K 0w)) factprog)``;

(* 10! is indeed 0x375F00 *)
*)

val _ = export_theory();
