
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open listTheory pairTheory combinTheory addressTheory finite_mapTheory set_sepTheory;

open toycpuTheory progTheory;

val _ = new_theory "prog_toy";
val _ = tight_equality();

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The TOY set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Datatype `
  toy_el = Runstate runstate
         | PC num
         | Inst num (instruction option)
         | Reg word2 word64
         | Flag flag bool
         | Context (addr -> α -> (value # α) option)
                   (addr -> value -> α -> α option) α
`

val toy_el_11 = DB.fetch "-" "toy_el_11";
val toy_el_distinct = DB.fetch "-" "toy_el_distinct";

val _ = Parse.type_abbrev("toy_set",``:('a toy_el) set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from TOY-state record to toy_set                                   *)
(* ----------------------------------------------------------------------------- *)

val toy_read_reg_def = Define `
  toy_read_reg (n:word2) s = s.registers ' (w2n n)`

val toy_read_flag_def = Define `
  toy_read_flag n s = s.flags n`

val toy_read_inst_def = Define `
  toy_read_inst n s =
    if n < LENGTH s.instructions then SOME (EL n s.instructions) else NONE`

val toy2set'_def = Define `
  toy2set' (rs,pc,is,rg,fl,cc) (s:'a cpustate) =
    (if rs then { Runstate s.runstate } else {}) UNION
    (if pc then { PC s.pc } else {}) UNION
    IMAGE (\a. Inst a (toy_read_inst a s)) is UNION
    IMAGE (\a. Reg a (toy_read_reg a s)) rg UNION
    IMAGE (\a. Flag a (toy_read_flag a s)) fl UNION
    (if cc then { Context s.mload s.mstore s.context } else {})`;

val toy2set_def   = Define `toy2set s = toy2set' (T,T,UNIV,UNIV,UNIV,T) s`;
val toy2set''_def = Define `toy2set'' x s = toy2set s DIFF toy2set' x s`;

(* theorems *)

val toy2set'_SUBSET_toy2set = prove(
  ``!y s. toy2set' y s SUBSET toy2set s``,
  strip_tac
  \\ PairCases_on `y`
  \\ SIMP_TAC std_ss [SUBSET_DEF,toy2set'_def,toy2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_toy2set = prove(
  ``!x s. SPLIT (toy2set s) (toy2set' x s, toy2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,toy2set''_def]
  \\ `toy2set' x s SUBSET toy2set s` by METIS_TAC [toy2set'_SUBSET_toy2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. (x IN (if g then y else z)) = if g then x IN y else x IN z``;

val SUBSET_toy2set = prove(
  ``!u s. (u SUBSET toy2set s) = ?y. u = toy2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [toy2set'_SUBSET_toy2set]
  \\ Q.EXISTS_TAC `
       ((?y. Runstate y IN u),
        (?y. PC y IN u),
        { a |a| ?x. Inst a x IN u },
        { a |a| ?x. Reg a x IN u },
        { a |a| ?x. Flag a x IN u },
        (?y1 y2 y3. Context y1 y2 y3 IN u))`
  \\ FULL_SIMP_TAC std_ss [toy2set'_def,toy2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV,PUSH_IN_INTO_IF]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_X_ASSUM ``!x:'a. b:bool`` (IMP_RES_TAC)
  \\ FULL_SIMP_TAC std_ss [toy_el_11,toy_el_distinct]);

val SPLIT_toy2set_EXISTS = prove(
  ``!s u v. SPLIT (toy2set s) (u,v) = ?y. (u = toy2set' y s) /\ (v = toy2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_toy2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,toy2set'_def,toy2set''_def]
  \\ `u SUBSET (toy2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_toy2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ fs [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);

val IN_toy2set = store_thm("IN_toy2set[simp]",``
  (!x s. Runstate x IN (toy2set s) <=> (x = s.runstate)) /\
  (!x s. Runstate x IN (toy2set' (rs,pc,is,rg,fl,cc) s) <=> (x = s.runstate) /\ rs) /\
  (!x s. Runstate x IN (toy2set'' (rs,pc,is,rg,fl,cc) s) <=> (x = s.runstate) /\ ~rs) /\
  (!x s. PC x IN (toy2set s) <=> (x = s.pc)) /\
  (!x s. PC x IN (toy2set' (rs,pc,is,rg,fl,cc) s) <=> (x = s.pc) /\ pc) /\
  (!x s. PC x IN (toy2set'' (rs,pc,is,rg,fl,cc) s) <=> (x = s.pc) /\ ~pc) /\
  (!a x s. Inst a x IN (toy2set s) <=> (x = toy_read_inst a s)) /\
  (!a x s. Inst a x IN (toy2set' (rs,pc,is,rg,fl,cc) s) <=> (x = toy_read_inst a s) /\ a IN is) /\
  (!a x s. Inst a x IN (toy2set'' (rs,pc,is,rg,fl,cc) s) <=> (x = toy_read_inst a s) /\ ~(a IN is)) /\
  (!a x s. Reg a x IN (toy2set s) <=> (x = toy_read_reg a s)) /\
  (!a x s. Reg a x IN (toy2set' (rs,pc,is,rg,fl,cc) s) <=> (x = toy_read_reg a s) /\ a IN rg) /\
  (!a x s. Reg a x IN (toy2set'' (rs,pc,is,rg,fl,cc) s) <=> (x = toy_read_reg a s) /\ ~(a IN rg)) /\
  (!a x s. Flag a x IN (toy2set s) <=> (x = toy_read_flag a s)) /\
  (!a x s. Flag a x IN (toy2set' (rs,pc,is,rg,fl,cc) s) <=> (x = toy_read_flag a s) /\ a IN fl) /\
  (!a x s. Flag a x IN (toy2set'' (rs,pc,is,rg,fl,cc) s) <=> (x = toy_read_flag a s) /\ ~(a IN fl)) /\
  (!x1 x2 x3 s. Context x1 x2 x3 IN (toy2set s) <=>
                x1 = s.mload /\ x2 = s.mstore /\ x3 = s.context) /\
  (!x1 x2 x3 s. Context x1 x2 x3 IN (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
                x1 = s.mload /\ x2 = s.mstore /\ x3 = s.context /\ cc) /\
  (!x1 x2 x3 s. Context x1 x2 x3 IN (toy2set'' (rs,pc,is,rg,fl,cc) s) <=>
                x1 = s.mload /\ x2 = s.mstore /\ x3 = s.context /\ ~cc)``,
  SRW_TAC [] [toy2set'_def,toy2set''_def,toy2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

val toy2set''_11 = prove(
  ``!y y' s s'. (toy2set'' y' s' = toy2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ PairCases_on `y` \\ PairCases_on `y'`
  \\ rename1 `(rs,pc,is,rg,fl,cc) <> (rs',pc',is',rg',fl',cc')`
  \\ fs []
  THEN1
   (`(?x. Runstate x IN toy2set'' (rs,pc,is,rg,fl,cc) s) <>
     (?x. Runstate x IN toy2set'' (rs',pc',is',rg',fl',cc') s')` by fs []
    \\ rev_full_simp_tac std_ss [])
  THEN1
   (`(?x. PC x IN toy2set'' (rs,pc,is,rg,fl,cc) s) <>
     (?x. PC x IN toy2set'' (rs',pc',is',rg',fl',cc') s')` by fs []
    \\ rev_full_simp_tac std_ss [])
  THEN1
   (`?a. ~(a IN is <=> a IN is')` by METIS_TAC [EXTENSION]
    \\ `(?x. Inst a x IN toy2set'' (rs,pc,is,rg,fl,cc) s) <>
        (?x. Inst a x IN toy2set'' (rs',pc',is',rg',fl',cc') s')` by fs []
    \\ rev_full_simp_tac std_ss [])
  THEN1
   (`?a. ~(a IN rg <=> a IN rg')` by METIS_TAC [EXTENSION]
    \\ `(?x. Reg a x IN toy2set'' (rs,pc,is,rg,fl,cc) s) <>
        (?x. Reg a x IN toy2set'' (rs',pc',is',rg',fl',cc') s')` by fs []
    \\ rev_full_simp_tac std_ss [])
  THEN1
   (`?a. ~(a IN fl <=> a IN fl')` by METIS_TAC [EXTENSION]
    \\ `(?x. Flag a x IN toy2set'' (rs,pc,is,rg,fl,cc) s) <>
        (?x. Flag a x IN toy2set'' (rs',pc',is',rg',fl',cc') s')` by fs []
    \\ rev_full_simp_tac std_ss [])
  THEN1
   (`(?x1 x2 x3. Context x1 x2 x3 IN toy2set'' (rs,pc,is,rg,fl,cc) s) <>
     (?x1 x2 x3. Context x1 x2 x3 IN toy2set'' (rs',pc',is',rg',fl',cc') s')` by fs []
    \\ rev_full_simp_tac std_ss []));

val DELETE_toy2set = store_thm("DELETE_toy2set[simp]",``
  (!s. (toy2set' (rs,pc,is,rg,fl,cc) s) DELETE Runstate (s.runstate) =
       (toy2set' (F,pc,is,rg,fl,cc) s)) /\
  (!s. (toy2set' (rs,pc,is,rg,fl,cc) s) DELETE PC (s.pc) =
       (toy2set' (rs,F,is,rg,fl,cc) s)) /\
  (!s. (toy2set' (rs,pc,is,rg,fl,cc) s) DELETE Inst i (toy_read_inst i s) =
       (toy2set' (rs,pc,is DELETE i,rg,fl,cc) s)) /\
  (!s. (toy2set' (rs,pc,is,rg,fl,cc) s) DELETE Reg r (toy_read_reg r s) =
       (toy2set' (rs,pc,is,rg DELETE r,fl,cc) s)) /\
  (!s. (toy2set' (rs,pc,is,rg,fl,cc) s) DELETE Flag f (toy_read_flag f s) =
       (toy2set' (rs,pc,is,rg,fl DELETE f,cc) s)) /\
  (!s. (toy2set' (rs,pc,is,rg,fl,cc) s) DELETE Context s.mload s.mstore s.context =
       (toy2set' (rs,pc,is,rg,fl,F) s))``,
  SRW_TAC [] [toy2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_toy2set = store_thm("EMPTY_toy2set[simp]",``
  (toy2set' (rs,pc,is,rg,fl,cc) s = {}) <=>
  ~rs /\ ~pc /\ is = {} /\ rg = {} /\ fl = {} /\ ~cc``,
  Cases_on `rs` THEN1 fs [toy2set'_def]
  \\ Cases_on `pc` THEN1 fs [toy2set'_def]
  \\ Cases_on `cc` THEN1 fs [toy2set'_def]
  \\ fs [toy2set'_def] \\ metis_tac []);


(* ----------------------------------------------------------------------------- *)
(* Defining the TOY_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val tRunstate_def = Define `tRunstate x = SEP_EQ { Runstate x }`
val tPC_def = Define `tPC x = SEP_EQ { PC x }`
val tInst_def = Define `tInst i x = SEP_EQ { Inst i x }`
val tReg_def = Define `tReg i x = SEP_EQ { Reg i x }`
val tFlag_def = Define `tFlag i x = SEP_EQ { Flag i x }`
val tContext_def = Define `tContext x1 x2 x3 = SEP_EQ { Context x1 x2 x3 }`

val Flags_def = Define `tFlags (zf,posf) = tFlag ZF zf * tFlag SF posf`;

val TOY_NEXT_REL_def = Define `
  TOY_NEXT_REL s s' = (step s = s')`;

val TOY_INSTR_def = Define `
  TOY_INSTR (a,w) = {(Inst a (SOME w))}`;

val tm = rand ``SPEC (toy2set,
                      TOY_NEXT_REL,
                      TOY_INSTR,
                      (\x y. x = (y:'a cpustate)),
                      ((K F):('a cpustate) -> bool))``

val TOY_MODEL_def = Define `
  TOY_MODEL = ^tm`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_toy2set]
  ``p (toy2set' y s) ==>
    (?u v. SPLIT (toy2set s) (u,v) /\ p u /\ (\v. v = toy2set'' y s) v)``;

val TOY_SPEC_SEMANTICS = store_thm("TOY_SPEC_SEMANTICS",
  ``SPEC TOY_MODEL p {} q =
    !y s seq. p (toy2set' y s) /\ rel_sequence TOY_NEXT_REL seq s ==>
              ?k. q (toy2set' y (seq k)) /\ (toy2set'' y s = toy2set'' y (seq k))``,
  SIMP_TAC std_ss [GSYM RUN_EQ_SPEC,RUN_def,TOY_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_toy2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma)) o
               Q.SPECL [`s`,`(\v. v = toy2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_toy2set_EXISTS]
  \\ IMP_RES_TAC toy2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC TOY_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val STAR_toy2set = store_thm("STAR_toy2set",
  ``((tRunstate y * p) (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
      y = s.runstate /\ rs /\ p (toy2set' (F,pc,is,rg,fl,cc) s)) /\
    ((tPC v * p) (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
      v = s.pc /\ pc /\ p (toy2set' (rs,F,is,rg,fl,cc) s)) /\
    ((tContext x1 x2 x3 * p) (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
      x1 = s.mload /\ x2 = s.mstore /\ x3 = s.context /\ cc /\
      p (toy2set' (rs,pc,is,rg,fl,F) s)) /\
    ((tFlag f x * p) (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
      (x = toy_read_flag f s) /\ f IN fl /\
      p (toy2set' (rs,pc,is,rg,fl DELETE f,cc) s)) /\
    ((tReg r w * p) (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
      (w = toy_read_reg r s) /\ r IN rg /\
      p (toy2set' (rs,pc,is,rg DELETE r,fl,cc) s)) /\
    ((tInst n i * p) (toy2set' (rs,pc,is,rg,fl,cc) s) <=>
      (i = toy_read_inst n s) /\ n IN is /\
      p (toy2set' (rs,pc,is DELETE n,rg,fl,cc) s))``,
  SIMP_TAC std_ss [tRunstate_def, tPC_def, tInst_def, tReg_def,
    tFlag_def, tContext_def, EQ_STAR, INSERT_SUBSET, cond_STAR,
    EMPTY_SUBSET, IN_toy2set, GSYM DELETE_DEF]
  \\ rpt strip_tac \\ eq_tac \\ rw [] \\ fs []);

val tFlags_HIDE = store_thm("tFlags_HIDE",
  ``~tFlags = ~tFlag ZF * ~tFlag SF``,
  SIMP_TAC std_ss [SEP_HIDE_def,tFlag_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS,tFlag_def,EXISTS_PROD,Flags_def]);

val TOY_SPEC_CODE =
  SPEC_CODE |> ISPEC ``TOY_MODEL``
  |> SIMP_RULE std_ss [TOY_MODEL_def]
  |> RW [GSYM TOY_MODEL_def]
  |> Q.SPECL [`p`,`{(a,x)}`,`q`] |> GSYM
  |> SIMP_RULE std_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_SING,
        TOY_INSTR_def,GSYM (RW [SEP_EQ_def] tInst_def),TOY_SPEC_SEMANTICS]

val IMP_TOY_SPEC_LEMMA = prove(
  ``!a x p q.
      (!rs pc is rg fl cc s.
        (tInst a (SOME x) * p * emp) (toy2set' (rs,pc,is,rg,fl,cc) s) ==>
        (tInst a (SOME x) * q * emp) (toy2set' (rs,pc,is,rg,fl,cc) (step s)) /\
        (toy2set'' (rs,pc,is,rg,fl,cc) s =
         toy2set'' (rs,pc,is,rg,fl,cc) (step s))) ==>
      SPEC TOY_MODEL p {(a,x)} q``,
  fs [TOY_SPEC_CODE,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [RIGHT_EXISTS_IMP_THM] \\ REWRITE_TAC [TOY_SPEC_SEMANTICS]
  \\ rpt strip_tac
  \\ PairCases_on `y` \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,TOY_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC [PAIR,optionTheory.SOME_11]);

val PC_def = Define `TOY_PC p = tPC p * tRunstate RUNNING`;
val _ = overload_on("PC",``TOY_PC``)

val SOME_EQ_toy_read_inst_IFF = prove(
  ``SOME x = toy_read_inst s.pc s <=>
    s.pc < LENGTH s.instructions /\ EL s.pc s.instructions = x``,
  fs [toy_read_inst_def]);

val IS_SOME_EQ = prove(
  ``IS_SOME x <=> ?b. x = SOME b``,
  Cases_on `x` \\ fs []);

(* MOV *)

val MOV_CNST = store_thm("MOV_CNST",
  ``SPEC TOY_MODEL
      (PC p * tReg r w * tFlag ZF zf * tFlag SF n)
      {(p,MOV r (CNST v))}
      (PC (p+1) * tReg r v * tFlag ZF (v = 0w) * tFlag SF (word_msb v))``,
  match_mp_tac IMP_TOY_SPEC_LEMMA
  \\ fs [GSYM STAR_ASSOC,STAR_toy2set,PC_def]
  \\ fs [emp_def] \\ rw []
  \\ fs [step_def,SOME_EQ_toy_read_inst_IFF]
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,
         flag_update_def,eval_regc_def,APPLY_UPDATE_THM]
  THEN1 (Cases_on `r` \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC)
  \\ simp [EXTENSION]
  \\ Cases
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,flag_update_def,
         eval_regc_def]
  THEN1 (Cases_on `c` \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC
         \\ rw [] \\ fs [])
  \\ Cases_on `f` \\ fs [APPLY_UPDATE_THM] \\ rw []);

val MOV_REG = store_thm("MOV_REG",
  ``SPEC TOY_MODEL
      (PC p * tReg r w * tReg r1 v * tFlag ZF zf * tFlag SF n)
      {(p,MOV r (REG r1))}
      (PC (p+1) * tReg r v * tReg r1 v * tFlag ZF (v = 0w) * tFlag SF (word_msb v))``,
  match_mp_tac IMP_TOY_SPEC_LEMMA
  \\ fs [GSYM STAR_ASSOC,STAR_toy2set,PC_def]
  \\ fs [emp_def] \\ rw []
  \\ fs [step_def,SOME_EQ_toy_read_inst_IFF]
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,
         flag_update_def,eval_regc_def,APPLY_UPDATE_THM]
  THEN1 (Cases_on `r` \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC)
  THEN1 (Cases_on `r1` \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def])
  \\ simp [EXTENSION]
  \\ Cases
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,flag_update_def,
         eval_regc_def]
  THEN1 (Cases_on `c` \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC
         \\ rw [] \\ fs [])
  \\ Cases_on `f` \\ fs [APPLY_UPDATE_THM] \\ rw []);

(* ILOAD *)

val ILOAD = store_thm("ILOAD",
  ``SPEC TOY_MODEL
      (PC p * tReg a0 r0 * tReg a1 r1 * tContext mload mstore ctxt *
       cond (IS_SOME (mload r1 ctxt)))
      {(p,ILOAD a0 a1)}
      (PC (p+1) * tReg a0 (FST (THE (mload r1 ctxt))) * tReg a1 r1 *
       tContext mload mstore (SND (THE (mload r1 ctxt))))``,
  fs [SPEC_MOVE_COND] \\ strip_tac
  \\ match_mp_tac IMP_TOY_SPEC_LEMMA
  \\ fs [GSYM STAR_ASSOC,STAR_toy2set,PC_def]
  \\ fs [emp_def] \\ rw []
  \\ fs [step_def,SOME_EQ_toy_read_inst_IFF]
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,
         flag_update_def,eval_regc_def,APPLY_UPDATE_THM,IS_SOME_EQ]
  \\ TRY (PairCases_on `b` \\ fs [])
  THEN1 (Cases_on `a0`
     \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC)
  THEN1 (Cases_on `a1` \\ Cases_on `a0`
     \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC)
  \\ simp [EXTENSION]
  \\ Cases
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,flag_update_def,
         eval_regc_def]
  \\ Cases_on `c` \\ Cases_on `a0`
  \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC
  \\ rw [] \\ fs [])

val ILOAD' = store_thm("ILOAD'",
  ``SPEC TOY_MODEL
      (PC p * tReg a0 r0 * tContext mload mstore ctxt *
       cond (IS_SOME (mload r0 ctxt)))
      {(p,ILOAD a0 a0)}
      (PC (p+1) * tReg a0 (FST (THE (mload r0 ctxt))) *
       tContext mload mstore (SND (THE (mload r0 ctxt))))``,
  fs [SPEC_MOVE_COND] \\ strip_tac
  \\ match_mp_tac IMP_TOY_SPEC_LEMMA
  \\ fs [GSYM STAR_ASSOC,STAR_toy2set,PC_def]
  \\ fs [emp_def] \\ rw []
  \\ fs [step_def,SOME_EQ_toy_read_inst_IFF]
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,
         flag_update_def,eval_regc_def,APPLY_UPDATE_THM,IS_SOME_EQ]
  \\ TRY (PairCases_on `b` \\ fs [])
  THEN1 (Cases_on `a0`
     \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC)
  \\ simp [EXTENSION]
  \\ Cases
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,flag_update_def,
         eval_regc_def]
  \\ Cases_on `c` \\ Cases_on `a0`
  \\ fs [fcpTheory.FCP_BETA,fcpTheory.FCP_UPDATE_def] \\ EVAL_TAC
  \\ rw [] \\ fs []);

(* ISTORE *)

val ISTORE = store_thm("ISTORE",
  ``SPEC TOY_MODEL
      (PC p * tReg a0 r0 * tReg a1 r1 * tContext mload mstore ctxt *
       cond (IS_SOME (mstore r0 r1 ctxt)))
      {(p,ISTORE a1 a0)}
      (PC (p+1) * tReg a0 r0 * tReg a1 r1 *
       tContext mload mstore (THE (mstore r0 r1 ctxt)))``,
  fs [SPEC_MOVE_COND] \\ strip_tac
  \\ match_mp_tac IMP_TOY_SPEC_LEMMA
  \\ fs [GSYM STAR_ASSOC,STAR_toy2set,PC_def]
  \\ fs [emp_def] \\ rw []
  \\ fs [step_def,SOME_EQ_toy_read_inst_IFF]
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,
         flag_update_def,eval_regc_def,APPLY_UPDATE_THM,IS_SOME_EQ]
  \\ simp [EXTENSION] \\ Cases
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,flag_update_def,
         eval_regc_def]);

val ISTORE' = store_thm("ISTORE'",
  ``SPEC TOY_MODEL
      (PC p * tReg a0 r0 * tContext mload mstore ctxt *
       cond (IS_SOME (mstore r0 r0 ctxt)))
      {(p,ISTORE a0 a0)}
      (PC (p+1) * tReg a0 r0 *
       tContext mload mstore (THE (mstore r0 r0 ctxt)))``,
  fs [SPEC_MOVE_COND] \\ strip_tac
  \\ match_mp_tac IMP_TOY_SPEC_LEMMA
  \\ fs [GSYM STAR_ASSOC,STAR_toy2set,PC_def]
  \\ fs [emp_def] \\ rw []
  \\ fs [step_def,SOME_EQ_toy_read_inst_IFF]
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,
         flag_update_def,eval_regc_def,APPLY_UPDATE_THM,IS_SOME_EQ]
  \\ simp [EXTENSION] \\ Cases
  \\ fs [toy_read_inst_def,toy_read_reg_def,toy_read_flag_def,flag_update_def,
         eval_regc_def]);

val _ = export_theory();
