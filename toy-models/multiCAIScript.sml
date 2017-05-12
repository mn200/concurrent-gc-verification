open HolKernel Parse boolLib bossLib;

open toycpuTheory llistTheory

val _ = new_theory "multiCAI";
  (* multiple CPUs, Concurrent Atomic Interleaving updates *)

val _ = Datatype`otherACT = OTHER_STORE word64 word64`
(* write word2 into address word1 *)

val _ = temp_type_abbrev ("multiCAI_oracle", ``:otherACT list llist``)

val _ = Datatype`multiCAI_ctxt = <| oracle : multiCAI_oracle ;
                                    mem : word64 -> word64 |>`

val apply_ACT_def = Define`
  apply_ACT (OTHER_STORE a v) c = c with mem updated_by (a =+ v)
`;

val multiCAI_mload_def = Define`
  multiCAI_mload a ctxt =
    case LTL_HD ctxt.oracle of
        SOME (rest, actions) =>
          let c' = FOLDL (λc a. apply_ACT a c) ctxt actions
          in
            SOME (c'.mem a, c' with oracle := rest)
      | NONE => (* oracle exhausted; everything else quiescent *)
          SOME (ctxt.mem a, ctxt)
`;

val multiCAI_mstore_def = Define`
  multiCAI_mstore a v ctxt = SOME (ctxt with mem updated_by (a =+ v))
`;

val list_repeat_def = zDefine`
  list_repeat l = if NULL l then [||]
                  else LUNFOLD (λn. SOME ((n + 1) MOD LENGTH l, EL n l)) 0
`;

val fromList_EQ_LNIL = Q.store_thm(
  "fromList_EQ_LNIL[simp]",
  `(fromList l = [||] <=> l = []) /\
   ([||] = fromList l <=> l = [])`,
  Cases_on `l` >> simp[]);

val LHD_fromList = Q.store_thm(
  "LHD_fromList",
  `LHD (fromList l) = case l of [] => NONE | h::t => SOME h`,
  Cases_on `l` >> simp[]);

val LNTH_list_repeat = Q.prove(
  `!m. ~NULL l /\ m < LENGTH l ==>
       (LNTH n (LUNFOLD (λn. SOME ((n + 1) MOD LENGTH l, EL n l)) m) =
        SOME (EL ((n + m) MOD LENGTH l) l))`,
  Induct_on `n` >> simp[Once LUNFOLD] >>
  simp[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD1]);

val list_repeat_thm = Q.store_thm(
  "list_repeat_thm",
  `list_repeat l = LAPPEND (fromList l) (list_repeat l)`,
  simp[LNTH_EQ, list_repeat_def] >>
  Cases_on `NULL l` >> simp[]
  >- (Cases_on `l` >> fs[]) >>
  `0 < LENGTH l` by (Cases_on `l` >> fs[]) >>
  simp[LNTH_list_repeat, LNTH_LAPPEND, LLENGTH_fromList] >> rw[]
  >- simp[LNTH_fromList] >>
  simp[arithmeticTheory.SUB_MOD]);

val LTL_HD_LAPPEND = Q.store_thm(
  "LTL_HD_LAPPEND",
  `LTL_HD (LAPPEND l1 l2) =
    case LTL_HD l1 of
      NONE => LTL_HD l2
    | SOME (t, h) => SOME (LAPPEND t l2, h)`,
  Cases_on `l1` >> simp[LTL_HD_LNIL, LTL_HD_LCONS]);

val LTL_HD_list_repeat = Q.store_thm(
  "LTL_HD_list_repeat[compute]",
  `LTL_HD (list_repeat l) =
     if NULL l then NONE
     else SOME (LAPPEND (fromList (TL l)) (list_repeat l), HD l)`,
  simp[Once list_repeat_thm, SimpLHS] >> rw[]
  >- (simp[list_repeat_def] >> Cases_on `l` >> fs[LTL_HD_LNIL]) >>
  simp[LTL_HD_LAPPEND] >> Cases_on `l` >> fs[LTL_HD_LCONS]);

(*
EVAL ``FUNPOW (step multiCAI_mload multiCAI_mstore) 3
              (state0 <| mem := (0w =+ 10w) (K 0w);
                         oracle := list_repeat [[OTHER_STORE 1w 20w;
                                                 OTHER_STORE 2w 30w]] |>
                      factprog)``
*)

val _ = export_theory();
