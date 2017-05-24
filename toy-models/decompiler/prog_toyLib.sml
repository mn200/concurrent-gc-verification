structure prog_toyLib :> prog_toyLib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory prog_toyTheory helperLib wordsTheory progTheory
     finite_mapTheory decompilerLib;

val toy_status = tFlags_HIDE;
val toy_pc = ``PC``;
fun toy_jump tm1 tm2 jump_length forward = ("",1)

val lemmas = [ILOAD',ILOAD,ISTORE',ISTORE,MOV_CNST,MOV_REG]

fun toy_spec s = let
  val tm = Term [QUOTE s]
  (* find right lemma *)
  fun inst_lemma lemma = let
    val pat = lemma |> concl |> rator |> rand |> rator |> rand |> rand
    val i = fst (match_term pat tm)
    in INST i lemma end
  val th = inst_lemma (first (can inst_lemma) lemmas)
  (* fix reg names *)
  val tms = find_terms (can (match_term ``tReg x y``)) (concl th |> rator)
  fun renamer tm = let
    val y = rand tm
    val x = rator tm |> rand |> rand |> numSyntax.int_of_term |> int_to_string
    in y |-> mk_var("r" ^ x,type_of y) end
  val th = INST (map renamer tms) th
  in ((th,1,SOME 1),NONE) end

val toy_tools =
  ((toy_spec, toy_jump, toy_status, toy_pc):decompiler_tools);

fun custom_set_pc i th =
  INST [mk_var("p",``:num``) |-> ``p + ^(numSyntax.term_of_int i)``]
    (th |> SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC])

val _ = (decompiler_set_pc := custom_set_pc);

val q = helperLib.quote_to_strings
val tools = toy_tools
val name = "test"
val code = `
  ILOAD 1w 2w
  MOV 2w (CNST 2w)
`

(*
  decompile tools name code
*)


(*

  toy_spec "ILOAD 2w 3w"
  toy_spec "ILOAD 3w 3w"
  toy_spec "ISTORE 1w 2w"
  toy_spec "MOV 1w (REG 2w)"
  toy_spec "MOV 1w (CNST 2w)"

*)

end
