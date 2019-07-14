structure HermesOptimizer :> HermesOptimizer =
struct
  open Hermes

  (* Utility functions. *)
  fun except l1 l2 = List.filter (fn x => not (List.exists (fn y => x = y) l2)) l1
  fun contains n xs = List.exists (fn x => x = n) xs

  fun unpackOptions ((SOME s)::xs) = s :: unpackOptions xs
    | unpackOptions (NONE::xs) = unpackOptions xs
    | unpackOptions [] = []

  fun unpackOption (SOME s) = s
    | unpackOption NONE = Skip

  (* Mask out anything but constant parameter declarations from function
     declarations. *)
  fun makeConstParamMask decls =
    let
      fun inner (ConstParDecl _) = 1
        | inner (ConstArrayParDecl _) = 1
        | inner _ = 0
    in
      List.map inner decls
    end

  (* Retrieve all variables occuring in expression. *)
  fun getLvsFromExp exp =
    case exp of
      Rval (Array (n, e, pos)) => [Array (n, e, pos)] @ (getLvsFromExp e)
    | Rval lv => [lv]
    | Const (s, pos) => []
    | Bin (binOp, e1, e2, pos) => (getLvsFromExp e1) @ (getLvsFromExp e2) 
    | Un (unOp, e, pos) => getLvsFromExp exp

  (* Retrieve non-root variables from lVal. *)
  fun getNonRootFromLval (Var _) = []
    | getNonRootFromLval (Array (_, e, _)) = getLvsFromExp e

  fun getNonRootFromLvals lvs = List.foldl (fn (lv,acc) => acc @
    (getNonRootFromLval lv)) [] lvs

  fun getNameFromDecl (VarDecl (n, _, _)) = n
    | getNameFromDecl (ConstDecl (n, _, _, _)) = n
    | getNameFromDecl (ConstParDecl (n, _, _)) = n
    | getNameFromDecl (ConstArrayParDecl (n, _, _, _)) = n
    | getNameFromDecl (ArrayDecl (n, _, _, _)) = n

  (* Retrieve name of root variable from lVal. *)
  fun getNameFromLval (Var (n, _)) = n
    | getNameFromLval (Array (n, _, _)) = n

  fun isLive lv live = contains (getNameFromLval lv) live

  (* Add a variable to the live set if it is not in there already. *)
  fun addToLive lv live = if isLive lv live then live else (getNameFromLval lv) :: live

  fun addnToLive lvs live = List.foldl (fn (lv,acc) => addToLive lv acc) live lvs

  fun filterDecls ds deadDs =
    List.filter (fn d => not (List.exists (fn n => n = getNameFromDecl d) deadDs)) ds

  (* An optimized loop body is redundant if it only contains updates to 
     loop variables or skips. Thus, we only need to check root variables. *)
  fun loopBodyIsRedundant _ NONE = true
    | loopBodyIsRedundant is (SOME s) =
    case s of
      Skip => true
    | Update (updateOp, lv, exp, pos) => contains (getNameFromLval lv) is
    | Inc (lv, pos) => contains (getNameFromLval lv) is
    | Dec (lv, pos) => contains (getNameFromLval lv) is
    | Block (ds, ss, pos) =>
        let
          val shadowed = List.exists 
                           (fn d => contains (getNameFromDecl d) is) ds
        in
          (not shadowed) andalso (List.all (fn x => loopBodyIsRedundant is (SOME x)) ss)
        end
    | For (i',e1,e2,s',pos) =>
        (* if i' shadows a variable in is then the shadowed loop variable
           cannot be updated in s'. In any case, we must check that only loop
           variables are updated. *)
        loopBodyIsRedundant (i'::is) (SOME s')
    | _ => false

  fun containsIO (Block (_, ss, _)) = List.exists containsIO ss
    | containsIO (For (_, _, _, s, _)) = containsIO s
    | containsIO (Printf _) = true
    | containsIO (Scanf _) = true
    | containsIO _ = false

  (* Remove updates targeted towards zeroing local variables. I.e. updates that
     occur after the final time a local variables has been used to update an
     actual argument or another local variable later used in updating an actual
     argument. *)
  fun optimizeStat s live ftab =
    case s of
      Skip => (SOME s, live)
    | Update (updateOp, lv, exp, pos) =>
        if isLive lv live then
          let
            val live' = List.foldl (fn (lv, acc) => addToLive lv acc)
            live (getLvsFromExp exp)
            val live'' = addnToLive (getNonRootFromLval lv) live'
          in
            (SOME (Update (updateOp, lv, exp, pos)), live'')
          end
        else (NONE, live)
    | CondUpdate (cexp, updateOp, lv, exp, pos) =>
        if isLive lv live then
          let
            val live' = List.foldl (fn (lv, acc) => addToLive lv acc) 
            live ((getLvsFromExp cexp) @ (getLvsFromExp exp))
            val live'' = addnToLive (getNonRootFromLval lv) live'
          in
            (SOME (Update (updateOp, lv, exp, pos)), live'')
          end
        else (NONE, live)
    | Inc (lv, pos) => if (isLive lv live) then (SOME s, addnToLive (getNonRootFromLval lv) live) else (NONE, live)
    | Dec (lv, pos) => if (isLive lv live) then (SOME s, addnToLive (getNonRootFromLval lv) live) else (NONE, live)
    | Swap (lv1, lv2, pos) => 
        if ((isLive lv1 live) orelse (isLive lv2 live)) then
        (SOME s, addnToLive ((getNonRootFromLvals [lv1, lv2]) @ [lv1, lv2]) live)
        else (NONE, live)
    | CondSwap (cexp, lv1, lv2, pos) =>
        if ((isLive lv1 live) orelse (isLive lv2 live)) then
        (SOME s, addnToLive ((getLvsFromExp cexp) @ [lv1, lv2] @ (getNonRootFromLvals [lv1, lv2])) live)
        else (NONE, live)
    (* Optimize the statements bottom-up.
       Live variables after optimizing the block are given by:
       live-after := live-before U (live-after - variables-shadowed-in-block) *)
    | Block (ds, ss, pos) =>
        let
          val blockLvs = List.map getNameFromDecl ds
          val liveInBlock = except live blockLvs
          val (optStats, live') = 
            List.foldr (fn (s, (oss, l)) => 
            let
              val (os, l') = optimizeStat s l ftab
            in
              (os :: oss, l')
            end) ([], liveInBlock) ss
          val liveAfterOpt = 
            List.foldl 
            (fn (lv, acc) => if contains lv acc then acc else lv :: acc) 
            live (except live' blockLvs)
          val optDs = filterDecls ds (except blockLvs live')
        in
          if List.all (fn x => x = NONE orelse x = (SOME Skip)) optStats 
          then (NONE, liveAfterOpt)
          else 
            (SOME (Block (optDs, unpackOptions optStats, pos)), liveAfterOpt)
        end
    (* Variables used in initial and final expressions are live before the
       loop. The iteration variable might shadow local variables or parameters,
       and is live only while executing the loop. Variables alive at any point
       in the loop cannot be optimized away. *)
    | For (i,e1,e2,s',pos) =>
        let
          val (_, live') = optimizeStat s' (i :: live) ftab
          val (optStat, live'') = optimizeStat s' live' ftab
          val liveAfterOpt = 
            if contains i live then live''
            else (List.filter (fn x => x <> i) live'')
        in
          (* Check if loop body is redundant *)
          if loopBodyIsRedundant [i] optStat then (NONE, liveAfterOpt)
          else
            (SOME (For (i, e1, e2, unpackOption optStat, pos)), liveAfterOpt) 
        end
    (* If all arguments are constant or not live, the call can be optimized
       away. Otherwise, all arguments in the call are added to the live list. *)
    | Call (f,lvs,pos) =>
        let 
          val (body, mask) = valOf (SymTab.lookup f ftab)
          val (_,lvs') = ListPair.unzip (List.filter (fn (b,lv) => b = 0)
          (ListPair.zip (mask, lvs)))
          val live' = addnToLive (lvs @ (getNonRootFromLvals lvs)) live
        in
          if List.all (fn lv => not (isLive lv live)) lvs' andalso 
          not (containsIO body) then (NONE, live)
          else (SOME (Call (f,lvs,pos)), live')
        end
    | Uncall (f,lvs,pos) => 
        let 
          val (body, mask) = valOf (SymTab.lookup f ftab)
          val (_,lvs') = ListPair.unzip (List.filter (fn (b,lv) => b = 0)
          (ListPair.zip (mask, lvs)))
          val live' = addnToLive (lvs @ (getNonRootFromLvals lvs)) live
        in
          if List.all (fn lv => not (isLive lv live)) lvs' andalso
          not (containsIO body) then (NONE, live)
          else (SOME (Uncall (f,lvs,pos)), live')
        end
    (* Printf and Scanf have side-effects and, hence, cannot be optimized and
       the variables used are live. *)
    | Printf (str,lvs,pos) => 
        let
          val live' = addnToLive (lvs @ (getNonRootFromLvals lvs)) live
        in
          (SOME (Printf (str,lvs,pos)), live')
        end
    | Scanf (str,lvs,pos) =>
        let
          val live' = addnToLive (lvs @ (getNonRootFromLvals lvs)) live
        in
          (SOME (Scanf (str,lvs,pos)), live')
        end
    (* Assertions are removed in optimized code. *)
    | Assert (c,p) => (NONE, live)

  (* build symbol table that maps function names to names of constant parameters. *)
  fun makeFtab [] = SymTab.empty ()
    | makeFtab (f :: fs) =
        let
          val ftab = makeFtab fs
          val (name, decls, stat, pos) = f
          val mask = makeConstParamMask decls
        in
          SymTab.bind name (stat, mask) ftab
        end

  (* Extract parameters, tag as live variables and optimize function body. *)
  fun optimizeProc (name, decls, stat, pos) ftab = 
    let 
      val (optStat, _) = optimizeStat stat (List.map getNameFromDecl decls) ftab
    in
      (name, decls, unpackOption optStat, pos)
    end

  fun optimizeProgram (fs : program) = 
    let val ftab = makeFtab fs in List.map (fn f => optimizeProc f ftab) fs end

end
