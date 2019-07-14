structure HermesStaticAnalysis :> HermesStaticAnalysis =
struct
  open Hermes

  exception Error of string * (int * int)

  (* Get id and type pair from declaration *)
  (* Constant parameters are treated locally as constant declarations. *)
  fun getType (VarDecl (n, t, _)) = (n, V t)
    | getType (ConstDecl (n, v, t, _)) = (n, C (v, t))
    | getType (ConstParDecl (n, t, _)) = (n, C ("", t)) 
    | getType (ConstArrayParDecl (n, _, t, _)) = (n, C ("array", t)) 
    | getType (ArrayDecl (n, _, t, _)) = (n, A t)

  (* generate id and type pair list from a list of declarations *)
  fun getTypes decls = List.map (fn decl => getType decl) decls

  (* matches a formal paramter to an actual parameter *)
  fun paramTypesMatch (C ("", t)) (C (v, t)) = v <> "array"
    | paramTypesMatch (C ("", t)) (V t) = true
    | paramTypesMatch (C ("", t)) L = true
    | paramTypesMatch (C ("array", t)) (A t) = true
    | paramTypesMatch x y = x = y
 
  fun getNameFromLval (Var (n, _)) = n
    | getNameFromLval (Array (n, _, _)) = n

  fun getPosFromLval (Var (_, pos)) = pos
    | getPosFromLval (Array (_, _, pos)) = pos

  fun isArray (A t) = true
    | isArray (C ("array", t)) = true
    | isArray tv = false

  fun isLoopVar L = true
    | isLoopVar v = false

  fun isConstVar (C (_,_)) = true
    | isConstVar N = true
    | isConstVar v = false

  fun isConstParam (C ("",_)) = true
    | isConstParam (C ("array",_)) = true
    | isConstParam _ = false

  (* check if name n occurs in expression e *)
  fun occursInExp e n =
    case e of
      Rval lv => occursInLval lv n
    | Const (s, pos) => false
    | Bin (binOp, e1, e2, pos) => (occursInExp e1 n) orelse (occursInExp e2 n)
    | Un (unOp, e, pos) => occursInExp e n

  and occursInLval (Var (n', pos)) n = (n = n')
    | occursInLval (Array (n',e,pos)) n = (n = n') orelse occursInExp e n

  (* check if lv is indexed by n *)
  fun indexedBy (Var (n', pos)) n = false
    | indexedBy (Array (n', e, pos)) n = occursInExp e n
 
  (* extract names of variables from current scope that are updated in s *)
  fun updatedInStat s =
    case s of
      Skip => []
    | Update (updateOp, lv, exp, pos) => [getNameFromLval lv]
    | CondUpdate (cexp, updateOp, lv, exp, pos) => [getNameFromLval lv]
    | Inc (lv, pos) => [getNameFromLval lv]
    | Dec (lv, pos) => [getNameFromLval lv]
    | Swap (lv1, lv2, pos) => [getNameFromLval lv1, getNameFromLval lv2]
    | CondSwap (cexp, lv1, lv2, pos) => [getNameFromLval lv1, getNameFromLval lv2]
    | Block (ds, ss, pos) =>
        let
          val updated = List.concat (List.map updatedInStat ss)
          val declared = List.map (fn (n, t) => n) (getTypes ds)
        in
          (* updated - declared *) 
          List.filter
            (fn x => not (List.exists (fn y => x=y) declared))
            updated
        end
    | For (i,e1,e2,s,pos) => updatedInStat s
    | Call (f,lvs,pos) => List.map getNameFromLval lvs
    | Uncall (f,lvs,pos) => List.map getNameFromLval lvs
    | Printf (str,lvs,pos) => List.map getNameFromLval lvs
    | Scanf (str,lvs,pos) => List.map getNameFromLval lvs
    | Assert (c,p) => []

  (* check type of local variable *)
  fun checkLval vtab ftab lv =
      (case SymTab.lookup (getNameFromLval lv) vtab of
         NONE => raise Error ("use of undeclared local variable",
         getPosFromLval lv)
       | SOME L => L
       | SOME (A t) => (* name refers to array declaration *)
           (case lv of
            (* lv := a *)
              Var (_, _) => A t
            (* lv := a[exp]. So check the exp, verifying it is not of array
               type, and return type of element *)
            | Array (_, e, _) => 
                (case checkExp vtab ftab e of
                   A _ => raise Error ("Index expression is an array",
                   getPosFromLval lv)
                 | C ("array",_) => raise Error ("Index expression is an array",
                   getPosFromLval lv)
                 | _ => V t))
       | SOME (C ("array", t)) => (* name refers to constant array parameter *)
           (case lv of
            (* lv := a *)
              Var (_, _) => C ("array", t)
            (* lv := a[exp]. So check the exp, verifying it is not of array
               type, and return type of element. *)
            | Array (_, e, _) => 
                (case checkExp vtab ftab e of
                   A _ => raise Error ("Index expression is an array",
                   getPosFromLval lv)
                 | C ("array",_) => raise Error ("Index expression is an array",
                   getPosFromLval lv)
                 | _ => C ("", t)))
       (* name refers to variable declaration *)
       | SOME tv => 
           (case lv of
              Array (n, _, pos) => 
              let val _ = print(showTVar tv ^ "\n") in raise Error (n ^ " is not an array", pos) end
            | _ => tv))

  and checkExp vtab ftab exp =
    case exp of
      Rval lv => checkLval vtab ftab lv
    (* Constants return dummy type since their type is inferred *)
    | Const (s, pos) => N
    (* do not allow binary operations on array variables. Allow binary
    * operations on any integer type *)
    | Bin (binOp, e1, e2, pos) => 
        let
          val t1 = checkExp vtab ftab e1
          val t2 = checkExp vtab ftab e2
        in
          (case (t1, t2) of
             (A t, _) => 
               raise Error ("First operand of binary operation is array", pos)
           | (_, A t) => 
               raise Error ("Second operand in binary operation is array", pos)
           | (C ("array",t), _) => 
               raise Error ("First operand of binary operation is array", pos)
           | (_, C ("array",t)) => 
               raise Error ("Second operand in binary operation is array", pos)
             (* case (N, C t) and (C t, N) will infer the type to be C t *)
           |  (N , t) => t (* C will infer correct type for the constant *)
           | (t, N)  => t
           | (C _, V _) => t2
           | (V _, C _) => t1
           | (C _, L) => t2
           | (L, C _) => t1
           | _  => t1)
        end
    | Un (unOp, e, pos) => checkExp vtab ftab e

  (* get value of constant variable or numeric constant *)
  fun getNumConst vtab (Const (x, _)) = SOME x
    | getNumConst vtab (Rval lv) =
        (case SymTab.lookup (getNameFromLval lv) vtab of
          SOME (C (v, _)) => SOME v
        | _ => NONE)
    | getNumConst _ _ = NONE

  (* Checks if 
     1. Two lvars are aliased.
     2. If an array is passed, the root variable cannot occur again in the list.
     3. If an array is indexed with a numerical constant index, all other
      entries to the same array must be constantly indexed with a different
      constant.
     4. If an array is indexed with a non numerical constant, then no more
     entries from the same array can be passed E.g. f(n, v[n[1]], v[3]) is not
     allowed since v[n[1]] is indexed with non numerical constant. f(n j[n[1]],
     v[3]) and f(x, j[n[1]], v[3]) are allowed. *)
  fun isAlias vtab ftab (Var (n1, _)) (Var (n2, _)) = n1 = n2
    | isAlias vtab ftab (Array (n1, e1, _)) (Array (n2, e2, _)) =
        (case (getNumConst vtab e1, getNumConst vtab e2) of
        (* both indexes are numerical constants, we compare them *)
          (SOME x, SOME y) => n1 = n2 andalso x = y
        (* at least one index is not a numerical constant, so no other
           argument can have the same rootvar *)
        | _ => n1 = n2)
    | isAlias vtab ftab lv1 lv2 = (getNameFromLval lv1) = (getNameFromLval lv2)

  (* checks for aliasing in actual parameters if entries in the same array are
     passed, we require index expressions to be numerical constants *)
  fun containsAlias vtab ftab [] = false
    | containsAlias vtab ftab (x::xs) =
        List.exists (fn y => isAlias vtab ftab x y) xs
        orelse containsAlias vtab ftab xs

  fun checkStat vtab ftab stat =
    case stat of
      Skip => ()
    (* Only update integers by other integers or numerical constants. lv root
       variable is not allowed in exp, i.e. a := a[i] and a[a[i]] += 1 are not
       allowed, but a[i] += i is. Loop variables can only be updated with
       constant expressions. *)
    | Update (updateOp, lv, exp, pos) => 
        (case (checkLval vtab ftab lv, checkExp vtab ftab exp) of
           (L, N) => ()
         | (L, C (s,_)) => if s <> "" andalso s <> "array" then ()
                           else raise Error 
                           ("Loop variable updated with constant parameter",
                           pos)
         | (L, t) => 
             raise Error ("Loop variable updated with non-constant expression",
             pos)
         | (A _, _) => raise Error ("LHS is array type in update", pos)
         | (_, A _) => raise Error ("RHS is array type in update", pos)
         | (C (_,_), _) => raise Error ("LHS is constant type in update", pos)
         | _ =>
             if indexedBy lv (getNameFromLval lv) then
               raise Error ("LHS indexed with root variable", pos) 
             else if occursInExp exp (getNameFromLval lv) then 
               raise Error ("LHS root variable occurs in RHS expression", pos)
             else ())
    | CondUpdate (cexp, updateOp, lv, exp, pos) =>
        if checkLval vtab ftab lv = L then
          raise Error ("Loop variable conditionally updated", pos)
        else
          let
              val _ = checkExp vtab ftab cexp 
              val _ = checkStat vtab ftab (Update (updateOp, lv, exp, pos))
          in 
            (* verify that LHS root variable does not occur in condition *)
            if occursInExp cexp (getNameFromLval lv) then 
              raise Error ("conditional expression contains LHS root variable",
              pos)
            else ()
          end
    | Inc (lv, pos) => 
        (case checkLval vtab ftab lv of
           L => ()
         | V t => ()
         (* const or array variable *)
         | _ => raise Error ("type mismatch for increment", pos))
    | Dec (lv, pos) =>
        (case checkLval vtab ftab lv of
           L => ()
         | V t => ()
         | _ => raise Error ("type mismatch for decrement", pos))
    (* A swap is legal if both sides have the same type, neither are constants
       or loop variables, and no root variable occurs in any index expression.
       Whole arrays are not allowed to be swapped. *)
    | Swap (lv, rv, pos) =>
        (case (checkLval vtab ftab lv, checkLval vtab ftab rv) of
           (L, _) => raise Error ("Loop variable swapped", pos)
         | (_, L) => raise Error ("Loop variable swapped", pos)
         | (V t1, V t2) => 
             if t1 <> t2 then raise Error ("type mismatch in swap", pos)
             else if indexedBy lv (getNameFromLval lv) orelse 
             indexedBy lv (getNameFromLval rv) orelse 
             indexedBy rv (getNameFromLval rv) orelse
             indexedBy rv (getNameFromLval lv) then
               raise Error ("indexing with root variable in swap", pos)
             else ()
         | _ => raise Error ("swap operands are not variables or array" ^
         "elements", pos))
    | CondSwap (cexp, lv, rv, pos) =>
        let
          val _ = checkExp vtab ftab cexp
          val _ = checkStat vtab ftab (Swap (lv, rv, pos))
        in
          if occursInExp cexp (getNameFromLval lv) orelse
          occursInExp cexp (getNameFromLval rv) then
            raise Error ("conditional expression contains root variable", pos)
          else ()
        end
    (* add new declarations and recursively check statements *)
    | Block (ds, ss, pos) =>
      let
        fun bindDecl (n, t) vtab =
          if SymTab.lookup n vtab = NONE then
            SymTab.bind n t vtab
          else
            raise Error (n ^ "declared twice", pos)
        (* generate new variable symbol table s.t. new declarations shadows
           previous ones *)
        val vtab' = 
          List.foldl (fn (d, tab) => bindDecl d tab) (SymTab.empty ())
          (getTypes ds)
        val vtab'' = SymTab.combine vtab' vtab
        val _ = List.map (fn s => checkStat vtab'' ftab s) ss
      in
        ()
      end
    | For (i, iexp, fexp, s, pos) =>
        let
          val vtab' = SymTab.bind i L vtab (* i is inferred to be type V I32 *)
          val t1 = checkExp vtab' ftab iexp
          val t2 = checkExp vtab' ftab fexp
          val _ = checkStat vtab' ftab s
          val updated = updatedInStat s
        in
          (* iexp and fexp cannot be array type (not mentioned in Hermes
             article) *)
          if isArray t1 then
            raise Error ("initial expression cannot be an array", pos)
          else if isArray t2 then
            raise Error ("final expression cannot be an array", pos)
          (* iexp and fexp may only contain constant variables. This does not
             include constant parameters. *)
          else if (not (isConstVar t1)) orelse isConstParam t1 then
            raise Error ("initial expression contains iteration variable or " ^
            "variable updated in body or non constant variable", pos)
          else if (not (isConstVar t2)) orelse isConstParam t2 then
            raise Error ("final expression contains iteration variable or " ^
            "variable updated in body or non constant variable", pos)
          else ()
        end
    (* check for aliases and loop variables *)
    | Call (f, lvs, pos) =>
        (case SymTab.lookup f ftab of
           NONE => raise Error ("procedure " ^ f ^ " not declared", pos)
         | SOME formals =>
             let
               val fts = List.map (fn (n,t) => t) formals
               (* get types of actuals, ensuring that indexing is done with
                  numerical constants *)
               val ats = List.foldr 
               (fn (lv, acc) => (checkLval vtab ftab lv) :: acc) [] lvs
               val zipped = (ListPair.zip (fts,ats))
             in
               (* check for loop variables and verify that types of actual
                  parameters match formal parameters *)
               if (List.length fts <> List.length ats) orelse 
               not (List.all (fn (x,y) => paramTypesMatch x y) zipped) then
                   raise Error ("actual parameters to " ^ f ^ " does not match" ^
                   " formals", pos)
               (* check for aliased args *)
               else if containsAlias vtab ftab lvs then
                 raise Error ("aliased variables in call to " ^ f, pos)
               else ()
             end)
    (* can be checked as a call *)
    | Uncall (f, lvs, pos) => checkStat vtab ftab (Call (f, lvs, pos))
    (* only integer variables and array entries can be printed/scanned *)
    | Printf (str, lvs, pos) => 
        let 
          val ts = List.map (fn lv => checkLval vtab ftab lv) lvs
        in
          if List.exists isLoopVar ts then
            raise Error ("Loop variable printed or scanned", pos)
          else if List.exists isConstVar ts then
            raise Error ("Constant variable printed or scanned", pos)
          else if List.exists isArray ts then
            raise Error ("Array variable printed or scanned", pos)
          else ()
        end
    | Scanf (str, lvs, pos) => checkStat vtab ftab (Printf (str, lvs, pos))
    | Assert (cexp, pos) => let val _ = checkExp vtab ftab cexp in () end

  (* verify that parameter names are unique and check function body *)
  fun checkProc (name, decls, stat, pos) ftab =
    let
      (* adds a parameter to the variable symbol table *)
      fun bindParam (n, t) vtab =
        if SymTab.lookup n vtab = NONE then
          SymTab.bind n t vtab
        else
          raise Error ("Multiple definitions of parameter name " ^ n, pos)
      val vtab = 
        List.foldl (fn (d, tab) => bindParam d tab) (SymTab.empty ())
        (getTypes decls)
    in
      checkStat vtab ftab stat
    end

  (* Build function symbol table, checking for multiple declarations of the
     same parameter name. *)
  fun makeFtab [] = SymTab.empty ()
    | makeFtab (f :: fs) =
        let
          val ftab = makeFtab fs
          val (name, decls, stat, pos) = f
          val argtypes = getTypes decls
        in
          if SymTab.lookup name ftab = NONE then 
            (* procedure types are on the form ((t1,...,tn) -> unit), so we
               only have to store (t1,...,tn) *)
            SymTab.bind name argtypes ftab
          else 
            raise Error ("procedure " ^ name ^ "declared twice", pos)
        end

  (* begin static analysis from main *)
  fun checkProgram (fs : program) = 
    let
      val ftab = makeFtab fs
      val _ = List.map (fn f => checkProc f ftab) fs
    in
      case SymTab.lookup "main" ftab of
        SOME [] => () (* type checking was successful *)
      | SOME ts => 
          raise Error ("Main function cannot have arguments.", (0, 0))
      | NONE => raise Error ("Main function missing.", (0, 0))
    end

end
