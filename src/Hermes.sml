structure Hermes =
struct

  (* types for abstract syntax for Hermes *)

  type pos = int * int  (* position: line, column *)

  datatype binOp
    = Plus | Minus | Times | Divide | Modulo
    | Xor | BAnd | BOr | ShiftL | ShiftR
    | Equal | Less | Greater | Neq | Leq | Geq

  datatype unOp = Uminus | Negate

  datatype updateOp = Add | Sub | XorWith | RoL | RoR

  datatype lVal
    = Var of string * pos
    | Array of string * exp * pos

  and exp
    = Rval of lVal
    | Const of string * pos
    | Bin of binOp * exp * exp * pos
    | Un of unOp * exp * pos
 
  datatype typ
    = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64

  (* Simpler, tagged union type for type checking, that still allow checking
     for implicit casts (e.g. from pointer to integer in function call). The
     addition of a loop variable type also makes type checking much more
     elegant. *)
  datatype tVar
    = A of typ (* array variable *)
    | C of string * typ (* constant variable or parameter *)
    | V of typ (* integer variable *)
    | N (* numerical constant *)
    | L (* loop variable *)

  datatype decl
    = VarDecl of string * typ * pos
    | ConstDecl of string * string * typ * pos
    | ConstParDecl of string * typ * pos
    | ConstArrayParDecl of string * string * typ * pos
    | ArrayDecl of string * string * typ * pos

  datatype stat
    = Skip
    | Update of updateOp * lVal * exp * pos
    | CondUpdate of exp * updateOp * lVal * exp * pos
    | Inc of lVal * pos
    | Dec of lVal * pos
    | Swap of lVal * lVal * pos
    | CondSwap of exp * lVal * lVal * pos
    | Block of decl list * stat list * pos
    | For of string * exp * exp * stat * pos (* update is part of body *)
    | Call of string * lVal list * pos
    | Uncall of string * lVal list * pos
    | Printf of string * lVal list * pos
    | Scanf of string * lVal list * pos
    | Assert of exp * pos

  type procedure = string * decl list * stat * pos

  type program = procedure list

(* printing syntax *)

  fun showBinOp Plus = " + "
    | showBinOp Minus = " - "
    | showBinOp Times = " * "
    | showBinOp Divide = " / "
    | showBinOp Modulo = " % "
    | showBinOp Xor = " ^ "
    | showBinOp BAnd = " & "
    | showBinOp BOr  = " | "
    | showBinOp ShiftL = " << "
    | showBinOp ShiftR = " >> "
    | showBinOp Equal = " == "
    | showBinOp Less = " < "
    | showBinOp Greater = " > "
    | showBinOp Neq = " != "
    | showBinOp Leq = " <= "
    | showBinOp Geq = " >= "

  fun showUnOp Uminus = " -"
    | showUnOp Negate = " ~"

  fun showUpdateOp Add = " += "
    | showUpdateOp Sub = " -= "
    | showUpdateOp XorWith = " ^= "
    | showUpdateOp RoL = " <<= "
    | showUpdateOp RoR = " >>= "

  fun showLVal (Var (x,p)) = x
    | showLVal (Array (x,e,p)) = x ^ "[" ^ showExp e false ^ "]"

  and showLVals ls = String.concat (List.map (fn x => showLVal x ^ ", ") ls)

  (* 2nd argument tells whether parens are needed for compund expressions *)
  and showExp (Rval l) _ = showLVal l
    | showExp (Const (s,p)) _ = s
    | showExp (Bin (bop, e1, e2, p)) true =
         "(" ^ showExp e1 true ^ showBinOp bop ^ showExp e2 true ^ ")"
    | showExp (Bin (bop, e1, e2, p)) false =
         showExp e1 true ^ showBinOp bop ^ showExp e2 true
    | showExp (Un (uop, e1, p)) true =
         "(" ^ showUnOp uop ^ showExp e1 true ^ ")"
    | showExp (Un (uop, e1, p)) false =
         showUnOp uop ^ showExp e1 true

  fun showType I8 = "i8 "
    | showType U8 = "u8 "
    | showType I16 = "i16 "
    | showType U16 = "u16 "
    | showType I32 = "i32 "
    | showType U32 = "u32 "
    | showType I64 = "i64 "
    | showType U64 = "u64 "

  (* for type checker *)
  fun showTVar (A t) = showType t ^ "array."
    | showTVar (C ("",t)) = showType t ^ "constant param."
    | showTVar (C ("array",t)) = showType t ^ "constant array param."
    | showTVar (C (v,t)) = showType t ^ "constant."
    | showTVar (V t) = showType t ^ "variable."
    | showTVar (N) = "numerical constant."
    | showTVar (L) = "loop variable."

  fun showDecl (VarDecl (x,t,p)) = showType t ^ x
    | showDecl (ConstDecl (x,v,t,p)) =
        "const " ^ showType t ^ x ^ " = " ^ v
    | showDecl (ConstParDecl (x,t,p)) =
        "const " ^ showType t ^ x
    | showDecl (ConstArrayParDecl (x,s,t,p)) = 
        "const " ^ showType t ^ x ^ "[" ^ s ^ "]"
    | showDecl (ArrayDecl (x,s,t,p)) =
        showType t ^ x ^ "[" ^ s ^ "]"

  fun showStat Skip = ";"
    | showStat (Update (uop, lv, e, p)) =
         showLVal lv ^ showUpdateOp uop ^ showExp e false ^ ";\n"
    | showStat (CondUpdate (exp, uop, lv, e, p)) =
         "if (" ^ showExp exp false ^ ") " ^
         showLVal lv ^ showUpdateOp uop ^ showExp e false ^ ";\n"
    | showStat (Inc (lv, p)) = showLVal lv ^ "++;\n"
    | showStat (Dec (lv, p)) = showLVal lv ^ "--;\n"
    | showStat (Swap (lv1, lv2, p)) =
         showLVal lv1 ^ " <-> " ^ showLVal lv2 ^ ";\n"
    | showStat (CondSwap (exp, lv1, lv2, p)) =
         "if (" ^ showExp exp false ^ ") " ^
         showLVal lv1 ^ " <-> " ^ showLVal lv2 ^ ";\n"
    | showStat (Block (ds, ss, p)) =
         "{\n" ^
         String.concat (List.map (fn d => showDecl d ^ ";\n") ds) ^
         String.concat (List.map showStat ss) ^
         "}\n"
    | showStat (For (x, e1, e2, s, p)) =
         "for (" ^ x ^ " = " ^ showExp e1 false ^ ";" ^
         showExp e2 false ^ ")\n" ^ showStat s
    | showStat (Call (f, xs, p)) =
         "call " ^ f ^ "(" ^
         let
           val args = String.concat (List.map (fn x => showLVal x ^ ", ") xs)
         in
           String.substring (args, 0, String.size args - 2)
         end ^ ");\n"
    | showStat (Uncall (f, xs, p)) =
         "uncall " ^ f ^ "(" ^
         let
           val args = showLVals xs
         in
           String.substring (args, 0, String.size args - 2)
         end ^ ");\n"
    | showStat (Printf (format, ls, pos)) =
         "printf(" ^ String.toCString format ^ ", " ^ showLVals ls ^ ");\n"
    | showStat (Scanf (format, ls, pos)) =
         "scanf(" ^ String.toCString format ^ ", " ^ showLVals ls ^ ");\n"
    | showStat (Assert (e, pos)) =
         "assert(" ^ showExp e false ^ ");\n"

  fun showProcedure (f, ds, s, p) =
         f ^ "(" ^
         let
           val args = String.concat (List.map (fn d => showDecl d ^ ", ") ds)
         in
           if args = "" then ""
           else String.substring (args, 0, String.size args - 2)
         end ^ ")\n" ^ showStat s ^ "\n"

  fun showProgram ps =
         String.concat (List.map showProcedure ps)

end
