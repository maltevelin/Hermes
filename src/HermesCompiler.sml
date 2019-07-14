structure HermesCompiler :> HermesCompiler =
struct

  exception Error of string*(int*int)

  val fO = ref false
  val fZ = ref false

  fun concatWith [] s = ""
    | concatWith [x] s = x
    | concatWith (x :: xs) s = x ^ s ^ concatWith xs s

  fun compileType Hermes.I8 = "int8_t "
    | compileType Hermes.U8 = "uint8_t "
    | compileType Hermes.I16 = "int16_t "
    | compileType Hermes.U16 = "uint16_t "
    | compileType Hermes.I32 = "int32_t "
    | compileType Hermes.U32 = "uint32_t "
    | compileType Hermes.I64 = "int64_t "
    | compileType Hermes.U64 = "uint64_t "

  fun lookup x [] pos =
        raise Error ("undeclared variable " ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos

  fun invertUop Hermes.Add = Hermes.Sub
    | invertUop Hermes.Sub = Hermes.Add
    | invertUop Hermes.XorWith = Hermes.XorWith
    | invertUop Hermes.RoL = Hermes.RoR
    | invertUop Hermes.RoR = Hermes.RoL

  fun invertStat s =
    case s of
      Hermes.Skip => Hermes.Skip
    | Hermes.Update (uop, lv, exp, pos) =>
         Hermes.Update (invertUop uop, lv, exp, pos)
    | Hermes.CondUpdate (cond, uop, lv, exp, pos) =>
         Hermes.CondUpdate (cond, invertUop uop, lv, exp, pos)
    | Hermes.Inc lval => Hermes.Dec lval
    | Hermes.Dec lval => Hermes.Inc lval
    | Hermes.Swap lvals => Hermes.Swap lvals
    | Hermes.CondSwap condlvals => Hermes.CondSwap condlvals
    | Hermes.Block (ds, ss, pos) =>
         Hermes.Block (ds, List.map invertStat (List.rev ss), pos)
    | Hermes.For (i, e1, e2, s, pos) =>
         Hermes.For (i, e2, e1, invertStat s, pos)
    | Hermes.Call call => Hermes.Uncall call
    | Hermes.Uncall call => Hermes.Call call
    | Hermes.Printf args => Hermes.Scanf args
    | Hermes.Scanf args => Hermes.Printf args
    | Hermes.Assert c => Hermes.Assert c

  fun compileBinop Hermes.Plus = " + "
    | compileBinop Hermes.Minus = " - "
    | compileBinop Hermes.Times = " * "
    | compileBinop Hermes.Divide = " / "
    | compileBinop Hermes.Modulo = " % "
    | compileBinop Hermes.Xor = " ^ "
    | compileBinop Hermes.BAnd = " & "
    | compileBinop Hermes.BOr = " | "
    | compileBinop Hermes.ShiftL = " << "
    | compileBinop Hermes.ShiftR = " >> "
    | compileBinop Hermes.Equal = " == "
    | compileBinop Hermes.Less = " < "
    | compileBinop Hermes.Greater = " > "
    | compileBinop Hermes.Neq = " != "
    | compileBinop Hermes.Leq = " <= "
    | compileBinop Hermes.Geq = " >= "


  fun compileUnop Hermes.Uminus = "-"
    | compileUnop Hermes.Negate = "~"

  fun compileUpdateOp Hermes.Add = " += "
    | compileUpdateOp Hermes.Sub = " -= "
    | compileUpdateOp Hermes.XorWith = " ^= "
    | compileUpdateOp _ =
         raise Error ("This should never happen", (0,0))

  fun getSize t pos =
    case t of
      "int8_t " => (t, "0x7", "0xff", "8")
    | "uint8_t " => (t, "0x7", "0xff", "8")
    | "int16_t " => (t, "0xf", "0xffff", "16")
    | "uint16_t " => (t, "0xf", "0xffff", "16")
    | "int32_t " => (t, "0x1f", "0xffffffff", "32")
    | "uint32_t " => (t, "0x1f", "0xffffffff", "32")
    | "int64_t " => (t, "0x3f", "0xffffffffffffffff", "64")
    | "uint64_t " => (t, "0x3f", "0xffffffffffffffff", "64")
    | _ => let val _ = print(t) in raise Error ("Bad C type", pos) end

  fun findWordSize env (Hermes.Var (x,pos)) =
        let val (ct,_) = lookup x env pos in getSize ct pos end
    | findWordSize env (Hermes.Array (x,e,pos)) =
        let val (ct,_) = lookup x env pos in getSize ct pos end

  fun compileLval env (Hermes.Var (x,pos)) =
    let
      val (ctyp, size) = lookup x env pos
    in
      x
    end
    | compileLval env (Hermes.Array (x,e,pos)) =
    let
      val (ctyp, size) = lookup x env pos
      val cexp = compileExp e env false
    in
      x ^ "[" ^ cexp ^ "]"
    end

  and lvalScan env count [] =
      ("", "")
    | lvalScan env count (Hermes.Var (x,pos) :: lvs) =
    let
      val (test, addrs) = lvalScan env (count+1) lvs
    in
      (if test = "" then x else x ^ " | " ^ test,  (* test *)
      ", &" ^ x ^ addrs)                  (* address *)
    end
    | lvalScan env count (Hermes.Array (x,e,pos) :: lvs) =
    let
      val (test, addrs) = lvalScan env (count+1) lvs
      val clv = x ^ "[" ^ compileExp e env false ^ "]"
    in
      (if test = "" then clv else clv ^ " | " ^ test,  (* test *)
      ", &" ^ clv ^ addrs)                            (* address *)
    end

  and compileExp e env pneeded =
    case e of
      Hermes.Rval lv => compileLval env lv
    | Hermes.Const (s,p) => s
    | Hermes.Bin (bop, e1, e2, pos) =>
        (if pneeded then "(" else "") ^
        compileExp e1 env true ^ compileBinop bop ^ compileExp e2 env true ^
        (if pneeded then ")" else "")
    | Hermes.Un (uop, e, pos) =>
        compileUnop uop ^ compileExp e env true

  (* make local variables for block *)
  fun compileDecls [] space = ("", [])
    | compileDecls (Hermes.VarDecl (name, typ, pos) :: ds) space =
        let
          val (entry, env) = compileDecls ds space
          val ctype = compileType typ
        in
          (space ^ ctype ^ name ^ " = 0;\n" ^ entry,
          (name, (ctype, "")) :: env)
        end
    | compileDecls (Hermes.ConstDecl (name, value, typ, pos) :: ds) space =
        let
          val (entry, env) = compileDecls ds space
          val ctype = compileType typ
        in
          (space ^ "const " ^ ctype ^ name ^ " = " ^ value ^ ";\n" ^ entry,
          (name, (ctype, "const")) :: env)
        end
    | compileDecls (Hermes.ArrayDecl (name, size, typ, pos) :: ds) space =
        let
          val (entry, env) = compileDecls ds space
          val ctype = compileType typ
        in
          (space ^ ctype ^ name ^ "[" ^ size ^ "] = {0};\n" ^ entry,
          (name, (ctype, size)) :: env)
        end
    | compileDecls ((Hermes.ConstParDecl _) :: ds) space = compileDecls ds space
    | compileDecls ((Hermes.ConstArrayParDecl _) :: ds) space = compileDecls ds space

  (* check if local variables are 0 at end of block *)
  fun checkFor0 [] space = ""
    | checkFor0 (Hermes.VarDecl (name, typ, (line,_)) :: ds) space =
        let
          val checks = checkFor0 ds space
        in
          checks ^ space ^ "if (" ^ name ^ " != 0)\n" ^ space ^
          "  fprintf(stderr,\""^ name ^
          " not zero at end of block starting at line " ^
           Int.toString line ^ "\\n\");\n"
        end
    | checkFor0 (Hermes.ConstDecl (name, value, typ, (line,_)) :: ds) space =
        checkFor0 ds space
    | checkFor0 (Hermes.ConstParDecl (name, typ, (line,_)) :: ds) space =
        checkFor0 ds space
    | checkFor0 (Hermes.ConstArrayParDecl (name, size, typ, (line,_)) :: ds) space =
        checkFor0 ds space
    | checkFor0 (Hermes.ArrayDecl (name, size, typ, (line,_)) :: ds) space =
        let
          val checks = checkFor0 ds space
        in
          checks ^ space ^ "{ int i_; for (i_=0; i_<" ^ size ^ "; i_++)\n" ^
          space ^ "   if  (" ^ name ^ "[i_] != 0)\n" ^ space ^
          "     fprintf(stderr,\"element of "^ name ^
          " not zero at end of block starting at line " ^
           Int.toString line ^ "\\n\");\n" ^ space ^ "}\n"
        end

  (* Insert explicit zeroing of non-constant local variables. *)
  fun zeroClear [] space = ""
    | zeroClear (Hermes.VarDecl (name, typ, (line,_)) :: ds) space =
        let
          val checks = zeroClear ds space
        in
          checks ^ space ^ name ^ " = 0;\n"
        end
    | zeroClear (Hermes.ConstDecl (name, value, typ, (line,_)) :: ds) space =
        zeroClear ds space
    | zeroClear (Hermes.ConstParDecl (name, typ, (line,_)) :: ds) space =
        zeroClear ds space
    | zeroClear (Hermes.ConstArrayParDecl (name, size, typ, (line,_)) :: ds) space =
        zeroClear ds space
    | zeroClear (Hermes.ArrayDecl (name, size, typ, (line,_)) :: ds) space =
        let
          val checks = zeroClear ds space
        in
          checks ^ space ^ "{ int i_; for (i_=0; i_<" ^ size ^ "; i_++)\n" ^
          space ^ "   " ^ name ^ "[i_] = 0;\n" ^ space ^ "}\n"
        end

  (* If formal is a constant integer, then actual is passed by value; this is
     when decl is used. *)
  fun compileActuals env [] [] pos = []
    | compileActuals env (Hermes.Var (x,pos) :: lvs) (decl :: decls) pos =
      let
        val (ctyp, size) = lookup x env pos
        val refOrValue = (case decl of
                            Hermes.ConstParDecl _ => ""
                          | _ => "&")
      in
        if size = "" then (refOrValue ^ x) :: compileActuals env lvs decls pos
        else x :: compileActuals env lvs decls pos
      end
    | compileActuals env (Hermes.Array (x,e,pos) :: lvs) (decl :: decls) pos =
        ("&" ^ x ^ "[" ^ compileExp e env true ^ "]") :: compileActuals env lvs
        decls pos
    | compileActuals _ actuals _ _ = raise Error ("This should never happen",(0,0))

  fun convertFormat0 prefix [] pos = ""
    | convertFormat0 prefix (#"%" :: cs) pos =
        (case cs of
           (#"u" :: #"8" :: cs1) => "%\"" ^ prefix ^ "u8\"" ^ convertFormat0
           prefix cs1 pos
         | (#"i" :: #"8" :: cs1) => "%\"" ^ prefix ^ "i8\"" ^ convertFormat0
         prefix cs1 pos
         | (#"u" :: #"1" :: #"6" :: cs1) =>
              "%\"" ^ prefix ^ "u16\"" ^ convertFormat0 prefix cs1 pos
         | (#"i" :: #"1" :: #"6" :: cs1) =>
              "%\"" ^ prefix ^ "i16\"" ^ convertFormat0 prefix cs1 pos
         | (#"u" :: #"3" :: #"2" :: cs1) =>
              "%\"" ^ prefix ^ "u32\"" ^ convertFormat0 prefix cs1 pos
         | (#"i" :: #"3" :: #"2" :: cs1) =>
              "%\"" ^ prefix ^ "i32\"" ^ convertFormat0 prefix cs1 pos
         | (#"u" :: #"6" :: #"4" :: cs1) =>
              "%\"" ^ prefix ^ "u64\"" ^ convertFormat0 prefix cs1 pos
         | (#"i" :: #"6" :: #"4" :: cs1) =>
              "%\"" ^ prefix ^ "i64\"" ^ convertFormat0 prefix cs1 pos
         | _ => raise Error ("Bad format string", pos)
        )
    | convertFormat0 prefix (#"\\" :: cs) pos =
        "\\\\" ^ convertFormat0 prefix cs pos
    | convertFormat0 prefix (c :: cs) pos =
        Char.toString c ^ convertFormat0 prefix cs pos

  fun convertFormat prefix f pos = convertFormat0 prefix (String.explode f) pos

  fun compilePrint env (Hermes.Var (x, pos)) = x
    | compilePrint env (Hermes.Array (x, e, pos)) =
        x ^ "[" ^ compileExp e env false ^ "]"

  fun compileStat s env fenv space =
    case s of
      Hermes.Skip => ";"
    | Hermes.Update (Hermes.RoL, lv, exp, pos) =>
         let
           val (ctyp, mask0, mask1, size) = findWordSize env lv
           val cl = compileLval env lv
         in
           space ^ "{ int tmp_ = " ^
           compileExp exp env true ^ " & " ^ mask0 ^ ";\n" ^
           space ^ "  " ^ cl ^
           " = ((" ^ cl ^ " << tmp_) | (" ^ cl ^
           " >> (" ^ size ^ " - tmp_))) & " ^ mask1 ^ ";\n" ^
           space ^ "  tmp_ = 0; }\n"
         end
    | Hermes.Update (Hermes.RoR, lv, exp, pos) =>
         let
           val (ctyp, mask0, mask1, size) = findWordSize env lv
           val cl = compileLval env lv
         in
           space ^ "{ int tmp_ = " ^
           compileExp exp env true ^ " & " ^ mask0 ^ ";\n" ^
           space ^ "  " ^ cl ^
           " = ((" ^ cl ^ " >> tmp_) | (" ^ cl ^
           " << (" ^ size ^ " - tmp_))) & " ^ mask1 ^ ";\n" ^
           space ^ "  tmp_ = 0; }\n"
         end
    | Hermes.CondUpdate (cond, Hermes.RoL, lv, exp, pos) =>
         let
           val (ctyp, mask0, mask1, size) = findWordSize env lv
           val cl = compileLval env lv
           val condMask = "-(" ^ compileExp cond env false ^ ")"
         in
           space ^ "{ int tmp_ = " ^
           compileExp exp env true ^ " & " ^ mask0 ^ ";\n" ^
           space ^ "  " ^ cl ^
           " = " ^
           "(((" ^ cl ^ " << (tmp_ & " ^ condMask ^ ")) | (" ^ cl ^
           " >> ((" ^ size ^ " - tmp_) & " ^ condMask ^ "))) & " ^ mask1 ^ ");\n" ^
           space ^ "  tmp_ = 0; }\n"
         end
    | Hermes.CondUpdate (cond, Hermes.RoR, lv, exp, pos) =>
         let
           val (ctyp, mask0, mask1, size) = findWordSize env lv
           val cl = compileLval env lv
           val condMask = "-(" ^ compileExp cond env false ^ ")"
         in
           space ^ "{ int tmp_ = " ^
           compileExp exp env true ^ " & " ^ mask0 ^ ";\n" ^
           space ^ "  " ^ cl ^
           " = " ^
           "(((" ^ cl ^ " >> (tmp_ & " ^ condMask ^ ")) | (" ^ cl ^
           " << ((" ^ size ^ " - tmp_) & " ^ condMask ^ "))) & " ^ mask1 ^ ");\n" ^
           space ^ "  tmp_ = 0; }\n"
         end
    | Hermes.Update (updateOp, lv, exp, pos) =>
        space ^ compileLval env lv ^
        compileUpdateOp updateOp ^ compileExp exp env false ^ ";\n"
    | Hermes.CondUpdate (cond, updateOp, lv, exp, pos) =>
        space ^ compileLval env lv ^
        compileUpdateOp updateOp ^
        "-(" ^ compileExp cond env false ^ ")&" ^
        compileExp exp env true ^
        ";\n"
    | Hermes.Inc (lv, pos) =>
        space ^ compileLval env lv ^ "++;\n"
    | Hermes.Dec (lv, pos) =>
        space ^ compileLval env lv ^ "--;\n"
    | Hermes.Swap (lv1, lv2, pos) =>
        let
          val clv1 = compileLval env lv1
          val clv2 = compileLval env lv2
        in
          (* implemented using three XOR updates to avoid using extra variable *)
          space ^ clv1 ^ " ^= " ^ clv2 ^"; " ^
          clv2 ^ " ^= " ^ clv1 ^ "; " ^
          clv1 ^ " ^= " ^ clv2 ^";\n"
        end
    | Hermes.CondSwap (cond, lv1, lv2, pos) =>
        let
          val cc = compileExp cond env false
          val clv1 = compileLval env lv1
          val clv2 = compileLval env lv2
        in
          (* implemented using three conditional XOR updates to avoid extra variable *)
          space ^ clv1 ^ " ^= -(" ^ cc ^ ")& " ^ clv2 ^"; " ^
          clv2 ^ " ^= -(" ^ cc ^ ")& " ^ clv1 ^ "; " ^
          clv1 ^ " ^= -(" ^ cc ^ ")& " ^ clv2 ^";\n"
        end
    | Hermes.Block (ds, ss, pos) =>
         let
           val space1 = "  " ^ space
           val (decls, env1) = compileDecls ds space1
           val env2 = env1 @ env
           val body = String.concat
                        (List.map
                           (fn s => compileStat s env2 fenv space1)
                         ss)
           (* If optimized code is being compiled (fO flag is set) we use
              zeroClear, otherwise, we use checkFor0. *)
           val tail = if !fO then zeroClear ds space1 else checkFor0 ds space1
         in
           space ^ "{\n" ^ decls ^ body ^ tail ^ space ^ "}\n"
         end
    | Hermes.Assert (c, (line,col)) =>
        space ^ "if (!(" ^ compileExp c env false ^ ")) " ^
        "fprintf(stderr,\"assertion failed near line " ^
        Int.toString line ^ "\\n\");\n"
    | Hermes.Call (f, lvs, pos) =>
        let
          val decls = lookup f fenv pos
          val actuals =  compileActuals env lvs decls pos
          val actuals1 = concatWith actuals ", "
        in
          space ^ f ^ "_F(" ^ actuals1 ^ ");\n"
        end
    | Hermes.Uncall (f, lvs, pos) =>
        let
          val decls = lookup f fenv pos
          val actuals = compileActuals env lvs decls pos
          val actuals1 = concatWith actuals ", "
        in
          space ^ f ^ "_B(" ^ actuals1 ^ ");\n"
        end
    | Hermes.Printf (format, lvs, pos) =>
         let
           val format1 = convertFormat "PRI" format pos
         in
           space ^ "printf(\"" ^ format1 ^ "\", " ^
           concatWith (List.map (compilePrint env) lvs) ", " ^ ");\n" ^
           space ^
           concatWith (List.map (compileLval env) lvs) " = " ^ " = 0;\n"
         end
    | Hermes.Scanf (format, lvs, pos) =>
         let
           val format1 = convertFormat "SCN" format pos
           val (test, addrs) = lvalScan env 0 lvs
           val space1 = "  " ^ space
         in
           space ^ "if (" ^ test ^ ") {\n" ^
           space1 ^ "fprintf(stderr,\"variables must be 0 before scan\\n\");\n" ^
           space1 ^ "exit(1);\n" ^
           space ^ "} else {\n" ^
           space1 ^ "scanf(\"" ^ format1 ^ "\"" ^ addrs ^ ");\n" ^
           space ^ "}\n"
         end
    | Hermes.For (i, e1, e2, s, pos) =>
        space ^ "{ int32_t " ^ i ^ " = " ^ compileExp e1 env false ^ ";\n" ^
        space ^ "  int32_t " ^ i ^ "_end = " ^ compileExp e2 env false ^ ";\n" ^
        space ^ "  while (" ^ i ^ " != " ^ i ^ "_end)\n" ^
        compileStat s ((i, ("int32_t ", "for")) :: env) fenv (space ^ "    ") ^
        space ^ "}\n"

  (* Non-arrays passed by reference. Constants are passed by value if integers,
     else as reference. *)
  fun makeFormal (Hermes.VarDecl (name, typ, pos)) =
        compileType typ ^ "*" ^ name ^ "_P"
    | makeFormal (Hermes.ArrayDecl (name, size, typ, pos)) =
        compileType typ ^ name ^ "[]"
    | makeFormal (Hermes.ConstParDecl (name, typ, pos)) =
        compileType typ ^ name
    | makeFormal (Hermes.ConstArrayParDecl (name, size, typ, pos)) =
        compileType typ ^ name ^ "[]"
    | makeFormal _ =
        raise Error ("This should never happen", (0,0))

  fun makeFormals [] = ""
    | makeFormals [d] = makeFormal d
    | makeFormals (d :: ds) = makeFormal d ^ ", " ^ makeFormals ds

  (* Make local variables for non-array and non-constant parameters *)
  fun declareFormals [] = ("", [])
    | declareFormals (Hermes.VarDecl (name, typ, pos) :: ds) =
        let
          val (entry, env) = declareFormals ds
          val ctype = compileType typ
        in
          ("  " ^ ctype ^ name ^ " = *" ^ name ^ "_P;\n" ^ entry,
          (name, (ctype, "")) :: env)
        end
    | declareFormals (Hermes.ConstParDecl (name, typ, pos) :: ds) =
        let
          val (entry, env) = declareFormals ds
          val ctype = compileType typ
        in
          (entry, (name, (ctype, "")) :: env)
        end
    | declareFormals (Hermes.ConstArrayParDecl (name, size, typ, pos) :: ds) =
        let
          val (entry, env) = declareFormals ds
          val ctype = compileType typ
        in
          (entry, (name, (ctype, size)) :: env)
        end
    | declareFormals (Hermes.ArrayDecl (name, size, typ, pos) :: ds) =
        let
          val (entry, env) = declareFormals ds
          val ctype = compileType typ
        in
          (entry, (name, (ctype, size)) :: env)
        end
    | declareFormals _ =
        raise Error ("This should never happen", (0,0))

  (* Copy back and subsequently zero non-array variables. Call by value
     parameters, i.e. integer constants, are not copied back but cleared
     instead. *)
  fun returnFormals [] = ""
    | returnFormals (Hermes.ConstParDecl (name, typ, pos) :: ds) = 
        "  " ^ name ^ " = 0;\n" ^ returnFormals ds
    | returnFormals (Hermes.ConstArrayParDecl (name, size, typ, pos) :: ds) =
        returnFormals ds
    | returnFormals (Hermes.VarDecl (name, typ, pos) :: ds) =
        "  *" ^ name ^ "_P = " ^ name ^ ";\n" 
        ^ "  " ^ name ^ " = 0;\n" ^ returnFormals ds
    | returnFormals (Hermes.ArrayDecl (name, size, typ, pos) :: ds) =
        returnFormals ds
    | returnFormals _ =
        raise Error ("This should never happen", (0,0))

  (* If zero stack flag is set then procedures return 0.
     If inverted is true then we suffix functions with _B, else _F. *)
  fun compileProcedure fenv inverted (name, decls, body, pos) =
    let
      val formals = makeFormals decls
      val (entry, env) = declareFormals decls
      val exit = returnFormals decls
      val rettype = if !fZ then "__attr_zerostack int " else "void "
      val ret = if !fZ then "  return 0;\n" else ""
      val suffix = if inverted then "_B(" else "_F("
    in
      rettype ^ name ^ suffix ^ formals ^ ")\n{\n" ^
      entry ^ compileStat body env fenv "  " ^ exit ^ ret ^ "}\n\n"
    end
    
  fun makeForwards (name, decls, body, pos) =
    let 
      val rettype = if !fZ then "int " else "void "
    in
      rettype ^ name ^"_F(), " ^ name ^"_B();\n"
    end

  fun makeFenv [] = []
    | makeFenv ((name, decls, body, pos) :: fs) =
        (name, decls) :: (makeFenv fs)

  fun invertProgram fs = List.map 
    (fn (name, decls, body, pos) => (name, decls, invertStat body, pos)) fs

  fun optimizeProgram fs = HermesOptimizer.optimizeProgram fs

  (* We generate an inverted version of the program and, if optimize flag is
     set, optimize both programs. Afterwards, code for both directions is
     generated. *)
  fun compile fs opt zerostack =
    let
      val _ = (fO := opt)
      val _ = (fZ := zerostack)
      val forwardDecls = String.concat (List.map makeForwards fs)
      val fenv = makeFenv fs
      val forwardFs = if !fO then optimizeProgram fs else fs
      val backwardFs = if !fO then optimizeProgram (invertProgram fs) 
                       else (invertProgram fs)
      val functions = ListPair.foldr (fn (f,b,acc) => f ^ b ^ acc) ""
        ((List.map (compileProcedure fenv false) forwardFs),
        (List.map (compileProcedure fenv true) backwardFs))
      val header = "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <inttypes.h>\n\n" ^
      "#define __STDC_FORMAT_MACROS\n#include <inttypes.h>\n\n"
      (* Add zerostack macro if zerostack flag is set. *)
      val header' = if !fZ then (header ^ 
                    "#define __attr_zerostack __attribute__((annotate(\"SENSITIVE\")))\n\n")
                    else header
    in
      header'
       ^
      forwardDecls ^ "\n" ^ functions ^
      "int main(int ac, char **av)\n{\n" ^
      "  if (ac>1 && strcmp(av[1],\"-r\")==0) main_B();\n  else main_F();\n" ^
      "  exit(0);\n}"
    end

end
