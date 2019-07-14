(* Hermes compiler, outputs C *)
(* compile with mosmlc hc.sml -o hc *)
structure hc =
struct

  fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n)

  fun errorMess s = TextIO.output (TextIO.stdErr,s ^ "\n");
 
  fun except l1 l2 = List.filter (fn x => not (List.exists (fn y => x = y) l2)) l1

  (* opt and zerostack are for code generation *)
  fun hs filename opt zerostack =
      let
        val lexbuf = createLexerStream
			  (BasicIO.open_in (filename ^ ".hms"))
      in
        let
          val pgm = HermesParser.Program HermesLexer.Token lexbuf
          (* val _ = TextIO.output (TextIO.stdErr, Hermes.showProgram pgm) *)
          val outstream = TextIO.openOut (filename ^ ".c")
          val _ = HermesStaticAnalysis.checkProgram pgm
          val target = HermesCompiler.compile pgm opt zerostack
        in
          TextIO.output(outstream, target);
          TextIO.closeOut outstream
        end
          handle Parsing.yyexit ob => errorMess "Parser-exit\n"
               | Parsing.ParseError ob =>
                   let val (lin,col) = HermesLexer.getPos lexbuf
                   in
                     errorMess ("Parse-error at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
                   end
               | HermesLexer.LexicalError (mess,(lin,col)) =>
                     errorMess ("Lexical error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
               | HermesCompiler.Error (mess, (lin,col)) =>
                     errorMess ("Compiler error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
               | HermesStaticAnalysis.Error (mess, (lin,col)) =>
                     errorMess ("Static analysis error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
               | SysErr (s,_) => errorMess ("Exception: " ^ s)
               | Subscript =>  errorMess "subscript error"
      end

  val _ = 
    let
      val argv = Mosml.argv ()
      val flags = List.filter (fn arg => String.substring(arg,0,1) = "-") argv
      val opt = List.exists (fn arg => arg = "-O") flags
      val zerostack = List.exists (fn arg => arg = "-Z") flags
      val argv' = except argv flags
    in
    (hs (List.nth(argv', 1)) opt zerostack)
      handle Subscript => errorMess "call by, e.g., hc tinyCrypt"
    end

end
