signature HermesStaticAnalysis =
sig

  exception Error of string * (int * int)

  (* typechecks a hermes program. We do not return an updated AST, as we do not
     construct any new declarations during traversal. I.e., if checkProgram
     returns, the program is typed correctly. *)
  val checkProgram : Hermes.program -> unit

end
