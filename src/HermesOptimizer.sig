signature HermesOptimizer =
sig

  (* Removes decalculations *)
  val optimizeProgram : Hermes.program -> Hermes.program

end
