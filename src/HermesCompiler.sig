signature HermesCompiler =
sig

  exception Error of string*(int*int)

  val compile : Hermes.program -> bool -> bool -> string
end
