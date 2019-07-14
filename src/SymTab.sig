(* Polymorphic and persistent symbol table using lists. See section 3.1 in
   Introduction to Compiler Design. *)
signature SymTab =
sig

  type 'a SymTab

  val empty : unit -> 'a SymTab

  val toList : 'a SymTab -> (string * 'a) list

  val bind : string -> 'a -> 'a SymTab -> 'a SymTab

  val lookup : string -> 'a SymTab -> 'a option

  val remove : string -> 'a SymTab -> 'a SymTab

  val removeMany : string list -> 'a SymTab -> 'a SymTab

  val combine : 'a SymTab -> 'a SymTab -> 'a SymTab

end
