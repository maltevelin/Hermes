structure SymTab :> SymTab =
struct

  datatype 'a SymTab = SymTab of (string * 'a) list

  fun empty () = SymTab [] 

  fun toList (SymTab tab) = tab

  fun bind n v (SymTab tab) = SymTab ((n, v)::tab)

  fun lookup n tab = 
    case tab of
         SymTab [] => NONE
       | SymTab ((n',v)::tab') => 
           if n = n' then SOME v 
           else lookup n (SymTab tab')

  fun remove n (SymTab tab) = 
    SymTab (List.filter (fn (n', _) => n <> n') tab)

  fun removeMany ns (SymTab tab) =
    SymTab (List.filter (fn (n, _) => 
    not (List.exists (fn n' => n' = n) ns)) tab)

  fun combine (SymTab tab) (SymTab tab') = SymTab (tab @ tab')

end
