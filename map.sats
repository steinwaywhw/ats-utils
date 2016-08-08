staload "symintr.sats"
staload "maybe.sats"

abstype map (k:t@ype, v:t@ype) = ptr 

local 

typedef nat = [n:nat] int n 

in 

fun {k,v:t@ype} map_make (): map (k, v) 
fun {a:t@ype}   map_cmp$elm (a, a): int 
fun {k,v:t@ype} map_eq (map (k, v), map (k, v)): bool

fun {k,v:t@ype} map_insert (map (k, v), k, v): map (k, v)
fun {k,v:t@ype} map_delete (map (k, v), k): map (k, v)  
fun {k,v:t@ype} map_update (map (k, v), k, v): map (k, v)
fun {k,v:t@ype} map_find   (map (k, v), k): maybe v
fun {k,v:t@ype} map_member (map (k, v), k): bool 

fun {k,v:t@ype} map_empty (map (k, v)): bool
fun {k,v:t@ype} map_size (map (k, v)): nat

fun {k,v:t@ype} map_foreach (map (k, v), k -<cloref1> void): void 
fun {k,v:t@ype} map_filter (map (k, v), k -<cloref1> bool): map (k, v)

fun {k,v:t@ype} map_any (map (k, v), k -<cloref1> bool): bool 
fun {k,v:t@ype} map_all (map (k, v), k -<cloref1> bool): bool

end


overload eq      with map_eq 
overload =       with map_eq 
overload insert  with map_insert 
overload delete  with map_delete 
overload update  with map_update 
overload find    with map_find 
overload make    with map_make 
overload member  with map_member 
overload empty   with map_empty 
overload size    with map_size 
overload foreach with map_foreach 
overload filter  with map_filter 
overload any     with map_any 
overload all     with map_all 