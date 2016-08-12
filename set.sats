staload "symintr.sats"

abstype set (a:t@ype) = ptr 

typedef nat = intGte 0

fun {a:t@ype}   set_make (): set a 

fun {a:t@ype}   set_insert (set a, a): set a
fun {a:t@ype}   set_delete (set a, a): set a  

fun {a:t@ype}   set_empty (set a): bool
fun {a:t@ype}   set_size (set a): nat

fun {a:t@ype}   set_foreach (set a, a -<cloref1> void): void 
fun {a:t@ype}   set_filter (set a, a -<cloref1> bool): set a
fun {a,b:t@ype} set_foldr (set a, b, (a, b) -<cloref1> b): b
fun {a,b:t@ype} set_map (set a, a -<cloref1> b): set b

fun {a:t@ype}   set_subset (set a, set a): bool
fun {a:t@ype}   set_member (set a, a): bool 
fun {a:t@ype}   set_any (set a, a -<cloref1> bool): bool 
fun {a:t@ype}   set_all (set a, a -<cloref1> bool): bool

fun {a:t@ype}   set_union (set a, set a): set a
fun {a:t@ype}   set_intersect (set a, set a): set a 
fun {a:t@ype}   set_diff (set a, set a): set a 


overload make    with set_make 
overload insert  with set_insert 
overload delete  with set_delete 

overload empty   with set_empty 
overload size    with set_size 

overload foreach with set_foreach 
overload foldr   with set_foldr
overload filter  with set_filter 
overload map     with set_map 

overload member  with set_member 
overload any     with set_any 
overload all     with set_all 