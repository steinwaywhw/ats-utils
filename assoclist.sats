staload "./symintr.sats"
staload "./maybe.sats"


abstype assoclist (a:t@ype, b:t@ype) = ptr 


typedef nat = intGte 0

fun {a,b:t@ype}   assoclist_make     (): assoclist (a, b)
fun {a,b:t@ype}   assoclist_empty    (assoclist (a, b)): bool

fun {a,b:t@ype}   assoclist_insert   (assoclist (a, b), a, b): assoclist (a, b)    
fun {a,b:t@ype}   assoclist_delete   (assoclist (a, b), a): assoclist (a, b)
fun {a,b:t@ype}   assoclist_update   (assoclist (a, b), a, b): assoclist (a, b)
fun {a,b:t@ype}   assoclist_find     (assoclist (a, b), a): maybe b

overload make   with assoclist_make 
overload empty  with assoclist_empty

overload insert with assoclist_insert 
overload delete with assoclist_delete 
overload update with assoclist_update
overload find   with assoclist_find
