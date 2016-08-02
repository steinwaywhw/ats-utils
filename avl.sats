staload "./symintr.sats"
staload "./maybe.sats"


abstype avltree (k:t@ype, v:t@ype) = ptr 

local 

typedef nat = [n:nat] int n 

in 

fun {a:t@ype}   avltree_cmp$elm  (a, a): int
fun {k,v:t@ype} avltree_cmp      (avltree (k, v), avltree (k, v)): int 
fun {k,v:t@ype} avltree_eq       (avltree (k, v), avltree (k, v)): bool

fun {k,v:t@ype} avltree_make     (): avltree (k, v)
fun {k,v:t@ype} avltree_insert   (avltree (k, v), k, v): avltree (k, v)
fun {k,v:t@ype} avltree_replace  (avltree (k, v), k, v): avltree (k, v)
fun {k,v:t@ype} avltree_delete   (avltree (k, v), k): avltree (k, v)
fun {k,v:t@ype} avltree_find     (avltree (k, v), k): maybe v
fun {k,v:t@ype} avltree_member   (avltree (k, v), k): bool
fun {k,v:t@ype} avltree_insert_or_replace (avltree (k, v), k, v): avltree (k, v)

fun {k,v:t@ype} avltree_empty    (avltree (k, v)): bool
fun {k,v:t@ype} avltree_size     (avltree (k, v)): nat
fun {k,v:t@ype} avltree_height   (avltree (k, v)): nat

fun {k,v:t@ype} avltree_any      (avltree (k, v), k -<cloref1> bool): bool 
fun {k,v:t@ype} avltree_all      (avltree (k, v), k -<cloref1> bool): bool

fun {a:t@ype}   avltree_show$elm (a): void
fun {k,v:t@ype} avltree_show     (avltree (k, v)): void 

end

fun avltree_selftest (): void 

overload eq      with avltree_eq 
overload =       with avltree_eq 
overload compare with avltree_cmp

overload empty   with avltree_empty
overload member  with avltree_member 
overload size    with avltree_size 
overload height  with avltree_height 

overload make    with avltree_make 
overload insert  with avltree_insert 
overload replace with avltree_replace 
overload delete  with avltree_delete
overload find    with avltree_find 

overload any     with avltree_any 
overload all     with avltree_all 

overload show    with avltree_show
