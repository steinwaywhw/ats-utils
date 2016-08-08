staload "./symintr.sats"
staload "./list.sats"
staload "./maybe.sats"

abstype avltree (k:t@ype) = ptr 

local 

typedef nat = [n:nat] int n 

in 

fun {a:t@ype}   avltree_cmp$elm  (a, a): int
//fun {a:t@ype}   avltree_cmp      (avltree a, avltree a): int 
fun {a:t@ype}   avltree_eq       (avltree a, avltree a): bool
  
fun {a:t@ype}   avltree_make     (): avltree a
fun {a:t@ype}   avltree_insert   (avltree a, a): avltree a
fun {a:t@ype}   avltree_delete   (avltree a, a): avltree a
fun {a:t@ype}   avltree_member   (avltree a, a): bool
fun {a:t@ype}   avltree_find     (avltree a, a): maybe a
  
fun {a:t@ype}   avltree_empty    (avltree a): bool
fun {a:t@ype}   avltree_size     (avltree a): nat
fun {a:t@ype}   avltree_height   (avltree a): nat
  
fun {a:t@ype}   avltree_foreach  (avltree a, a -<cloref1> void): void 
//fun {a:t@ype}   avltree_iforeach (avltree a, (a, nat) -<cloref1> void): void 
fun {a,b:t@ype} avltree_foldr    (avltree a, b, (a, list b) -<cloref1> b): b
fun {a:t@ype}   avltree_filter   (avltree a, a -<cloref1> bool): avltree a
fun {a,b:t@ype} avltree_map      (avltree a, a -<cloref1> b): avltree b

fun {a:t@ype}   avltree_flatten  (avltree a): list a

fun {a:t@ype}   avltree_any      (avltree a, a -<cloref1> bool): bool 
fun {a:t@ype}   avltree_all      (avltree a, a -<cloref1> bool): bool
  
fun {a:t@ype}   avltree_show$elm (a): void
fun {a:t@ype}   avltree_show     (avltree a): void 

end

fun avltree_selftest (): void 

overload eq      with avltree_eq 
overload =       with avltree_eq 
//overload compare with avltree_cmp

overload empty   with avltree_empty
overload member  with avltree_member 
overload size    with avltree_size 
overload height  with avltree_height 

overload foreach with avltree_foreach
overload foldr   with avltree_foldr
overload filter  with avltree_filter 
overload map     with avltree_map

overload make    with avltree_make 
overload insert  with avltree_insert 
overload delete  with avltree_delete

overload any     with avltree_any 
overload all     with avltree_all 

overload show    with avltree_show
