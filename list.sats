staload "./symintr.sats"
staload "./maybe.sats"

datatype list (a:t@ype) =
| ListCons of (a, list a)
| ListNil  of ()

typedef nat = intGte 0

fun {a:t@ype}   list_empty    (list a): bool
fun {a:t@ype}   list_len      (list a): nat
    
fun {a:t@ype}   list_get 	  (list a, nat): a
fun {a:t@ype}   list_append   (list a, a): list a
fun {a:t@ype}   list_prepend  (list a, a): list a
fun {a:t@ype}   list_concat   (list a, list a): list a
fun {a:t@ype}   list_head     (list a): a
fun {a:t@ype}   list_tail     (list a): list a
fun {a:t@ype}   list_take     (list a, nat): list a
fun {a:t@ype}   list_drop     (list a, nat): list a
fun {a:t@ype}   list_reverse  (list a): list a
fun {a:t@ype}   list_find     (list a, a): maybe nat 

fun {a:t@ype}   list_any      (list a, a -<cloref1> bool): bool 
fun {a:t@ype}   list_all      (list a, a -<cloref1> bool): bool
fun {a:t@ype}   list_member   (list a, a): bool
  
fun {a:t@ype}   list_filter   (list a, a -<cloref1> bool): list a
fun {a:t@ype}   list_foreach  (list a, a -<cloref1> void): void 
fun {a:t@ype}   list_iforeach (list a, (a, nat) -<cloref1> void): void
fun {a,b:t@ype} list_foldl    (list a, b, (a, b) -<cloref1> b): b
fun {a,b:t@ype} list_foldr    (list a, b, (a, b) -<cloref1> b): b
fun {a,b:t@ype} list_map      (list a, a -<cloref1> b): list b 
fun {a,b:t@ype} list_zip      (list a, list b): list (@(a, b))

fun list_selftest (): void 

overload [] 	  with list_get

overload len 	  with list_len
overload empty 	  with list_empty 

overload append   with list_append
overload prepend  with list_prepend
overload head 	  with list_head  
overload tail 	  with list_tail  
overload take     with list_take
overload drop 	  with list_drop  
overload concat   with list_concat
overload reverse  with list_reverse
overload find     with list_find 
 
overload foreach  with list_foreach
overload iforeach with list_iforeach
overload filter   with list_filter
overload map 	  with list_map 
overload foldl 	  with list_foldl
overload foldr 	  with list_foldr
overload zip 	  with list_zip
 
overload member   with list_member
overload any      with list_any 
overload all      with list_all 
