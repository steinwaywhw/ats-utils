staload "./util.sats"
staload "./maybe.sats"

datatype list (a:t@ype) =
	| Cons of (a, list a)
	| Nil  of ()

fun list_empty   {a:t@ype} (list a): bool

fun {a:t@ype} list_find    (list a, a, (a, a) -> bool): maybe int 
//fun list_find_int (list int, int): maybe int 
//fun list_find_string (list string, string): maybe int 

fun {a:t@ype} list_get 	   (list a, int): maybe a
fun {a:t@ype} list_len     (list a): int
fun {a:t@ype} list_append  (list a, a): list a
fun {a:t@ype} list_prepend (list a, a): list a
fun {a:t@ype} list_head    (list a): maybe a
fun {a:t@ype} list_tail    (list a): list a
fun {a:t@ype} list_drop    (list a, int): list a
fun {a:t@ype} list_take    (list a, int): list a
fun {a:t@ype} list_concat  (list a, list a): list a
fun {a:t@ype} list_filter  (list a, a -> bool): list a
fun {a:t@ype} list_foreach (list a, a -> void): void 
fun {a:t@ype} list_reverse (list a): list a

fun {a:t@ype} {b:t@ype}    list_foldl (list a, b, (a, b) -> b): b
fun {a:t@ype} {b:t@ype}    list_foldr (list a, b, (a, b) -> b): b
fun {a:t@ype} {b:t@ype}    list_map   (list a, a -> b): list b 
fun {a,b:t@ype} {r:t@ype}  list_zip   (list a, list b, (a, b) -> r): list r

overload [] 	 with list_get 
overload len 	 with list_len
overload empty 	 with list_empty 
overload append  with list_append
overload prepend with list_prepend
overload head 	 with list_head  
overload tail 	 with list_tail  
overload take    with list_take
overload drop 	 with list_drop  
overload concat  with list_concat
overload filter  with list_filter
overload foreach with list_foreach
overload map 	 with list_map 
overload foldl 	 with list_foldl
overload foldr 	 with list_foldr
overload zip 	 with list_zip

fun {a:t@ype} list_show (list a, a -> void): void

fun list_show_int 		(list int): void
fun list_show_char 		(list char): void 
fun list_show_string 	(list string): void

overload show 	 with list_show_int 
overload show 	 with list_show_char 
overload show	 with list_show_string
overload show 	 with list_show