staload "./symintr.sats"
staload "./stream.sats"

datavtype _linstream (a:vt@ype+) = 
| LinStreamCons (a) of (a, linstream a)
| LinStreamNil  (a) of () 
where linstream (a:vt@ype) = lazy_vt (_linstream a)

local 

typedef nat = [n:nat] int n

in 

fun {a:vt@ype}   linstream_force     (linstream a): _linstream a
 
fun {a:vt@ype}   linstream_free_elm$default (a): void 
fun {a:vt@ype}   linstream_free_elm         (a): void
fun {a:vt@ype}   linstream_free             (linstream a): void
 
fun {a:vt@ype}   linstream_empty     (linstream a): bool 

fun {a:vt@ype}   linstream_head      (&linstream a >> _): a
fun {a:vt@ype}   linstream_tail      (linstream a): linstream a
fun {a:vt@ype}   linstream_take      (&linstream a >> _, nat): linstream a
fun {a:vt@ype}   linstream_drop      (linstream a, nat): linstream a
 
fun {a:vt@ype}   linstream_foreach   (linstream a, (&a) -<cloref1> void): void
fun {a:vt@ype}   linstream_iforeach  (linstream a, (&a, nat) -<cloref1> void): void
fun {a,b:vt@ype} linstream_zip       (linstream a, linstream b): linstream (@(a, b))
fun {a,b:vt@ype} linstream_map       (linstream a, (&a) -<cloref1> b): linstream b
fun {a,b:vt@ype} linstream_foldl     (linstream a, b, (&a, b) -<cloref1> b): b
fun {a,b:vt@ype} linstream_foldr     (linstream a, b, (&a, b) -<cloref1> b): b
fun {a:vt@ype}   linstream_filter    (linstream a, (&a) -<cloref1> bool): linstream a

fun {a:t@ype}    linstream_to_stream (linstream a): stream a 

//fun              linstream_show$sep  (): void
//fun {a:vt@ype}   linstream_show$elm  (&a): void 
//fun {a:vt@ype}   linstream_show      (linstream a): void 
//fun {a:vt@ype}   linstream_show_len  (&linstream a >> _, nat): void

end 

fun linstream_selftest (): void

overload empty 	  with linstream_empty 
//overload append   with linstream_append
//overload prepend  with linstream_prepend
overload head 	  with linstream_head  
overload tail 	  with linstream_tail  
overload take     with linstream_take
overload drop 	  with linstream_drop  
//overload concat   with linstream_concat
//overload reverse  with linstream_reverse
 
overload foreach  with linstream_foreach
overload iforeach with linstream_iforeach
overload filter   with linstream_filter
overload map 	  with linstream_map 
overload foldl 	  with linstream_foldl
overload foldr 	  with linstream_foldr
overload zip 	  with linstream_zip
 
//overload any      with linstream_any 
//overload all      with linstream_all 
//overload find     with linstream_find 

//overload show 	 with linstream_show
//overload show    with linstream_show_len