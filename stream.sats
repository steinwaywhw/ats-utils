staload "./symintr.sats"

datatype _stream (a:t@ype) =
| StreamCons of (a, stream a)
| StreamNil of ()
where stream (a:t@ype) = lazy (_stream a)


typedef nat = intGte 0

fun {a:t@ype}   stream_empty    (stream a): bool
fun {a:t@ype}   stream_len      (stream a): nat

fun {a:t@ype}   stream_get      (stream a, nat): a
fun {a:t@ype}   stream_head     (stream a): a
fun {a:t@ype}   stream_tail     (stream a): stream a
fun {a:t@ype}   stream_take     (stream a, nat): stream a
fun {a:t@ype}   stream_drop     (stream a, nat): stream a

fun {a:t@ype}   stream_interleave (stream a, stream a): stream a
fun {a:t@ype}   stream_merge      (stream a, stream a, (a, a) -<cloref1> int): stream a

fun {a,b:t@ype} stream_zip      (stream a, stream b): stream (@(a, b))
fun {a:t@ype}   stream_foreach  (stream a, a -<cloref1> void): void
fun {a:t@ype}   stream_iforeach (stream a, (a, nat) -<cloref1> void): void
fun {a:t@ype}   stream_filter   (stream a, a -<cloref1> bool): stream a
fun {a,b:t@ype} stream_map      (stream a, a -<cloref1> b): stream b
fun {a,b:t@ype} stream_foldr    (stream a, b, (a, b) -<cloref1> b): b 
fun {a,b:t@ype} stream_foldl    (stream a, b, (a, b) -<cloref1> b): b 

fun {a:t@ype}   stream_any      (stream a, a -<cloref1> bool): bool
fun {a:t@ype}   stream_all      (stream a, a -<cloref1> bool): bool

fun stream_selftest (): void

overload [] 	  with stream_get

overload len      with stream_len 
overload empty 	  with stream_empty	    

overload head 	  with stream_head	     
overload tail 	  with stream_tail	     
overload take 	  with stream_take	     
overload drop 	  with stream_drop	

overload map  	  with stream_map 	     
overload filter	  with stream_filter      	
overload foldl 	  with stream_foldl	     
overload foldr 	  with stream_foldr	     
overload zip 	  with stream_zip	     
overload foreach  with stream_foreach	
overload iforeach with stream_iforeach  

overload any      with stream_any 
overload all      with stream_all     	


	