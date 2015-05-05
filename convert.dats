#define ATS_DYNLOADFLAG 0

staload "./util.sats"
staload "./list.sats"
staload "./stream.sats"

#define :: Cons

implement string_to_stream (s) = 
	if empty s
	then $delay Nil ()
	else $delay s[0] :: string_to_stream (string_range (s, 1, len (s) - 1))


implement {a} stream_to_list (xs) = 
	case+ !xs of 
	| x :: xs => Cons (x, stream_to_list xs)
	| Nil _ => Nil ()