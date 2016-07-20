#include "share/atspre_staload.hats"
#define ATS_DYNLOADFLAG 0

staload "libats/ML/SATS/string.sats"
staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./stream.sats"

exception StreamException of string

#define :: StreamCons
#define nil StreamNil

implement {a} stream_empty (xs) = 
	case+ !xs of 
	| nil () => true
	| _      => false

implement {a} stream_len (xs) = let 
	typedef nat = [n:nat] int n
in 
	stream_foldl<a,nat> (xs, 0, lam (_, len) => len + 1)
end

implement {a} stream_eq$eq (x, y) = 
	gcompare_val_val<a> (x, y) = 0 

implement {a} stream_eq (xs, ys) = 
	case+ (!xs, !ys) of 
	| (nil (), nil ()) => true 
	| (x :: xs, y :: ys) => stream_eq$eq<a> (x, y) andalso stream_eq (xs, ys)
	| (_, _) => false


implement {a,b} stream_zip (xs, ys) = $delay (
	case+ !xs of 
	| nil ()  => nil ()
	| x :: xs =>
		case+ !ys of 
		| nil ()  => nil ()
		| y :: ys => @(x, y) :: stream_zip (xs, ys)
)

implement {a} stream_foreach (xs, f) = let 
	val _ = stream_foldl<a,int> (xs, 0, lam (x, n) => (f x; 0))
in 
	()
end

implement {a} stream_iforeach (xs, f) = let 
	typedef nat = [n:nat] int n
	val _ = stream_foldl<a,nat> (xs, 0, lam (x, n) => (f (x, n); n+1))
in 
	()
end

implement {a} stream_head (xs) = 
	case+ !xs of
	| x :: _ => x
	| nil () => $raise StreamException ("stream is empty: " + $mylocation)

implement {a} stream_tail (xs) = 
	case+ !xs of
	| _ :: xs => xs
	| nil ()  => $raise StreamException ("stream is empty: " + $mylocation)
 
implement {a} stream_drop (xs, n) =
	if n = 0
	then xs 
	else stream_drop (stream_tail xs, n-1)

implement {a} stream_take (xs, n) = $delay (
	if n = 0 
	then nil ()
	else stream_head xs :: stream_take (stream_tail xs, n-1)
)
		

implement {a} stream_filter (xs, f) = 
	$delay stream_foldr<a, _stream a> (xs, nil (), lam (x, xs) => if f x then x :: ($delay xs) else xs)
 
implement {a, b} stream_map (xs, f) = 
	$delay stream_foldr<a, _stream b> (xs, nil (), lam (x, xs) => f x :: ($delay xs))

implement {a, b} stream_foldr (xs, base, f) = 
	case+ !xs of 
	| x :: xs => f (x, stream_foldr (xs, base, f))
	| nil ()  => base 

implement {a, b} stream_foldl (xs, base, f) = 
	case+ !xs of 
	| x :: xs => stream_foldl (xs, f (x, base), f)
	| nil ()  => base 

implement {a} stream_get (xs, n) = 
	stream_head (stream_drop (xs, n))

implement {a} stream_interleave (xs, ys) = $delay (
	case+ !xs of
	| x :: xs => x :: stream_interleave (ys, xs)
	| nil ()  => !ys
)
	 
implement {a} stream_merge (xs, ys, f) = $delay (
	case+ !xs of 
	| nil _ => !ys
	| x :: xs0 =>
		case+ !ys of 
		| nil _ => !xs
		| y :: ys0 => 
			if f (x, y) = 0
			then x :: stream_merge (xs0, ys, f)
			else y :: stream_merge (xs, ys0, f)
)

implement {a} stream_any (xs, f) = 
	stream_foldl (xs, false, lam (x, r) => f x orelse r)

implement {a} stream_all (xs, f) = 
	stream_foldl (xs, true, lam (x, r) => f x andalso r)


implement {a} stream_show$elm (x) = gprint_val<a> x
implement     stream_show$sep () = gprint_val<char> ':'

implement {a} stream_show_len (xs, n) = 
	if n = 0
	then ()
	else 
		case+ !xs of 
		| nil () => ()
		| x :: xs => 
			if stream_empty xs 
			then stream_show$elm<a> x
			else (stream_show$elm<a> x; stream_show$sep (); stream_show_len (xs, n - 1))


implement {a} stream_show (xs) = 
	stream_show_len (xs, stream_len xs)

local 
%{
#include <time.h>
#include <stdlib.h>

void stream_init () {
	srand(time(NULL));
}

%}
in 

implement stream_selftest () = () where {
	val _ = $extfcall (void, "stream_init")

	typedef nat = [n:nat] int n

	fun {a:t@ype} stream_random (n: nat): stream a = let 
		implement grandom_val<int> () = ($extfcall (int, "rand")) mod 31
	in 	
		$delay (if n = 0
				then nil{a} ()
				else grandom_val<a> () :: stream_random (n-1))
	end

	val passed = "\033[1mpassed\033[0m\n"

	val xs: stream int = stream_random<int> (10)
	val ys: stream char = $delay ('c' :: $delay ('d' :: $delay ('e' :: $delay nil ())))
	val zs: stream string = $delay ("asda" :: $delay ("asdddd" :: $delay (nil ())))
	val sep = "\n-----------------------\n"

	val _ = show xs
	val _ = show ()
	val _ = show ys 
	val _ = show ()
	val _ = show zs
	val _ = show sep

	val _ = show "stream_empty: "
	val _ = assertloc (stream_empty xs = false)
	val _ = assertloc (stream_empty ($delay nil ()))
	val _ = show passed

	val _ = show "stream_len: "
	val _ = assertloc ((stream_len xs) = stream_len (stream_tail xs) + 1)
	val _ = assertloc (stream_len ($delay nil{int} ()) = 0)
	val _ = show passed

	val _ = show "stream_eq: "
	val _ = assertloc (xs = xs)
	val _ = show passed

//	val _ = show "stream_append/stream_prepend: "
//	val _ = assertloc (stream_append (xs, 10) = stream_reverse (stream_prepend (stream_reverse xs, 10)))
//	val _ = show passed

//	val _ = show "stream_concat/stream_reverse: "
//	val t = stream_random (10)
//	val _ = assertloc (stream_reverse (stream_concat (xs, t)) = stream_concat (stream_reverse t, stream_reverse xs))
//	val _ = show passed

	val _ = show "stream_head/stream_tail: "
	val _ = assertloc (xs = $delay (stream_head xs :: stream_tail xs))
	val _ = show passed

	val _ = show "stream_take/stream_drop: "
	val _ = show (stream_merge (stream_take (ys, stream_len ys), stream_drop (ys, stream_len ys), lam (x, y) => 0))
	val _ = assertloc (ys = stream_merge (stream_take (ys, 2), stream_drop (ys, 2), lam (_, _) => 0))
	val _ = assertloc (ys = stream_merge (stream_take (ys, 0), stream_drop (ys, 0), lam (_, _) => 0))
	val _ = assertloc (ys = stream_merge (stream_take (ys, stream_len ys), stream_drop (ys, stream_len ys), lam (x, y) => 0))
	val _ = show passed

//	val _ = show "stream_find/stream_get: "
//	implement gcompare_val_val<nat> (x, y) = $effmask_all ((to_int x) - (to_int y))
//	val _ = assertloc (Just 3 = stream_find (xs, stream_get (xs, 3)))
//	val _ = show passed

	val _ = show "stream_any/stream_all: "
	val _ = assertloc (stream_any (xs, lam x => x = stream_get (xs, 3)) = true)
	val _ = assertloc (stream_all (xs, lam x => x = stream_get (xs, 3)) = false)
	val _ = show passed

	val _ = show "stream_map/stream_zip: "
	val _ = assertloc (xs = stream_map<int,int> (stream_map<int,int> (xs, lam x => x + 10), lam x => x - 10))
	val _ = assertloc (xs = stream_map<@(int,int),int> (stream_zip<int,int> (xs, xs), lam x => x.0))
	val _ = show passed 

	val _ = show "stream_filter/stream_foreach/stream_iforeach: "
	val count1 = ref<int> 0
	val count2 = ref<int> 0
	val _ = stream_foreach<int> (xs, lam x => if x <= 3 then !count1 := !count1 + 1)
	val _ = stream_iforeach<int> (xs, lam (x, n) => if x <= 3 then !count2 := !count2 + 1)
	val _ = assertloc (stream_len xs - !count1 = stream_len (stream_filter (xs, lam x => x > 3)))
	val _ = show passed
}
end