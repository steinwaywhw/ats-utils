#include "share/atspre_staload.hats"
#define ATS_DYNLOADFLAG 0

staload "libats/ML/SATS/string.sats"
staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./linstream.sats"
staload "./stream.sats"

#define ::  LinStreamCons 
#define nil LinStreamNil

exception LinStreamException of string

implement {a} linstream_free (xs)  = lazy_vt_free xs
implement {a} linstream_force (xs) = lazy_vt_force xs

implement {a} linstream_free_elm$default (x) = let 
	staload UN = "prelude/SATS/unsafe.sats"
in 
	$UN.cast2void x 
end 

implement (a:t@ype) linstream_free_elm<a> (x) = linstream_free_elm$default<a> x

implement {a} linstream_empty (xs) = 
	case+ !xs of 
	| ~(nil _)   => true 
	| ~(x :: xs) => let val _ = (linstream_free_elm x; ~xs) in false end 

implement {a} linstream_head (xs) = 
	case+ !xs of 
	| ~(nil _)   => (xs := $ldelay (nil ()); $raise LinStreamException ("stream is empty: " + $mylocation))
	| ~(x :: ys) => (xs := ys; x)

implement {a} linstream_tail (xs) = 
	case+ !xs of 
	| ~(nil _)   => $raise LinStreamException ("stream is empty: " + $mylocation)
	| ~(x :: xs) => let val () = linstream_free_elm x in xs end

implement {a} linstream_take (xs, n) = let 
	typedef nat = [n:nat] int n
	fun loop (xs: &linstream a >> _, n: nat): _linstream a =
		if n = 0 
		then LinStreamNil ()
		else 
			case+ !xs of 
			| ~(nil _)   => let val () = xs := $ldelay (nil ()) in $raise LinStreamException ("stream is too short: " + $mylocation) end 
			| ~(x :: ys) => let val () = xs := ys in x :: $ldelay (loop (xs, n-1)) end 
in 
	$ldelay (loop (xs, n))
end

implement {a} linstream_drop (xs, n) = 
	if n = 0
	then xs 
	else 
		case+ !xs of 
		| ~(x :: xs) => let val () = linstream_free_elm x in linstream_drop (xs, n-1) end 
		| ~(nil _)   => $raise LinStreamException ("stream is too short: " + $mylocation)

implement {a} linstream_foreach (xs, f) = let 
	val _ = linstream_foldl<a,int> (xs, 0, lam (x, n) => (f x; 0))
in 
	() 
end

implement {a} linstream_iforeach (xs, f) = let 
	typedef nat = [n:nat] int n
	val _ = linstream_foldl<a,nat> (xs, 0, lam (x, n) => (f (x, n); n+1))
in 
	() 
end

implement {a,b} linstream_zip (xs, ys) = let
	fun loop (xs: linstream a, ys: linstream b): _linstream (@(a, b)) = 
		case+ !xs of 
		| ~(nil _)   => let val () = ~ys in LinStreamNil () end
		| ~(x :: xs) => 
			case+ !ys of 
			| ~(nil _) => 
				let 
					val () = ~xs 
					val () = linstream_free_elm x
				in 
					LinStreamNil () 
				end 
			| ~(y :: ys) => LinStreamCons (@(x, y), $ldelay (loop (xs, ys), (~xs; ~ys)))
in 
	$ldelay (loop (xs, ys), (~xs; ~ys))
end

implement {a,b} linstream_map (xs, f) = let 
	fun loop (xs: linstream a): _linstream b = let 
		val forced = !xs 
	in 
		case+ forced of 
		| ~LinStreamNil () => LinStreamNil ()
		| @LinStreamCons (x, xs) => 
			let 
				val y = f x 
				val () = linstream_free_elm x
				val xs = xs 
				val () = free@ forced
			in 
				LinStreamCons (y, $ldelay (loop xs, ~xs))
			end
	end 
in 
	$ldelay (loop xs, ~xs)
end


implement {a,b} linstream_foldl (xs, base, f) = let 
	val forced = !xs 
in 
	case+ forced of 
	| ~LinStreamNil () => base 
	| @LinStreamCons (x, xs) => 
		let 
			val base = f (x, base)
			val () = linstream_free_elm x
			val xs = xs 
			val () = free@ forced
		in 
			linstream_foldl (xs, base, f)
		end
end

implement {a,b} linstream_foldr (xs, base, f) = let 
	val forced = !xs 
in 
	case+ forced of 
	| ~LinStreamNil () => base 
	| @LinStreamCons (x, xs) => 
		let 
			val ret = f (x, linstream_foldr (xs, base, f))
			val () = linstream_free_elm x
			val () = free@ forced 
		in 
			ret 
		end
end

implement {a} linstream_filter (xs, f) = let 
	fun loop (xs: linstream a, f: (&a) -<cloref1> bool): _linstream a = let 
		val forced = !xs
	in 
		case+ forced of 
		| ~LinStreamNil _ => nil ()
		| @LinStreamCons (x, xs) => 
			if f x
			then (xs := linstream_filter (xs, f); fold@ forced; forced)
			else 
				let 
					val () = linstream_free_elm x
					val xs = xs
					val () = free@ forced
				in 
					loop (xs, f)
				end
	end
in 
	$ldelay (loop (xs, f), ~xs)
end

implement {a} linstream_to_stream (xs) = let 
	staload UN = "prelude/SATS/unsafe.sats"
in 
	case+ !xs of 
	| ~(nil _)   => $delay StreamNil ()
	| ~(x :: xs) => 
		let 
			val xs = $UN.castvwtp0{ptr} xs
		in 
			$delay StreamCons (x, linstream_to_stream ($UN.castvwtp0{linstream a} xs))
		end
end



implement linstream_selftest () = () where {
	
}

