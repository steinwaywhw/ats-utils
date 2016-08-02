#include "share/atspre_staload.hats"
#define ATS_DYNLOADFLAG 0

staload "libats/ML/SATS/string.sats"
staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./list.sats"

staload "./maybe.sats"
staload _ = "./maybe.dats"

#define :: ListCons
#define nil ListNil

exception ListException of string

implement {a} list_empty (xs) = 
	case+ xs of 
	| ListCons _ => false
	| ListNil  _ => true

implement {a} list_len (xs) = 
	case+ xs of
	| x :: xs => 1 + (list_len xs)
	| nil ()  => 0

implement {a} list_eq$eq (x, y) = gcompare_val_val<a> (x, y) = 0

implement {a} list_eq (xs, ys) = 
	case+ (xs, ys) of 
	| (nil (), nil ())   => true 
	| (x :: xs, y :: ys) => list_eq$eq<a> (x, y) andalso list_eq (xs, ys)
	| (_, _)             => false

implement {a} list_get (xs, i) = 
	list_head (list_drop (xs, i))

implement {a} list_prepend (xs, x) = 
	x :: xs

implement {a} list_append (xs, x) = 
	list_foldr (xs, x :: nil (), lam (x, xs) => x :: xs)

implement {a} list_head (xs) = 
	case+ xs of 
	| x :: _ => x
	| _ => $raise ListException ("list is empty: " + $mylocation)

implement {a} list_tail (xs) = 
	case+ xs of 
	| x :: xs => xs 
	| nil ()  => $raise ListException ("list is empty: " + $mylocation)

implement {a} list_drop (xs, i) = 
	if i = 0
	then xs 
	else list_drop (list_tail xs, i-1)

implement {a} list_take (xs, i) = 
	if i = 0
	then nil () 
	else list_head xs :: list_take (list_tail xs, i-1)

implement {a} list_concat (xs, ys) =  
	list_foldr (xs, ys, lam (x, xs) => x :: xs)

implement {a} list_reverse (xs) = 
	list_foldl (xs, nil (), lam (x, xs) => x :: xs)

implement {a, b} list_map (xs, f) =
	list_foldr (xs, nil (), lam (x, xs) => (f x) :: xs)

implement {a, b} list_foldr (xs, base, f) =
	case+ xs of 
	| nil ()  => base
	| x :: xs => f (x, list_foldr (xs, base, f)) 

implement {a, b} list_foldl (xs, base, f) =
	case+ xs of 
	| nil ()  => base
	| x :: xs => list_foldl<a,b> (xs, f (x, base), f)

implement {a} list_filter (xs, f) =
	list_foldr<a,list a> (xs, nil{a} (), lam (x, xs) => if f x then x :: xs else xs)

implement {a} list_foreach (xs, f) = let 
	val _ = list_foldl<a,int> (xs, 0, lam (x, n) => (f x; 0))
in 
	()
end

implement {a} list_iforeach (xs, f) = let 
	typedef nat = [n:nat] int n 
	val _ = list_foldl<a,nat> (xs, 0, lam (x, i) => (f (x, i); i + 1))
in 
	()
end

implement {a, b} list_zip (xs, ys) = 
	case+ (xs, ys) of 
	| (nil _, _) => nil ()
	| (_, nil _) => nil () 
	| (x :: xs, y :: ys) => @(x, y) :: list_zip (xs, ys)


implement {a} list_find$eq (x, y) = gcompare_val_val<a> (x, y) = 0

implement {a} list_find (xs, obj) = let 
	typedef nat = [n:nat] int n 
in 
	case+ xs of 
	| nil _ => Nothing{nat} ()
	| x :: xs => 
		if list_find$eq<a> (x, obj)
		then Just 0
		else maybe_bind<nat,nat> (list_find<a> (xs, obj), lam x => x + 1)
end

implement {a} list_any (xs, f) =
	list_foldl (xs, false, lam (x, b) => f x orelse b)

implement {a} list_all (xs, f) = 
	list_foldl (xs, true, lam (x, b) => f x andalso b)
	

implement     list_show$sep () = show ":"
implement {a} list_show$elm (x) = gprint_val<a> x 

implement {a} list_show (xs) = 
	case+ xs of 
	| nil () => () 
	| x :: nil () => list_show$elm<a> x 
	| x :: xs => (list_show$elm<a> x; list_show$sep (); list_show<a> xs)


//local
//staload "./stream.sats"
//staload _ = "./stream.dats"
//in
//implement {a} list_to_stream (xs) = $delay (
//	case+ xs of 
//	| ListNil () => StreamNil ()
//	| ListCons (x, xs) => StreamCons (x, list_to_stream xs)
//)

//implement {a} list_from_stream (xs) = 
//	case+ !xs of 
//	| StreamNil () => ListNil ()
//	| StreamCons (x, xs) => ListCons (x, list_from_stream xs)
//end


local 

typedef nat = [n:nat] int n
extern castfn to_int {a:t@ype} (a): int 
extern castfn to_nat {a:t@ype} (a): nat

%{
#include <time.h>
#include <stdlib.h>

void init () {
	srand(time(NULL));
}

%}

in 

implement list_selftest () = () where {

	val _ = $extfcall (void, "init")

	fun {a:t@ype} list_random (n: nat): list a = let 
		implement grandom_val<int> () = ($extfcall (int, "rand")) mod 31
	in
		if n = 0
		then nil{a} ()
		else grandom_val<a> () :: list_random (n-1)
	end

	val passed = "\033[1mpassed\033[0m\n"

	val xs: list int = list_random<int> (10)
	val ys: list char = 'c' :: 'd' :: 'e' :: nil ()
	val zs: list string = "asda" :: "asdddd" :: nil ()
	val sep = "\n-----------------------\n"

	val _ = show xs
	val _ = show ()
	val _ = show ys 
	val _ = show ()
	val _ = show zs
	val _ = show sep

	val _ = show "list_empty: "
	val _ = assertloc (list_empty xs = false)
	val _ = assertloc (list_empty (nil ()))
	val _ = show passed

	val _ = show "list_len: "
	val _ = assertloc ((list_len xs) = list_len (list_tail xs) + 1)
	val _ = assertloc (list_len (nil{int} ()) = 0)
	val _ = show passed

	val _ = show "list_eq: "
	val _ = assertloc (xs = xs)
	val _ = show passed

	val _ = show "list_append/list_prepend: "
	val _ = assertloc (list_append (xs, 10) = list_reverse (list_prepend (list_reverse xs, 10)))
	val _ = show passed

	val _ = show "list_concat/list_reverse: "
	val t = list_random (10)
	val _ = assertloc (list_reverse (list_concat (xs, t)) = list_concat (list_reverse t, list_reverse xs))
	val _ = show passed

	val _ = show "list_head/list_tail: "
	val _ = assertloc (xs = list_head xs :: list_tail xs)
	val _ = show passed

	val _ = show "list_take/list_drop: "
	val _ = assertloc (xs = list_concat (list_take (xs, 5), list_drop (xs, 5)))
	val _ = assertloc (xs = list_concat (list_take (xs, 0), list_drop (xs, 0)))
	val _ = assertloc (xs = list_concat (list_take (xs, list_len xs), list_drop (xs, list_len xs)))
	val _ = show passed

	val _ = show "list_find/list_get: "
	implement gcompare_val_val<nat> (x, y) = $effmask_all ((to_int x) - (to_int y))
	val _ = assertloc (Just 3 = list_find (xs, list_get (xs, 3)))
	val _ = show passed

	val _ = show "list_any/list_all: "
	val _ = assertloc (list_any (xs, lam x => x = list_get (xs, 3)) = true)
	val _ = assertloc (list_all (xs, lam x => x = list_get (xs, 3)) = false)
	val _ = show passed

	val _ = show "list_map/list_zip: "
	val _ = assertloc (xs = list_map<int,int> (list_map<int,int> (xs, lam x => x + 10), lam x => x - 10))
	val _ = assertloc (xs = list_map<@(int,int),int> (list_zip<int,int> (xs, xs), lam x => x.0))
	val _ = show passed 

	val _ = show "list_filter/list_foreach/list_iforeach: "
	val count1 = ref<int> 0
	val count2 = ref<int> 0
	val _ = list_foreach<int> (xs, lam x => if x <= 3 then !count1 := !count1 + 1)
	val _ = list_iforeach<int> (xs, lam (x, n) => if x <= 3 then !count2 := !count2 + 1)
	val _ = assertloc (list_len xs - !count1 = list_len (list_filter (xs, lam x => x > 3)))
	val _ = show passed

}

end