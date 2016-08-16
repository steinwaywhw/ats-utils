#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "./list.sats"
staload "./maybe.sats"
staload _ = "./maybe.dats"

#define :: ListCons
#define nil ListNil

exception ListException of string

(******************************)

staload "./order.sats"
staload _ = "./order.dats"

implement (a) order_compare<list a> (xs, ys) = 
	case+ (xs, ys) of 
	| (nil _, nil _)     => 0
	| (nil _, ys)        => ~(list_len ys)
	| (xs, nil _)        => list_len xs
	| (x :: xs, y :: ys) =>
		let val cmp = order_compare (x, y)
		in if cmp = 0 then order_compare (xs, ys) else cmp end

(******************************)

staload "./show.sats"
staload _ = "./show.dats"

implement (a) show_any<list a> (xs) = 
	case+ xs of 
	| nil ()      => ()
	| x :: nil () => ignoret (show_any<a> x)
	| x :: xs     => ignoret (show_any<a> x; show_sep<> (); show_any xs)

(******************************)

implement {a} list_empty (xs) = 
	case+ xs of 
	| ListCons _ => false
	| ListNil  _ => true

implement {a} list_len (xs) = 
	case+ xs of
	| x :: xs => 1 + list_len xs
	| nil ()  => 0

(******************************)

implement {a} list_get (xs, i) = 
	list_head (list_drop (xs, i))

implement {a} list_prepend (xs, x) = 
	x :: xs

implement {a} list_append (xs, x) = 
	list_foldr (xs, x :: nil (), lam (x, xs) => x :: xs)

implement {a} list_head (xs) = 
	case+ xs of 
	| x :: _ => x
	| _ => $raise ListException ($mylocation)

implement {a} list_tail (xs) = 
	case+ xs of 
	| x :: xs => xs 
	| nil ()  => $raise ListException ($mylocation)

implement {a} list_drop (xs, i) = 
	if i = 0
	then xs 
	else 
		if list_empty xs then xs 
		else list_drop (list_tail xs, i-1)

implement {a} list_take (xs, i) = 
	if i = 0
	then nil () 
	else 
		if list_empty xs then xs 
		else list_head xs :: list_take (list_tail xs, i-1)

implement {a} list_concat (xs, ys) =  
	list_foldr (xs, ys, lam (x, xs) => x :: xs)

implement {a} list_reverse (xs) = 
	list_foldl (xs, nil (), lam (x, xs) => x :: xs)

implement {a} list_find (xs, obj) =
	case+ xs of 
	| nil _ => Nothing{nat} ()
	| x :: xs => 
		if order_eq (x, obj)
		then Just 0
		else maybe_bind<nat,nat> (list_find (xs, obj), lam x => x + 1)

(******************************)

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
	val _ = list_foldl<a,nat> (xs, 0, lam (x, i) => (f (x, i); i + 1))
in 
	()
end

implement {a, b} list_zip (xs, ys) = 
	case+ (xs, ys) of 
	| (nil _, _) => nil ()
	| (_, nil _) => nil () 
	| (x :: xs, y :: ys) => @(x, y) :: list_zip (xs, ys)


(******************************)

implement {a} list_any (xs, f) =
	list_foldl (xs, false, lam (x, b) => f x orelse b)

implement {a} list_all (xs, f) = 
	list_foldl (xs, true, lam (x, b) => f x andalso b)
	
implement {a} list_member (xs, x) = 
	list_any (xs, lam y => order_eq<a> (x, y))



