#include "share/atspre_staload.hats"
#include "./atsutils.hats"
staload "./list.sats"
staload "./string.sats"
staload "./maybe.sats"

%{
#include <time.h>
#include <stdlib.h>

void init () {
	srand(time(NULL));
}
%}

implement maybe_selftest () = {

	val _ = show (Nothing{int} ())
	val _ = show ()

	val _ = show (Just{string} "hahaha")
	val _ = show ()

	val _ = show (Just{int} 123)
	val _ = show () 

	val x: maybe string = maybe_bind (Just 123, lam (x:int):string => "after bind")
	val _ = show x
	val _ = show ()

	val _ = assertloc (Nothing{int} () \eq Nothing ())
	val _ = assertloc (Just{int} 3 \eq Just 3)
	val _ = assertloc (Just{string} "aaa" \eq Just "aaa")
}

implement list_selftest () = {
	#define :: ListCons 
	#define nil ListNil
	val _ = $extfcall (void, "init")

	fun {a:t@ype} list_random (n: nat): list a = let 
		implement grandom_val<int> () = ($extfcall (int, "rand")) mod 31
	in
		if n = 0
		then nil{a} ()
		else grandom_val<a> () :: list_random<a> (n-1)
	end

	val passed = "\033[1mpassed\033[0m\n"

	val xs: list int = list_random<int> (10)
	val ys: list char = 'c' :: 'd' :: 'e' :: nil () 
	val zs: list string = "asda" :: "asdddd" :: nil ()
	val sep:string = "\n-----------------------\n"

	val _ = show xs
	val _ = show ()
	val _ = show ys 
	val _ = show ()
	val _ = show zs
	val _ = show<string> sep

	val _ = show<string> "list_empty: "
	val _ = assertloc (list_empty xs = false)
	val _ = assertloc (list_empty (nil{int} ()))
	val _ = show<string> passed

	val _ = show<string> "list_len: "
	val _ = assertloc ((list_len xs) = list_len (list_tail xs) + 1)
	val _ = assertloc (list_len (nil{int} ()) = 0)
	val _ = show<string> passed

	val _ = show<string> "list_eq: "
	val _ = assertloc (xs \eq xs)
	val _ = show<string> passed

	val _ = show<string> "list_append/list_prepend: "
	val _ = assertloc (list_append (xs, 10) \eq list_reverse (list_prepend (list_reverse xs, 10)))
	val _ = show<string> passed

	val _ = show<string> "list_concat/list_reverse: "
	val t = list_random (10)
	val _ = assertloc (list_reverse (list_concat (xs, t)) \eq list_concat (list_reverse t, list_reverse xs))
	val _ = assertloc (list_concat<int> (1 :: 2 :: nil (), 3 :: 4 :: nil ()) \eq 1 :: 2 :: 3 :: 4 :: nil ())
	val _ = show<string> passed

	val _ = show<string> "list_head/list_tail: "
	val _ = assertloc (xs \eq (list_head xs :: list_tail xs))
	val _ = show<string> passed

	val _ = show<string> "list_take/list_drop: "
	val _ = assertloc (xs \eq list_concat (list_take (xs, 5), list_drop (xs, 5)))
	val _ = assertloc (xs \eq list_concat (list_take (xs, 0), list_drop (xs, 0)))
	val _ = assertloc (xs \eq list_concat (list_take (xs, list_len xs), list_drop (xs, list_len xs)))
	val _ = show<string> passed

	val _ = show<string> "list_find/list_get: "
	implement gcompare_val_val<nat> (x, y) = x - y
	val _ = assertloc (Just 3 \eq list_find (xs, xs[3]))
	val _ = show<string> passed

	val _ = show<string> "list_any/list_all: "
	val _ = assertloc (list_any (xs, lam x => x = list_get (xs, 3)) = true)
	val _ = assertloc (list_all (xs, lam x => x = list_get (xs, 3)) = false)
	val _ = show<string> passed

	val _ = show<string> "list_map/list_zip: "
	val _ = assertloc (xs \eq list_map<int,int> (list_map<int,int> (xs, lam x => x + 10), lam x => x - 10))
	val _ = assertloc (xs \eq list_map<@(int,int),int> (list_zip<int,int> (xs, xs), lam x => x.0))
	val _ = show<string> passed

	val _ = show<string> "list_filter/list_foreach/list_iforeach: "
	val count1 = ref<int> 0
	val count2 = ref<int> 0
	val _ = list_foreach<int> (xs, lam x => if x <= 3 then !count1 := !count1 + 1)
	val _ = list_iforeach<int> (xs, lam (x, n) => if x <= 3 then !count2 := !count2 + 1)
	val _ = assertloc (list_len xs - !count1 = list_len (list_filter (xs, lam x => x > 3)))
	val _ = show<string> passed
}

implement string_selftest () = {

	#define :: ListCons 
	#define nil ListNil

	val sep = "\n----------------\n" : string
	val _ = show (string_from_char('C'))
	val _ = show sep
	val _ = show (string_from_int(~12345222))
	val _ = show sep
	val _ = show (string_to_int(" -1234562222 "))
	val _ = show sep 
	val _ = show (string_to_double("  -123.456 \n") = ~123.456)
	val _ = show sep
	val _ = show (string_explode "Abcdefg")
	val _ = show sep
	val _ = show (string_unexplode (string_explode "Abcdefg") = "Abcdefg")
	val _ = show sep
	val _ = show<maybe nat> (string_find ("abcdefgsssasdsssa", "sss"))
	val _ = show sep 
	val _ = show (string_concat("abcde", "12345"))
	val _ = show sep
	val _ = show (string_join ("aaa" :: "bbb" :: "ccc" :: nil(), "XX"))
	val _ = show sep
	val _ = foreach (string_split ("aaaXXXbbbXXcccXXX", "XX"), lam x => show<string> x where { val _ = print_newline ()})
	val _ = show sep 
	val _ = show (string_append ("abc", 'C'))
	val _ = show sep 
	val _ = show (string_prepend ("abc", 'C'))
	val _ = show sep 
	val _ = show (string_range ("abcde", 1, 4))
	val _ = show sep 
	val _ = show (string_range ("abcde", 2, 1))
	val _ = show sep 
	val _ = show (cmp<string> ("abcde", "abcde"))
	val _ = show sep 
	val _ = show (cmp<string> ("abc", "ABC"))
	val _ = show sep 
	val _ = show (eq<string> ("ab", "ab"))
	val _ = show sep 
	val _ = show ()

}


implement main0 () = () where {
	val _ = maybe_selftest ()
	val _ = list_selftest ()
	val _ = string_selftest ()
//	val _ = stream_selftest ()
//	val _ = avltree_selftest ()
}