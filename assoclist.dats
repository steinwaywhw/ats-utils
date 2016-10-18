#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "./assoclist.sats"
staload "./list.sats"
staload _ = "./list.dats"
staload "./maybe.sats"
staload _ = "./maybe.dats"

#define :: ListCons
#define nil ListNil

assume assoclist (a, b) = list (@(a, b))

(******************************)

staload "./order.sats"
staload _ = "./order.dats"

implement (a,b) order_compare<assoclist (a,b)> (xs, ys) = 
	case+ (xs, ys) of 
	| (nil _, nil _)     => 0
	| (nil _, ys)        => ~(list_len ys)
	| (xs, nil _)        => list_len xs
	| (x :: xs, y :: ys) =>
		let 
			val cmp = order_compare<@(a,b)> (x, y)
		in 
			if cmp = 0 then order_compare (xs, ys) else cmp 
		end

(******************************)

staload "./show.sats"
staload _ = "./show.dats"

implement (a:t@ype,b:t@ype) show_any<assoclist (a,b)> (xs) = let 
	fun show_list (xs: assoclist (a, b)): void = 
		case+ xs of 
		| nil ()      => ()
		| x :: nil () => ignoret (show_any x)
		| x :: xs     => ignoret (show_any x; show_sep<> (); show_list xs)
in 
	ignoret (show_begin (); show_list xs; show_end ())
end


(******************************)

implement {a,b} assoclist_make () = nil ()
implement {a,b} assoclist_empty (xs) = list_empty xs
implement {a,b} assoclist_insert (xs, k, v) = @(k,v) :: xs

implement {a,b} assoclist_delete (xs, k) = 
	case+ xs of 
	| nil () => nil ()
	| @(kk, vv) :: xs => if k \order_eq kk then xs else @(kk, vv) :: assoclist_delete (xs, k)

implement {a,b} assoclist_update (xs, k, v) = 
	case+ xs of 
	| nil () => nil ()
	| @(kk, vv) :: xs => if k \order_eq kk then @(k, v) :: xs else @(kk, vv) :: assoclist_update (xs, k, v)

implement {a,b} assoclist_find (xs, k) =
	case+ xs of 
	| nil () => Nothing ()
	| @(kk, vv) :: xs => if k \order_eq kk then Just vv else assoclist_find (xs, k)

