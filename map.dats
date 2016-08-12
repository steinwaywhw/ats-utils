#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats" (* for int/nat/max *)

staload "./map.sats"
staload "./avl.sats"
staload "./list.sats"
staload "./maybe.sats"

staload _ = "./list.dats"
staload _ = "./avl.dats"
staload _ = "./maybe.dats"

exception MapException of string

local 

assume map (k, v) = avltree (@(k, v))

in 

(******************************)

staload "./order.sats"
staload _ = "./order.dats"

implement (k,v:t@ype) order_compare<map(k,v)> (xs, ys) = 
	order_compare<avltree (@(k,v))> (xs, ys)

(******************************)

staload "./show.sats"
staload _ = "./show.dats"

implement (k,v:t@ype) show_any<map(k,v)> (m) = let 
	
	implement show_any<@(k,v)> (x) = 
		(show_any<k> x.0; show_any<string> ":"; show_any<v> x.1)

	implement show_sep<> () = show_any<string> ", "
in 
	show_any<list @(k,v)> (avltree_flatten m)
end

(******************************)

implement {k,v} map_make () = avltree_make<@(k,v)> ()

implement {k,v} map_insert (m, k, v) = let 
	implement order_compare<@(k,v)> (a, b) = order_compare<k> (a.0, b.0)
in 
	avltree_insert (m, @(k, v))
end 

implement {k,v} map_delete (m, k) = let 
	implement order_compare<@(k,v)> (a, b) = order_compare<k> (a.0, b.0)
in 
	avltree_delete (m, @(k, $UNSAFE.cast{v} 0))
end

implement {k,v} map_update (m, k, v) = 
	map_insert (map_delete (m, k), k, v)

implement {k,v} map_get (m, k) = 
	case+ map_find<k,v> (m, k) of 
	| Nothing _ => $raise MapException ($mylocation)
	| Just v    => v

implement {k,v} map_find (m, k) = let 
	implement order_compare<@(k,v)> (a, b) = order_compare<k> (a.0, b.0)
in 
	maybe_bind (avltree_find (m, @(k, $UNSAFE.cast{v} 0)), lam x => x.1)
end

(******************************)

implement {k,v} map_empty (m) = avltree_empty<@(k,v)> m
implement {k,v} map_size (m) = avltree_size<@(k,v)> m

(******************************)

implement {k,v} map_foreach (m, f) = avltree_foreach<@(k,v)> (m, lam entry => f (entry.0))
implement {k,v} map_filter (m, f) = avltree_filter<@(k,v)> (m, lam entry => f (entry.0))

(******************************)

implement {k,v} map_member (m, k) = 
	case+ map_find (m, k) of 
	| Nothing () => false 
	| Just (_)   => true 

implement {k,v} map_any (m, f) = avltree_any<@(k,v)> (m, lam x => f (x.0))
implement {k,v} map_all (m, f) = avltree_all<@(k,v)> (m, lam x => f (x.0))

end
