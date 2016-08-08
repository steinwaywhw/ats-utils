#include "share/atspre_staload.hats" (* for int/nat/max *)
#define ATS_DYNLOADFLAG 0

//staload "libats/ML/SATS/string.sats"
//staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./map.sats"
staload "./avl.sats"
staload _ = "./avl.dats"
staload "./list.sats"
staload _ = "./list.dats"
staload "./maybe.sats"
staload _ = "./maybe.dats"

//staload "./list.sats"
//staload _ = "./list.dats"

local 

assume map (k, v) = avltree (@(k, v))
//implement {a} avltree_cmp$elm (a, b) = map_cmp$elm (a, b)

in 

implement {k,v} map_make () = avltree_make<@(k,v)> ()
implement {a}   map_cmp$elm (a, b) = gcompare_val_val<a> (a, b)
implement {k,v} map_eq (a, b) = let 
	implement avltree_cmp$elm<@(k,v)> (a, b) = map_cmp$elm<k> (a.0, b.0)
in 
	avltree_eq (a, b)
end

implement {k,v} map_insert (m, k, v) = let 
	implement avltree_cmp$elm<@(k,v)> (a, b) = map_cmp$elm<k> (a.0, b.0)
in 
	avltree_insert (m, @(k, v))
end 

implement {k,v} map_delete (m, k) = let 
	implement avltree_cmp$elm<@(k,v)> (a, b) = map_cmp$elm<k> (a.0, b.0)
	staload UN = "prelude/SATS/unsafe.sats"
in 
	avltree_delete (m, @(k, $UN.cast{v} 0))
end

implement {k,v} map_update (m, k, v) = 
	map_insert (map_delete (m, k), k, v)

implement {k,v} map_find (m, k) = let 
	implement avltree_cmp$elm<@(k,v)> (a, b) = map_cmp$elm<k> (a.0, b.0)
	staload UN = "prelude/SATS/unsafe.sats"
in 
	maybe_bind (avltree_find (m, @(k, $UN.cast{v} 0)), lam x => x.1)
end

implement {k,v} map_member (m, k) = 
	case+ map_find (m, k) of 
	| Nothing () => false 
	| Just (_)   => true 

implement {k,v} map_empty (m) = avltree_empty<@(k,v)> m
implement {k,v} map_size (m) = avltree_size<@(k,v)> m
implement {k,v} map_foreach (m, f) = avltree_foreach<@(k,v)> (m, f)
implement {k,v} map_filter (m, f) = avltree_filter<@(k,v)> (m, f)
//implement {k,v,b} map_foldr (m, b, f) = list_foldr (avltree_flatten<a> m, b, f)
//implement {k,v,b} map_map (m, f) = avltree_map<a,b> (m, f)
implement {k,v} map_any (m, f) = avltree_any<@(k,v)> (m, f)
implement {k,v} map_all (m, f) = avltree_all<@(k,v)> (m, f)

end
