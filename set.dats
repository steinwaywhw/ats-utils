#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats" (* for int/nat/max *)

staload "./set.sats"
staload "./avl.sats"
staload "./list.sats"

staload _ = "./avl.dats"
staload _ = "./list.dats"

local 

assume set a = avltree a

in 

(******************************)

staload "./order.sats"
staload _ = "./order.dats"

implement (a) order_compare<set a> (xs, ys) = order_compare<avltree a> (xs, ys)

(******************************)

staload "./show.sats"
staload _ = "./show.dats"

implement (a) show_any<set a> (xs) = show_any<list a> (avltree_flatten xs)

(******************************)

implement {a} set_make () = avltree_make<a> ()
implement {a} set_insert (s, x) = avltree_insert (s, x)
implement {a} set_delete (s, x) = avltree_delete (s, x)

implement {a} set_empty (s) = avltree_empty<a> s 
implement {a} set_size (s) = avltree_size<a> s

implement {a} set_foreach (s, f) = avltree_foreach<a> (s, f)
implement {a} set_filter (s, f) = avltree_filter<a> (s, f)
implement {a,b} set_foldr (s, b, f) = list_foldr (avltree_flatten<a> s, b, f)
implement {a,b} set_map (s, f) = avltree_map<a,b> (s, f)

implement {a} set_subset (s, sub) = set_all (sub, lam x => set_member (s, x))
implement {a} set_member (s, x) = set_any (s, lam y => order_eq<a> (x, y))
implement {a} set_any (s, f) = avltree_any<a> (s, f)
implement {a} set_all (s, f) = avltree_all<a> (s, f)

implement {a} set_union (a, b) = set_foldr<a,set a> (b, a, lam (x, s) => if not (set_member (s, x)) then set_insert<a> (s, x) else s)
implement {a} set_intersect (a, b) = set_foldr<a, set a> (b, a, lam (x, s) => if not (set_member (s, x)) then set_delete (s, x) else s)
implement {a} set_diff (a, b) = set_foldr<a, set a> (b, a, lam (x, s) => if set_member (s, x) then set_delete (s, x) else s)

end
