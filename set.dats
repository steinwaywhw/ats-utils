#include "share/atspre_staload.hats" (* for int/nat/max *)
#define ATS_DYNLOADFLAG 0

//staload "libats/ML/SATS/string.sats"
//staload _ = "libats/ML/DATS/string.dats"

staload "./symintr.sats"
staload "./set.sats"
staload "./avl.sats"
staload _ = "./avl.dats"
staload "./list.sats"
staload _ = "./list.dats"

//staload "./list.sats"
//staload _ = "./list.dats"

local 

assume set a = avltree a

in 

implement {a} set_make () = avltree_make<a> ()
implement {a} set_eq$elm (a, b) = gcompare_val_val<a> (a, b) = 0
implement {a} set_eq (a, b) = set_subset (a, b) andalso set_subset (b, a)
implement {a} set_subset (s, sub) = set_all (sub, lam x => set_member (s, x))
implement {a} set_insert (s, x) = avltree_insert (s, x)
implement {a} set_delete (s, x) = avltree_delete (s, x)
implement {a} set_member (s, x) = set_any (s, lam y => set_eq$elm (x, y))
implement {a} set_empty (s) = avltree_empty<a> s 
implement {a} set_size (s) = avltree_size<a> s
implement {a} set_foreach (s, f) = avltree_foreach<a> (s, f)
implement {a} set_filter (s, f) = avltree_filter<a> (s, f)
implement {a,b} set_foldr (s, b, f) = list_foldr (avltree_flatten<a> s, b, f)
implement {a,b} set_map (s, f) = avltree_map<a,b> (s, f)
implement {a} set_any (s, f) = avltree_any<a> (s, f)
implement {a} set_all (s, f) = avltree_all<a> (s, f)

end
