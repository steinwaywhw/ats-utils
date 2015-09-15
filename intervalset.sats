staload "./list.sats"

abstype interval_set (t@ype) = ptr 

(* interval domain *)
fun {pt:t@ype} intdom_compare (pt, pt): int 
fun {pt:t@ype} intdom_succ (pt): pt 
fun {pt:t@ype} intdom_pred (pt): pt 
fun {pt:t@ype} intdom_is_succ (pt, pt): bool 
fun {pt:t@ype} intdom_lowerbound (): pt 
fun {pt:t@ype} intdom_upperbound (): pt 

fun {pt:t@ype} intdom_min (pt, pt): pt 
fun {pt:t@ype} intdom_max (pt, pt): pt

(* bounds *)
fun {pt:t@ype} intset_empty (): interval_set pt
fun {pt:t@ype} intset_universe (): interval_set pt

(* constructors *)
fun {pt:t@ype} intset_singleton (pt): interval_set pt 
fun {pt:t@ype} intset_interval (pt, pt): interval_set pt 

(* predicates *)
fun {pt:t@ype} intset_is_empty (interval_set pt): bool
fun {pt:t@ype} intset_is_universe (interval_set pt): bool
fun {pt:t@ype} intset_member (interval_set pt, pt): bool 

(* accessors *)
fun {pt:t@ype} intset_items (interval_set pt): list pt
fun {pt:t@ype} intset_intervals (interval_set pt): list @(pt, pt)

(* modifiers *)
fun {pt:t@ype} intset_add (interval_set pt, pt): interval_set pt 
fun {pt:t@ype} intset_add_interval (interval_set pt, pt, pt): interval_set pt 

(* set operation *)
fun {pt:t@ype} intset_complement (interval_set pt): interval_set pt 
fun {pt:t@ype} intset_union (interval_set pt, interval_set pt): interval_set pt
fun {pt:t@ype} intset_intersect (interval_set pt, interval_set pt): interval_set pt
fun {pt:t@ype} intset_difference (interval_set pt, interval_set pt): interval_set pt

(* order *)
fun {pt:t@ype} intset_compare (interval_set pt, interval_set pt): int 
fun {pt:t@ype} intset_is_subset (interval_set pt, interval_set pt): bool


