staload "symintr.sats"


fun {a:t@ype} order_compare (a, a): int 

fun {a:t@ype} order_eq (a, a): bool 
fun {a:t@ype} order_neq (a, a): bool 
fun {a:t@ype} order_gt (a, a): bool
fun {a:t@ype} order_lt (a, a): bool 
fun {a:t@ype} order_gte (a, a): bool 
fun {a:t@ype} order_lte (a, a): bool

fun {a:t@ype} order_min (a, a): a 
fun {a:t@ype} order_max (a, a): a

overload cmp  with order_compare
overload eq   with order_eq
overload neq  with order_neq
overload gt   with order_gt
overload lt   with order_lt
overload gte  with order_gte
overload lte  with order_lte
