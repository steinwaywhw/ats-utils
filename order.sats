staload "symintr.sats"


fun {a:t@ype} order_compare (INV(a), a): int 

fun {a:t@ype} order_eq (INV(a), a): bool 
fun {a:t@ype} order_neq (INV(a), a): bool 
fun {a:t@ype} order_gt (INV(a), a): bool
fun {a:t@ype} order_lt (INV(a), a): bool 
fun {a:t@ype} order_gte (INV(a), a): bool 
fun {a:t@ype} order_lte (INV(a), a): bool

fun {a:t@ype} order_min (INV(a), a): a 
fun {a:t@ype} order_max (INV(a), a): a

overload cmp  with order_compare
overload eq   with order_eq
overload neq  with order_neq
overload gt   with order_gt
overload lt   with order_lt
overload gte  with order_gte
overload lte  with order_lte
