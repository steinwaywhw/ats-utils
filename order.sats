staload "symintr.sats"


fun {a:t@ype} order_compare (INV(a), INV(a)): int 
fun {a:t@ype} order_compare_addr (INV(a), INV(a)): int 

fun {a:t@ype} order_eq (INV(a), INV(a)): bool 
fun {a:t@ype} order_neq (INV(a), INV(a)): bool 
fun {a:t@ype} order_gt (INV(a), INV(a)): bool
fun {a:t@ype} order_lt (INV(a), INV(a)): bool 
fun {a:t@ype} order_gte (INV(a), INV(a)): bool 
fun {a:t@ype} order_lte (INV(a), INV(a)): bool

fun {a:t@ype} order_min (INV(a), INV(a)): a 
fun {a:t@ype} order_max (INV(a), INV(a)): a

overload cmp  with order_compare
overload eq   with order_eq
overload neq  with order_neq
overload gt   with order_gt
overload lt   with order_lt
overload gte  with order_gte
overload lte  with order_lte
