staload "./symintr.sats"

datatype maybe (a:t@ype) = 
| Nothing of ()
| Just of (a)

fun {a:t@ype}   maybe_eq$eq (a, a): bool
fun {a:t@ype}   maybe_eq (maybe a, maybe a): bool

fun {a,b:t@ype} maybe_bind (maybe a, a -<cloref1> b): maybe b
fun {a:t@ype}   maybe_show$elm (a): void
fun {a:t@ype}   maybe_show (maybe a): void

fun maybe_selftest (): void

overload show with maybe_show
overload eq   with maybe_eq 
overload =    with maybe_eq

