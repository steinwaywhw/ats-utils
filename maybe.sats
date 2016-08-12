staload "./symintr.sats"

datatype maybe (a:t@ype) = 
| Nothing of ()
| Just of (a)

fun {a,b:t@ype} maybe_bind (maybe a, a -<cloref1> b): maybe b

fun maybe_selftest (): void

