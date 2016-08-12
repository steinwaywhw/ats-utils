staload "symintr.sats"

fun {a:t@ype} show_addr (a): void 

fun {a:t@ype} show_any (a): void

fun {}        show_begin (): void 
fun {}        show_sep (): void
fun {}        show_end (): void

//overload show with print_bool
//overload show with print_string
//overload show with print_char
//overload show with print_int
//overload show with print_float
//overload show with print_double

overload show with print_newline
overload show with show_any