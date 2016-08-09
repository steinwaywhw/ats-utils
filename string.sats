staload "./symintr.sats"
staload "./list.sats"
staload "./maybe.sats"

local 

typedef nat = [n:nat] int n

in 

fun string_explode    (string): list (char)
fun string_unexplode  (list char): string 


// all decimal number
fun string_from_char  (char): string
fun string_from_int   (int): string

fun string_to_int     (string): int
fun string_to_uint    (string): int 
fun string_to_double  (string): double
fun string_to_udouble (string): double 

fun string_find       (string, string): maybe nat 
   
fun string_join       (list string, string): string
fun string_split      (string, string): list string
fun string_concat     (string, string): string 
fun string_append     (string, char): string
fun string_prepend    (string, char): string
   
fun string_range      (string, nat, nat): string // [a,b)
fun string_compare    (string, string): int
fun string_eq         (string, string): bool
   
fun string_get        (string, nat): char = "mac#"
fun string_len        (string): nat 
   
fun string_empty      (string): bool
fun string_head       (string): char 
fun string_tail       (string): string 
   
fun string_trim       (string): string 


end

//overload = with string_eq
overload []      with string_get
overload empty   with string_empty
overload len     with string_len
overload compare with string_compare
overload append  with string_append
overload prepend with string_prepend
overload concat  with string_concat
overload eq      with string_eq
overload head    with string_head
overload tail    with string_tail
overload find    with string_find