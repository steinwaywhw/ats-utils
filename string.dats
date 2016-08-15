#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "libc/SATS/math.sats"
staload _ = "libc/DATS/math.dats"

staload "./symintr.sats"
staload "./string.sats"
staload "./list.sats"
staload "./maybe.sats"

staload _ = "./list.dats"
staload _ = "./maybe.dats"


#define ::  ListCons
#define nil ListNil

implement string_unexplode (xs) = let
	val length = len (xs) + 1
	val (view, gc | ptr) = malloc_gc (i2sz length)

	fun loop (xs: list char, p: ptr): void = 
		case+ xs of
		| x :: xs => loop (xs, ptr_succ<char>(p)) where { val _ = $UNSAFE.ptr0_set<char>(p, x) }
		| nil () => $UNSAFE.ptr0_set<char>(p, $UNSAFE.cast{char}(0))

	val _ = loop (xs, ptr)
in 
	$UNSAFE.castvwtp0{string}((view, gc | ptr))
end

implement string_explode (str) = let 
	val len = string_len str
	fun loop (index: nat, ret: list (char)): list (char) =
		if index >= len
		then ret 
		else loop (index + 1, str[index] :: ret)

	val ret = loop (0, nil ())
in 
	list_reverse ret
end

implement string_empty (s) = s = ""

implement string_from_char (c) = string_unexplode (c :: nil())

implement string_from_int (n) = let 
	fun loop (n: int, s: string): string = 
		if n >= 10
		then loop (n / 10, string_prepend (s, '0' + (n mod 10)))
		else string_prepend (s, '0' + n) 
in 
	if n > 0 then loop (n, "") else string_prepend (loop (~n, ""), '-')
end

implement string_to_uint (s) = let 
	fun loop (s: string, r: int): int = 
		if empty s 
		then r 
		else loop (tail s, (head s - '0') + 10 * r)
in 
	loop (string_trim s, 0)
end

implement string_to_int (s) = let 
	val sign = head (string_trim s) 
in 
	case+ sign of 
	| _ when sign = '-' => ~ (string_to_uint (tail (string_trim s)))
	| _ when sign = '+' => string_to_uint (tail (string_trim s))
	| _ 				=> string_to_uint (s)
end

implement string_to_udouble (s) = let 
	val s = string_trim s 
	val pos = string_find (s, ".")
in 
	case+ pos of 
	| Nothing () => (string_to_uint s) * 1.0
	| Just pos   => 
		let 
			val a = string_range (s, 0, pos)
			val b = string_range (s, pos + 1, len s)
			val aint = string_to_uint a 
			val bint = string_to_uint b
		in 
			aint * 1.0 + bint * 1.0 * pow (10.0, ~(len b * 1.0))
		end
end

implement string_to_double (s) = let 
	val sign = head (string_trim s)
in 
	case+ sign of 
	| _ when sign = '-' => ~ (string_to_udouble (tail (string_trim s)))
	| _ when sign = '+' => string_to_udouble (tail (string_trim s))
	| _ 				=> string_to_udouble (s)
end

implement string_join (xs, sep) = 
	case+ xs of 
	| x :: nil () => x
	| x :: xs => concat (concat (x, sep), string_join (xs, sep))
	| nil () => ""

implement string_split (s, sep) = let 
	val len = string_len s
	val lensep = string_len sep 
	fun loop (s: string, ls: list string): list string = let 
		val pos = string_find (s, sep)
	in 	
		case+ pos of 
		| Just pos   => loop (string_range (s, pos + lensep, len), string_range (s, 0, pos) :: ls)
		| Nothing () => ls 
	end 
in 
	list_reverse<string>(loop (s, nil ()))
end

implement string_concat (a, b) = 
	string_unexplode (list_concat (string_explode a, string_explode b))

implement string_append (s, c) = string_concat (s, string_from_char c)
implement string_prepend (s, c) = string_concat (string_from_char (c), s)

implement string_range (s, b, e) = 
	if b <= e 
	then string_unexplode (take (drop (string_explode s, b), e - b))
	else ""

//implement string_compare (a, b) = $extfcall (int, "strcmp", a, b)
//implement string_eq (a, b) = string_compare (a, b) = 0
implement string_len (str) = $UNSAFE.cast{nat} ($extfcall (int, "strlen", str))

implement string_head (str) = if empty str then '\0' else str[0]
implement string_tail (str) = if empty str then "" else string_range (str, 1, string_len str)

implement string_trim (str) = let 
	fun loop1 (p: nat): nat =
		if isspace (str[p])
		then loop1 (p+1)
		else p 
	fun loop2 (p: nat): nat = 
		if isspace (str[p])
		then if p > 0 then loop2 (p-1) else 0
		else p

	val len = len str
in 
	if len > 0
	then string_range (str, loop1 0, loop2 (len - 1) + 1)
	else ""
end 

implement string_find (str, sub) = let 
	val result = $extfcall(nat, "_string_find", str, sub)
in 
	if result < 0
	then Nothing{nat} ()
	else Just{nat} (result)
end

implement string_contains (str, sub) = 
	case+ string_find (str, sub) of 
	| Nothing _ => false
	| Just _ => true

%{

int string_get (char *str, int pos) {
	if (pos < strlen(str)) {
		return str[pos];
	} else {
		return 0;
	}
}

int _string_find (char *str, char *sep) {
	char *p = strstr (str, sep);
	if (p == NULL)
		return -1;
	else 
		return p - str;
}

%}




////

