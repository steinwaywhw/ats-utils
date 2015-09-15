
datatype regex_t = 
	| Epsilon of () 
	| Any of ()
	| None of ()
	| Char of char 
	| CharClass of 
	| Concat of (regex_t, regex_t)
	| Closure of regex_t
	| Or of (regex_t, regex_t)
	| Not of regex_t
	| And of (regex_t, regex_t)
//	| Opt of regex_t

assume regex = regex_t 


fun prec (re: regex): int =
	case+ re of 
	| Any _     => 6
	| None _    => 6
	| Epsilon _ => 6
	| Char _    => 6
	| Closure _ => 5
	| Not _     => 4
	| Concat _  => 3
	| And _     => 2
	| Or _      => 0


fun parse (re: string): regex = let 
	exception ParsingError of ()

	var pivot = 0
(*
	https://web.archive.org/web/20090129224504/http://faqts.com/knowledge_base/view.phtml/aid/25718/fid/200

	regex     ::= term | regex
	          |   term & regex
	          |   term
			
	term      ::= factor
	          |   factor term

	factor    ::= atom
	          |   atom meta
	          |   ! atom

	atom      ::= char
			  	  .
			  	  (regex)
			  	  [charclass]
			  	  [^charclass]
			  	  
	charclass ::= charrange
	          |   charrange charclass

	charrange ::= char
	          |   char - char

	char      ::= anychar except: ! $ & ( ) * + . ? @ [ \ ] ^ { | } 
	          |   \ anychar

	meta      ::= 
//			  |   ^ $
			  |   ? * + 
//			  |   {n} {n,} {m,n}

	\t \n \r \f \cX \NNN \b \B \d \D \s \S \w \W

	anychar   ::= ! " # $ % & ' ( ) * + , - . / :
                  ; < = > ? @ [ \ ] ^ _ ` { | } ~
                  0 1 2 3 4 5 6 7 8 9
                  A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
                  a b c d e f g h i j k l m n o p q r s t u v w x y z

*)

	fun peek (): char = if more () then string_get (re, i) else '\0'
	
	fun eat (c: char): void = 
		if c = string_get (re, pivot)
		then pivot := pivot + 1
		else let 
			val _ = show "Expecting "
			val _ = show c 
			val _ = show " but got "
			val _ = show string_get (re, pivot)
		in 
			$raise ParsingError ()
		end 
	
	fun next (): char = let 
		val c = peek ()
		val _ = pivot := pivot + 1
	in 
		c
	end 

	fun more (): bool = pivot < string_len re 

	fun parse_regex (): regex = let 
		val term = parse_term ()
	in 
		if !(more ())
		then term 
		else 
			if peek () = '|' 
			then let val _ = eat ('|') in normalize (Or (term, parse_regex ()))
			else if peek () = '&'
			then let val _ = eat ('&') in normalize (And (term, parse_regex ())) 
			else $raise ParsingError () (* should not happen*)
	end 

	fun parse_term (): regex = let 
		val factor = parse_factor ()
	in 
		if !(more ())
		then factor 
		else normalize (Concat (factor, parse_term ()))
	end 

	fun parse_factor (): regex = 
		if peek () = '!'
		then let val _ = eat '!' in normalize (Not (parse_atom ()))
		else 
			let 
				val atom = parse_atom ()
			in 
				if !(more ())
				then atom 
				else parse_meta (atom)
			end 

	fun parse_meta (re: regex): regex = let 
		val c = peek ()
	in 
		if c = '?' 
		then let val _ = eat '?' in normalize (Or (Epsilon (), re))
		else if c = '*' 
		then let val _ = eat '*' in normalize (Closure re)
		else if c = '+'
		then let val _ = eat '+' in normalize (Concat (re, Closure re))
		else $raise ParsingError () (* things not supported yet *)
	end

	fun parse_atom (): regex = let 
		val c = peek ()
	in 
		if c = '.' then Any ()
		else if c = '[' then 
			let 
				val _ = eat '['
				val c = peek ()
				val charclass = if c = '^' then normalize (Not (parse_charclass ())) else normalize (parse_charclass ())
				val _ = eat ']'
			in 
				charclass
			end 
		else if c = '(' then 
			let 
				val _ = eat '('
				val re = parse_regex ()
				val _ = eat ')'
			in 
				re 
			end 
		else parse_char ()
	end 

	fun parse_charclass (): regex = let 
		val range = parse_charrange ()
	in 
		if !(more ())
		then range 
		else 




	
in 
end 



(* give a total order to all regex *)
fun compare (a: regex, b: regex): int = 
	case+ (a, b) of 
	| (Epsilon (), Epsilon ())           =>  0
	| (Epsilon (), _)                    =>> ~1
	| (_, Epsilon ())                    =>> 1
	| (Any (), Any ())                   =>> 0
	| (Any (), _)                        =>> ~1
	| (_, Any ())                        =>> 1
	| (None (), None ())                 =>> 0
	| (None (), _)                       =>> ~1
	| (_, None ())                       =>> 1
	| (Char a, Char b)                   =>> a - b
	| (Char _, _)                        =>> ~1
	| (_, Char _)                        =>> 1
	| (Concat (a1, a2), Concat (b1, b2)) =>> let val o = compare (a1, b1) in if o = 0 then compare (a2, b2) else o
	| (Concat _, _)                      =>> ~1
	| (_, Concat _ )                     =>> 1
	| (Closure a, Closure b)             =>> compare (a, b)
	| (Closure _, _)                     =>> ~1
	| (_, Closure _)                     =>> 1
	| (Or (a1, a2), Or (b1, b2))         =>> let val o = compare (a1, b1) in if o = 0 then compare (a2, b2) else o
	| (Or _, _)                          =>> ~1
	| (_, Or _ )                         =>> 1
	| (And (a1, a2), And (b1, b2))       =>> let val o = compare (a1, b1) in if o = 0 then compare (a2, b2) else o
	| (And _, _)                         =>> ~1
	| (_, And _ )                        =>> 1
	| (Not a, Not b)                     =>> compare (a, b)


fun nu (re: regex): bool = 
	case+ re of 
	| Any _ => false 
	| None _ => false 
	| Epsilon _ => true
	| Char _ => false  
	| Concat (a, b) => (nu a) && (nu b)
	| Closure re => true
	| Or (a, b) => (nu a) || (nu b)
	| Not re => not (nu re)
	| And (a, b) => (nu a) && (nu b)

fun delta (re: regex): regex = if nu re then Epsilon () else None ()



(* 
	this is only a one-step normalization, 
	intended for use as constructors
*)
fun normalize (re: regex): regex =
	case+ re of 
	| And (a, b) when compare (a, b) = 0 =>  a
	| And (a, b) when compare (a, b) > 0 =>  And (b, a)
	| And (And (a, b), c)                =>  And (a, And (b, c))
	| And (None (), _)                   =>  None ()
	| And (_, None ())                   =>  None ()
	| And (Not (None ()), re)            =>  re
	| Concat (Concat (a, b), c)          =>  Concat (a, Concat (b, c))
	| Concat (None (), _)                =>  None ()
	| Concat (_, None ())                =>  None ()
	| Concat (Epsilon (), re)            =>  re
	| Concat (re, Epsilon ())            =>  re
	| Or (a, b) when compare (a, b) = 0  =>  a
	| Or (a, b) when compare (a, b) > 0  =>  Or (b, a)
	| Or (Or (a, b), c)                  =>  Or (a, Or (b, c))
	| Or (Not (None ()), _)              =>  Not (None ())
	| Or (None (), re)                   =>  re
	| Or (re, None ())                   =>  re
	| Closure (Closure re)               =>  re
	| Closure (Epsilon ())               =>  Epsilon ()
	| Closure (None ())                  =>  Epsilon ()
	| Not (Not re)                       =>  re
	| Not (None ())                      =>  Any ()
	| _                                  =>> re

//fun equal (a: regex, b: regex): bool = 
//	case+ (a, b) of 
//	| (None (), None ())           =>  true
//	| (Epsilon (), Epsilon ())         =>  true
//	| (Char a, Char b)             =>  a = b
//	| (Concat (a1, a2), Concat (b1, b2)) =>  equal (a1, b1) && equal (a2, b2)
//	| (Closure a, Closure b)             =>  equal (a, b)
//	| (Or (a1, a2), Or (b1, b2)) =>  equal (a1, b1) && equal (a2, b2)
//	| (Not a, Not b)               =>  equal (a, b)
//	| (_, _)                       =>> false

fun derive (re: regex, c: char): regex = 
	case+ re of 
	| Any _         => Epsilon ()
	| None _        => re
	| Epsilon _     => None ()
	| Char t        => if t = c then Epsilon () else None ()
	| Closure re    => normalize (Concat (derive (re, c), Closure re))
	| Concat (a, b) =>
		normalize (Or (
			normalize (Concat (derive (a, c), b)), 
			normalize (Concat (delta a, derive (b, c)))))
	| Or (a, b)     => normalize (Or (derive (a, c), derive (b, c)))
	| And (a, b)    => normalize (And (derive (a, c), derive (b, c)))
	| Not re        => normalize (Not (derive (re, c)))


fun match_direct (re: regex, input: string): bool = let
	fun iter (re: regex, i: int): regex = 
		if i = string_len input
		then re 
		else 
			let 
				val c = string_get (input, i)
				val d = derive(re, c)
			in 
				case+ d of 
				| None _ => d
				| _      => iter (d, i+1)
			end 
in 
	nu (iter (re, 0))
end



fun test_match_direct (): void = let 
	






 