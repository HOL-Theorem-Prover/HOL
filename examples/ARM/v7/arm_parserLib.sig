signature arm_parserLib =
sig

  datatype arm_code
    = Ascii of string
    | Byte of Abbrev.term list
    | Short of Abbrev.term list
    | Word of Abbrev.term list
    | Instruction of Abbrev.term * Abbrev.term * Abbrev.term

  val expr : int -> string

  (* val arm_lex_from_file     : string -> Substring.substring list *)

  val arm_parse_from_file   : string -> (Arbnum.num * arm_code) list

  val arm_parse_from_string : string -> (Arbnum.num * arm_code) list

  val arm_parse_from_quote  : string frag list -> (Arbnum.num * arm_code) list

(* ..........................................................................

     Comments are:

         /* ... */
         (* ... *)
          @ ...
          ; ...
         // ...

     Source lines are:

       {label:} {instruction | directive}

     where

       - a label is [a-zA-Z._][a-zA-Z0-9._]*

       - an instruction is in ARM UAL (Unified Assembler Language) syntax

       - the directives are

         ARCH  (ARMv4 | ARMv4T | ARMv5T | ARMv5TE | ARMv6 | ARMv6K | ARMv6T2
                ARMv7 | ARMv7-A | ARMv7-M | ARMv7-R)

         THUMB
         CODE16
         CODE 16

         ARM
         CODE32
         CODE 32

         ASCII <string>
         BYTE  <v1>{,<v2>,...}
         SHORT <v1>{,<v2>,...}
         WORD  <v1>{,<v2>,...}

         (values are excepted in standard bases e.g. 0b1100, 0xC, 014 and 12)

         ALIGN (2 | 4 | 8)

         SPACE <bytes>



     Examples:

       arm_parse_from_string "thumb\n add r1,r2"

       arm_parse_from_quote
         `// this is an example
		ARCH	ARMv6T2
		THUMB @ enter thumb code (does an ALIGN 2 too)

	label:	add	r1,r2
		add.w	r1,r8,r3
		b.n	+#4	; branch to the next instruction
		b	-#8	/* branches to the labelled instruction
				   (assumes the first add is narrow) */

		ARM @ enter ARM code (does an ALIGN 4 too)

		ASCII	"a"
		BYTE	0b1011
		ALIGN	4	; ensures next short is in the following word
		SHORT	0xABCD	(* no need for another ALIGN because
				   instructions are always aligned *)
		blx	label	; branch to thumb code

		SPACE	40	; skip 10 instructions

		mov	r1,#^(expr (~8 + 4 - 2))
				; can use expr for int arith
				; will covert to mvn r1,#5
		pop	{r1-r6,pc}`

  ......................................................................... *)

end
