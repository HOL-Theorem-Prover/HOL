(* =====================================================================*)
(* FILE		: string_rules.sml   				        *)
(* DESCRIPTION  : Defines useful derived rules for strings.		*)
(*									*)
(* AUTHOR	: T. Melham						*)
(* DATE		: 87.10.09						*)
(*									*)
(* RENAMED	: M. Gordon (from string.ml)				*)
(* DATE		: 23 March 1989						*)
(*									*)
(* REVISED	: 90.10.27 (melham)					*)
(* TRANSLATED   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)

structure stringLib :> stringLib =
struct

local open stringTheory in end;

open HolKernel Parse boolTheory Drule Conv;
infix 5 |->;

fun STRING_RULES_ERR function message = 
             HOL_ERR{origin_structure = "String_rules",
                     origin_function = function,
                     message = message};


val string_CONV   = String_conv.string_CONV;
val ascii_EQ_CONV = Ascii.ascii_EQ_CONV;

(* --------------------------------------------------------------------- *)
(* string_EQ_CONV : determines if two string constants are equal.	 *)
(*									 *)
(* string_EQ_CONV `"abc" = "abc"` ---> `("abc" = "abc") = T`             *)
(* string_EQ_CONV `"abc" = "abx"` ---> `("abc" = "abx") = F`             *)
(* string_EQ_CONV `"abc" = "ab"`  ---> `("abc" = "ab") = F` 	         *)
(*									 *)
(* ...  etc								 *)
(* --------------------------------------------------------------------- *)


local val Estr = Term`""`
      and a = genvar (Type`:ascii`)
      and s = genvar (Type`:string`)
      val Nth' = EQF_INTRO(SPECL [s,a] (stringTheory.NOT_STRING_EMPTY)) 
      val pat = mk_eq{lhs= (mk_eq{lhs=Estr, rhs=s}), rhs= (--`F`--)}
      and b = genvar Type.bool
      val a' = genvar (Type`:ascii`)
      and s' = genvar (Type`:string`)
      val S11 = SPECL [a,s,a',s'] stringTheory.STRING_11
      val MKeq = let val c = Term`$= :string->string->bool`
                 in fn t1 => fn t2 => MK_COMB(AP_TERM c t1,t2) end
      fun check c = #Tyop (dest_type(type_of c)) = "string"
      val Tand = CONJUNCT1 (SPEC b AND_CLAUSES)
      val mkC =  AP_THM o (AP_TERM (--`$/\`--)) 
fun conv l r = 
     if (l=Estr) 
     then let 
	      (* thm is something like
	         |- "abc" = STRING (ASCII F T T F F F F T) "bc" *)
              val thm = String_conv.string_CONV r 
              (* A is ASCII b0 ... b7, which indicates the first char
                in string, S is the rest of the string *)
	      val {Rator, Rand=S} = (dest_comb (rand(concl thm)))
              val A = rand Rator
          in
	  (* result of SUBST below is a thm: |- ("" = <r>) = F *)
    	  SUBST [s |-> SYM thm] pat (INST [a |-> A, s |-> S] Nth')
          end
     else if (r=Estr) 
          then let val thm = String_conv.string_CONV l 
	           val {Rator, Rand=S} = dest_comb (rand(concl thm))
		   val A = rand Rator
    	           (* result of SUBST below is a thm: |- ("" = <l>) = F *)
		   val sth = SUBST [s |-> SYM thm] pat
				   (INST [(a |-> A), (s |-> S)] Nth') 
               in
	       (* result of TRANS below is a thm: |- (<l> = "") = F *)
	       TRANS (SYM(SYM_CONV (lhs(concl sth)))) sth 
               end
          else let (* a1 = ASCII b0 ... b7, indicating first char of l
		      a2 = ASCII b0' ... b7', indicating first char of r
		      s1 = rest of l, s2 = rest of r *)
		   val th1 = String_conv.string_CONV l 
                   and th2 = String_conv.string_CONV r 
		   val {Rator, Rand=s1} = (dest_comb(rand(concl th1))) 
		   val a1 = rand Rator
                   val {Rator, Rand=s2} = (dest_comb(rand(concl th2))) 
		   val a2 = rand Rator
		   (* ooth is something like 
		     |- (<l> = <r>) = (<a1> = <a2>) /\ (<s1> = <s2>) *)
                   val ooth = TRANS (MKeq th1 th2) 
                                    (INST [(a |-> a1), (a' |-> a2),
					   (s |-> s1), (s' |-> s2)] S11) 
               in
               if (a1=a2) 
               then let (* thm1 = |- (<l> = <r>) = T /\ (<s1> = <s2>),
			   thm2 = |- (<l> = <r>) = <s1> = <s2> *)
			val thm1 = TRANS ooth (mkC(EQT_INTRO(REFL a1))
                                                  (mk_eq{lhs=s1, rhs=s2}))
                        val sub1 = (b |-> mk_eq{lhs=s1, rhs=s2})
                        val thm2 = TRANS thm1 (INST [sub1] Tand)
                    in
		    (* result of TRANS below is |- (<l> = <r>) = F *)
	            TRANS thm2 (conv s1 s2) 
                    end
               else let (* th1 = .|- <a1> = <a2>
			   th2 = .|- F *)
			val eq1 = mk_eq {lhs=l,rhs=r}
			val th1 = CONJUNCT1 (EQ_MP ooth (ASSUME (eq1)))
			val eq2 = mk_eq {lhs=a1, rhs=a2}
                        val th2 = EQ_MP (Ascii.ascii_EQ_CONV (eq2)) th1 
                    in
		    (* result of EQF_INTRO below is |- (<l> = <r>) = F *)
                    EQF_INTRO(NOT_INTRO(DISCH eq1 th2))
                    end
               end
in
fun string_EQ_CONV tm =
   let val {lhs, rhs} = dest_eq tm
       val _ = assert check lhs
       val _ = assert check rhs
   in 
     if (lhs=rhs)  then EQT_INTRO(REFL lhs)  else conv lhs rhs
   end
   handle _ => raise STRING_RULES_ERR "string_EQ_CONV" ""
end;


(* ------------------------- TESTS ---------------------------------------
   string_EQ_CONV (--`"" = ""`--);
   string_EQ_CONV (--`"z" = ""`--);
   string_EQ_CONV (--`"" = "f"`--);
   string_EQ_CONV (--`"abc" = "abc"`--);
   string_EQ_CONV (--`"a" = "a"`--);
   string_EQ_CONV (--`"abc" = "abx"`--);
   string_EQ_CONV (--`"abc" = "ab"`--);
   string_EQ_CONV (--`"ab" = "abc"`--);
   string_EQ_CONV (--`"xab" = "abc"`--);
   string_EQ_CONV 
         (--`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyz"`--);
   string_EQ_CONV
         (--`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyA"`--);

 *--------------------------------------------------------------------------*)

end; (* stringLib *)
