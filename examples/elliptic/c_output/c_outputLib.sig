signature c_outputLib =
sig
   include Abbrev

	(*
		translate_to_c dirname filename defs rewrites main_func tests
		
		This function translates all the functions defined in defs to
		C. Before translating, the theorems in rewrites are applied to the 
		defs.

		translate_to_c generates 3 files: filename.h, filename.c and filename-test.c in the directory dirname. The directory name must end with a "/". The file filename.c contains the main function definitions, filename.h the headers. 

		filename-test.c contains code for testing. It checks for the tests passed in tests automatically and afterwards provides interactive for
		the function main_func. The parameter tests is a list of pairs
		(f, (arg, res) list). f is the function to be tested, the other list
		contains pairs of arguments and expected results for these arguments.
	*)
		
	val translate_to_c : string -> string -> thm list -> thm list ->  term -> (term * (term * term) list) list -> unit;	

	(* This function is intended to generate tests.
		generate_word_pair_list pair_size max_word list_length
		It generates a random list of word32-pairs with pair_size elements in
		each pair. The words are all less to max_word if max_word is not set to 0. Otherwise there is no limit. Finally, the parameter list_length
		specifies the number of pairs generated
	*)
	
	val generate_word_pair_list : int -> int -> int -> term list
end
