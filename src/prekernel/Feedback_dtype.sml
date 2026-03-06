structure Feedback_dtype =
struct

type origin =
      {origin_structure:string,
       origin_function:string,
       source_location : locn.locn}

datatype hol_error = HOL_ERROR of
        {origins : origin list,
         message : string}

end
