structure cv_trans_dtype =
struct

datatype pat = cvRaw
             | cvEval of Conv.conv
             | cvName of string
             | cvTuple of pat list
             | cvSome of pat

end
