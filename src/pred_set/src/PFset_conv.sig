signature PFset_conv =
sig
   type conv = Abbrev.conv

 val FINITE_CONV : conv
 val IN_CONV :conv -> conv
 val DELETE_CONV :conv -> conv
 val UNION_CONV :conv -> conv
 val INSERT_CONV :conv -> conv
 val IMAGE_CONV :conv -> conv ->conv
 val CARD_CONV : conv
 val MAX_SET_CONV : conv
 val SUM_IMAGE_CONV : conv
end
