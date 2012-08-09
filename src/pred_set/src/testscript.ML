set_trace "Unicode" 0;
Feedback.WARNINGs_as_ERRs := true;
fun myload s = load s handle HOL_ERR _ => OS.Process.exit OS.Process.failure;
myload "arithmeticTheory";
myload "pred_setTheory";
