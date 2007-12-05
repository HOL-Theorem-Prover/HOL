(* --------------------------------------------------------------------*)
(* Elliptic curve crypographic.                                        *)
(* --------------------------------------------------------------------*)

val field_neg_def =
 Define
   `field_neg (x:word32) = if x = 0w then (0w:word32) else 751w - x`;

val field_add_def =
 Define
  `field_add (x:word32,y:word32) =
     let z = x + y
      in
       if z < 751w then z else z - 751w`;

val field_sub_def =
 Define
  `field_sub (x,y) = field_add(x,field_neg y)`;

val defs0 = [field_neg_def, field_add_def, field_sub_def]

val code0 = pp_compile defs0;

(* --------------------------------------------------------------------*)

val field_mult_aux_def =
 Define
   `field_mult_aux (x:word32,y:word32,acc:word32) =
      if y = 0w then acc
      else let
        x' = field_add (x,x) in let
        y' = y >>> 1         in let
        acc' = (if y && 1w = 0w then acc else field_add (acc,x))
        in
          field_mult_aux (x',y',acc')`;

(* --------------------------------------------------------------------*)

val field_mult_def = 
 Define
   `field_mult (x,y) = field_mult_aux (x,y,0w)`;

val defs1 = [field_neg_def, field_add_def, field_sub_def, field_mult_aux_def, field_mult_def];

val code1 =  pp_compile defs1;

(* --------------------------------------------------------------------*)

val field_exp_aux_def = 
 Define
   `field_exp_aux (x:word32,n:word32,acc:word32) =
      if n = 0w then acc
      else
       let x' = field_mult (x,x) in
       let n' = n >>> 1 in
       let acc' = (if n && 1w = 0w then acc else field_mult (acc,x))
        in
          field_exp_aux (x',n',acc')`;

(*
val (def2, ind2) =  f_compile_one field_exp_aux_def;

val defs2 = [field_neg_def, field_add_def, field_sub_def, field_mult_aux_def, field_mult_def, field_exp_aux_def, field_exp_aux_def];
val code2 =  pp_compile defs2;

 `field_exp_aux' (r0,r1,r2) =
        (if r1 = 0w then
           r2
         else
           (let m1 = r1 in
            let m0 = r0 in
            let r1' = r0 in
            let r0' = field_mult (r0,r1') in
            let r3 = r0' in
            let r1'' = m1 in
            let r0'' = m0 in
            let r4 = r1'' >>> 1 in
            let r1''' = r1'' && 1w in
              (if r1''' = 0w then
                 (let r0''' = r3 in
                  let r1'''' = r4 in
                    field_exp_aux' (r0''',r1'''',r2))
               else
                 (let r5 = r0'' in
                  let r0''' = r2 in
                  let r1'''' = r5 in
                  let r0'''' = field_mult (r0''',r1'''') in
                  let r5' = r0'''' in
                  let r0''''' = r3 in
                  let r1''''' = r4 in
                  let r2' = r5' in
                    field_exp_aux' (r0''''',r1''''',r2')))))
`
*)

(* --------------------------------------------------------------------*)

val field_exp_def = 
 Define
   `field_exp (x,n) = field_exp_aux (x,n,1w)`;

val field_inv_def =
 Define 
   `field_inv x = field_exp (x,749w)`;

val field_div_def = 
 Define
   `field_div (x,y) = field_mult (x,field_inv y)`;

val curve_neg_def = 
 Define
   `curve_neg (x1,y1) =
       if (x1 = 0w) /\ (y1 = 0w) then (0w,0w)
       else
        let y = field_sub
                  (field_sub
                    (field_neg y1,field_mult (0w,x1)),1w)
         in
            (x1,y)`;

val curve_double_def = 
 Define
   `curve_double (x1,y1) =
      if (x1 = 0w) /\ (y1 = 0w) then (0w,0w)
      else
       let d = field_add
                 (field_add
                   (field_mult (2w,y1),
                    field_mult (0w,x1)),1w)
       in
        if d = 0w then (0w,0w)
        else
         let l = field_div
                  (field_sub
                    (field_add
                      (field_add
                        (field_mult(3w,field_exp (x1,2w)),
                         field_mult(field_mult (2w,0w),x1)),750w),
                       field_mult (0w,y1)),d) in
         let m = field_div
                  (field_sub
                    (field_add
                      (field_add
                           (field_neg (field_exp (x1,3w)),
                            field_mult (750w,x1)),
                       field_mult (2w,0w)),
                     field_mult (1w,y1)),d) in
         let x = field_sub
                  (field_sub
                    (field_add(field_exp (l,2w),
                                   field_mult (0w,l)),0w),
                     field_mult (2w,x1)) in
         let y = field_sub
                  (field_sub
                     (field_mult
                       (field_neg (field_add (l,0w)),x),m),1w)
         in
           (x,y)`;


val curve_add_def = 
 Define
   `curve_add (x1,y1,x2,y2) =
       if (x1 = x2) /\ (y1 = y2) then curve_double (x2,y2) else 
       if (x1 = 0w) /\ (y1 = 0w) then (x2,y2) else
       if (x2 = 0w) /\ (y2 = 0w) then (x1,y1) else
       if x1 = x2 then (0w,0w)
       else
         let d = field_sub (x2,x1) in
         let l = field_div (field_sub (y2,y1),d) in
         let m = field_div
                   (field_sub (field_mult (y1,x2),
                                   field_mult (y2,x1)),d) in
         let x = field_sub
                  (field_sub
                    (field_sub
                      (field_add
                        (field_exp (l,2w),
                         field_mult (0w,l)),0w),x1),x2) in
         let y = field_sub
                  (field_sub
                    (field_mult
                      (field_neg (field_add (l,0w)),x),m),1w)
         in
          (x,y)`;

val curve_mult_aux_def = 
 Define
   `curve_mult_aux (x,y,n:word32,acc_x,acc_y) =
      if n = 0w then (acc_x:word32,acc_y:word32)
      else
       let (x',y') = curve_double (x,y) in
       let n' = n >>> 1 in
       let (acc_x',acc_y') =
              (if n && 1w = 0w then (acc_x,acc_y)
               else curve_add (x,y,acc_x,acc_y))
       in
        curve_mult_aux (x',y',n',acc_x',acc_y')`;

val curve_mult_def = 
 Define
   `curve_mult (x,y,n) = curve_mult_aux (x,y,n,0w,0w)`;

(* --------------------------------------------------------------------*)

val defs = [field_neg_def, field_add_def, field_sub_def, field_mult_aux_def]
