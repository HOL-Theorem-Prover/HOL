public class F1 {

    // function f1 of FlasherManager where calls to random function nondet_in()
    // have been replaced with function parameters i1,...,i6 

    /* @ ensures  Model_Outputs4<2; */
    static void f1(int i1, int i2,int i3,int i4,int i5,int i6) {
	in8=i1;
	in9=i2;
	in10=i3;
	in11=i4;
	in12=i5;
	in13=i6;
     if (in18==1) {
     Data_Type_Conversion_a = in11;
     if ((in10 == 1) && (1 != Unit_Delay_a_DSTATE))
         {and_b = 1;} else  {and_b = 0;}
     Unit_Delay_g = Unit_Delay_g_DSTATE;
     cas = ((1 + in12) + Data_Type_Conversion_a * 2);
     if (cas==1) {Multiport_Switch = Unit_Delay_g;}
     else {if (cas==2) { Multiport_Switch = 1;}
     else {if (cas==3) {Multiport_Switch = 0;}}}
     if ((Unit_Delay_g == 0) && (0 != Unit_Delay_b_DSTATE))
         {and_c = 1;} else {and_c =0;}
     if (in13==1) {
     	Switch5 = in8;
     }
     else {
     	Switch5 = 0;
     }
     if ((Switch5 == 1) && (1 != Unit_Delay3_a_DSTATE))
         {and1_a =1;} else {and1_a =0;}
     if ((and1_a - Unit_Delay_c_DSTATE) != 0) {
     	rtb_Switch_b = 0;
     }
     else {
     	add_a = (1 + Unit_Delay1_b_DSTATE);
     	rtb_Switch_b = add_a;
     }
     if (rtb_Switch_b >= 3)
         {superior_a = 1;} else {superior_a = 0;}
     if (superior_a==1) {
     	Switch1_c = 0;
     }
     else {
     	Switch1_c = rtb_Switch_b;
     }
     if (Switch5==1) {
     	if (and1_a==1) {
     	 	Switch1_b = 1;
     	}
     	else {
     	 	if (superior_a==1) {
     	 		if (Unit_Delay1_a_DSTATE==1) {
     	 		 	Switch4_b = 0;
     	 		}
     	 		else {
     	 		 	Switch4_b = 1;
     	 		}
     	 		Switch2_b = Switch4_b;
     	 	}
     	 	else {
     	 		Switch2_b = Unit_Delay1_a_DSTATE;
     	 	}
     	 	Switch1_b = Switch2_b;
     	}
     	Switch3_b = Switch1_b;
     }
     else {
     	Switch3_b = 0;
     }
     if (in13==1) {
     	Switch4_a = in9;
     }
     else {
     	Switch4_a = 0;
     }
     if ((Switch4_a == 1) && (1 != Unit_Delay_d_DSTATE))
         {and_d = 1;} else {and_d = 0;}
     if ((1 == (and_d - Unit_Delay_e_DSTATE))) {
     	rtb_Switch_c = 0;
     }
     else {
     	add_b = (1 + Unit_Delay1_d_DSTATE);
     	rtb_Switch_c = add_b;
     }
     if (rtb_Switch_c >= 3)
         {superior_b = 1;} else {superior_b =0;}
     if (superior_b==1) {
     	Switch1_e = 0;
     }
     else {
     	Switch1_e = rtb_Switch_c;
     }
     if (Switch4_a==1) {
     	if (and_d==1) {
     		Switch1_d = 1;
     	}
        	else {
     		if (superior_b==1) {
     			if (Unit_Delay1_c_DSTATE==1) {
     		        	Switch4_c = 0;
     			}
     			else {
     				Switch4_c = 1;
     			}
     			Switch2_c = Switch4_c;
     		}
     		else {
     			Switch2_c = Unit_Delay1_c_DSTATE;
     		}
     		Switch1_d = Switch2_c;
     	}
     	Switch3_c = Switch1_d;
     }
     else {
     	Switch3_c = 0;
     }
     if (Data_Type_Conversion_a==1 && ( ! (Unit_Delay_g==1)))
         {rtb_and_a = 1;} else {rtb_and_a = 0;}
     if (rtb_and_a==1 || Unit_Delay_g==1)
         {OR = 1;} else {OR = 0;}
     if ((OR == 1) && (1 != Unit_Delay_f_DSTATE))
         {and_e =1;}else {and_e =0;}
     if (rtb_and_a==1) {
     	Switch7 = 60;
     }
     else {
     	Switch7 = 20;
     }
     if (counter_b_DSTATE == 0) {
     	rtb_Switch1_g = 0;
     }
     else {
     	rtb_Switch1_g = 1;
     }
     if (rtb_Switch1_g != 0)
         {Data_Type_Conversion_d = 1;} else {Data_Type_Conversion_d =0;}
     if (and_e==1) {
     	Switch_e = Switch7;
     }
     else {
     	add_d = (( - rtb_Switch1_g) + counter_b_DSTATE);
     	Switch_e = add_d;
     }
     if ((Data_Type_Conversion_d == 1) && (1 != Unit_Delay3_d_DSTATE))
         {and1_c = 1;} else {and1_c = 0;}
     if (1 == (and1_c - Unit_Delay_i_DSTATE)) {
     	rtb_Switch_h = 0;
     }
     else {
     	add_f = (1 + Unit_Delay1_h_DSTATE);
     	rtb_Switch_h = add_f;
     }
     if (rtb_Switch_h >= 1)
         {superior_d =1;} else {superior_d =0;}
     if (superior_d==1) {
     	Switch1_k = 0;
     }
     else {
     	Switch1_k = rtb_Switch_h;
     }
     if (Data_Type_Conversion_d==1) {
     	if (and1_c==1) {
     		Switch1_j = 1;
     	}
     	else {
     		if (superior_d==1) {
     			if (Unit_Delay1_g_DSTATE==1) {
     			 	Switch4_e = 0;
     			}
     			else {
     				Switch4_e = 1;
     			}
     			Switch2_e = Switch4_e;
     		}
     		else {
     			Switch2_e = Unit_Delay1_g_DSTATE;
     		}
     		Switch1_j = Switch2_e;
     	}
     	Switch3_e = Switch1_j;
     }
     else {
     	Switch3_e = 0;
     }
     if (counter_a_DSTATE == 0) {
     	rtb_Switch1_f = 0;
     }
     else {
     	rtb_Switch1_f = 1;
     }
     if (rtb_Switch1_f != 0)
           {Data_Type_Conversion_c = 1;} else {Data_Type_Conversion_c = 0;}
     if (and_c==1) {
     	Switch_d = 10;
     }
     else {
     	add_c = (( - rtb_Switch1_f) + counter_a_DSTATE);
     	Switch_d = add_c;
     }
     if ((Data_Type_Conversion_c == 1) && (1 != Unit_Delay3_e_DSTATE))
         {and1_d = 1;} else {and1_d = 0;}
     if (1 == (and1_d - Unit_Delay_j_DSTATE)) {
     	rtb_Switch_i = 0;
     }
     else {
     	add_g = (1 + Unit_Delay1_j_DSTATE);
     	rtb_Switch_i = add_g;
     }
     if (rtb_Switch_i >= 10)
         {superior_e = 1;} else {superior_e = 0;}
     if (superior_e==1) {
     	Switch1_m = 0;
     }
     else {
     	Switch1_m = rtb_Switch_i;
     }
     if (Data_Type_Conversion_c==1) {
     	if (and1_d==1) {
     	 	Switch1_l = 1;
     	}
     	else {
     		if (superior_e==1) {
     			if (Unit_Delay1_i_DSTATE==1) {
     				Switch4_f = 0;
     			}
     		else {
     				Switch4_f = 1;
     			}
     			Switch2_f = Switch4_f;
     		}
     		else {
     			Switch2_f = Unit_Delay1_i_DSTATE;
     		}
     		Switch1_l = Switch2_f;
     	}
     	Switch3_f = Switch1_l;
     }
     else {
     	Switch3_f = 0;
     }
     if (Switch3_e==1 || Switch3_f==1)
          {rtb_Logical_Operator =1;} else {rtb_Logical_Operator =0;}
     if (Data_Type_Conversion_d==1 || Data_Type_Conversion_c==1)
         {rtb_Logical_Operator1 = 1;} else {rtb_Logical_Operator1 = 0;}
     if ((and_b==1 && ( ! (Warning_Acti_ZCE==1)))) {
     	if (in10==1) {
     	    if (! (Unit_Delay3_c_DSTATE==1))
     		{Logical_Operator2 =1;} 
                   else { Logical_Operator2 =0;
     		  Switch_g = Logical_Operator2;}
     	}
     	else {
     	 	Switch_g = 0;
     	}
     	Unit_Delay3_c_DSTATE = Switch_g;
     }
     Warning_Acti_ZCE = and_b;
     if (in13==1) {
     	Switch6 = Switch_g;
     }
     else {
     	Switch6 = 0;
     }
     if ((Switch6 == 1) && (1 != Unit_Delay3_b_DSTATE))
         {and1_b = 1;} else 	{and1_b = 0;}
     if (1 == (and1_b - Unit_Delay_h_DSTATE)) {
     	rtb_Switch_f = 0;
     }
     else {
     	add_e = (1 + Unit_Delay1_f_DSTATE);
     	rtb_Switch_f = add_e;
     }
     if (rtb_Switch_f >= 3)
         {superior_c =  1;} else {superior_c = 0;}
     if (superior_c==1) {
     	Switch1_i = 0;
     }
     else {
     	Switch1_i = rtb_Switch_f;
     }
     if (Switch6==1) {
     	if (and1_b==1) {
     		Switch1_h = 1;
     	}
     	else {
     		if (superior_c==1) {
     			if (Unit_Delay1_e_DSTATE==1) {
     			 	Switch4_d = 0;
     		}
     			else {
     				Switch4_d = 1;
     			}
     			Switch2_d = Switch4_d;
     		}
     		else {
     			Switch2_d = Unit_Delay1_e_DSTATE;
     		}
     		Switch1_h = Switch2_d;
     	}
     	Switch3_d = Switch1_h;
     }
     else {
     	Switch3_d = 0;
     }
     if (rtb_Logical_Operator1==1) {
     	Switch2_a = rtb_Logical_Operator;
     }
     else {
     	if (Switch6==1) {
     		Switch1_a = Switch3_d;
     	}
     	else {
     		Switch1_a = Switch3_b;
     	}
     	Switch2_a = Switch1_a;
     }
     if (rtb_Logical_Operator1==1) {
     	Switch3_a = rtb_Logical_Operator;
     }
     else {
     	if (Switch6==1) {
     	 	Switch_a = Switch3_d;
     	}
     	else {
     		Switch_a = Switch3_c;
     	}
     	Switch3_a = Switch_a;
     }
   }
   Model_Outputs3 = Switch2_a;
   Model_Outputs4 = Switch3_a;
   if (in18==1) {
     Unit_Delay_a_DSTATE = in10;
     Unit_Delay_g_DSTATE = Multiport_Switch;
     Unit_Delay_b_DSTATE = Unit_Delay_g;
     Unit_Delay3_a_DSTATE = Switch5;
     Unit_Delay_c_DSTATE = and1_a;
     Unit_Delay1_b_DSTATE = Switch1_c;
     Unit_Delay1_a_DSTATE = Switch3_b;
     Unit_Delay_d_DSTATE = Switch4_a;
     Unit_Delay_e_DSTATE = and_d;
     Unit_Delay1_d_DSTATE = Switch1_e;
     Unit_Delay1_c_DSTATE = Switch3_c;
     Unit_Delay_f_DSTATE = OR;
     counter_b_DSTATE = Switch_e;
     Unit_Delay3_d_DSTATE = Data_Type_Conversion_d;
     Unit_Delay_i_DSTATE = and1_c;
     Unit_Delay1_h_DSTATE = Switch1_k;
     Unit_Delay1_g_DSTATE = Switch3_e;
     counter_a_DSTATE = Switch_d;
     Unit_Delay3_e_DSTATE = Data_Type_Conversion_c;
     Unit_Delay_j_DSTATE = and1_d;
     Unit_Delay1_j_DSTATE = Switch1_m;
     Unit_Delay1_i_DSTATE = Switch3_f;
     Unit_Delay3_b_DSTATE = Switch6;
     Unit_Delay_h_DSTATE = and1_b;
     Unit_Delay1_f_DSTATE = Switch1_i;
     Unit_Delay1_e_DSTATE = Switch3_d;
}




}
}
