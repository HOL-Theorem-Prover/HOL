// FlasherManager where calls to function F1 are replaced with argument of the method
public class FlasherManager{

    /*@ ensures \result<20; */
    int flashManager(int callF1) {
        // initialization of global variables
	int in8=0;
	int in9=0;
	int in10=0;
	int in11=0;
	int in12=0;
	int in13=0;
	int in18=1;
	int Model_Outputs3=0;
	int Model_Outputs4=0;
	int counter_a_DSTATE=0;
	int counter_b_DSTATE=0;
	int Unit_Delay1_d_DSTATE=0;
	int Unit_Delay1_f_DSTATE=0;
	int Unit_Delay1_h_DSTATE=0;
	int Unit_Delay1_j_DSTATE=0;
	int Unit_Delay1_b_DSTATE=0;
	int Unit_Delay_c_DSTATE=0;
	int Unit_Delay_e_DSTATE=0;
	int Unit_Delay_h_DSTATE=0;
	int Unit_Delay3_c_DSTATE=0;
	int Unit_Delay_i_DSTATE=0;
	int Unit_Delay_j_DSTATE=0;
	int Unit_Delay_a_DSTATE=0;
	int Unit_Delay_b_DSTATE=0;
	int Unit_Delay3_a_DSTATE=0;
	int Unit_Delay_d_DSTATE=0;
	int Unit_Delay_f_DSTATE=0;
	int Unit_Delay3_b_DSTATE=0;
	int Unit_Delay3_d_DSTATE=0;
	int Unit_Delay3_e_DSTATE=0;
	int Unit_Delay1_a_DSTATE=0;
	int Unit_Delay1_c_DSTATE=0;
	int Unit_Delay1_e_DSTATE=0;
	int Unit_Delay1_g_DSTATE=0;
	int Unit_Delay1_i_DSTATE=0;
	int Unit_Delay_g_DSTATE=0;
	int Switch7=0;
	int Switch1_m=0;
	int add_g=0;
	int Switch1_k=0;
	int add_f=0;
	int Switch1_i=0;
	int add_e=0;
	int Switch_e=0;
	int add_d=0;
	int Switch_d=0;
	int add_c=0;
	int Switch1_e=0;
	int add_b=0;
	int Switch1_c=0;
	int add_a=0;
	int Data_Type_Conversion_a=0;
	int Switch5=0;
	int Switch4_a=0;
	int OR=0;
	int Switch6=0;
	int Switch2_a=0;
	int Switch3_a=0;
	int superior_e=0;
	int Switch3_f=0;
	int Switch1_l=0;
	int Switch2_f=0;
	int Switch4_f=0;
	int and1_d=0;
	int superior_d=0;
	int Switch3_e=0;
	int Switch1_j=0;
	int Switch2_e=0;
	int Switch4_e=0;
	int and1_c=0;
	int Switch_g=0;
	int Logical_Operator2=0;
	int superior_c=0;
	int Switch3_d=0;
	int Switch1_h=0;
	int Switch2_d=0;
	int Switch4_d=0;
	int and1_b=0;
	int Data_Type_Conversion_d=0;
	int Data_Type_Conversion_c=0;
	int Unit_Delay_g=0;
	int Multiport_Switch=0;
	int and_e=0;
	int superior_b=0;
	int Switch3_c=0;
	int Switch1_d=0;
	int Switch2_c=0;
	int Switch4_c=0;
	int and_d=0;
	int superior_a=0;
	int Switch3_b=0;
	int Switch1_b=0;
	int Switch2_b=0;
	int Switch4_b=0;
	int and1_a=0;
	int and_c=0;
	int and_b=0;
	int Switch1_a=0;
	int Switch_a=0;
	int Warning_Acti_ZCE=0;
	int rtb_Switch_i=0;
	int rtb_Switch_h=0;
	int rtb_Switch_f=0;
	int rtb_Switch1_g=0;
	int rtb_Switch1_f=0;
	int rtb_Switch_c=0;
	int rtb_Switch_b=0;
	int rtb_and_a=0;
	int rtb_Logical_Operator=0;
	int rtb_Logical_Operator1=0;
	// initialization that were donne in the main of the original program
	Unit_Delay_g = 0;
	Unit_Delay_a_DSTATE = 0;
	Unit_Delay_g_DSTATE = 0;
	Unit_Delay_b_DSTATE = 0;
	Unit_Delay3_a_DSTATE = 0;
	Unit_Delay_c_DSTATE = 0;
	Unit_Delay1_b_DSTATE = 0;
	Unit_Delay1_a_DSTATE = 0;
	Unit_Delay_d_DSTATE = 0;
	Unit_Delay_e_DSTATE = 0;
	Unit_Delay1_d_DSTATE = 0;
	Unit_Delay1_c_DSTATE = 0;
	Unit_Delay_f_DSTATE = 0;
	counter_b_DSTATE = 0;
	Unit_Delay3_d_DSTATE = 0;
	Unit_Delay_i_DSTATE = 0;
	Unit_Delay1_h_DSTATE = 0;
	Unit_Delay1_g_DSTATE = 0;
	counter_a_DSTATE = 0;
	Unit_Delay3_e_DSTATE = 0;
	Unit_Delay_j_DSTATE = 0;
	Unit_Delay1_j_DSTATE = 0;
	Unit_Delay1_i_DSTATE = 0;
	Unit_Delay3_c_DSTATE = 0;
	Unit_Delay3_b_DSTATE = 0;
	Unit_Delay_h_DSTATE = 0;
	Unit_Delay1_f_DSTATE = 0;
	Unit_Delay1_e_DSTATE = 0;
	int i=0;
	int j=0;
	while (i<30) {
            // to simulate call to F1 function
	    int F1 = callF1;
	    if (Model_Outputs4==1)
		{j= j+1;}
	    else { j=0;}
	    // assert (j<20); // output is true for 20 steps
            i=i+1;
	}
        return j;
    }

}

