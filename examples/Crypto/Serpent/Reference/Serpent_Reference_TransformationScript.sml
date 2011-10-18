
open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitTheory
     markerTheory pairTheory arithmeticTheory numSyntax wordsTheory
     Serpent_Reference_UtilityTheory wordsLib;

val _ = new_theory "Serpent_Reference_Transformation";

(*---------------------------------------------------------------------------*)
(* linear transformation table used in encryption                            *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* for efficient evaluation in the place of BOUNDED_FORALL_THM               *)
(*---------------------------------------------------------------------------*)

val row_conv =
  REPEATC (numLib.BOUNDED_FORALL_CONV EVAL) THENC REWRITE_CONV [];

val LTTable_def = Define
`LTTable =
[
[16;52;56;70;83;94;105];
[72;114;125];
[2;9;15;30;76;84;126];
[36;90;103];
[20;56;60;74;87;98;109];
[1;76;118];
[2;6;13;19;34;80;88];
[40;94;107];
[24;60;64;78;91;102;113];
[5;80;122];
[6;10;17;23;38;84;92];
[44;98;111];
[28;64;68;82;95;106;117];
[9;84;126];
[10;14;21;27;42;88;96];
[48;102;115];
[32;68;72;86;99;110;121];
[2;13;88];
[14;18;25;31;46;92;100];
[52;106;119];
[36;72;76;90;103;114;125];
[6;17;92];
[18;22;29;35;50;96;104];
[56;110;123];
[1;40;76;80;94;107;118];
[10;21;96];
[22;26;33;39;54;100;108];
[60;114;127];
[5;44;80;84;98;111;122];
[14;25;100];
[26;30;37;43;58;104;112];
[3;118];
[9;48;84;88;102;115;126];
[18;29;104];
[30;34;41;47;62;108;116];
[7;122];
[2;13;52;88;92;106;119];
[22;33;108];
[34;38;45;51;66;112;120];
[11;126];
[6;17;56;92;96;110;123];
[26;37;112];
[38;42;49;55;70;116;124];
[2;15;76];
[10;21;60;96;100;114;127];
[30;41;116];
[0;42;46;53;59;74;120];
[6;19;80];
[3;14;25;100;104;118];
[34;45;120];
[4;46;50;57;63;78;124];
[10;23;84];
[7;18;29;104;108;122];
[38;49;124];
[0;8;50;54;61;67;82];
[14;27;88];
[11;22;33;108;112;126];
[0;42;53];
[4;12;54;58;65;71;86];
[18;31;92];
[2;15;26;37;76;112;116];
[4;46;57];
[8;16;58;62;69;75;90];
[22;35;96];
[6;19;30;41;80;116;120];
[8;50;61];
[12;20;62;66;73;79;94];
[26;39;100];
[10;23;34;45;84;120;124];
[12;54;65];
[16;24;66;70;77;83;98];
[30;43;104];
[0;14;27;38;49;88;124];
[16;58;69];
[20;28;70;74;81;87;102];
[34;47;108];
[0;4;18;31;42;53;92];
[20;62;73];
[24;32;74;78;85;91;106];
[38;51;112];
[4;8;22;35;46;57;96];
[24;66;77];
[28;36;78;82;89;95;110];
[42;55;116];
[8;12;26;39;50;61;100];
[28;70;81];
[32;40;82;86;93;99;114];
[46;59;120];
[12;16;30;43;54;65;104];
[32;74;85];
[36;90;103;118];
[50;63;124];
[16;20;34;47;58;69;108];
[36;78;89];
[40;94;107;122];
[0;54;67];
[20;24;38;51;62;73;112];
[40;82;93];
[44;98;111;126];
[4;58;71];
[24;28;42;55;66;77;116];
[44;86;97];
[2;48;102;115];
[8;62;75];
[28;32;46;59;70;81;120];
[48;90;101];
[6;52;106;119];
[12;66;79];
[32;36;50;63;74;85;124];
[52;94;105];
[10;56;110;123];
[16;70;83];
[0;36;40;54;67;78;89];
[56;98;109];
[14;60;114;127];
[20;74;87];
[4;40;44;58;71;82;93];
[60;102;113];
[3;18;72;114;118;125];
[24;78;91];
[8;44;48;62;75;86;97];
[64;106;117];
[1;7;22;76;118;122];
[28;82;95];
[12;48;52;66;79;90;101];
[68;110;121];
[5;11;26;80;122;126];
[32;86;99]
]`;

(* linear transformation table used in decryption *)

val InvLTTable_def = Define
`InvLTTable =
[
[53;55;72];
[1;5;20;90];
[15;102];
[3;31;90];
[57;59;76];
[5;9;24;94];
[19;106];
[7;35;94];
[61;63;80];
[9;13;28;98];
[23;110];
[11;39;98];
[65;67;84];
[13;17;32;102];
[27;114];
[1;3;15;20;43;102];
[69;71;88];
[17;21;36;106];
[1;31;118];
[5;7;19;24;47;106];
[73;75;92];
[21;25;40;110];
[5;35;122];
[9;11;23;28;51;110];
[77;79;96];
[25;29;44;114];
[9;39;126];
[13;15;27;32;55;114];
[81;83;100];
[1;29;33;48;118];
[2;13;43];
[1;17;19;31;36;59;118];
[85;87;104];
[5;33;37;52;122];
[6;17;47];
[5;21;23;35;40;63;122];
[89;91;108];
[9;37;41;56;126];
[10;21;51];
[9;25;27;39;44;67;126];
[93;95;112];
[2;13;41;45;60];
[14;25;55];
[2;13;29;31;43;48;71];
[97;99;116];
[6;17;45;49;64];
[18;29;59];
[6;17;33;35;47;52;75];
[101;103;120];
[10;21;49;53;68];
[22;33;63];
[10;21;37;39;51;56;79];
[105;107;124];
[14;25;53;57;72];
[26;37;67];
[14;25;41;43;55;60;83];
[0;109;111];
[18;29;57;61;76];
[30;41;71];
[18;29;45;47;59;64;87];
[4;113;115];
[22;33;61;65;80];
[34;45;75];
[22;33;49;51;63;68;91];
[8;117;119];
[26;37;65;69;84];
[38;49;79];
[26;37;53;55;67;72;95];
[12;121;123];
[30;41;69;73;88];
[42;53;83];
[30;41;57;59;71;76;99];
[16;125;127];
[34;45;73;77;92];
[46;57;87];
[34;45;61;63;75;80;103];
[1;3;20];
[38;49;77;81;96];
[50;61;91];
[38;49;65;67;79;84;107];
[5;7;24];
[42;53;81;85;100];
[54;65;95];
[42;53;69;71;83;88;111];
[9;11;28];
[46;57;85;89;104];
[58;69;99];
[46;57;73;75;87;92;115];
[13;15;32];
[50;61;89;93;108];
[62;73;103];
[50;61;77;79;91;96;119];
[17;19;36];
[54;65;93;97;112];
[66;77;107];
[54;65;81;83;95;100;123];
[21;23;40];
[58;69;97;101;116];
[70;81;111];
[58;69;85;87;99;104;127];
[25;27;44];
[62;73;101;105;120];
[74;85;115];
[3;62;73;89;91;103;108];
[29;31;48];
[66;77;105;109;124];
[78;89;119];
[7;66;77;93;95;107;112];
[33;35;52];
[0;70;81;109;113];
[82;93;123];
[11;70;81;97;99;111;116];
[37;39;56];
[4;74;85;113;117];
[86;97;127];
[15;74;85;101;103;115;120];
[41;43;60];
[8;78;89;117;121];
[3;90];
[19;78;89;105;107;119;124];
[45;47;64];
[12;82;93;121;125];
[7;94];
[0;23;82;93;109;111;123];
[49;51;68];
[1;16;86;97;125];
[11;98];
[4;27;86;97;113;115;127]
]`;

val LTFun_def = Define `LTFun x = EL x LTTable`;

val invLTFun_def = Define `invLTFun x = EL x InvLTTable`;

val LTFunVal = Q.store_thm(
"LTFunVal",
`
(LTFun 0 = [ 16;52;56;70;83;94;105])  /\
(LTFun 1 = [ 72;114;125])  /\
(LTFun 2 = [ 2;9;15;30;76;84;126])  /\
(LTFun 3 = [ 36;90;103])  /\
(LTFun 4 = [ 20;56;60;74;87;98;109])  /\
(LTFun 5 = [ 1;76;118])  /\
(LTFun 6 = [ 2;6;13;19;34;80;88])  /\
(LTFun 7 = [ 40;94;107])  /\
(LTFun 8 = [ 24;60;64;78;91;102;113])  /\
(LTFun 9 = [ 5;80;122])  /\
(LTFun 10 = [ 6;10;17;23;38;84;92])  /\
(LTFun 11 = [ 44;98;111])  /\
(LTFun 12 = [ 28;64;68;82;95;106;117])  /\
(LTFun 13 = [ 9;84;126])  /\
(LTFun 14 = [ 10;14;21;27;42;88;96])  /\
(LTFun 15 = [ 48;102;115])  /\
(LTFun 16 = [ 32;68;72;86;99;110;121])  /\
(LTFun 17 = [ 2;13;88])  /\
(LTFun 18 = [ 14;18;25;31;46;92;100])  /\
(LTFun 19 = [ 52;106;119])  /\
(LTFun 20 = [ 36;72;76;90;103;114;125])  /\
(LTFun 21 = [ 6;17;92])  /\
(LTFun 22 = [ 18;22;29;35;50;96;104])  /\
(LTFun 23 = [ 56;110;123])  /\
(LTFun 24 = [ 1;40;76;80;94;107;118])  /\
(LTFun 25 = [ 10;21;96])  /\
(LTFun 26 = [ 22;26;33;39;54;100;108])  /\
(LTFun 27 = [ 60;114;127])  /\
(LTFun 28 = [ 5;44;80;84;98;111;122])  /\
(LTFun 29 = [ 14;25;100])  /\
(LTFun 30 = [ 26;30;37;43;58;104;112])  /\
(LTFun 31 = [ 3;118])  /\
(LTFun 32 = [ 9;48;84;88;102;115;126])  /\
(LTFun 33 = [ 18;29;104])  /\
(LTFun 34 = [ 30;34;41;47;62;108;116])  /\
(LTFun 35 = [ 7;122])  /\
(LTFun 36 = [ 2;13;52;88;92;106;119])  /\
(LTFun 37 = [ 22;33;108])  /\
(LTFun 38 = [ 34;38;45;51;66;112;120])  /\
(LTFun 39 = [ 11;126])  /\
(LTFun 40 = [ 6;17;56;92;96;110;123])  /\
(LTFun 41 = [ 26;37;112])  /\
(LTFun 42 = [ 38;42;49;55;70;116;124])  /\
(LTFun 43 = [ 2;15;76])  /\
(LTFun 44 = [ 10;21;60;96;100;114;127])  /\
(LTFun 45 = [ 30;41;116])  /\
(LTFun 46 = [ 0;42;46;53;59;74;120])  /\
(LTFun 47 = [ 6;19;80])  /\
(LTFun 48 = [ 3;14;25;100;104;118])  /\
(LTFun 49 = [ 34;45;120])  /\
(LTFun 50 = [ 4;46;50;57;63;78;124])  /\
(LTFun 51 = [ 10;23;84])  /\
(LTFun 52 = [ 7;18;29;104;108;122])  /\
(LTFun 53 = [ 38;49;124])  /\
(LTFun 54 = [ 0;8;50;54;61;67;82])  /\
(LTFun 55 = [ 14;27;88])  /\
(LTFun 56 = [ 11;22;33;108;112;126])  /\
(LTFun 57 = [ 0;42;53])  /\
(LTFun 58 = [ 4;12;54;58;65;71;86])  /\
(LTFun 59 = [ 18;31;92])  /\
(LTFun 60 = [ 2;15;26;37;76;112;116])  /\
(LTFun 61 = [ 4;46;57])  /\
(LTFun 62 = [ 8;16;58;62;69;75;90])  /\
(LTFun 63 = [ 22;35;96])  /\
(LTFun 64 = [ 6;19;30;41;80;116;120])  /\
(LTFun 65 = [ 8;50;61])  /\
(LTFun 66 = [ 12;20;62;66;73;79;94])  /\
(LTFun 67 = [ 26;39;100])  /\
(LTFun 68 = [ 10;23;34;45;84;120;124])  /\
(LTFun 69 = [ 12;54;65])  /\
(LTFun 70 = [ 16;24;66;70;77;83;98])  /\
(LTFun 71 = [ 30;43;104])  /\
(LTFun 72 = [ 0;14;27;38;49;88;124])  /\
(LTFun 73 = [ 16;58;69])  /\
(LTFun 74 = [ 20;28;70;74;81;87;102])  /\
(LTFun 75 = [ 34;47;108])  /\
(LTFun 76 = [ 0;4;18;31;42;53;92])  /\
(LTFun 77 = [ 20;62;73])  /\
(LTFun 78 = [ 24;32;74;78;85;91;106])  /\
(LTFun 79 = [ 38;51;112])  /\
(LTFun 80 = [ 4;8;22;35;46;57;96])  /\
(LTFun 81 = [ 24;66;77])  /\
(LTFun 82 = [ 28;36;78;82;89;95;110])  /\
(LTFun 83 = [ 42;55;116])  /\
(LTFun 84 = [ 8;12;26;39;50;61;100])  /\
(LTFun 85 = [ 28;70;81])  /\
(LTFun 86 = [ 32;40;82;86;93;99;114])  /\
(LTFun 87 = [ 46;59;120])  /\
(LTFun 88 = [ 12;16;30;43;54;65;104])  /\
(LTFun 89 = [ 32;74;85])  /\
(LTFun 90 = [ 36;90;103;118])  /\
(LTFun 91 = [ 50;63;124])  /\
(LTFun 92 = [ 16;20;34;47;58;69;108])  /\
(LTFun 93 = [ 36;78;89])  /\
(LTFun 94 = [ 40;94;107;122])  /\
(LTFun 95 = [ 0;54;67])  /\
(LTFun 96 = [ 20;24;38;51;62;73;112])  /\
(LTFun 97 = [ 40;82;93])  /\
(LTFun 98 = [ 44;98;111;126])  /\
(LTFun 99 = [ 4;58;71])  /\
(LTFun 100 = [ 24;28;42;55;66;77;116])  /\
(LTFun 101 = [ 44;86;97])  /\
(LTFun 102 = [ 2;48;102;115])  /\
(LTFun 103 = [ 8;62;75])  /\
(LTFun 104 = [ 28;32;46;59;70;81;120])  /\
(LTFun 105 = [ 48;90;101])  /\
(LTFun 106 = [ 6;52;106;119])  /\
(LTFun 107 = [ 12;66;79])  /\
(LTFun 108 = [ 32;36;50;63;74;85;124])  /\
(LTFun 109 = [ 52;94;105])  /\
(LTFun 110 = [ 10;56;110;123])  /\
(LTFun 111 = [ 16;70;83])  /\
(LTFun 112 = [ 0;36;40;54;67;78;89])  /\
(LTFun 113 = [ 56;98;109])  /\
(LTFun 114 = [ 14;60;114;127])  /\
(LTFun 115 = [ 20;74;87])  /\
(LTFun 116 = [ 4;40;44;58;71;82;93])  /\
(LTFun 117 = [ 60;102;113])  /\
(LTFun 118 = [ 3;18;72;114;118;125])  /\
(LTFun 119 = [ 24;78;91])  /\
(LTFun 120 = [ 8;44;48;62;75;86;97])  /\
(LTFun 121 = [ 64;106;117])  /\
(LTFun 122 = [ 1;7;22;76;118;122])  /\
(LTFun 123 = [ 28;82;95])  /\
(LTFun 124 = [ 12;48;52;66;79;90;101])  /\
(LTFun 125 = [ 68;110;121])  /\
(LTFun 126 = [ 5;11;26;80;122;126])  /\
(LTFun 127 = [ 32;86;99])`,
REPEAT STRIP_TAC THEN EVAL_TAC);

(* linear transformation table used in decryption *)

val invLTFunVal = Q.store_thm(
"invLTFunVal",
`
(invLTFun 0 = [53;55;72])  /\
(invLTFun 1 = [1;5;20;90])  /\
(invLTFun 2 = [15;102])  /\
(invLTFun 3 = [3;31;90])  /\
(invLTFun 4 = [57;59;76])  /\
(invLTFun 5 = [5;9;24;94])  /\
(invLTFun 6 = [19;106])  /\
(invLTFun 7 = [7;35;94])  /\
(invLTFun 8 = [61;63;80])  /\
(invLTFun 9 = [9;13;28;98])  /\
(invLTFun 10 = [23;110])  /\
(invLTFun 11 = [11;39;98])  /\
(invLTFun 12 = [65;67;84])  /\
(invLTFun 13 = [13;17;32;102])  /\
(invLTFun 14 = [27;114])  /\
(invLTFun 15 = [1;3;15;20;43;102])  /\
(invLTFun 16 = [69;71;88])  /\
(invLTFun 17 = [17;21;36;106])  /\
(invLTFun 18 = [1;31;118])  /\
(invLTFun 19 = [5;7;19;24;47;106])  /\
(invLTFun 20 = [73;75;92])  /\
(invLTFun 21 = [21;25;40;110])  /\
(invLTFun 22 = [5;35;122])  /\
(invLTFun 23 = [9;11;23;28;51;110])  /\
(invLTFun 24 = [77;79;96])  /\
(invLTFun 25 = [25;29;44;114])  /\
(invLTFun 26 = [9;39;126])  /\
(invLTFun 27 = [13;15;27;32;55;114])  /\
(invLTFun 28 = [81;83;100])  /\
(invLTFun 29 = [1;29;33;48;118])  /\
(invLTFun 30 = [2;13;43])  /\
(invLTFun 31 = [1;17;19;31;36;59;118])  /\
(invLTFun 32 = [85;87;104])  /\
(invLTFun 33 = [5;33;37;52;122])  /\
(invLTFun 34 = [6;17;47])  /\
(invLTFun 35 = [5;21;23;35;40;63;122])  /\
(invLTFun 36 = [89;91;108])  /\
(invLTFun 37 = [9;37;41;56;126])  /\
(invLTFun 38 = [10;21;51])  /\
(invLTFun 39 = [9;25;27;39;44;67;126])  /\
(invLTFun 40 = [93;95;112])  /\
(invLTFun 41 = [2;13;41;45;60])  /\
(invLTFun 42 = [14;25;55])  /\
(invLTFun 43 = [2;13;29;31;43;48;71])  /\
(invLTFun 44 = [97;99;116])  /\
(invLTFun 45 = [6;17;45;49;64])  /\
(invLTFun 46 = [18;29;59])  /\
(invLTFun 47 = [6;17;33;35;47;52;75])  /\
(invLTFun 48 = [101;103;120])  /\
(invLTFun 49 = [10;21;49;53;68])  /\
(invLTFun 50 = [22;33;63])  /\
(invLTFun 51 = [10;21;37;39;51;56;79])  /\
(invLTFun 52 = [105;107;124])  /\
(invLTFun 53 = [14;25;53;57;72])  /\
(invLTFun 54 = [26;37;67])  /\
(invLTFun 55 = [14;25;41;43;55;60;83])  /\
(invLTFun 56 = [0;109;111])  /\
(invLTFun 57 = [18;29;57;61;76])  /\
(invLTFun 58 = [30;41;71])  /\
(invLTFun 59 = [18;29;45;47;59;64;87])  /\
(invLTFun 60 = [4;113;115])  /\
(invLTFun 61 = [22;33;61;65;80])  /\
(invLTFun 62 = [34;45;75])  /\
(invLTFun 63 = [22;33;49;51;63;68;91])  /\
(invLTFun 64 = [8;117;119])  /\
(invLTFun 65 = [26;37;65;69;84])  /\
(invLTFun 66 = [38;49;79])  /\
(invLTFun 67 = [26;37;53;55;67;72;95])  /\
(invLTFun 68 = [12;121;123])  /\
(invLTFun 69 = [30;41;69;73;88])  /\
(invLTFun 70 = [42;53;83])  /\
(invLTFun 71 = [30;41;57;59;71;76;99])  /\
(invLTFun 72 = [16;125;127])  /\
(invLTFun 73 = [34;45;73;77;92])  /\
(invLTFun 74 = [46;57;87])  /\
(invLTFun 75 = [34;45;61;63;75;80;103])  /\
(invLTFun 76 = [1;3;20])  /\
(invLTFun 77 = [38;49;77;81;96])  /\
(invLTFun 78 = [50;61;91])  /\
(invLTFun 79 = [38;49;65;67;79;84;107])  /\
(invLTFun 80 = [5;7;24])  /\
(invLTFun 81 = [42;53;81;85;100])  /\
(invLTFun 82 = [54;65;95])  /\
(invLTFun 83 = [42;53;69;71;83;88;111])  /\
(invLTFun 84 = [9;11;28])  /\
(invLTFun 85 = [46;57;85;89;104])  /\
(invLTFun 86 = [58;69;99])  /\
(invLTFun 87 = [46;57;73;75;87;92;115])  /\
(invLTFun 88 = [13;15;32])  /\
(invLTFun 89 = [50;61;89;93;108])  /\
(invLTFun 90 = [62;73;103])  /\
(invLTFun 91 = [50;61;77;79;91;96;119])  /\
(invLTFun 92 = [17;19;36])  /\
(invLTFun 93 = [54;65;93;97;112])  /\
(invLTFun 94 = [66;77;107])  /\
(invLTFun 95 = [54;65;81;83;95;100;123])  /\
(invLTFun 96 = [21;23;40])  /\
(invLTFun 97 = [58;69;97;101;116])  /\
(invLTFun 98 = [70;81;111])  /\
(invLTFun 99 = [58;69;85;87;99;104;127])  /\
(invLTFun 100 = [25;27;44])  /\
(invLTFun 101 = [62;73;101;105;120])  /\
(invLTFun 102 = [74;85;115])  /\
(invLTFun 103 = [3;62;73;89;91;103;108])  /\
(invLTFun 104 = [29;31;48])  /\
(invLTFun 105 = [66;77;105;109;124])  /\
(invLTFun 106 = [78;89;119])  /\
(invLTFun 107 = [7;66;77;93;95;107;112])  /\
(invLTFun 108 = [33;35;52])  /\
(invLTFun 109 = [0;70;81;109;113])  /\
(invLTFun 110 = [82;93;123])  /\
(invLTFun 111 = [11;70;81;97;99;111;116])  /\
(invLTFun 112 = [37;39;56])  /\
(invLTFun 113 = [4;74;85;113;117])  /\
(invLTFun 114 = [86;97;127])  /\
(invLTFun 115 = [15;74;85;101;103;115;120])  /\
(invLTFun 116 = [41;43;60])  /\
(invLTFun 117 = [8;78;89;117;121])  /\
(invLTFun 118 = [3;90])  /\
(invLTFun 119 = [19;78;89;105;107;119;124])  /\
(invLTFun 120 = [45;47;64])  /\
(invLTFun 121 = [12;82;93;121;125])  /\
(invLTFun 122 = [7;94])  /\
(invLTFun 123 = [0;23;82;93;109;111;123])  /\
(invLTFun 124 = [49;51;68])  /\
(invLTFun 125 = [1;16;86;97;125])  /\
(invLTFun 126 = [11;98])  /\
(invLTFun 127 = [4;27;86;97;113;115;127])`,
REPEAT STRIP_TAC THEN EVAL_TAC);


(* compute the parity on select bits *)

val selParity_def = Define
`(selParity (w:word128) [] = F) /\
 (selParity w (pos::t) = boolXor (w ' pos) (selParity w t))`;

val selParityAppend = Q.store_thm(
 "selParityAppend",
 `!w l1 l2. selParity w (l1++l2) = boolXor (selParity w l1) (selParity w l2)`,
 Induct_on `l1` THEN
 RW_TAC list_ss [selParity_def] THEN
 METIS_TAC [boolXorFacts,boolXorComm,boolXorAssoc,selParity_def]);

(*linear transform*)

val transform_def = Define
`(transform transFun 0 (w:word128)
  = let newBit = selParity w (transFun 0)
    in
    if newBit
       then (1w:word128)
       else (0w:word128))
 /\
 (transform transFun (SUC i) w
 = let newBit = selParity w (transFun (SUC i))
   in
   let newWord = if newBit
                  then ((1w:word128)<<(SUC i))
          else (0w:word128)
   in
   newWord || transform transFun i w)`;

val transformEval = Q.store_thm(
 "transformEval",
 `!n transFun (w:word128).
    transform transFun n w =
        if n = 0
           then let newBit = selParity w (transFun 0)
                in
            if newBit
               then (1w:word128)
               else (0w:word128)
           else    let newBit = selParity w (transFun n)
                in
              let newWord = if newBit
                           then ((1w:word128)<<n)
                            else (0w:word128)
               in
             newWord || transform transFun (n-1) w`,
  RW_TAC std_ss [transform_def,LET_THM] THEN
  (Cases_on `n` THENL [
     METIS_TAC [],
     FULL_SIMP_TAC arith_ss [transform_def,LET_THM]]));

val LT_def = Define `LT w =  transform LTFun 127 w`;

val invLT_def = Define `invLT w =  transform invLTFun 127 w`;

(*desired properties of transform*)

val transform_inv1_w128 = Q.store_thm(
 "transform_inv1_w128",
 `!to d w transFun.
     to < 128 /\
      d < 128 /\
     to > d
     ==>
     ~((transform transFun d w) ' to)`,
  Induct_on `d` THEN
  SRW_TAC [WORD_BIT_EQ_ss,BIT_ss] [n2w_def,transform_def,LET_THM]);

val transform_inv2_w128 = Q.store_thm(
 "transform_inv2_w128",
 `!to d w transFun.
     to < 128 /\
      d < 128 /\
     to <= d
     ==>
     ((transform transFun d w) ' to = selParity w (transFun to))`,
 Induct_on `d` THEN
  SRW_TAC [WORD_BIT_EQ_ss] [transform_def,LET_THM] THEN
  `d < 128` by DECIDE_TAC THEN
  Cases_on `to <= d` THEN
  ASM_SIMP_TAC arith_ss [] THEN
  `to = SUC d` by DECIDE_TAC THEN
  SRW_TAC [WORD_BIT_EQ_ss,BIT_ss] [n2w_def,transform_inv1_w128]);

(* the composite of two linear transformations *)

val transCompose_def = Define `transCompose f1 f2 = \x. FLAT (MAP f1 (f2 x))`;

(* a transform function is legal *)

val transInRange_def = Define
 `transInRange transFun =
    !i. i < 128 ==> ALL_EL (\x. x < 128) (transFun i)`;

val LTFunInRange = Q.store_thm(
 "LTFunInRange",
 `transInRange LTFun`,
 SIMP_TAC std_ss [transInRange_def] THEN CONV_TAC (time row_conv));

val invLTFunInRange = Q.store_thm(
 "invLTFunInRange",
 `transInRange invLTFun`,
 SIMP_TAC std_ss [transInRange_def] THEN CONV_TAC (time row_conv));

(* desired properties of composite of linear transformations *)

val transformComposeLemma = Q.store_thm(
 "transformComposeLemma",
 `!transFun1 transL2 w.
    transInRange transFun1  /\
    ALL_EL (\x. x < 128) transL2
    ==>
    (selParity (transform transFun1 127 w) transL2
     = selParity w (FLAT (MAP transFun1 transL2)))`,
 Induct_on `transL2` THEN
 FULL_SIMP_TAC list_ss
   [MAP,FLAT,selParity_def,transform_def,selParityAppend,transform_inv2_w128]);

val transformComposeBit = Q.store_thm(
 "transformComposeBit",
 `!i transFun1 transFun2 w.
    i < 128                 /\
    transInRange transFun1  /\
    transInRange transFun2
    ==>
    ((transform transFun2 127 (transform transFun1 127 w)) ' i =
     (transform (transCompose transFun1 transFun2) 127 w) ' i)`,
 RW_TAC arith_ss [transCompose_def,transInRange_def,transform_inv2_w128,
                  transformComposeLemma]);

val transformComposeWord = Q.store_thm(
 "transformComposeWord",
 `!transFun1 transFun2 w.
    transInRange transFun1  /\
    transInRange transFun2
    ==>
    (transform transFun2 127 (transform transFun1 127 w) =
     transform (transCompose transFun1 transFun2) 127 w)`,
 SRW_TAC [WORD_BIT_EQ_ss] [transformComposeBit]);

val TL128_eq_makeTL128 = save_thm(
 "TL128_eq_makeTL128", SYM (EVAL ``makeTL 128``));

(* the intermediate values of the composite of the two given linear
   transformation functions, used to speed up the verification *)

val Res_def = Define `Res i = FLAT (MAP LTFun (invLTFun i))`;

(*load "numSyntax";
quietdec := true;
open numSyntax;
quietdec := false;*)

val ResTable =
  LIST_CONJ (map EVAL (map (fn i => ``Res ^(term_of_int i)``) (upto 0 127)));

val _ = computeLib.add_thms [ResTable] computeLib.the_compset;

(* parity check is the same as counting EVEN or ODD.
   countEvenL and countEven is the two equivalent description,
   while countEvenL reduce a layer of loop *)

val countL_def = Define
`(countL l []= l) /\
 (countL l (h::t) = let x = makeL h
                  in
                  let tmp = zipXor x l
          in
                  countL tmp t)`;

val countEvenL_def = Define`
 countEvenL tl =
   countL
     [T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
       T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
       T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
       T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
       T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
       T; T; T; T; T; T; T; T; T; T; T; T; T] tl`;

val countEvenL_LT_facts = Q.store_thm(
 "countEvenL_LT_facts",
 `!i.
    i < 128
    ==>
        (countEvenL (Res i) = countEvenL [i]) `,
 SIMP_TAC std_ss [] THEN CONV_TAC (time row_conv) THEN REWRITE_TAC []);

val countEven_def = Define`
 (countEven x [] = T) /\
 (countEven x (h::t) = boolXor (x = h) (countEven x t))`;

val countL_fact = Q.store_thm(
 "countL_fact",
 `!i al h tl.
    i < LENGTH al  /\
    h < LENGTH al  /\
    ALL_EL (\x. x < LENGTH al) tl
    ==>
    (EL i (countL (zipXor (makeL h) al) tl) =
     boolXor (i = h) (EL i (countL al tl)))`,
 Induct_on `tl` THEN
 RW_TAC list_ss [countL_def,LET_THM,zipXor_makeL,
                 zipXor_makeL_COMM,LENGTH_zipXor,boolXorComm3]);

val Res_fact = Q.store_thm(
 "Res_fact",
 `!i.
    i < 128
    ==>
    ALL_EL (\x. x < 128) (Res i)`,
 SIMP_TAC std_ss [] THEN CONV_TAC (time row_conv));

(* equivalence between countEven and countEvenL *)

val countEvenL_countEven_eq = Q.store_thm(
 "countEvenL_countEven_eq",
 `!i tl.
    i < 128 /\
    ALL_EL (\x. x < 128) tl
    ==>
    (EL i (countEvenL tl) = countEven i tl)`,
 SIMP_TAC std_ss [] THEN
 Induct_on `tl` THENL [
   FULL_SIMP_TAC arith_ss [countEvenL_def,countEven_def,countL_def,
                           TL128_eq_makeTL128,makeTL_fact],

   FULL_SIMP_TAC std_ss [ALL_EL,countEvenL_def,countEven_def,countL_def,
                         LET_THM,TL128_eq_makeTL128,makeTL_fact,
                         zipXor_makeL_COMM,LENGTH_zipXor,boolXorComm3,
                         LENGTH_makeTL] THEN
   FULL_SIMP_TAC std_ss [countEven_def,countL_fact,countEvenL_def,
                         TL128_eq_makeTL128,LENGTH_makeTL]]);

val LTFun_invLTFun_fact = Q.store_thm(
 "LTFun_invLTFun_fact",
 `!i.
    i < 128
    ==>
    !j.
         j < 128
         ==>
         (countEven j ((transCompose LTFun invLTFun) i)
          = countEven j [i])`,
 RW_TAC std_ss [GSYM Res_def, transCompose_def, GSYM countEvenL_countEven_eq,
                countEvenL_LT_facts,Res_fact,ALL_EL]);

(* desired properties of countEven *)

val countEven_filter1 = Q.store_thm(
 "countEven_filter1",
 `!i L d transL.
    LENGTH transL <= L /\
    i < d+1  /\
    ALL_EL (\x. x < d+1) transL

    ==>
    countEven i (FILTER (\x. ~(x = i)) transL)`,
 Induct_on `L` THEN
 RW_TAC arith_ss [countEven_def,ALL_EL,LENGTH_NIL,FILTER] THEN
 Cases_on `transL` THEN
 RW_TAC arith_ss [countEven_def,ALL_EL,LENGTH_NIL,FILTER] THEN
 FULL_SIMP_TAC list_ss [boolXor_def] THEN
 METIS_TAC []);


val countEven_filter2 = Q.store_thm(
 "countEven_filter2",
 `!i k L d transL.
    LENGTH transL <= L /\
    i < d+1  /\
    k < d+1  /\
    ALL_EL (\x. x < d+1) transL
    ==>
    (countEven k (FILTER (\x. ~(x = i)) transL)
     = if k = i
          then T
          else countEven k transL)`,
 Induct_on `L` THEN
 RW_TAC arith_ss [countEven_def,ALL_EL,LENGTH_NIL,FILTER] THEN
 Cases_on `transL` THEN
 FULL_SIMP_TAC list_ss [countEven_def,ALL_EL,LENGTH_NIL,FILTER]THEN
 Cases_on `k = i` THEN Cases_on `h = i` THEN
 RW_TAC std_ss [boolXor_def,countEven_def] THEN
 METIS_TAC []);

val countEven_filter3 = Q.store_thm(
 "countEven_filter3",
 `!i k L d transL1 transL2.
    LENGTH transL1 <= L /\
    LENGTH transL2 <= L /\
    (!j. j < d+1 ==> (countEven j transL1 = countEven j transL2)) /\
    i < d+1  /\
    k < d+1  /\
    ALL_EL (\x. x < d+1) transL1 /\
    ALL_EL (\x. x < d+1) transL2
    ==>
    (countEven k (FILTER (\x. ~(x = i)) transL1) =
     countEven k (FILTER (\x. ~(x = i)) transL2))`,
 RW_TAC std_ss [] THEN METIS_TAC [countEven_filter2]);

(* desired properties of selParity *)

val selParity_filter = Q.store_thm(
 "selParity_filter",
 `!i transL w.
    i < 128 /\
    ALL_EL (\x. x < 128) transL
    ==>
    (selParity w transL
     = if countEven i transL
          then  selParity w (FILTER (\x. ~(x = i)) transL)
          else  boolXor (w ' i) (selParity w (FILTER (\x. ~(x = i)) transL)))`,
 Induct_on `transL`  THEN1 METIS_TAC [FILTER,countEven_def] THEN
   SRW_TAC [] [selParity_def,countEven_def,FILTER,ALL_EL] THEN
   FULL_SIMP_TAC std_ss [boolXor_def] THEN METIS_TAC []);

(*equivalence between two position list used in selParity*)

val selParity_eq1 = Q.store_thm(
 "selParity_eq1",
 `!L transL1 transL2 w.
    ALL_EL (\x. x < 128) transL1 /\
    ALL_EL (\x. x < 128) transL2 /\
    LENGTH transL1 <= L /\
    LENGTH transL2 <= L /\
    (!j. j < 128 ==> (countEven j transL1 = countEven j transL2 ))
    ==>
    (selParity w transL1  = selParity w transL2)`,
 Induct_on `L` THEN
 RW_TAC arith_ss [boolXor_def,countEven_def,selParity_def,LENGTH_NIL] THEN
 Cases_on `transL1` THEN Cases_on `transL2` THENL [
    RW_TAC arith_ss [selParity_def],
    `h < 128` by FULL_SIMP_TAC list_ss [ALL_EL] THEN
    `!j. j < 128 ==>
      countEven j (FILTER (\x. ~(x = h)) (h::t)) = countEven h (h::t)`
      by METIS_TAC [countEven_def, countEven_filter2,
                    numLib.num_CONV ``128``, ADD1] THEN
    `!j:num. countEven j []` by METIS_TAC [countEven_def] THEN
    `!j. j < 128 ==> countEven j (FILTER (\x. ~(x = h)) (h::t))`
      by METIS_TAC [countEven_def] THEN
    FULL_SIMP_TAC bool_ss [FILTER] THEN
    `LENGTH (FILTER (\x. ~(x = h)) t) <= L`
      by (FULL_SIMP_TAC list_ss [] THEN
          METIS_TAC [LENGTH_FILTER, LESS_EQ_TRANS]) THEN
    `LENGTH ([]:num list) <= L` by RW_TAC arith_ss [LENGTH] THEN
    `ALL_EL (\x. x < 128) t` by FULL_SIMP_TAC list_ss [ALL_EL] THEN
    `!j. j < 128 ==> (countEven j [] = countEven j (FILTER (\x. ~(x = h)) t))`
       by METIS_TAC [] THEN
    `ALL_EL (\x. x < 128) (FILTER (\x. ~(x = h)) t)`
       by METIS_TAC [ALL_EL_FILTER] THEN
    `selParity w [] = selParity w (FILTER (\x. ~(x = h)) t)`
       by METIS_TAC [] THEN
     `countEven h (h::t)` by METIS_TAC [] THEN
     `~countEven h t`
       by FULL_SIMP_TAC std_ss [countEven_def,boolXor_def] THEN
     METIS_TAC [selParity_filter, boolXor_def, selParity_def, countEven_def],
    `h < 128` by FULL_SIMP_TAC list_ss [ALL_EL] THEN
    `!j. j < 128 ==>
      countEven j (FILTER (\x. ~(x = h)) (h::t)) = countEven h (h::t)`
      by METIS_TAC [countEven_def, countEven_filter2,
                    numLib.num_CONV ``128``, ADD1] THEN
    `!j:num. countEven j []` by METIS_TAC [countEven_def] THEN
    `!j. j < 128 ==> countEven j (FILTER (\x. ~(x = h)) (h::t))`
      by METIS_TAC [countEven_def] THEN
    FULL_SIMP_TAC bool_ss [FILTER] THEN
    `LENGTH (FILTER (\x. ~(x = h)) t) <= L`
      by (FULL_SIMP_TAC list_ss [] THEN
          METIS_TAC [LENGTH_FILTER, LESS_EQ_TRANS]) THEN
    `LENGTH ([]:num list) <= L` by RW_TAC arith_ss [LENGTH] THEN
    `ALL_EL (\x. x < 128) t` by FULL_SIMP_TAC list_ss [ALL_EL] THEN
    `!j. j < 128 ==> (countEven j [] = countEven j (FILTER (\x. ~(x = h)) t))`
       by METIS_TAC [] THEN
    `ALL_EL (\x. x < 128) (FILTER (\x. ~(x = h)) t)`
       by METIS_TAC [ALL_EL_FILTER] THEN
    `selParity w [] = selParity w (FILTER (\x. ~(x = h)) t)`
       by METIS_TAC [] THEN
     `countEven h (h::t)` by METIS_TAC [] THEN
     `~countEven h t`
       by FULL_SIMP_TAC std_ss [countEven_def,boolXor_def] THEN
     METIS_TAC [selParity_filter, boolXor_def, selParity_def, countEven_def],
    `(h < 128) /\ (h' < 128)` by FULL_SIMP_TAC std_ss [ALL_EL] THEN
    `!j. j < 128 ==>
        (countEven j (FILTER (\x. ~(x = h')) (h::t)) =
         countEven j (FILTER (\x. ~(x = h')) (h'::t')))`
         by METIS_TAC [countEven_def, numLib.num_CONV ``128``, ADD1,
                       countEven_filter3] THEN
    `ALL_EL (\x. x < 128) (FILTER (\x. ~(x = h')) (h::t)) /\
     ALL_EL (\x. x < 128) (FILTER (\x. ~(x = h')) (h'::t'))`
        by METIS_TAC [ALL_EL_FILTER] THEN
    `LENGTH (FILTER (\x. ~(x = h')) (h::t)) <= LENGTH (h::t) /\
     LENGTH (FILTER (\x. ~(x = h')) (h'::t')) <= LENGTH (h'::t')`
        by FULL_SIMP_TAC arith_ss [LENGTH_FILTER] THEN
    `LENGTH (FILTER (\x. ~(x = h')) (h'::t')) <= SUC L /\
     LENGTH (FILTER (\x. ~(x = h')) (h::t)) <= SUC L`
        by FULL_SIMP_TAC arith_ss [] THEN
    `!j. j < 128 ==>
        (countEven j (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h::t))) =
         countEven j (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h'::t'))))`
        by METIS_TAC [countEven_filter3,ADD1,numLib.num_CONV ``128``] THEN
    `(FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h::t)) =
      FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) t)) /\
     (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h'::t')) =
      FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) t'))`
        by  RW_TAC list_ss [FILTER_COMM, FILTER] THEN
    `ALL_EL (\x. x < 128)
            (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h'::t'))) /\
     ALL_EL (\x. x < 128)
            (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h::t)))`
        by METIS_TAC [ALL_EL_FILTER] THEN
    `LENGTH (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) t)) <= L /\
     LENGTH (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) t')) <= L`
        by (FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC [LENGTH_FILTER, LESS_EQ_TRANS]) THEN
    `selParity w (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h::t))) =
     selParity w (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h'::t')))`
        by METIS_TAC [] THEN
    `(selParity w (h::t) =
        if countEven h' (h::t)
        then selParity w (FILTER (\x. ~(x = h')) (h::t))
        else boolXor (w ' h') (selParity w (FILTER (\x. ~(x = h')) (h::t)))) /\
     (selParity w (h'::t') =
        if countEven h' (h'::t')
        then selParity w (FILTER (\x. ~(x = h')) (h'::t'))
        else boolXor (w ' h') (selParity w (FILTER (\x. ~(x = h')) (h'::t'))))`
        by METIS_TAC [selParity_filter] THEN
     `(selParity w (FILTER (\x. ~(x = h')) (h::t)) =
        if countEven h (FILTER (\x. ~(x = h')) (h::t))
        then selParity w (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h::t)))
        else boolXor (w ' h) (selParity w
               (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h::t))))) /\
      (selParity w (FILTER (\x. ~(x = h')) (h'::t')) =
        if countEven h (FILTER (\x. ~(x = h')) (h'::t'))
        then selParity w (FILTER (\x. ~(x = h))
                            (FILTER (\x. ~(x = h')) (h'::t')))
        else boolXor (w ' h) (selParity w
               (FILTER (\x. ~(x = h)) (FILTER (\x. ~(x = h')) (h'::t')))))`
        by METIS_TAC [selParity_filter] THEN
      Cases_on `countEven h' (h::t)` THEN
      Cases_on `countEven h (h::t)` THEN
      Cases_on `countEven h' (h'::t')` THEN
      Cases_on `countEven h (h'::t')` THEN
      FULL_SIMP_TAC std_ss [] THEN
      METIS_TAC []]);

val selParity_eq2 = Q.store_thm(
 "selParity_eq2",
  `!transL1 transL2 w.
    ALL_EL (\x. x < 128) transL1 /\
    ALL_EL (\x. x < 128) transL2 /\
    (!j.
        j <  128
        ==>
        (countEven j transL1 = countEven j transL2 ))
    ==>
    (selParity w transL1 = selParity w transL2)`,
 RW_TAC std_ss [] THEN
 Cases_on `LENGTH transL1 < LENGTH transL2` THENL [
    `LENGTH transL1 <=  LENGTH transL2` by RW_TAC arith_ss [] THEN
    `LENGTH transL2 <=  LENGTH transL2` by RW_TAC arith_ss [] THEN
    METIS_TAC [selParity_eq1],
    `LENGTH transL1 <=  LENGTH transL1` by RW_TAC arith_ss [] THEN
    `LENGTH transL2 <=  LENGTH transL1` by RW_TAC arith_ss [] THEN
    METIS_TAC [selParity_eq1]]);

(* given linear transformations cancel each other *)

val invLT_LT_cancel = Q.store_thm(
 "invLT_LT_cancel",
 `!w. invLT (LT w) = w`,
 SRW_TAC [fcpLib.FCP_ss]
   [invLT_def,LT_def,transformComposeWord,LTFunInRange,invLTFunInRange] THEN
 `w ' i = selParity w [i]` by RW_TAC std_ss [selParity_def,boolXor_def] THEN
 FULL_SIMP_TAC arith_ss [transform_inv2_w128] THEN
 `ALL_EL (\x. x < 128) (transCompose LTFun invLTFun i)`
   by FULL_SIMP_TAC arith_ss [GSYM Res_def,transCompose_def] THENL [
    `!i. i < 128 ==> ALL_EL (\x. x < 128) (Res i)`
       by METIS_TAC [Res_fact] THEN
    FULL_SIMP_TAC arith_ss [],
    `ALL_EL (\x. x < 128) [i]` by RW_TAC list_ss [ALL_EL] THEN
    RW_TAC arith_ss [LTFun_invLTFun_fact,selParity_eq2]]);

val _ = export_theory();
