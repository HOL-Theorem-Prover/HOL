#!/usr/bin/perl -w

=head1 NAME

runepar.pl (Script running special large-theory E strategies)

=head1 SYNOPSIS

runepar.pl timelimit sine file [doproof serial cleanup]

=head1 DESCRIPTION

parallelizes (or serializes) E with different (now hardwired) large-theory strategies, 
possibly calling --sine=Auto 

=head1 CONTACT

Josef Urban (firstname dot lastname at gmail dot com)

=head1 COPYRIGHT

Copyright (C) 2012-2013 Josef Urban (firstname dot lastname at gmail dot com)

=head1 LICENCE

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

=cut



use strict;
my @allargs = @ARGV;

my $tl = shift @ARGV;
my $sine = shift @ARGV; # 0 or 1
my $file = shift @ARGV;
my $doproof = shift @ARGV; # 0, 1, 2 or nothing (which means 1); 2 means proofs go to stdout too
my $serial = shift @ARGV; # 0, 1 or nothing (which means 0 - run in parallel)
my $cleanup = shift @ARGV; # 0, 1 or nothing (which means 1 - do cleanup)
my $strset = shift @ARGV; # the strategy set to use: default, greedy, f6_40_128, m10u2_184, new_mzt_small
my $gcache = shift @ARGV; # string or nothing

$doproof = 1 unless(defined($doproof));
$serial = 0 unless(defined($serial));
$cleanup = 1 unless(defined($cleanup));
$gcache = '' unless(defined($gcache));

# this is handled below
#$strset = 'default' unless(defined($strset));


die "runepar.pl takes at least three paramaters: timelimit dosine inputfile" unless((defined $tl) && (defined $sine) && (defined $file));

my $tl1 = 1 + $tl;

## only do caching if the last argument is a readable file
# if(($gcache ne '') && (-r $file)) 
# {
#     die "Bad cache" unless(-d $gcache);
#     # filename and cache name are not relevant
#     my @relevantargs = ($tl,$sine,@allargs[3 .. ($#allargs - 1)]);
#     use Digest::SHA;

#     my $sh1=Digest::SHA->new; 
#     $sh1->addfile($file); 
#     my $inputsha1 = $sh1->hexdigest;
#     my ($twochars) = $inputsha1 =~ m/^(..).*/;
#     my $optsname = Digest::SHA::sha1_hex(join(':::',@relevantargs));

#     if(-r "$gcache/$optsname/$twochars/$inputsha1") # we have found the cached result
#     {
# 	exec("cat $gcache/$optsname/$twochars/$inputsha1");
#     }
#     else
#     {
# 	unless(-d "$gcache/$optsname")
# 	{
# 	    `mkdir -p $gcache/$optsname`;
# 	    open(P,">$gcache/$optsname/.params");
# 	    print P (join(':::',@relevantargs), "\n");
# 	    close(P);
# 	}
# 	`mkdir -p $gcache/$optsname/$twochars` unless(-d "$gcache/$optsname/$twochars");
# 	open(STDOUT, "| tee $gcache/$optsname/$twochars/$inputsha1");
#     }
# }


my @strats;  # the strategies used, now set to @mizstratsold

# mizstratsold without four (protokoll_X----_sauto_300 ,
# protokoll_my14simple, protokoll_my16simple, protokoll_my22simple)
my @mizstrats1 =
(
'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05',
# 'protokoll_my14simple',
# 'protokoll_my16simple',
'protokoll_my18simple',
# 'protokoll_my22simple',
'protokoll_my21simple',
'protokoll_my24simple',
'protokoll_my8simple_sine13',
'protokoll_my11simple_sine13',
'protokoll_my1_SOS',
'protokoll_my13simple',
'protokoll_X----_auto_sine03',
# 'protokoll_X----_sauto_300',
'protokoll_my23simple'
);

my @greedymizstrats =
(
 'protokoll_my21simple',
 'protokoll_my14simple',
 'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y',
 'protokoll_my8simple_sine13',
 'protokoll_my18simple',
 'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y',
 'protokoll_my16simple',
 'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05',
 'protokoll_X----_sauto_300',
 'protokoll_X----_auto_sine03',
 'protokoll_my23simple',
 'protokoll_my1_SOS',
 'protokoll_my22simple',
 'protokoll_my11simple_sine13'
# 'protokoll_my24simple',
# 'protokoll_my13simple'
);



# tstf6_40_128
my @f6_40_128 =
(
'protokoll_atpstr_my_37be21ea059a2fcb865621e373a97f33a9d07b12',
'protokoll_atpstr_my_5fce846ef89413a220d0951fb615d42ded72b119',
'protokoll_atpstr_my_05c900b7acd7e0314c15fce53bb9e79cf904cd89',
'protokoll_atpstr_my_4e6e6157a8ac18b9bae11142d40377c9660db06b',
'protokoll_atpstr_my_a175515211bb22b22434eae9bbbfab623676a2ba',
'protokoll_atpstr_my_c284f1f10aedfccc65cdb7d9b1210ef814cb8f1a',
'protokoll_atpstr_my_0b08a1d1a32ffc279e90769114bdfda18e672e1c',
'protokoll_atpstr_my_3e6c84c618b85cc326775b240e7b2b07e3a2dde9',
'protokoll_atpstr_my_e4d2b8713a71da3a6bc64790217310975ccdde24',
'protokoll_atpstr_my_a473e2c35f909af4ba00d9f1a7a8a454a851ed9c',
'protokoll_atpstr_my_e8ac4ce30401bd9e99200725cfa03816a32e3aa4',
'protokoll_atpstr_my_92168ebc2ef464a6f2d6a311a4fa90219fd0aa91',
'protokoll_atpstr_my_7b674c1081cd73ca6ce34d02596e6f6fd903ac6c',
'protokoll_atpstr_my_a74b37f2d8b7e35be554fc999f671188cf40f113'
);

# m10u2_184
my @m10u2_184 =
(
'protokoll_atpstr_my_88760aa43d575e84b7030b8a6188f74ba5f80dc7',
'protokoll_atpstr_my_cfee9ff42189552c6557cda7d36f20820c827219',
'protokoll_atpstr_my_2eeaa79326ed674ea9ebfc3531c32ba1feec013b',
'protokoll_atpstr_my_eba37f91665fc364eeb63558058658ee9a149d9a',
'protokoll_atpstr_my_a3154f3180cc47331f1b05c36960c32e4805a7c5',
'protokoll_atpstr_my_e6869afe09f22abfbe1163ee95524cfdbfe77603',
'protokoll_atpstr_my_a4a4da5778ba9bebf9bc5e616786c7ad501b1af5',
'protokoll_atpstr_my_e3b5200232138aedc93b8882335da60ccd317d87',
'protokoll_atpstr_my_69856783cec8fab1acccfe08bb382ad42c8475df',
'protokoll_atpstr_my_8fb389ef013a89e03c1aa87be52b2f151b1819cc',
'protokoll_atpstr_my_304d2e324da665c057353a60ddd91c0712280c88',
'protokoll_atpstr_my_fc3fb6907f504dffe1a6181663296b37fe358480',
'protokoll_atpstr_my_e6ff24ca1a5013a612ccffc94da0b282477718de',
'protokoll_atpstr_my_1518b94b1627f7a5f7ce55e37817c09306fe714c'
);



# new mzt small
my @new_mzt_small =
(
'protokoll_atpstr_my_2af8b399ea0b8c22c6fc1b13069ad80214f9fa8b',
'protokoll_atpstr_my_2d0c1ae7703dba890de879a4f4409a64f9856908',
'protokoll_atpstr_my_40306ce1a432dd48c918ac611d77fc5069b2fbc7',
'protokoll_atpstr_my_43029cedefea4858aae9c4ebd6be482056ce22f4',
'protokoll_atpstr_my_9cb7c8ca63fd56afb053ade56353a3b00eee7e6a',
'protokoll_atpstr_my_9f72062a403172caf26fbe878a32becf1403c276',
'protokoll_atpstr_my_9fde028f05afb32f97bced19843d73b32d923682',
'protokoll_atpstr_my_c0d9db6a7b7a90437bd07739f25aa91c0ffc1607',
'protokoll_atpstr_my_c13d4886baa4fa2cef7b4f50892895255b04b078',
'protokoll_atpstr_my_d60b37aca40b6e560cee4bde2efc36c05a24873f',
'protokoll_atpstr_my_edc94794a7d25c504761344c2a8b4afaac43a2d0',
'protokoll_atpstr_my_f67d73f57ffeda22ddd93400237cd848911520e5',
'protokoll_atpstr_my_f9ecf400d7420b0148b2ef7cf4b1498512cf83fd',
'protokoll_atpstr_my_fe548d15a6fc730fd350de634ad9d912ae198efd'
);


# we only run these 16 now (first version for mizar used for casc mzt 12)
# it seems that some are redundant, see above
my @mizstratsold =
(
'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05',
'protokoll_my14simple',
'protokoll_my16simple',
'protokoll_my18simple',
'protokoll_my22simple',
'protokoll_my21simple',
'protokoll_my24simple',
'protokoll_my8simple_sine13',
'protokoll_my11simple_sine13',
'protokoll_my1_SOS',
'protokoll_my13simple',
'protokoll_X----_auto_sine03',
'protokoll_X----_sauto_300',
'protokoll_my23simple'
);

# the E strategies before CliStr growing, inlcuding the six covering MZT training problems
my @origEStrats =
(
'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05',
'protokoll_G-E--_008_B31_F1_PI_AE_S4_CS_SP_S2S',
'protokoll_G-E--_010_B02_F1_PI_AE_S4_CS_SP_S0Y',
'protokoll_G-E--_045_B31_F1_PI_AE_S4_CS_SP_S0Y',
'protokoll_G-E--_024_B07_F1_PI_AE_Q4_CS_SP_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S', 
'protokoll_X----_auto_sine03',
'protokoll_X----_sauto_300',
'protokoll_X----_auto_sine05',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y_sine13',
'protokoll_G-E--_052_K18_F1_PI_AE_Q4_CS_SP_S0Y',
'protokoll_G-E--_092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_008_C18_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_008_B07_F1_PI_AE_Q4_CS_SP_S2S'
);

# only those from which strats could be grown, plus auto
my @strictorigEStrats =
(
'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05',
'protokoll_G-E--_008_B31_F1_PI_AE_S4_CS_SP_S2S',
'protokoll_G-E--_010_B02_F1_PI_AE_S4_CS_SP_S0Y',
'protokoll_G-E--_045_B31_F1_PI_AE_S4_CS_SP_S0Y',
'protokoll_G-E--_024_B07_F1_PI_AE_Q4_CS_SP_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S', 
'protokoll_X----_auto_sine03',
'protokoll_X----_sauto_300',
'protokoll_X----_auto_sine05',
);

my @EAutoStrat =
(
'protokoll_X----_sauto_300'
);


if((!defined($strset)) || ($strset eq 'default'))
{
    if($serial == 1) {@strats = @greedymizstrats;}
    else { @strats = @mizstratsold; }
}
elsif($strset eq 'greedy')  {@strats = @greedymizstrats;}
elsif($strset eq 'f6_40_128')  {@strats = @f6_40_128;}
elsif($strset eq 'm10u2_184')  {@strats = @m10u2_184;}
elsif($strset eq 'new_mzt_small')  {@strats = @new_mzt_small;}
else { die "Unknown strategy set: $strset" }

# possible SZS statuses
sub szs_INIT        ()  { 'Initial' } # system was not run on the problem yet
sub szs_UNKNOWN     ()  { 'Unknown' } # used when system dies
sub szs_THEOREM     ()  { 'Theorem' }
sub szs_COUNTERSAT  ()  { 'CounterSatisfiable' }
sub szs_RESOUT      ()  { 'ResourceOut' }
sub szs_GAVEUP      ()  { 'GaveUp' }   # system exited before the time limit for unknown reason

# add --sine=Auto to these when $sine=1
#
my @nsine = (
'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_my10simple',
'protokoll_my11simple',
'protokoll_my12simple',
'protokoll_my13simple',
'protokoll_my14simple',
'protokoll_my15simple',
'protokoll_my16simple',
'protokoll_my17simple',
'protokoll_my18simple',
'protokoll_my19simple',
'protokoll_my1KBO_SOS',
'protokoll_my1_SOS',
'protokoll_my20simple',
'protokoll_my21simple',
'protokoll_my22simple',
'protokoll_my23simple',
'protokoll_my24simple',
'protokoll_my25simple',
'protokoll_my2simple',
'protokoll_my3simple',
'protokoll_my4simple',
'protokoll_my5simple',
'protokoll_my6simple',
'protokoll_my7simple',
'protokoll_my8simple',
'protokoll_my9simple',
'protokoll_G-E--_008_B31_F1_PI_AE_S4_CS_SP_S2S',
'protokoll_G-E--_010_B02_F1_PI_AE_S4_CS_SP_S0Y',
'protokoll_G-E--_045_B31_F1_PI_AE_S4_CS_SP_S0Y',
'protokoll_G-E--_024_B07_F1_PI_AE_Q4_CS_SP_S0Y',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S',
'protokoll_G-E--_052_K18_F1_PI_AE_Q4_CS_SP_S0Y',
'protokoll_G-E--_092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_008_C18_F1_PI_AE_Q4_CS_SP_PS_S0Y',
'protokoll_G-E--_008_B07_F1_PI_AE_Q4_CS_SP_S2S'
);

# do not add --sine=Auto to these
my @wsine =
(
'protokoll_X----_sauto_300',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05',
'protokoll_X----_auto_sine03',
'protokoll_X----_auto_sine05',
'protokoll_X----_auto_sine13',
'protokoll_my11simple_sine13',
'protokoll_my17simple_sine13',
'protokoll_my8simple_sine13',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y_sine13'
);

# no auto sine for f6_40_128
@wsine = (@wsine, @f6_40_128);

my %wsinestr = ();
my %nsinestr = ();

@wsinestr{@wsine} = ();
@nsinestr{@nsine} = ();

# strategy defs
my %sdef =
(
'protokoll_G-E--_008_K18_F1_PI_AE_CS_SP_S0Y' => '  --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\' ',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S_sine05' => '  --sine=gf120_gu_RUU_F100_L00100 --oriented-simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(4*Refinedweight(SimulateSOS,1,1,2,1.5,2),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y' => '  --definitional-cnf=24 --split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --presat-simplify --prefer-initial-clauses -tKBO6 -warity -c1 -Ginvconjfreq -F1  --delete-bad-limit=1024000000 -WSelectMaxLComplexAvoidPosPred -H\'(4*RelevanceLevelWeight2(SimulateSOS,0,2,1,2,100,100,100,400,1.5,1.5,1),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\'  ',
'protokoll_X----_auto_sine03' => '  --delete-bad-limit=1024000000 -xAuto -tAuto --sine=gf120_gu_R02_F100_L20000 ',
'protokoll_X----_auto_sine05' => '  --delete-bad-limit=1024000000 -xAuto -tAuto --sine=gf120_gu_RUU_F100_L00100 ',
'protokoll_X----_auto_sine13' => '   --delete-bad-limit=1024000000 -xAuto -tAuto --sine=gf120_h_gu_R02_F100_L20000 ',
'protokoll_X----_sauto_300' => '   --delete-bad-limit=1024000000 --auto ',
'protokoll_my10simple' => '  --definitional-cnf=24 --split-clauses=7 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(PreferProcessed),1*FIFOWeight(ConstPrio))\'  ',
'protokoll_my11simple' => '  --definitional-cnf=24 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(PreferProcessed),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Refinedweight(SimulateSOS,1,1,2,1.5,2),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ',
'protokoll_my11simple_sine13' => '  --sine=gf120_h_gu_R02_F100_L20000 --definitional-cnf=24 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(PreferProcessed),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Refinedweight(SimulateSOS,1,1,2,1.5,2),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ',
'protokoll_my12simple' => '  --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my13simple' => '  --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tAuto -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),8*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my14simple' => '  --definitional-cnf=24 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(ConstPrio))\'  ',
'protokoll_my15simple' => '  --definitional-cnf=24 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectNewComplexAHP -H\'(1*Refinedweight(SimulateSOS,1,1,2,1.5,2),6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5))\'  ',
'protokoll_my16simple' => '  --definitional-cnf=24 --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ',
'protokoll_my17simple' => '  --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),3*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100,1.5, 1.5, 1),10*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ',
'protokoll_my17simple_sine13' => '  --sine=gf120_h_gu_R02_F100_L20000 --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),3*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100,1.5, 1.5, 1),10*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ',
'protokoll_my18simple' => '  --definitional-cnf=24  --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectNewComplexAHP -H\'(1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5))\'  ',
'protokoll_my19simple' => '  --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),10*Refinedweight(SimulateSOS,1,1,2,1.5,2),2*FIFOWeight(PreferProcessed),8*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\' ',
'protokoll_my1KBO_SOS' => '  --definitional-cnf=24  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(4*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),10*Refinedweight(SimulateSOS,1,1,2,1.5,2),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my1_SOS' => '  --definitional-cnf=24  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(4*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),10*Refinedweight(SimulateSOS,1,1,2,1.5,2),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my20simple' => '  --definitional-cnf=24  --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -Garity -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*Refinedweight(SimulateSOS,1,1,2,1.5,2),1*FIFOWeight(ConstPrio),10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5))\'  ',
'protokoll_my21simple' => '  --definitional-cnf=24 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(ConstPrio),2*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my22simple' => '  --definitional-cnf=24  --split-clauses=7 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tAuto -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*FIFOWeight(ConstPrio),6*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*FIFOWeight(PreferProcessed),1*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ',
'protokoll_my23simple' => '  --definitional-cnf=24  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*FIFOWeight(PreferProcessed),10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ',
'protokoll_my24simple' => '  --definitional-cnf=24  --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),8*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ',
'protokoll_my25simple' => '  --definitional-cnf=24  --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -Garity -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(2*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*FIFOWeight(PreferProcessed),1*FIFOWeight(ConstPrio))\'  ',
'protokoll_my2simple' => ' --definitional-cnf=24  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*Clauseweight(PreferProcessed,1,1,1),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my3simple' => ' --definitional-cnf=24 --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Clauseweight(PreferProcessed,1,1,1),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my4simple' => ' --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tAuto -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1))\'  ',
'protokoll_my5simple' => '  --definitional-cnf=24  --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -Garity -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(ConstPrio),8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my6simple' => '  --definitional-cnf=24  --split-clauses=7 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5))\'  ',
'protokoll_my7simple' => '  --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(PreferProcessed),1*FIFOWeight(ConstPrio),2*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5))\'  ',
'protokoll_my8simple' => '  --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(ConstPrio),4*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my8simple_sine13' => '  --sine=gf120_h_gu_R02_F100_L20000 --definitional-cnf=24 --split-aggressive --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tKBO -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(1*FIFOWeight(ConstPrio),4*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*FIFOWeight(PreferProcessed))\'  ',
'protokoll_my9simple' => '  --definitional-cnf=24 --split-aggressive --split-clauses=7 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tAuto -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(ConstPrio),2*Refinedweight(SimulateSOS,1,1,2,1.5,2),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*FIFOWeight(PreferProcessed),10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),3*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1))\' ',
'protokoll_G-E--_008_B31_F1_PI_AE_S4_CS_SP_S2S' => '  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectNewComplexAHP -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\' ',
'protokoll_G-E--_010_B02_F1_PI_AE_S4_CS_SP_S0Y' => '  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Garity -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(4*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),3*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_G-E--_045_B31_F1_PI_AE_S4_CS_SP_S0Y' => '  --split-aggressive --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreqconstmin -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(4*Refinedweight(SimulateSOS,1,1,2,1.5,2),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_G-E--_024_B07_F1_PI_AE_Q4_CS_SP_S0Y' => '  --split-reuse-defs --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(4*ConjectureGeneralSymbolWeight(SimulateSOS,100,100,100,50,50,50,50,1.5,1.5,1),3*ConjectureGeneralSymbolWeight(PreferNonGoals,100,100,100,50,50,1000,100,1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_G-E--_045_K18_F1_PI_AE_CS_OS_S0S' => '  --oriented-simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectComplexG -H\'(4*Refinedweight(SimulateSOS,1,1,2,1.5,2),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_G-E--_107_C37_F1_PI_AE_Q4_CS_SP_PS_S0Y_sine13' => '  --sine=gf120_h_gu_R02_F100_L20000 --split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --presat-simplify --prefer-initial-clauses -tKBO6 -warity -c1 -Ginvconjfreq -F1 -s --delete-bad-limit=1024000000 -WSelectMaxLComplexAvoidPosPred -H\'(4*RelevanceLevelWeight2(SimulateSOS,0,2,1,2,100,100,100,400,1.5,1.5,1),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ', 
'protokoll_G-E--_052_K18_F1_PI_AE_Q4_CS_SP_S0Y' => '  --split-reuse-defs --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -winvfreqrank -c1 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.05, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(SimulateSOS))\' ',
'protokoll_G-E--_092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y' => '  --definitional-cnf=24 --tstp-in --presat-simplify --split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 -s --delete-bad-limit=1024000000 -WSelectMaxLComplexAvoidPosPred -tKBO6 -H\'(4*RelevanceLevelWeight2(SimulateSOS,1,2,0,2,100,100,100,400,1.5,1.5,1),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_G-E--_008_C18_F1_PI_AE_Q4_CS_SP_PS_S0Y' => '  --definitional-cnf=24 --split-reuse-defs --split-clauses=4 --tstp-in --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er  --presat-simplify --prefer-initial-clauses -tKBO6 -winvfreqrank -c1 -Ginvfreq -F1 -s --delete-bad-limit=1024000000 -WSelectMaxLComplexAvoidPosPred -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\' ',
'protokoll_G-E--_008_B07_F1_PI_AE_Q4_CS_SP_S2S' => '  --split-reuse-defs --split-clauses=4 --simul-paramod --forward-context-sr --destructive-er-aggressive --destructive-er --prefer-initial-clauses -tLPO4 -Ginvfreq -F1 --delete-bad-limit=150000000 -WSelectNewComplexAHP -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\' ',


# the tstf6_40_128 prots
'protokoll_atpstr_my_05c900b7acd7e0314c15fce53bb9e79cf904cd89' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.5,, 03, 40,1.0)\' --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectNewComplexAHP --simul-paramod --split-aggressive --split-clauses=4 -tLPO4 -H\'(8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),4*Clauseweight(ConstPrio,3,1,1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),4*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'   ' ,
'protokoll_atpstr_my_0b08a1d1a32ffc279e90769114bdfda18e672e1c' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.1,, 03, 40,1.0)\' -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-aggressive --split-reuse-defs -tAuto -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),4*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),12*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),7*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed))\'  ' ,
'protokoll_atpstr_my_37be21ea059a2fcb865621e373a97f33a9d07b12' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 2.0,, 02, 100,1.0)\' --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --simul-paramod --split-clauses=7 --split-reuse-defs -tKBO -H\'(4*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed))\'  ' ,
'protokoll_atpstr_my_3e6c84c618b85cc326775b240e7b2b07e3a2dde9' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Ginvfreqconstmin -WSelectNewComplexAHP --simul-paramod --split-aggressive --split-clauses=4 -tAuto -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),3*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(ConstPrio,3,1,1),1*FIFOWeight(ConstPrio))\'  ' ,
'protokoll_atpstr_my_4e6e6157a8ac18b9bae11142d40377c9660db06b' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 6.0,, 02, 100,1.0)\' --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred --simul-paramod -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),2*Clauseweight(ConstPrio,3,1,1),2*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),10*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),2*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ' ,
'protokoll_atpstr_my_5fce846ef89413a220d0951fb615d42ded72b119' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Garity -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),3*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(ConstPrio,3,1,1),1*FIFOWeight(PreferProcessed),8*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),1*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ' ,
'protokoll_atpstr_my_7b674c1081cd73ca6ce34d02596e6f6fd903ac6c' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 5.0,, 02, 80,1.0)\' -Garity -WSelectNewComplexAHP --simul-paramod -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),7*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ConstPrio,3,1,1),2*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),4*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ' ,
'protokoll_atpstr_my_92168ebc2ef464a6f2d6a311a4fa90219fd0aa91' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 6.0,, 02, 20000,1.0)\' --forward-context-sr -Garity -WSelectNewComplexAHP --simul-paramod --split-aggressive --split-reuse-defs -tAuto -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),12*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),8*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),4*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ' ,
'protokoll_atpstr_my_a175515211bb22b22434eae9bbbfab623676a2ba' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectComplexG --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*FIFOWeight(PreferProcessed),2*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\'  ' ,
'protokoll_atpstr_my_a473e2c35f909af4ba00d9f1a7a8a454a851ed9c' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.4,, , 20,1.0)\' -Ginvfreqconstmin -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-aggressive --split-clauses=4 -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*FIFOWeight(PreferProcessed))\'  ' ,
'protokoll_atpstr_my_a74b37f2d8b7e35be554fc999f671188cf40f113' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 6.0,, 01, 80,1.0)\' -Ginvfreqconstmin -WSelectComplexG --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),3*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ' ,
'protokoll_atpstr_my_c284f1f10aedfccc65cdb7d9b1210ef814cb8f1a' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 5.0,, 02, 60,1.0)\' --forward-context-sr -Garity -WSelectComplexG --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(2*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),1*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\'  ' ,
'protokoll_atpstr_my_e4d2b8713a71da3a6bc64790217310975ccdde24' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.1,, 01, 20000,1.0)\' -winvfreqrank -c1 -Ginvfreq -WSelectComplexG --simul-paramod --split-clauses=7 --split-reuse-defs -tLPO4 -H\'(1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),7*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*FIFOWeight(PreferProcessed),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\' ' ,
'protokoll_atpstr_my_e8ac4ce30401bd9e99200725cfa03816a32e3aa4' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 5.0,, 01, 20000,1.0)\' --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --simul-paramod --split-aggressive -tLPO4 -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),12*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\' ', 

# m10u2_184
'protokoll_atpstr_my_1518b94b1627f7a5f7ce55e37817c09306fe714c' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.2,, 02, 40,1.0)\' -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred --simul-paramod -tAuto -H\'(1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),8*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Clauseweight(ByCreationDate,2,1,0.8),2*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ', 
'protokoll_atpstr_my_2eeaa79326ed674ea9ebfc3531c32ba1feec013b' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Garity -WSelectComplexG --simul-paramod -tAuto -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed))\'  ', 
'protokoll_atpstr_my_304d2e324da665c057353a60ddd91c0712280c88' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.1,, 02, 60,1.0)\' --forward-context-sr -Garity -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 -tLPO4 -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),4*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ', 
'protokoll_atpstr_my_69856783cec8fab1acccfe08bb382ad42c8475df' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 6.0,, , 100,1.0)\' -Garity -WSelectComplexG --simul-paramod --split-clauses=7 -tKBO -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),7*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\'  ', 
'protokoll_atpstr_my_88760aa43d575e84b7030b8a6188f74ba5f80dc7' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 2.0,, 02, 100,1.0)\' --forward-context-sr -Garity -WSelectComplexG --simul-paramod --split-clauses=7 -tKBO -H\'(8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),3*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ', 
'protokoll_atpstr_my_8fb389ef013a89e03c1aa87be52b2f151b1819cc' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.1,, 04, 80,1.0)\' -Garity -WSelectNewComplexAHP --simul-paramod --split-aggressive --split-clauses=4 --split-reuse-defs -tAuto -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),2*FIFOWeight(PreferProcessed),1*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\'  ', 
'protokoll_atpstr_my_a3154f3180cc47331f1b05c36960c32e4805a7c5' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 6.0,, 01, 20000,1.0)\' --forward-context-sr -Garity -WSelectComplexG --simul-paramod --split-clauses=4 -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),3*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\'  ', 
'protokoll_atpstr_my_a4a4da5778ba9bebf9bc5e616786c7ad501b1af5' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.1,, 03, 20,1.0)\' --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-aggressive --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\'  ', 
'protokoll_atpstr_my_cfee9ff42189552c6557cda7d36f20820c827219' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.5,, 04, 100,1.0)\' --forward-context-sr -Garity -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 -tLPO4 -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),6*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),4*Clauseweight(ConstPrio,3,1,1),1*Clauseweight(PreferProcessed,1,1,1),2*FIFOWeight(PreferProcessed),2*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),2*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ', 
'protokoll_atpstr_my_e3b5200232138aedc93b8882335da60ccd317d87' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.2,, 01, 80,1.0)\' --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --simul-paramod --split-clauses=7 --split-reuse-defs -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*Clauseweight(PreferProcessed,1,1,1))\'  ', 
'protokoll_atpstr_my_e6869afe09f22abfbe1163ee95524cfdbfe77603' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 2.0,, 04, 40,1.0)\' --forward-context-sr -Garity -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 -tLPO4 -H\'(2*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(ConstPrio,3,1,1),2*FIFOWeight(PreferProcessed),10*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),1*Refinedweight(SimulateSOS,1,1,2,1.5,2))\'  ', 
'protokoll_atpstr_my_e6ff24ca1a5013a612ccffc94da0b282477718de' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.5,, 02, 100,1.0)\' --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --simul-paramod -tKBO -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\'  ', 
'protokoll_atpstr_my_eba37f91665fc364eeb63558058658ee9a149d9a' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 1.1,, 02, 60,1.0)\' --forward-context-sr -Garity -WSelectNewComplexAHP --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),6*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),10*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),2*Clauseweight(ConstPrio,3,1,1),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(PreferProcessed),3*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),8*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\'  ', 
'protokoll_atpstr_my_fc3fb6907f504dffe1a6181663296b37fe358480' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 -Ginvfreqconstmin -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),7*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5))\' ',

# new_mzt_small
'protokoll_atpstr_my_2af8b399ea0b8c22c6fc1b13069ad80214f9fa8b' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 5.0,, 6, 80,1.0)\' -Ginvfreqconstmin -WSelectComplexG --simul-paramod --split-reuse-defs -tKBO -H\'(8*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),4*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*FIFOWeight(PreferProcessed),10*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_2d0c1ae7703dba890de879a4f4409a64f9856908' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.5,, 2, 60,1.0)\' --forward-context-sr -Garity -WSelectMaxLComplexAvoidPosPred --oriented-simul-paramod --split-aggressive --split-reuse-defs -tLPO4 -H\'(1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),8*Clauseweight(ConstPrio,3,1,1),2*Clauseweight(PreferProcessed,1,1,1),2*FIFOWeight(PreferProcessed),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),10*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),4*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_40306ce1a432dd48c918ac611d77fc5069b2fbc7' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Garity -WSelectComplexG --simul-paramod -tKBO -H\'(2*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),3*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),10*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*FIFOWeight(ConstPrio),4*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),2*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_43029cedefea4858aae9c4ebd6be482056ce22f4' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --simul-paramod -tKBO -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),1*FIFOWeight(PreferProcessed),1*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_9cb7c8ca63fd56afb053ade56353a3b00eee7e6a' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 1.2,, 4, 100,1.0)\' --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 --split-reuse-defs -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed))\' ',
'protokoll_atpstr_my_9f72062a403172caf26fbe878a32becf1403c276' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 2.0,, 3, 20,1.0)\' -Garity -WSelectComplexG --simul-paramod --split-clauses=7 --split-reuse-defs -tKBO -H\'(4*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),6*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),3*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),10*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*FIFOWeight(ConstPrio),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),10*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_9fde028f05afb32f97bced19843d73b32d923682' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --oriented-simul-paramod --split-aggressive -tKBO -H\'(1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),3*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Refinedweight(PreferGroundGoals,2,1,2,1.0,1),2*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_c0d9db6a7b7a90437bd07739f25aa91c0ffc1607' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -Ginvfreqconstmin -WSelectComplexG --simul-paramod --split-clauses=4 -tKBO -H\'(10*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*FIFOWeight(PreferProcessed),1*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\' ',
'protokoll_atpstr_my_c13d4886baa4fa2cef7b4f50892895255b04b078' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, , 2.0,, 1, 80,1.0)\' --forward-context-sr -Garity -WSelectMaxLComplexAvoidPosPred --simul-paramod -tKBO -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureRelativeSymbolWeight(SimulateSOS,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),4*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),1*Refinedweight(PreferNonGoals,1,1,2,1.5,1.5),1*Refinedweight(SimulateSOS,1,1,2,1.5,2))\' ',
'protokoll_atpstr_my_d60b37aca40b6e560cee4bde2efc36c05a24873f' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 -Garity -WSelectComplexG --simul-paramod -tLPO4 -H\'(1*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),2*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_atpstr_my_edc94794a7d25c504761344c2a8b4afaac43a2d0' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000  --sine=\'GSinE(CountFormulas, hypos, 5.0,, , 100,1.0)\' --forward-context-sr -Ginvfreqconstmin -WSelectMaxLComplexAvoidPosPred --simul-paramod --split-clauses=4 --split-reuse-defs -tKBO -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*ConjectureRelativeSymbolWeight(PreferNonGoals,0.5, 100, 100, 100, 100, 1.5, 1.5, 1),2*ConjectureSymbolWeight(ConstPrio,10,10,5,5,5,1.5,1.5,1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*FIFOWeight(ConstPrio),1*FIFOWeight(PreferProcessed),1*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\' ',
'protokoll_atpstr_my_f67d73f57ffeda22ddd93400237cd848911520e5' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 -Garity -WSelectComplexG --simul-paramod --split-aggressive --split-clauses=4 -tLPO4 -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(PreferProcessed))\' ',
'protokoll_atpstr_my_f9ecf400d7420b0148b2ef7cf4b1498512cf83fd' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred --simul-paramod -tLPO4 -H\'(6*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*Clauseweight(ByCreationDate,2,1,0.8),1*Clauseweight(PreferProcessed,1,1,1),1*FIFOWeight(ConstPrio),2*FIFOWeight(PreferProcessed),2*Refinedweight(PreferGroundGoals,2,1,2,1.0,1))\' ',
'protokoll_atpstr_my_fe548d15a6fc730fd350de634ad9d912ae198efd' => '  --definitional-cnf=24 --destructive-er-aggressive --destructive-er --prefer-initial-clauses -F1 --delete-bad-limit=150000000 --simul-paramod --forward-context-sr -winvfreqrank -c1 -Ginvfreq -WSelectMaxLComplexAvoidPosPred -H\'(10*ConjectureRelativeSymbolWeight(ConstPrio,0.1, 100, 100, 100, 100, 1.5, 1.5, 1.5),1*FIFOWeight(ConstPrio))\' '
);


local $SIG{'TERM'} = \&Cleanup;
local $SIG{'INT'} = \&Cleanup;
local $SIG{'XCPU'} = \&Cleanup;

sub Cleanup
{
    if($cleanup == 1)
    {
	foreach my $strat (@strats)
	{
	    unlink("$file.err.$strat");
	    unlink("$file.out.$strat");
	}
	unlink("$file.out1");
    }
}


sub RunStrategyNoProof
{
    my ($strat) = @_;

    my $sinestr = '';
    if(($sine == 1) && exists($nsinestr{$strat})) { $sinestr = ' --sine=Auto '; }
    `ulimit -t $tl1; ./eprover $sdef{$strat} $sinestr --tstp-format -R -s --cpu-limit=$tl $file 2>$file.err.$strat | grep "\\(User\\|SZS status\\)" >$file.out.$strat`;
}

sub RunStrategyWithProof
{
    my ($strat) = @_;

    my $sinestr = '';
    if(($sine == 1) && exists($nsinestr{$strat})) { $sinestr = ' --sine=Auto '; }
    my $status_line = `ulimit -t 60001; ./eprover $sdef{$strat} $sinestr --cpu-limit=60000 --memory-limit=Auto --tstp-in -l4 -o- --pcl-terms-compressed --pcl-compact $file | ./epclextract --tstp-out -f -C --competition-framing |tee $file.out1 | grep "SZS status" `;

    # if epclextract breaks, add at least the correct status to the proof file
    unless ($status_line=~m/.*SZS status[ :]*(.*)/)
    {
	`echo "# SZS status Theorem" > $file.out1`;
    }

    if(($doproof==2) && ($status_line=~m/.*SZS status[ :]*Theorem/))
    {
	open(F,"$file.out1"); local $/; my $contents= <F>; close(F); print $contents;
    }
}

sub ProcessStrategyOutput
{
    my ($strat) = @_;

    if(open(OUT,"$file.out.$strat"))
    {
	while($_=<OUT>)
	{

	    if (m/.*SZS status[ :]*(.*)/)
	    {
		my $status = $1;

		if ($status eq szs_COUNTERSAT)
		{
		    print '# SZS status ', szs_COUNTERSAT, "\n";
		    Cleanup();
		    exit(0);
		}
		elsif ($status eq szs_THEOREM)
		{
		    print '# SZS status ', szs_THEOREM, "\n";
		    
		    if($doproof > 0)
		    {
			RunStrategyWithProof($strat);
		    }
		    else
		    {
			`echo "# SZS status Theorem" > $file.out1`;
		    }

		    #	    `eproof  $sdef{$strat} $sinestr --cpu-limit=60 --memory-limit=Auto --tstp-format $file > $file.out1`;
		    Cleanup();
		    exit(0);
		}
	    }
	}
	close(OUT);
    }
}

sub min { my ($x,$y) = @_; ($x <= $y)? $x : $y }
sub max { my ($x,$y) = @_; ($x <= $y)? $y : $x }

my $status = szs_UNKNOWN ;

if($serial == 1)
{
    my $oldtl = $tl;
    $tl = max( 1, int( $oldtl/(2+(scalar @greedymizstrats)) ));

    foreach my $strat (@strats)
    {
	RunStrategyNoProof($strat);
	ProcessStrategyOutput($strat);
    }

    print '# SZS status ', $status, "\n"; # only printed if everything failed
    Cleanup();
    exit(0);
}


my @childs = ();
foreach my $strat (@strats)
{

    my $pid = fork();
    if ($pid) 
    {
	# parent
	push(@childs, $pid);
    } 
    elsif ($pid == 0) 
    {
	# child
	RunStrategyNoProof($strat);
	exit(0);
    } 
    else 
    {
	die "couldn’t fork: $!\n";
    }
}

foreach (@childs) { waitpid($_, 0);}


foreach my $strat (@strats)
{
    ProcessStrategyOutput($strat);
}

print '# SZS status ', $status, "\n";
Cleanup();
exit(0);

