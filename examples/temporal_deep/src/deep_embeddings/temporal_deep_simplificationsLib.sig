signature temporal_deep_simplificationsLib =
sig

  val prop_logic_CS : congLib.congsetfrag;
  val prop_logic_nnf_CS : congLib.congsetfrag;
  val prop_logic_dnf_CS : congLib.congsetfrag;

  val prop_logic_cs : congLib.congset;
  val prop_logic_nnf_cs : congLib.congset;
  val prop_logic_dnf_cs : congLib.congset;


  val xprop_logic_CS : congLib.congsetfrag;
  val xprop_logic_nnf_CS : congLib.congsetfrag;
  val xprop_logic_dnf_CS : congLib.congsetfrag;

  val xprop_logic_cs : congLib.congset;
  val xprop_logic_nnf_cs : congLib.congset;
  val xprop_logic_dnf_cs : congLib.congset;


  val ltl_CS : congLib.congsetfrag;
  val ltl_nnf_CS : congLib.congsetfrag;

  val ltl_cs : congLib.congset;
  val ltl_nnf_cs : congLib.congset;
end

