================================================================================

                                     README

               		HOL PARSER 2023.6, HAOYANG ZHANG
               --------------------------------------------------


Welcome to the HOL PARSER readme! This document includes the guide of how to use HOL PARSER. HOL PARSER is a interactive visual file phasing system for theory/theorem dependency. 
for more information please view the report.
================================================================================
rquirements:

linux/Mac/WIN-(WSL2 or VirtualMachine for linux), openjdk 17.0.7

please make sure you have dot, to install dot do:
sudo apt install graphviz (in linux).
==============================
compile:

go to HOL/hol_parser/theory_parser/src then do:

javac -cp ../lib/zgrviewer.jar ./haoyang/*.java ./animator/*.java ./net/claribole/zgrviewer/*.java  -d ../bin -encoding utf-8
==============================
execute:

go to your HOL folder (e.g. /home/user/HOL) then do

HOL PARSER:
java -cp /your path/hol_parser/theory_parser/lib/zgrviewer.jar:/your path/hol_parser/theory_parser/bin haoyang.HolParser

HOL PARSER COMMANDS: (no interface, for timestamp check, tag check and unused theorems in a theory)
java -cp /your path/hol_parser/theory_parser/lib/zgrviewer.jar:/your path/hol_parser/theory_parser/bin haoyang.HolParser_commands

==============================
Known limitations:

Performance: It may take from 16sec(i5-13600K 3.50 GHz) to 60sec(i5-8300h 2.30GHz) to generate a huge graph for the main HOL folder.

Some special characters in the theorems'name may be conflict with DOT's naming rules in the theorem graph generation, for more details please visit: https://graphviz.org/. (hol parser supports current HOL's theorems' names, can use '\','@',''' in names)

It doesn't automatically delete the dot.txt and DAG.svg files when quit the program. Everytime using the HOL PARSER it will generate new files to replace the old versions.

Potential Renaming Issue: Some theories are created by different users and share the same name. The Hol Parser will apply functions on the first one.

Some customized operator symbols in the .sml/.sig may not show properly.

Because of the different standards of .sml, the theorems' sml viewer may not capture the content perfectly.

constant query[WIP]
==============================
Instruction of HOL PARSER


[Init] Kindly proceed to the primary directory of HOL (such as your path/HOL) initially and proceed with the execution (go to the folder in the terminal, not move the HOLPARSER). This action will provide the path of the HOL folder for subsequent file searches. Subsequently, you will encounter the path settings and the 'task start' indicator, followed by an animated waiting sequence for SVG generation. Once the wait is over, you will observe the outcome of the incompatible timestamp check. Then, you can navigate to the primary interface of HOL PARSER.

[Basic Functionality] The graph can be zoomed in or out by scrolling the mouse wheel. To move the camera, simply hold down the left mouse button and drag it in the desired direction. The left hidden toolkit is inherited from the original ZGRViewer. To locate specific elements, you can enter a partial name and use the find function, accessible by pressing CTRL-F or navigating to the Menu-View-Find option. More shortcut function details are in the HOL PARSER.

[timestamp check] Init or everytime open a new theory graph, it will first display the result of timestamp check. It will report the child theroy when it has a incompatible partent timestamp. It has the format: theory-child:child path. (when has renaming issue, the first and last elemet will have the same name)

[Open] You have the option to create a theory graph encompassing all theories within a folder or multiple folders located in different accessible locations. This can be done by accessing the Menu-File-Open-Open one Dir and generate an SVG/Open multi Dir feature. The generated graph will include the parents that exist outside of the folders.
For the multiple folders. You can select folders in the same level by holding left-ctrl and press in the JFileChooser, select folders in the different levels by pressing 'Yes' to create a new JFileChooser, pressing 'No' to end the folders selection.

[check tag] You can check whether some theorems in the current theory graph have abnormal tags (not empty and not DISK_THM) by accessing the Menu-View-check tag.

[Unused theorems] You can check whether some theorems in the a theory that are unused in the current theory graph by accessing the Menu-View-Unused theorems.

[Right Click Popmenu] You can right click a theory node in the theory graph, then you will see three options: 'open .sig', 'open .sml', 'theorems'. The first two options will take you to the .sig/.sml contents of related theory. The last one will generate the theorem graph.

[theorem graph] It covers all the theorems in a selected theory and their dependency. For the dependency outside the theory, please right click a theorem node and select 'external' in the popmenu. You can also view the related content of a theorem in the .sig/.sml by select options in the right-click popmenu. 

===================================================================================
Instruction of HOL PARSER COMMANDS

You also need to go to the HOL main folder then execute. It has three functions：timestamp check, tag check and unused theorems, these are same as in HOL PARSER.
===================================================================================
