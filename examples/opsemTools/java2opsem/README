------------------------------------------------------
java2opSem: a package to convert a Java file with a
JML specification into a relational specification as
defined in newOpsemTheory
------------------------------------------------------
 * @version September 2008
 * @author Hélène Collavizza
 * from an original student work by Eric Le Duff and Sébastien Derrien
 * Polytech'Nice Sophia Antipolis

   This tool takes as input a small subset of Java and 
   JML languages (see JML Home page at 
   http://www.eecs.ucf.edu/~leavens/JML/ for general information
   on JML).
   However, it uses standard tools for parsing Java 
   and jml, and can be extended by implementing
   visitors for new classes of Java of JML API.
     
   It uses JDT (Java Development Tooling, eclipse environment)
   for parsing Java.
   See http://help.eclipse.org/help31/index.jsp?topic=/org.eclipse.jdt.doc.isv/reference/api/index.html
   for description of the API and AST nodes.

   It uses jml-release.jar for parsing JML specifications.
   See http://sourceforge.net/project/showfiles.php?group_id=65346&package_id=62764&release_id=594123
   for downloading JML tools.
   jml-release.jar is part of JML.5.6_rc1.tar.gz, last version 
   May 2008.
   See http://www.cs.ucf.edu/~leavens/JML/ for information on JML

   Translation follows as mush as possible explanations given in 
   jml reference manual
   http://www.eecs.ucf.edu/~leavens/JML//OldReleases/jmlrefman.pdf.
   There is also a local copy of the  manual (version 
   august 2008) in directory java2opSem.



Directory content:
------------------

- lib: JML and Java librairies (.jar files)

- src: Java source files of the package

- bin: Java classes of the package

- testFiles/javaFiles: examples of Java files with JML 
  specifications

- testFiles/opsemFiles: theories that contains RSPEC specifications
  as defined in opsemTheory and that have been built from Java files 
  in testFiles/javaFiles

- java2opsem.ml: ml functions to build and load theories from Java files.


See comments in java2opsem.ml for more details about current 
restrictions and translation process.


