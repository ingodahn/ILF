# ILF
Updated repository for the ILF system, reduced to natural language presentation of Prover 9 proofs

# What is ILF?
ILF (Integrated Logic Functions) was a system for integrating various automated theorem provers, running distributed in a local network. 
ILF had an interactive theorem prover, called ProofPad, for block structured proofs with a graphical user interface. 
ILF was capable to automatically restructure proofs from various provers into natural language and to restructure them.

The ILF system was developed between 1988 and 1998 at the Humboldt University in Berlin/Germany. 
It's development was supported in part by the Deutsche Forschungsgemeinschaft within the DFG Schwerpunkt "Deduktion". 
Key developers of the system were Ingo Dahn (Project Leader), Juergen Gehne, Thomas Honigmann, Andreas Wolf, Thomas Baar, 
Lutz Walther, Thomas Baar, Oliver Becker and many others.

In response to a user request in 2016, Ingo Dahn revived the capability of the ILF system to generate English presentations of proofs
generated by the Prover 9 automated theorem prover, a successor of the Bill McCune's Otter prover which was integrated in the original ILF system.
This repository provides the actualized ILF sources to solve this problem.

# ILF's Proof Presentation
As a first step, ILF parses the proof as printed by the automated prover and translates it into a format that can be read by 
Prolog logic programming systems. Then this is connected with information about the axiom system used for the proof. In the next step, 
it is transformed into a block structured proof - sequence of proof steps, each justified from previous proof steps either
by a rule of inference or by a subproof.

Then this block structured proof is simplified and restructured, using a set of ILF's proof transformation tools. A natural language 
LaTeX presentation of this proof is generated using a variable set of templates.

# Installation
ILF requires an installation of the Eclipe Constraint Logic Programming System and of Perl as well as the files in this repository. 
The file `ilf_state.pl` need to be adapted for the local installation:
Adapt the paths `prologhome` to Eclipse prolog, `ilfhome` to the root of this repository, `userilfhome` can be set 
to the same value and `default_proof_file` for the LaTeX file to be generated.

# Using the System to Generate a Natural Language Presentation of a Prover 9 Proof
As a first step, the Prover 9 proof needs to be converted into a Prolog format as `preparation/JoaoProof4.opf.tmp.1`. 
The tool to do this conversion will hopefully be contributed to this repository by its author.

The following step requires an additional file, like `preparation/JoaoProof4.axn` that describes the axiom 
system that was used in the proof. The Eclipse Prolog program `preparation/convert.pl` connects both files and produces a file like
`preparation/JoaoProof4.out`. Copy this file to the root folder of this repository.

In order to transform this file into a block structured proof and simplify it, compile the Eclipse Prolog file `aa_ilfmnu.pl` and call 
`start` in the module `ilfmnu` (`call(start)@ilfmnu`). A listing of the prolog structure representing the proof to be Texed 
can be obtained by the Prolog command `call(lising(proof/3))@situation`.

The final step produces the LaTeX file with the Prolog command `prooftex`. It is normal that this command fails.

# Disclaimer
The files in this repository have been adapted from the original ILF system as little as possible and have not been 
systematically cleaned up. In fact, not all files will be needed.


