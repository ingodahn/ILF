/* File ilfmnu for restricted ILF version 2016 */
/* This has been converted into a module because Eclipse has dropped support for global predicates. */
:- module(ilfmnu).
:- compile("ilfsys.pl").
:- import ilfsys.
	
?- ini_ness_ilfmodules.
s1 :- ini_poss_ilfmodules.


/* beim start werden alle si-Ziele versucht */


start :- ilf_state(userilfhome,Uih),cd(Uih),fail.
start :- once((s1)), fail.
% start :- compile("OtterProof1.out"),fail.
start :- call((get_right_file("JoaoProof4.out",F),reconsult(F)))@ilf_serv,fail.
% start :- set_flag(toplevel_module,situation),call(transform_proof((o2bl)))@situation.

start :- set_flag(toplevel_module,situation),call(transform_proof((
/* Transforming Otter/Prover9-Proof to block structured proof */
	o2bl,
	/* Removing trivial inferences */
	remove_by_rule([intro]),
	remove_by_rule([clausify(_)]),
	remove_by_rule([copy(_),flip(_)]),
	/* Removing proof steps that are no longer needed */
	remove_unused,
	/* Trying to convert the indirect proof into a direct proof */
	indirect_direct,
	/* Transforming formulas used at least N times into lemmata */
	make_top_subproofs(5),
	/* structuring the proof by generating subproofs */
	move_into_subproof,
	/* Removing very short subproofs */
	remove_trivial_subproofs,
	/* Moving proof lines close to the place where they are needed */
	move_lines
	)))@situation.

/*
start :- set_flag(toplevel_module,situation),call(transform_proof((o2bl,remove_by_rule([intro]),remove_by_rule([copy(_),flip(_)]),remove_unused,
	     convert_indirect,
	     remove_duplicate,
	     remove_trivial_subproofs,
	     move_into_subproof,
	     move_lines
		 )))@situation.
*/
% start :- set_flag(toplevel_module,block),get_right_file("proof3.pl",F),call(compile(F))@block.

%:- start,call(prooftex)@situation.