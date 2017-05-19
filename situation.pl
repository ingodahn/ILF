% situation dient als Schnittstelle zum Nutzer
% Es sollte die Liste mit den verwendbaren Praedikaten enthalten
% und mehr der Dokumentation dienen
% author: T.Baar

/*
added imports from block and proofout
C. Wernhard Thu Nov 21 12:59:53 1996

*/



:- module(situation).
/*
?- import ex_start/1,
	  ex_start/2,
          ex_answer/0,
          ex_ping/0,
	  (':')/2,
	  kb_sync/1  from excomm.
*/

?- import
        latex_setheo_proof/1,
        latex_setheo_proof/2,

        build_spass_proof/1,

        transform_proof/1,

	me2bl/0,
	o2bl/0,
	dsc2bl/0,
	remove_query/0,
	me_answers/0,
	show_block_dependencies/1,

				% specified in ILF Server Manual -
				% Transforming Block Structured Proofs
	remove_by_rule/1,
	convert_indirect/0,
	conv_direct/0,
	remove_duplicate/0,
	remove_trivial_subproofs/0,
	remove_unused/0,
	move_lines/0,
	move_into_subproof/0,
	reduce_depth/1,
	rew_neg_clauses/0,
	make_chains/0,
	make_chains/1,
	make_chains/2,
	allcloseForms/0,
	gentzifyForms/0,

				% otter specific, specified in ILF Server
				% Manual
	rm_instantiation/0,
	remove_merge/0,
	rm_ModPon/0,
	local_constants/0,
	make_paramodulation_chains/0,
	rename_vars/0,
	unique_references/0
    from block.

:- import prooftex/0 from proofout.

:- export proof/3.
	
?- begin_module(situation).

%situation_top :- signature(P,A,O),op(P,A,O),fail.  wozu gut noch schleierhaft T.Baar
%situation_top.



