/* File @(#) block.pl 1.68 (12/12/98) based on block.pro 1.50 (3/19/96) 
   for restricted ILF version 2016
   Behandlung und Konvertierung des Praedikates proof/3 fuer Blockbeweise
   Modul ist Bestandteil des Vordergrundes
   Autoren: Dahn, Wolf
   (C) 1995
 
   me2bl based on seth2bl.pl 1.1, checked in 8/26/96
   Autor: A.Wolf (von T.Baar fuer ILF angepasst)

   Eclipse Port: C.Wernhard
*/


/* Contents:

   ME2BL  
   Transformation von Setheo-Block-Beweisen
   Aufbereitung von Blockbeweisen

   % not yet tested:
   O2BL
   Aufbereitung von Otter-Block-Beweisen
   Transformation von Modelleliminations-Beweisen, 
       die von pad im Hintergrund erzeugt wurden
   Aufbereitung von Discountbeweisen

*/

/*
Remarks

*** search for "cw" and "debug"
*** watch singleton variables at compilation
*** /u/ilf/dedsys/setheo/seth2bl.pl is now obsolete

C.Wernhard Thu Nov 21 12:40:12 1996

*/

/*

/* 
Some Documentation
==================
	
latex_setheo_proof(+Job,+Filename)

   Get proof with jobnumber <Job>, apply default proof transformations
   for setheo, convert to latex and write the latex file as <Filename>.tex
   into the current working directory. <Filename> is a String.

latex_setheo_proof(+Job)

   Like latex_setheo_proof/2, but start xdvi instead of writing a
   latex file.


transform_proof(+Transformation)

    The module block contains proof transformations implemented by
    modifying proof/3. Since the proof/3 representing the current proof
    can be in any module and Eclipse Prolog forbids assertion/retraction
    of imported predicates, calls to the transformation predicates have to
    be wrapped by transform_proof, which copies the proof/3 visible from
    the toplevel module into block and reinstalls it after calling
    <Transformation>.

*/

:- module(block).

:- export
	default_transformation/2,
	latex_setheo_proof/1,
	latex_setheo_proof/2,
	build_spass_proof/1,
	transform_proof/1.


:- export		          % used by ilf_serv.pl
	last_in_proof/2,
	me2bl/0,
	next_line/2,
	o2bl/0,
	dsc2bl/0,
	remove_query/0,
	me_answers/0,
	show_block_dependencies/1.

:- export			  % specified in ILF Server Manual -
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
	make_top_subproofs/0,
	allcloseForms/0,
	gentzifyForms/0,
	elim_true_false/0,
	raise_contradictory_cases/0,
	raise_neg_cases/0,
	remove_duplicate_cases/0,
	remove_last_directs/0.

/*
:- export			  % otter specific, specified in ILF Server
				  % Manual
	rm_instantiation/0,
	remove_merge/0,
	rm_ModPon/0,
	local_constants/0,
	make_paramodulation_chains/0,
	rename_vars/0,
	unique_references/0.

*/

:- export
	collect_proof_pars/0,
	collect_proof_pars/2,
	proof_pars/5.

:- tool(collect_proof_pars/0,collect_proof_pars/1),
	tool(collect_proof_pars/2,collect_proof_pars/3).
/*
	:- export (collect_proof_pars/0, collect_proof_pars/1).
collect_proof_pars :- current_module(M),collect_proof_pars(M).
:- export (collect_proof_pars/2, collect_proof_pars/3).
collect_proof_pars(X,Y) :- current_module(M),collect_proof_pars(X,Y,M).
*/

:- begin_module(block).


:- set_flag(syntax_option, nested_comments). % debug

:- lib(numbervars).
:- lib(cio).			  % tell/1 and told are used here
:- lib(apply_macros).             % used in  "Transformation von Spass-Blockbeweisen"


:- import			  % these are global in ilf_serv
	(translit/2),
	(ilf_serv_error/1),
	(ilf_serv_log/1),
	(check_me_proof/0)
    from ilf_serv.

:- import 
	log_op/2,
	(ax_name)/4,		  % global
	free_vars/2		  % global
    from thman.

:- import ilfsys.
/*	ilf_state/2,		  % global
	ilf_state/3,		  % global
	spy_ilf
    from ilfsys.
	*/
    
:- import
	strict_remove_l/3,	  % global
	strict_remove/3,	  % global
	strict_union/3,		  % global
	substitute/5,		  % global
	term2string/2,		  % global
	gensym/2,		  % global
	subterm/2,
	list_body/2,
	body_list/2,
	list_head/2,
	head_list/2,
	list_seq/3,
	remove_alls/2,
	serv_body_list/2,
	sort_by_functor/4,
	serv_head_list/2,
	serv_list_fmla/3,
	serv_negate_l/2
    from tools.

:- import
	(get_uih_file)/2	  % global
    from ilfsys.

:- import
	put_proof/1,		  % global
	get_proof/1,		  % global
	undo_enable/0		  % global
    from proof.

:- import
	prooftex/0,
	prooftex1/1
    from proofout.

:- import                         % used in "Transformation von Spass-Blockbeweisen"
        spass_filenames/6,
        spass_dfg_problem/2,
	spass_flotter_problem/2,
        spass_origin/2,
        spass_output/2,
	spass_axiom_names/2,
        ilf_select_referred/2,
        ilf_is_contradiction/1,
	ilf_aint_contradiction/1,
	ilf_is_splitpoint/2,
	ilf_aint_splitpoint/2,
        ilf_formula1/2,
	ilf_select_axioms/2,
	create_vars/3,
	substitute/3
    from spass_parser.

:- import parasys.

:- compile("ilf16_tools").

:- dynamic
	proof/3.

:- dynamic			  % used in "Aufbereitung ... Otter" and 
				  %         "Aufbereitung ...  Blockbeweise"
	proof_pars/5,
	used_for/2.

default_transformation(X,_) :- load_proof_pres_files(X),fail.
default_transformation(X,(Y0,Y1)) :- 
	concat_atom([proof_transformation_|X],S),
	ilf_state(S,Y1),
	necessary_transformation(S,Y0),!.
default_transformation([setheo],(me2bl,
	     remove_query,
	     remove_by_rule([insert,since]),
	     remove_by_rule([contrapositive]),
	     remove_by_rule([clausify([],[])]),
	     remove_unused,
	     convert_indirect,
	     remove_duplicate,
	     remove_trivial_subproofs,
	     move_lines,
	     collect_clausified,
	     reduce_depth(3),
	     rew_neg_clauses)) :- !.
default_transformation([cm],(me2bl,
	     remove_query,
	     remove_by_rule([insert,since]),
	     remove_by_rule([contrapositive]),
	     remove_by_rule([clausify([],[])]),
	     remove_unused,
	     convert_indirect,
	     remove_duplicate,
	     remove_trivial_subproofs,
	     move_lines,
	     collect_clausified,
	     reduce_depth(3),
	     rew_neg_clauses)) :- !.
default_transformation([spass], (sp2bl, add_ilf,
	remove_by_rule(['Inp']),
	remove_by_rule([clausify([],[])]),
	remove_unused,
	remove_duplicate,
	allcloseForms,
%	move_into_subproof,
%	move_lines,
	convert_indirect)):- !.
% default_transformation([protein],protein_mail) :- !.
default_transformation([protein],(pt2bl,
	gentzifyForms,
	remove_unused, 
	remove_duplicate,
	convert_indirect,
	remove_trivial_subproofs,
	unique_references,
	make_appendix(protein_theory,["We assume that the reader is acquainted with the elementary theory described in the appendix.\n\n"],[""]))) :- !.
default_transformation([discount],(make_chains(=),unique_references,move_lines,add_ilf)) :- !.
default_transformation([waldmeister],(make_chains(=),unique_references,move_lines,add_ilf)) :- !.
default_transformation([three_tap],(remove_unused, remove_duplicate_cases,rew_neg_clauses,raise_small_cases(10),remove_duplicate,convert_indirect, remove_trivial_subproofs,remove_duplicate,unique_references,move_lines,tap_skolem_const,add_ilf)) :- !.
default_transformation([hyper],(
	hyper2bl,
	elim_true_false,
	remove_unused,
	raise_contradictory_cases,
	raise_neg_cases,
	remove_duplicate_cases,
	remove_duplicate,
	remove_trivial_subproofs,
	remove_last_directs,
	add_ilf)) :- !.
default_transformation([satchmo],(
	hyper2bl,
	elim_true_false,
	remove_unused,
	raise_contradictory_cases,
	raise_neg_cases,
	remove_duplicate_cases,
	remove_duplicate,
	remove_trivial_subproofs,
	remove_last_directs,
	add_ilf)) :- !.
default_transformation(L,true) :- member(ilf,L),!.
default_transformation(S,true) :- ilf_warning("No default proof transformation defined for proofs from %w",[S]),!,fail.

necessary_transformation(proof_transformation_setheo,(me2bl,remove_query)).
necessary_transformation(proof_transformation_discount,true).
necessary_transformation(proof_transformation_spass,(sp2bl,add_ilf)).
necessary_transformation(proof_transformation_three_tap,add_ilf).
necessary_transformation(proof_transformation_protein,pt2bl).
necessary_transformation(proof_transformation_hyper,hyper2bl).
necessary_transformation(proof_transformation_satchmo,hyper2bl).

load_proof_pres_files(X) :- member(Sys,X),not X=ilf,load_proof_pres_sys(Sys),!.
load_proof_pres_files(_) :- get_right_file(".default.texop",F),
	reload_default_texop(F),!.

load_proof_pres_sys(Sys) :-
	ilf_state(out_mode, Mode),
	load_proof_pres_sys(Sys, Mode),
	!.
load_proof_pres_sys(Sys) :-
	load_proof_pres_sys(Sys, latex).

load_proof_pres_sys(Sys, Mode) :-
	(Mode = latex ->
	    Prefix = tex
	    ;
	    Prefix = Mode
	),
	concat_string(["dedsys/",Sys,"/.default.", Prefix, "op"], FS),
	get_right_file(FS, File),
	reload_default_texop(File),!.

/* ########## DEFAULT PROOF PROCESSING FOR SETHEO ########## */

latex_setheo_proof(Job) :-
	prepare_me_proof(Job),
	prooftex.

latex_setheo_proof(Job,Filename) :-
	prepare_me_proof(Job),
	prooftex1(Filename).

prepare_me_proof(Job) :-
	get_proof(Job),
	transform_proof(
	    (me2bl,
	     remove_query,
	     remove_by_rule([insert,since]),
	     remove_by_rule([contrapositive]),
	     remove_unused,
	     convert_indirect,
	     remove_duplicate,
	     remove_trivial_subproofs,
	     move_into_subproof,
	     move_lines,
	     reduce_depth(2),
	     rew_neg_clauses)).

/* ########## DEFAULT PROOF PROCESSING FOR SPASS ########## */

build_spass_proof(Job):-
	ilf_build_bsp(Job),
	get_flag(toplevel_module,ToplevelModule),
	checkin_proof(ToplevelModule).

sp2bl:-
	proof([Pf, global], system, [spass]),
	retract_all(proof(_,_,_)),
	ilf_build_bsp(Pf).

/* ########## AUXILIARY PREDICATES ########## */


transform_proof(Transformation) :-
	get_flag(toplevel_module,ToplevelModule),
	call(get_flag(proof/3, definition_module, Module),ToplevelModule),
	transform_proof(Transformation, Module).

transform_proof(Transformation, Module) :-
	checkout_proof(Module),
	/* make_proof_translit only used for threetap prover
	make_proof_translit,
	*/
	call(Transformation,block),
	checkin_proof(Module),
	retract_all(proof(_,_,_)). % just to free storage


checkout_proof(FromModule) :-
	retract_all(proof(_,_,_)),
	(       call(proof(X,Y,Z),FromModule),
	        assert(proof(X,Y,Z)),
		fail
	;       true
	).

checkin_proof(ToModule) :-
	call(retract_all(proof(_,_,_),ToModule)),
	(       proof(X,Y,Z),
	        call(assert(proof(X,Y,Z)),ToModule),
		fail
	;       true
	).

make_proof_translit :- call(retract_all(transliteration(_,_)),ilf_serv),fail.
make_proof_translit :- proof([_,global],system,S),
	member(three_tap,S),make_three_tap_translit,!.
make_proof_translit.

make_three_tap_translit :- call((
	assert(transliteration(false,contradiction)),
	assert(transliteration(not,sneg)),
	assert(transliteration('->',imp))
	),ilf_serv).
	
:- dynamic copying/1.

copy_term_preserving_metaterms(OldTerm,NewTerm) :-
	asserta(copying(OldTerm)),
	retract(copying(NewTerm)),
	!.	


%%% 
%%% unify(Term1,Term2).
%%% 
%%% Sound unification (ie. with occur check) - this Eclipse implementation is 
%%% from ProCom.
%%% 
%%% "The kind of unification algorithm used by \eclipse is determined at compile
%%% time of a predicate. For this purpose the flag |occur_check| is taken into
%%% account. Once a clause is compiled, the kind of unification can no longer be
%%% influenced (except by redefining the predicate).
%%% 
%%% We use the trick to retrieve the value of the flag |occur_check| and store it
%%% in a global variable of the same name. Then we define turn on the occur check
%%% and define the unify/2 predicate. Finally re restore the old value of the flag
%%% |occur_check|."
%%% NOTE 2016: set_flag(occur_check,on) now gives an error "unimplemented functionality"
%%% 
/*
:-      get_flag(occur_check,OC),
	call(setval(occur_check,OC))@ilfsys,
	set_flag(occur_check,on).
unify(X,X).
:-      call(getval(occur_check,OC))@ilfsys,
	set_flag(occur_check,OC).
*/

/* Thermometer */

thermo(N) :- N > 0, nl, write("|"), thermo1(N), write("|"), nl, write(" ").
thermo(N) :- N =< 0.

thermo1(N) :- N > 0, write("-"), N1 is N-1, thermo1(N1).
thermo1(N) :- N =< 0.

/* ILF zum System hinzufuegen */

add_ilf :- proof([Pf,global],goal,_),
	retract(proof([Pf,global],system,L)),
	append(L,[ilf],L1),
	assert(proof([Pf,global],system,L1)),!.

% cleanup after trafos (ini again)

/* ##########                   ME2BL                      ########### */

/* Adapted From: 
 *
 * File seth2bl.pl 1.1
 * checked in 8/26/96
 * Autor: A.Wolf (von T.Baar fuer ILF angepasst)
 * Kurzbeschreibung: Dieses File realisiert Transformation ME-Beweis 
 * zu Block-Beweis
 */
 
:- dynamic(proof/3),
   dynamic(block_proof/3),
   dynamic(r_tree/3),
   dynamic(r_connect/2),
   dynamic(main_con/2),
   dynamic(e_connect/2),
   dynamic(rem/1),
   dynamic(to_r_connect/2),
   dynamic(node_counter/1),
   dynamic(proof_counter/1).

me2bl:-
	clear_mod,
	transform_proof,
	dupli_block_proof,!.

dupli_block_proof :-
	retract_all(proof(_,_,_)),
	(    block_proof(X,Y,Z),
	     assert(proof(X,Y,Z)),
	     fail
	 ;   true
	).
    
clear_mod:-
	retract_all(block_proof(_,_,_)),
	retract_all(r_tree(_,_,_)),
	retract_all(r_connect(_,_)),
	retract_all(main_con(_,_)),
	retract_all(e_connect(_,_)),
	retract_all(rem(_)),
	retract_all(to_r_connect(_,_)),
	retract_all(node_counter(_)),
	retract_all(proof_counter(_)).
    
write_proof:-
    block_proof(Handle,Key,Info),
    printf("proof(%QDMTw,%QDMTw,(%QDMTw)).\n",[Handle,Key,Info]),
    fail.
write_proof.

transform_proof:-
    assert(node_counter(0)),
    assert(proof_counter(0)),
    setval('Setheo%Axiom', 0),
    setval('Setheo%Clause', 0),
    construct_reductions_tree,
    construct_initial_tree([Sub, Node]),
    setval('Setheo%FirstSubproof', Sub),
    translate_reductions_tree(none,[Sub, Node]),
    translate_extensions, 
    connect_axioms.

nextnode(N1):-
	retract(node_counter(N)),
	N1 is N + 1,
	assert(node_counter(N1)),
	!.

nextproof(sub(Job,N1)):-
	retract(proof_counter(N)),
	N1 is N + 1,
	assert(proof_counter(N1)),
	proof([Job,_],_,_),
	!.

nextaxiom(N1) :-
	getval('Setheo%Axiom', N),
	N1 is N+1,
	setval('Setheo%Axiom', N1).
 
nextclause(N1) :-
	getval('Setheo%Clause', N),
	N1 is N+1,
	setval('Setheo%Clause', N1).

construct_reductions_tree:-
    get_reductions,
    get_factorizations,
    get_extensions,
    order_r_tree(none,none,none),
    move_facs_up,
    control_facs_up,
    disconnect_lower_reds, 
    !.
    
get_reductions:-
    proof(Lower_node,status,red(Upper_node)),
    once((r_tree(red,Upper_node,Lower_node);
	  assert(r_tree(red,Upper_node,Lower_node))
	)),
    fail.
get_reductions:-
    !.

get_factorizations:-
    proof(Image_node,status,fac(Original_node)),
    once((r_tree(fak,Original_node,Image_node);
	  assert(r_tree(fak,Original_node,Image_node))
	)),
    once((r_tree(fak,Original_node,Original_node);
	  assert(r_tree(fak,Original_node,Original_node))
	)),
    fail.
get_factorizations:-
    !.
    
get_extensions:-
    proof(Node,status,ext),
    once((proof(Node,predecessors,[Contra,_]);
	  proof(Node,predecessors,[Contra])
	)),
    proof(Contra,status,contra),
    proof(Contra,contents,Contra_form),
    proof(Contra,predecessors,[ClauseOrAx_node]),
    (proof(ClauseOrAx_node,predecessors,[Axiom_node]) ->
	proof(ClauseOrAx_node,control,rule([clausify(_,_,Clause_name)],_)),
	proof(Axiom_node,status,axiom(Axiom_name))
	;
	proof(ClauseOrAx_node,status,axiom(Axiom_name)),
	Clause_name=[]
    ),
    once((r_tree(ext,Node,[Contra_form,Clause_name,Axiom_name]);
	  assert(r_tree(ext,Node,[Contra_form,Clause_name,Axiom_name]))
    )),
    fail.
get_extensions:-
    !.

order_r_tree(Root,Upper,Ex):-
    order_r_tree_1(Node,Root),	
    order_r_tree_2(Node,Upper,NUpper),
    order_r_tree_3(Node,Ex,Nex),
    order_r_tree(Node,NUpper,Nex),
    fail.
order_r_tree(_,_,_):-
    !. 
   
order_r_tree_1(Node,none):-
    get_root(Node).
order_r_tree_1(Node,Root):-
    proof(Node,predecessors,[Root]).
order_r_tree_1(Node,Root):-
    proof(Node,predecessors,[_,Root]).

get_root(Node):-  
	translit(not,Not),
	Notquery =..[Not,query],  
    proof(Node,contents,Notquery),
    !.    

order_r_tree_2(Node,Upper,Node):-
    r_tree(fak,Node,Node),
    (r_connect(Upper,Node);assert(r_connect(Upper,Node))),
    (main_con(Upper,Node);assert(main_con(Upper,Node))),
    !.
order_r_tree_2(Node,Upper,Node):-
    r_tree(fak,Node1,Node),
    (r_connect(Upper,Node1);assert(r_connect(Upper,Node1))),
    !.
order_r_tree_2(Node,Upper,Node):-
    r_tree(red,Node,_),
    (r_connect(Upper,Node);assert(r_connect(Upper,Node))),
    !.
order_r_tree_2(Node,Upper,Node):-
    r_tree(red,_,Node),
    (r_connect(Upper,Node);assert(r_connect(Upper,Node))),
    !.
order_r_tree_2(_,Upper,Upper):-
    !.
order_r_tree_3(Node,Ex,Node):-
    r_tree(ext,Node,_),
    (e_connect(Ex,Node);assert(e_connect(Ex,Node))),
    !.    
order_r_tree_3(_,Ex,Ex):-
    !.

move_facs_up:-
    remarking_faks,
    repeat,
    get_upper_fac(Node),
    move_facs_up_1(Node),
    Node=ready,
    !.

control_facs_up:-
    rem(_),
    write("SETHEO-2-BLOCK: WARNING! Factorization Order!"),
    nl, 
    !.    
control_facs_up.

remarking_faks:-
    r_tree(fak,Node,Node),
    assert(rem(Node)),
    fail.
remarking_faks:-!.    

get_upper_fac(Node):-
    rem(Node),
    upper_fac(Node),
    !.
get_upper_fac(ready).


upper_fac(Node):-
    rem(X),
    not(X=Node),
    r_d_connected(X,Node),
    !,fail.
upper_fac(_):-!.

move_facs_up_1(ready).
move_facs_up_1(Node):-
    main_con(Oneup,Node),
    get_lowest_red(Red,Oneup,Node),
    control_correct(Node,Red),
    disconnect_facs(Node),
    asserta(r_connect(Red,Node)),
    retract(rem(Node)),
    !.
    
get_lowest_red(Upper,X,Node):-
    r_d_connected(Upper,X),
    r_tree(red,Upper,Lower),
    r_d_connected(Node,Lower),
    !.
get_lowest_red(none,_,_):-
    !.
    
r_d_connected(U,U).
r_d_connected(U,L):-
    r_connect(X,L),
    r_d_connected(U,X).
    
control_correct(Node,Red):-
    r_connect(X,Node),
    not(r_d_connected(Red,X)),
    write("SETHEO-2-BLOCK: WARNING! Factorization Error!"),
    nl,
    !.
control_correct(_,_):-!.

disconnect_facs(Node):-
    r_connect(X,Node),
    retract(r_connect(X,Node)),
    fail.
disconnect_facs(_):-
    !.
    
disconnect_lower_reds:-
    r_tree(red,_,Node),
    retract(r_connect(_,Node)),
    fail.            
disconnect_lower_reds:-
    !.

construct_initial_tree([Sub1,Node3]):-
    proof([Job,_],_,_),
    get_system(Job,System1),
    strict_union(System1,[ilf],System2),
    assert(block_proof([Job,global],system,System2)),
    assert(block_proof([Job,global],control,proved)),
    assert(block_proof([Job,global],control,ready)),
    (proof([Job,global],goal,Goal);Goal=goal),
    assert(block_proof([Job,global],goal,Goal)),
    preserve_global_controls,
    nextnode(Node1),
    nextproof(Sub1), 
    nextnode(Node2), 
    nextnode(Node3), 
    assert(block_proof([Job,Node1],contents,query)),
    assert(block_proof([Job,Node1],predecessors,[])),    
    assert(block_proof([Job,Node1],status,subproof(Sub1))),
    assert(block_proof([Job,Node1],control,rule([indirect],[[Sub1,Node2],[Sub1,Node3]]))),
    translit(not,Not),
    Notquery=..[Not,query],
    assert(block_proof([Sub1,Node2],contents,Notquery)),
    assert(block_proof([Sub1,Node2],predecessors,[])),    
    assert(block_proof([Sub1,Node2],status,assumption([]))),
    translit(contradiction,Contradiction),
    assert(block_proof([Sub1,Node3],contents,Contradiction)),
    assert(block_proof([Sub1,Node3],predecessors,[[Sub1,Node2]])),    
    assert(block_proof([Sub1,Node3],status,proved)),
    assert(to_r_connect([Sub1,Node3],none)),
    !.
    
/* For otter o2bl in reduced ILF 2016 calls get_system after proof/3 in block has been replaced by oproof/3 */
get_system(Job,[System]) :- oproof([Job,global],system,System),!.
get_system(Job,[System]) :-
	proof([Job,global],system,[System]), !.
get_system(Job,[System]) :-
	proof([Job,global],system,System), !.
get_system(_,[anonymous]).

preserve_global_controls :-
     proof([Job,global],control,Control),
     once(member(Control,[
     	 used_goal(_),
     	 constants(_)
     ])),
     assert(block_proof([Job,global],control,Control)),
     fail.
preserve_global_controls :-
     proof([Job,global],goalnames,Control),
     assert(block_proof([Job,global],goalnames,Control)),
     fail.
preserve_global_controls :-
     proof([Job,global],name,Name),
     assert(block_proof([Job,global],name,Name)),
     fail.
preserve_global_controls.

translate_reductions_tree(Rold,[Sub,Anode]):-
    r_connect(Rold,Rnode),
    translate_reductions_tree_1(Rnode,[Sub,Anode],[Sub1,N2]),
    translate_reductions_tree(Rnode,[Sub1,N2]),
    fail.
translate_reductions_tree(_,_):-
    !.    
    
translate_reductions_tree_1(Rnode,[Sub,Anode],[Sub1,N2]):-
    proof(Rnode,contents,Formula),
    negate(Formula,Negformula,Rule),
    nextnode(Node),
    assert(block_proof([Sub,Node],contents,Negformula)),
    retract(block_proof([Sub,Anode],predecessors,L1)),
    assert(block_proof([Sub,Anode],predecessors,[[Sub,Node]])),
    assert(block_proof([Sub,Node],predecessors,L1)),
    nextproof(Sub1),
    assert(block_proof([Sub,Node],status,subproof(Sub1))),
    nextnode(N1),
    nextnode(N2),
    assert(block_proof([Sub,Node],control,rule([Rule],[[Sub1,N1],[Sub1,N2]]))),
    assert(block_proof([Sub1,N1],contents,Formula)),
    assert(block_proof([Sub1,N1],status,assumption([]))),
    assert(block_proof([Sub1,N1],predecessors,[])),
    translit(contradiction,Contradiction),
    assert(block_proof([Sub1,N2],contents,Contradiction)),
    assert(block_proof([Sub1,N2],status,proved)),
    assert(to_r_connect([Sub1,N2],Rnode)),
    assert(block_proof([Sub1,N2],predecessors,[[Sub1,N1]])),
    !.
	

negate(F,N,indirect) :-
	translit(not,Not),
	F=..[Not,N],
	!.    
negate(F,N,in(not)) :-
	translit(not,Not),
	N=..[Not,F],
	!.

translate_extensions:-
    get_task(Task),
    integrate_extension(Task),
    complete_task(Task),
    fail.
translate_extensions:-
    !.

get_task(none).
get_task(T):-
    r_connect(_,T).

integrate_extension(Task):-
    e_connect(Task,NTask),
    integrate_extension_1(NTask,Task),
    fail.
integrate_extension(Task):-
    integrate_extension_2(Task,Task),
    !.
integrate_extension_1(Task,_):-
    r_connect(_,Task),
    !.
integrate_extension_1(Task,Main):-
    e_connect(Task,NTask),
    integrate_extension_1(NTask,Main),
    fail.
integrate_extension_1(Task,Main):-
    integrate_extension_2(Task,Main),
    !.
integrate_extension_2(none,_):-
    !.
integrate_extension_2(Task,Main):-
    to_r_connect([Sub,Pos],Main),
    proof(Task,contents,Lit),
    negate(Lit,Conclusion,_),
    r_tree(ext,Task,[Contra,Axiom,Axform]),
    get_premises(Task,Poslist,[Sub,Pos]),
    integrate_extension_3([Sub,Pos],Contra,Conclusion,Axiom,Axform,Poslist),
    !.
integrate_extension_3([Sub,Pos],_,Conclusion,Clause,Axiom,[]):-
    integrate_axiom(Clause,Axiom,AxHandle),
    nextnode(N1),
    retract(block_proof([Sub,Pos],predecessors,Pred)),
    assert(block_proof([Sub,Pos],predecessors,[[Sub,N1]])),
    assert(block_proof([Sub,N1],predecessors,Pred)),
    assert(block_proof([Sub,N1],contents,Conclusion)),
    assert(block_proof([Sub,N1],status,proved)),
    assert(block_proof([Sub,N1],control,rule([contrapositive],[AxHandle]))),
    !.
integrate_extension_3([Sub,Pos],Contra,Conclusion,Clause,Axiom,Poslist):-
    integrate_axiom(Clause,Axiom,AxHandle),
    nextnode(N1),
    nextnode(N2),
    retract(block_proof([Sub,Pos],predecessors,Pred)),
    assert(block_proof([Sub,Pos],predecessors,[[Sub,N1]])),
    assert(block_proof([Sub,N1],predecessors,[[Sub,N2]])),
    assert(block_proof([Sub,N2],predecessors,Pred)),
    assert(block_proof([Sub,N1],contents,Conclusion)),
    assert(block_proof([Sub,N1],status,proved)),
    Usedlist=[[Sub,N2]|Poslist],
    assert(block_proof([Sub,N1],control,rule([in(and),out(imp)],Usedlist))),
    assert(block_proof([Sub,N2],contents,Contra)),
    assert(block_proof([Sub,N2],status,proved)),
    assert(block_proof([Sub,N2],control,rule([contrapositive],[AxHandle]))),
    !.
 
/* Testet, ob 
	- die Klausel mit zugehoerigem Axiom (integrate_axiom/3) bzw.
	- das Axiom (integrate_axiom/2)
   bereits in den Blockbeweis aufgenommen wurden und fuegt sie ggf.
   hinzu. Im letzten Argument wird das Handle der Klausel/des Axioms
   zurueckgegeben. */
 
integrate_axiom([], Axiom, AxHandle) :-
    integrate_axiom(Axiom, AxHandle).
integrate_axiom(Clause, _, ClHandle) :-
    block_proof(ClHandle,clausename,Clause),
    !.
integrate_axiom(Clause, Axiom, [SubPf,cl(N)]) :-
    integrate_axiom(Axiom, AxHandle),
    proof([Job, Handle], control, rule([clausify(FL,PL,Clause)],_)),
    proof([Job, Handle], contents, ClformSetheo),
    normalize_clause(ClformSetheo, Clform),
    nextclause(N),
    getval('Setheo%FirstSubproof', SubPf),
    (N==1 -> Preds=[] ; N1 is N-1, Preds=[[SubPf, cl(N1)]]),
    assert(block_proof([SubPf,cl(N)],predecessors,Preds)),
    assert(block_proof([SubPf,cl(N)],contents,Clform)),
    assert(block_proof([SubPf,cl(N)],status,proved)),
    assert(block_proof([SubPf,cl(N)],clausename,Clause)),
    assert(block_proof([SubPf,cl(N)],control,rule([clausify(FL,PL)],[AxHandle]))),
    !.
 
integrate_axiom(Axiom, AxHandle) :-
    block_proof(AxHandle,control,axiom(Axiom)),
    !.
integrate_axiom(Axiom, [Job,ax(N)]) :-
    proof([Job, Handle], status, axiom(Axiom)),
    proof([Job, Handle], contents, Axform),
    nextaxiom(N),
    (N==1 -> Preds=[] ; N1 is N-1, Preds=[[Job, ax(N1)]]),
    assert(block_proof([Job,ax(N)],predecessors,Preds)),
    assert(block_proof([Job,ax(N)],contents,Axform)),
    assert(block_proof([Job,ax(N)],status,proved)),
    assert(block_proof([Job,ax(N)],control,axiom(Axiom))),
    !.
 
/* normalize_clause/2 formt die Klausel in eine allquantifizierte 
   Sequenz um */

normalize_clause(Clause, ClauseNew) :-
	translit(':-', ColonMinus),
	Clause=..[ColonMinus, Head, Body],
	!,
	serv_body_list(Body, BodyList),
	serv_head_list(Head, HeadList),
	translit(not, Not),
	sort_by_functor(Not, HeadList, BodyList1, HeadList1),
	sort_by_functor(Not, BodyList, HeadList2, BodyList2),
	append(HeadList1, HeadList2, HeadListNew),
	append(BodyList2, BodyList1, BodyListNew),
	serv_list_fmla(BodyListNew, HeadListNew, ClauseNew0),
	a_close(ClauseNew0, ClauseNew).
normalize_clause(Head, ClauseNew) :-
	serv_head_list(Head, HeadList),
	translit(not, Not),
	sort_by_functor(Not, HeadList, BodyListNew, HeadListNew),
	serv_list_fmla(BodyListNew, HeadListNew, ClauseNew0),
	a_close(ClauseNew0, ClauseNew).
    
complete_task(Task):-
    to_r_connect([Sub,Node],Task),
    block_proof([Sub,Root],predecessors,[]),
    block_proof([Sub,Node],predecessors,[Pred]),
    assert(block_proof([Sub,Node],control,rule([in(contradiction),since],[[Sub,Root],Pred]))),
    !.
    
/* Verbindet die bisher "lose haengenden" Faeden der Axiome (und ggf. der
   Klauseln) mit dem Beweis. */

connect_axioms :-
    retract(block_proof([SubPf, cl(1)], predecessors, [])),
    once((
	block_proof([SubPf, First], predecessors, []),
	retract(block_proof([SubPf, Second], predecessors, [[SubPf, First]])),
    	getval('Setheo%Clause', ClN),
    	assert(block_proof([SubPf, Second], predecessors, [[SubPf, cl(ClN)]])),
	assert(block_proof([SubPf, cl(1)], predecessors, [[SubPf, First]]))
    )),
    fail.
connect_axioms :-
    block_proof([Job, ax(1)], predecessors, []),
    retract(block_proof([Job, ProofLine], predecessors, [])),
    getval('Setheo%Axiom', AxN),
    assert(block_proof([Job, ProofLine], predecessors, [[Job, ax(AxN)]])).

/* ACHTUNG!!! Dasjenige Alternativglied, das im ME-Baum zum Astabschluss 
   benutzt wird, MUSS(!) als erster Fakt unter allen solchen 
   Alternativgliedern des Praedikates proof/3 des Inputbeweises zugreifbar
   sein.
*/

get_premises(Task,Poslist,Above):-
    setof(X,premise(Task,Above,X),Poslist),
    !.
get_premises(_,[],_):-
    !.    

premise(Task,Above,Premise):-
    proof(NotThat,predecessors,[Task]),
    !,
    premise1(Task,Above,Premise,NotThat).
premise1(Task,Above,Premise,NotThat):-
    proof(Opos,predecessors,[Task]),
    not(Opos=NotThat),
    premise2(Opos,Above,Premise).
premise1(Task,Above,Premise,_):-
    proof(Opos,predecessors,[_,Task]),
    premise2(Opos,Above,Premise).
premise1(Task,Above,Premise,_):-
    proof(Opos,predecessors,[Task,_]),
    premise2(Opos,Above,Premise).
premise2(Opos,Above,Premise):-
    proof(Opos,contents,NForm),
    negate(NForm,Form,_),
    block_usable(Form,Above,Premise),
    !.
    
block_usable(Form,Above,Node):-
    block_usable_1(Above,Node),
    block_proof(Node,contents,Form).
block_usable(Form,Above,_):-
    write("SETHEO-2-BLOCK: WARNING! Usable formula "),
    write(Form),
    write(" above "),
    write(Above),
    write(" not found!"),
    nl,
    !,fail.
block_usable_1(Above,Node):-
    block_proof(Above,predecessors,[Node]).
block_usable_1([S,P],Node):-
    block_proof([S,P],predecessors,[]),
    block_proof(Node1,status,subproof(S)),
    block_proof(Node1,predecessors,[Node]).
block_usable_1(Above,Node):-
    block_proof(Above,predecessors,[Node1]),
    block_usable_1(Node1,Node).  
block_usable_1([S,P],Node):-
    block_proof([S,P],predecessors,[]),
    block_proof(Node1,status,subproof(S)),
    block_proof(Node1,predecessors,[Node2]),
    block_usable_1(Node2,Node).


/* ##########     ENDE ME2BL    ########### */

/***/

/* ##########     Transformation von Setheo-Block-Beweisen   ######### */


/* del_ins_contra/0 omits all nodes with rule([insert,since],...; rule([contrapositive],.. fuer Vereinfachung von Setheo-Beweisen
*/


del_ins_contra :- ilf_serv_log(write("Removing contrapositions.\n")),
	del_pos(H,L,del_test(H,L),true).

del_test(H,L) :- proof(H,control,rule([insert,since],L)).
del_test(H,L) :- proof(H,control,rule([contrapositive],L)).

convert_indirect :- ilf_serv_log(write("\nConverting indirect subproofs\n")),fail.
convert_indirect :- bagof(H,not_indirect(H),L),
	remove_indirect_l(L),!.
convert_indirect :- ilf_serv_log(write("No indirect proofs to remove.\n")).

not_indirect(H) :- 
	proof(H,control,rule(R,[Ass,H2|_])),
	proof_type(R,indirect),
	H2=[Pf,_],Ass=[Pf,_],
	ind_convertible(H,Ass,H2).
not_indirect(H) :- 
	proof(H,control,rule([indirect],[Ass,H2|_])),
	not((H2=[Pf,_],Ass=[Pf,_])).
not_indirect(H) :- 
	proof(H,control,rule([in(not)],[Ass,H2|_])),
	not((H2=[Pf,_],Ass=[Pf,_])).

ind_convertible(H,Ass,H2) :- 
	% Annahme fuer Widerspruch verwendet 
	proof(H2,control,rule(_,LC)),
	member(Ass,LC),!,
	% sonst nur noch fuer Gesamtbehauptung 
	not((
		proof(H1,control,rule(_,L)),
		member(Ass,L),
		H1 \= H2,
		H1 \= H
	)),!.

remove_indirect_l([H|L]) :- remove_indirect(H),remove_indirect_l(L),!.
remove_indirect_l([]).

remove_indirect(H) :- retract(proof(H,control,rule(_,[Ass,Cont|R]))),
	(Cont=[Pf,_], Ass=[Pf,_]  ->	
		proof(Ass,predecessors,PAss),
		retract_all(proof(Ass,_,_)),
		retract(proof(H2,predecessors,[Ass])),
		asserta(proof(H2,predecessors,PAss))
	;       true		
	),
	new_contra_rule(Cont,[Ass],CRule),
	asserta(proof(H,control,rule([direct],[Cont|R]))),
	proof(H,contents,CH),
	retract(proof(Cont,contents,_)),
	asserta(proof(Cont,contents,CH)),
	retract(proof(Cont,control,_)),
	asserta(proof(Cont,control,CRule)),!.

/* Falls noetig Regel aendeern */
new_contra_rule(Cont,L,CRule):-
	proof(Cont,control,rule(R,Arg)),
	strict_remove_l(L,Arg,Arg1),
	get_new_contra_rule(R,Arg,Arg1,CRule),!.

get_new_contra_rule(R,Arg,Arg,rule(R,Arg)) :- !.
get_new_contra_rule([direct_all(V),ilf_case],_,Arg1,rule([direct_all(V),ilf_step],Arg1)) :- !.
get_new_contra_rule(_,_,Arg1,rule([since],Arg1)).


check_for_nonempty(H,_) :- 
	proof(H,status,subproof(Pf)),proof([Pf,_],contents,_),!.
check_for_nonempty(H,S) :- proof(H,status,subproof(Pf)),
	proof(H,contents,F),
	retract(proof(H,control,rule([direct],L))),
	assert(proof([Pf,1],contents,F)),
	assert(proof([Pf,1],control,rule([since],L))),
	assert(proof([Pf,1],predecessors,[])),
	assert(proof([Pf,1],status,S)),
	assert(proof(H,control,rule([direct],[[Pf,1]]))),!.
check_for_nonempty(H,_) :- 
	ilf_serv_error((
		write("Ilf ERROR: Empty Subproof at "),
		write(H),
		(proof(H,contents,F) -> 
	                write(" proving "), 
			write(F)
		; true),
		write(" could not be filled\n")
		)).


/* remove_query/0 ersetzt query durch negiertes Ziel */


remove_query :-	ilf_serv_log(write("Removing query.\n")),fail.
remove_query :-	proof(_,contents,query),!,do_remove_query,!.
remove_query :- ilf_serv_log(write("WARNING: query not found!\n")),!.


do_remove_query :-
	get_goals(Goals),
	do_remove_query(Goals).

/*do_remove_query([]) :- 
	ilf_error("Goal not used in proof.\nSorry, removing query in this case is not yet implemented", []),
	!,
	fail.
*/
do_remove_query([]) :- 
	proof([Pf, global], goal, Goal),
	!,
	ilf_serv_log(write("Remove Query for Empty or Contradiction Goal,\n")),

	% Aeussere query durch contradiction ersetzen 

	last_in_proof(Pf,Thm),
	proof(Thm,status,subproof(Pf1)),
	retract(proof(Thm,contents,_)),
	assert(proof(Thm,contents,Goal)),

	% ind. Beweis fuer query in einen direkten fuer contradiction aendern
	% evtl. muss man auf proof(Cont, contents, Contradiction) testen ?
	
	last_in_proof(Pf1, Last),
	proof(Last, predecessors, [Query]),
	retract_all(proof(Last, _, _)),
	proof(Query, predecessors, [QueryCont]),
	retract(proof(Query, contents, query)),
	assert(proof(Query,contents,contradiction)),
	retract(proof(QueryCont,contents,(query :- QCont))),
	assert(proof(QueryCont,contents,(false :- QCont))),
	proof([Pf1,NQ], predecessors, []),
	retract(proof(H, predecessors, [[Pf1,NQ]])),
	assert(proof(H, predecessors, [])),
	retract_all(proof([Pf1,NQ] ,_ ,_)),
	retract_all(proof(Thm, control, _)),
	assert(proof(Thm, control, rule([contradictory], [Query]))),
	!.

do_remove_query(Goals) :-

	make_goal_fla(Goals,Fla),

	% Aeussere query durch Goals ersetzen 

	proof([Pf,global],goal,_),	
	last_in_proof(Pf,Thm),
	proof(Thm,status,subproof(Pf1)),
	retract(proof(Thm,contents,_)),
	assert(proof(Thm,contents,Fla)),

	% letztes query entfernen 
	
	proof([Pf1,Q],contents,query),
	proof([Pf1,Q],control,R),
	proof([Pf1,Q],predecessors,PQ),
	proof([Pf1,Q],status,S),
	proof([Pf1,C],predecessors,[[Pf1,Q]]),
	retract(proof([Pf1,C],control,_)),
	assert(proof([Pf1,C],control,R)),
	retract(proof([Pf1,C],predecessors,_)),
	assert(proof([Pf1,C],predecessors,PQ)),
	retract(proof([Pf1,C],status,_)),
	assert(proof([Pf1,C],status,S)),
	retract_all(proof([Pf1,Q],_,_)),

	% not query durch negiertes Theorem ersetzen und Verweise aendern

	proof([Pf1,NQ],predecessors,[]),  
	replace_not_query([Pf1,NQ],Goals,Fla),
	replace_query_by_contradiction,

	% Axiom/Kontrapositionen des Ziels entfernen

	remove_goal_axioms(Goals),
	!.


replace_query_by_contradiction :-
	translit(contradiction,Contradiction),
	(	retract(proof(HH, contents, (query :- Fla))),
		assert(proof(HH, contents, (Contradiction :- Fla))),
		fail
	;       true
	).

replace_not_query(H,Handles,Fla) :-
	retract(proof(H, contents, _)),
	negate_clause(Fla, NotFla),
	assert(proof(H, contents, NotFla)),
	change_refs_l(Handles, H).

remove_goal_axioms(Handles) :-
	member(HQ, Handles),
	once((
		proof(HQ, control, rule(_,[Ax])),
	        rm_line(Ax)
	        ;
	        true
	)),
	rm_line(HQ),
	fail.
remove_goal_axioms(_).

get_goals(Goals) :-
	proof([_,global], goalnames, GoalNames),
	name2handle(GoalNames, Goals).

name2handle([], []).
name2handle([Name|NameList], [Hdl|HdlList]) :- 
	proof(Hdl, clausename, Name), 
	!,
	name2handle(NameList, HdlList).
name2handle([Name|NameList], [Hdl|HdlList]) :- 
	proof(Hdl, control, Name),
	!,
	name2handle(NameList, HdlList).
name2handle([_|NameList], HdlList) :- 
	name2handle(NameList, HdlList).

make_goal_fla(Goals, Fla) :-
	maplist(get_goal_disjunct, Goals, Disjuncts),
	translit(not, Not),
	sort_by_functor(Not, Disjuncts, BodyList, HeadList),
	serv_list_fmla(BodyList, HeadList, Fla1),
	e_close(Fla1, Fla).

make_negated_goal_fla(Goals, Fla) :-
	maplist(get_goal_disjunct, Goals, Conjuncts),
	maplist(serv_negate_l, Conjuncts, Conjuncts1),
	list_body(Conjuncts1, Fla1),
	a_close(Fla1, Fla).
	
get_goal_disjunct(Hdl, Fla) :-
	proof(Hdl, contents, Fla1),
	!,
	remove_alls(Fla1, Fla0),
	negate_clause(Fla0,Fla).
 
negate_clause(Fla,not(Fla)) :- var(Fla),!,ilf_serv_error((
	write("ILF ERROR: Variable found instead of literal.\n")
	)),!.
negate_clause(Fla,not(Fla)) :- number(Fla),!,ilf_serv_error((
	write("ILF ERROR: Number found instead of literal.\n")
	)),!.
negate_clause(Fla,NotFla) :- Fla=..[Dis,Fla1,Fla2],
	translit(';',Dis),
	negate_clause(Fla1,NotFla1),
	negate_clause(Fla2,NotFla2),
	translit(',',And),
	NotFla=..[And,NotFla1,NotFla2],!.
negate_clause(Fla,NotFla) :- Fla=..[Not,NotFla],
	translit(not,Not),!.
negate_clause(Fla,NotFla) :- Fla=..[ColonMinus, False, NotFla],
	translit(':-', ColonMinus),
	translit(false,False),!.
negate_clause(Fla,NotFla) :- Fla=..[Imp, NotFla, False],
	translit('->', Imp),
	translit(false,False),!.
negate_clause(Fla,NotFla) :- Fla=..[Imp, Body, Head],
	translit('->', Imp),
	!,
	negate_clause(Head, NotHead),
	translit(',', And),
	NotFla=..[And, Body, NotHead].
negate_clause(Fla,NotFla) :- Fla=..[And,Fla1,Fla2],
	translit(',',And),
	negate_clause(Fla1,NotFla1),
	negate_clause(Fla2,NotFla2),
	translit(';',Dis),
	NotFla=..[Dis,NotFla1,NotFla2],!.
negate_clause(Fla,NotFla) :- Fla=..[Exists,Var,Fla1],
	translit(exists,Exists),
	negate_clause(Fla1,NotFla1),
	translit(forall,Forall),
	NotFla=..[Forall,Var,NotFla1],!.
negate_clause(Fla,NotFla) :- Fla=..[Ex,Var,Fla1],
	translit(ex,Ex),
	negate_clause(Fla1,NotFla1),
	translit(all,All),
	NotFla=..[All,Var,NotFla1],!.

negate_clause(Fla,NotFla) :- translit(not,Not),
	NotFla =.. [Not,Fla],!.
	
a_close_proof(Pf) :- proof([Pf,H],predecessors,[]),
	a_close_proof(Pf,[Pf,H]),!.
a_close_proof(_Pf,H) :- proof(H,status,subproof(Pf1)),
	a_close_proof(Pf1),fail.
a_close_proof(Pf,H) :- 
	once((
		retract(proof(H,contents,F)),
		a_close(F,F1),
		asserta(proof(H,contents,F1))
	)),
	proof([Pf,N],predecessors,[H]),
	a_close_proof(Pf,[Pf,N]),!.
a_close_proof(_,_).


/* Antwortsubstitutionen in ME-Beweisen */


dnf_to_list(F,[[F]]) :- var(F),!.
dnf_to_list(F,[[F]]) :- number(F),!.
dnf_to_list(F,FL) :- F=..[D,F1,F2],translit(';',D),!,
	dnf_to_list(F1,F1L),dnf_to_list(F2,F2L),
	append(F1L,F2L,FL),!.
dnf_to_list(F,[CL]) :- serv_body_list(F,CL).

get_ans(K,D,L) :- K=..[E,V,B],translit(exists,E),
	serv_body_list(B,BL),
	dnf_to_list(D,DL),
	get_ans_l(DL,BL,V,L),!.

get_ans_l([KL|DL],BL,V,[A|AL]) :- get_ans(KL,BL,V,A),
	get_ans_l(DL,BL,V,AL),!.
get_ans_l([],_,_,[]).

get_ans(KL,BL,V,A) :- length(KL,N),length(BL,N),
	copy_term_preserving_metaterms((BL,V),(BL1,A)),
	build_ans(KL,BL1).

build_ans([K|KL],BL) :- remove(K,BL,BL1),
	build_ans(KL,BL1).
build_ans([],[]).

remove(E,[E|L],L).
remove(E,[F|L],[F|L1]) :- remove(E,L,L1).

me_answers :- proof([Pf,global],goal,G),
	proof([Pf,N],status,subproof(Pf1)),
	proof([Pf,N],contents,D),
	get_ans(G,D,L),
	G=..[_,V,_],
	retract(proof([Pf,N],contents,_)),
	assert(proof([Pf,N],contents,G)),
	retract(proof([Pf,N],status,_)),
	assert(proof([Pf,N],status,subproof(ans(Pf)))),
	assert(proof([ans(Pf),1],contents,D)),
	assert(proof([ans(Pf),1],predecessors,[])),
	assert(proof([ans(Pf),1],status,subproof(Pf1))),
	retract(proof([Pf,N],control,R)),
	assert(proof([ans(Pf),1],control,R)),
	make_unique1(L,L1),
	assert(proof([Pf,N],control,rule([answer(V,L1)],[[ans(Pf),1]]))),!.
me_answers :- ilf_serv_log(write("No answers to generate\n")).

make_unique1(L1,L2) :- make_unique1(L1,_,L2).

make_unique1([E|L1],L,L2) :- member(E,L),make_unique1(L1,L,L2),!.
make_unique1([],L,[]) :- var(L),!.
make_unique1([],[E|L],[E|L1]) :- make_unique1([],L,L1),!.

last_in_proof(Pf,H) :- proof([Pf,N],predecessors,_),
	last_in_proof(Pf,[Pf,N],H).
last_in_proof(Pf,H1,H) :- proof(H2,predecessors,[H1]),
	last_in_proof(Pf,H2,H),!.
last_in_proof(_Pf,H,H).

dualize(F,F1) :- number(F),translit(not,Not),F1=..[Not,F1],!.
dualize(F,F1) :- var(F),translit(not,Not),F1=..[Not,F],!.
dualize(F,F1) :- 
	F=..[And,G1,G2],
	translit(',',And),
	translit(';',Or),
	dualize(G1,H1),
	dualize(G2,H2),
	F1=..[Or,H1,H2],!.
dualize(F,F1) :- F=..[Ex,G],translit(ex,Ex),
	dualize(G,H),
	translit(all,All),
	F1=..[All,_X,H],!.
dualize(F,F1) :- F=..[All,G],translit(all,All),
	dualize(G,H),
	translit(ex,Ex),
	F1=..[Ex,_X,H],!.
dualize(F,F1) :- F=..[Not,F1],translit(not,Not),!.
dualize(G,G1) :- translit(not,Not),G1=..[Not,G],!.

e_close(G,H) :- free_vars(G,L),e_close(G,L,H),!.

e_close(G,[],G) :- !.
e_close(G,L,F) :- translit(exists,Ex),F=..[Ex,L,G],!.

a_close(G,H) :- free_vars(G,L),a_close(G,L,H),!.

a_close(G,[],G) :- !.
a_close(G,L,F) :- translit(forall,All),F=..[All,L,G],!.


/*  ############# Ende Transformation von Setheo-Blockbeweisen ########### */

/* ##########     Aufbereitung von Blockbeweisen   ############# */

/* del_pos(Node,NodeList,Test1,Test2) retracts Node and replaces references to Node by references to NodeList */


:- dynamic                   % local in "Aufbereitung von Blockbeweisen"
	chi/2,
	line_stack/1,
	pf_chg/3,
	proof_ax/1,
	proof_known_ax/1,
	proof_known_theory/1,
	proof_lines/2,
	the_references/3,
	tmp/1,
	to_ins/1,
	used_pf/1,
	used_proof_line/1,
	used_subpf/1.


del_pos(H,L,Cond,Pred) :- bagof([H,L],(Cond,Pred),L1),length(L1,N),
	once((ilf_state(ilf_serv,on);thermo(N))),fail.
del_pos(H,L,Cond,Pred) :- Cond,Pred,change_pos(H,L),
	retract_all(proof(H,_,_)),
	once((ilf_state(ilf_serv,on);write("*"))),fail.
del_pos(_,_,_,_) :- nl.

del_pos(Node,NodeList,Cond) :- del_pos(Node,NodeList,Cond,true),!.


/* del_pos(P) omits node with handle P */


del_pos(P) :- proof(P,status,subproof(Pf)),!,used_in_subproof(Pf,Pred),
	retract_all(proof(P,status,_)),
	assert(proof(P,status,proved)),
	retract_all(proof(P,control,_)),
	assert(proof(P,control,rule([subproof(Pf)],Pred))),!.
del_pos(P) :- del_pos(P,L,true,proof(P,control,rule(_,L))),!.

clausify_rule(rule([clausify(A,N)],[H]),clausify(A,N),H).
clausify_rule(rule([clausify(A,N,_)],[H]),clausify(A,N,xxx),H).

is_clause(C) :- C=..[UAll,_,C1],
	(translit(all,UAll);translit(forall,UAll)),!,
	is_clause(C1).
is_clause(C) :- C=..[UOr,C1,C2],translit(';',UOr),!,
	is_clause(C1),is_clause(C2).
is_clause(C) :- C=..[Op,C1],translit(not,Op),!,
	is_at(C1).
is_clause(C) :- C=..[UImp,C1,C2],translit('->',UImp),
	body_list(C1,BL),head_list(C2,HL),
	is_at_l(BL),is_at_l(HL).
is_clause(C) :- is_at(C).

is_at(C) :- var(C),!.
is_at(C) :- C=..[Op|Arg],translit(OpI,Op),C1=..[OpI|Arg],not log_op(C1,_).

is_at_l([A|L]) :- is_at(A),is_at_l(L).
is_at_l([]).

rm_clausified_clauses :- collect_proof_pars,
	clausify_rule(Rule,_,H),
	proof(P,control,Rule),
	do_rm_clausified_clause(P,H),
	fail.
rm_clausified_clauses.

do_rm_clausified_clause(P,H) :- proof(H,contents,C),
	is_clause(C),
	rm_pos(P,[H]),!.

/* collect_clausified bringt Klauseln aus dem selben Axiom zusammen */
collect_clausified :- get_multiple_clauses(CL),
	collect_proof_pars,
	collect_clausified_l(CL).
collect_clausified.

collect_clausified_l([R|L]) :- setof(P,proof(P,control,R),PL),
	get_common_predecessor(PL,H),
	collect_clauses(PL,H),
	collect_clausified_l(L),!.
collect_clausified_l([]).

get_common_predecessor(PL,H) :- get_path_l(PL,PaL),
	get_common_proof(PaL,LL,Pf),
	get_common_point(PL,LL,Pf,H).

get_path_l([P|L],[Pa|PaL]) :- get_path(P,Pa0),rev(Pa0,Pa),get_path_l(L,PaL),!.
get_path_l([],[]).

get_path([Pf,_],[Pf|PaL]) :- proof(H,status,subproof(Pf)),
	get_path(H,PaL),!.
get_path([Pf,_],[Pf]).

get_common_proof([Pa],[],Pf) :- append(_,[Pf],Pa),!.
get_common_proof([Pa|PL],LL,Pf) :- get_common_proof(Pa,PL,_,LL,Pf),!.


get_common_proof([P|Pa],PL,_,LL,Pf) :- 
	rm_1_el(P,PL,PL1),
	get_common_proof(Pa,PL1,P,LL,Pf),!.
get_common_proof(_,LL,Pf,LL,Pf).

rm_1_el(P,[[P|PL]|L],[PL|L1]) :- rm_1_el(P,L,L1).
rm_1_el(_,[],[]).

get_common_point(PL,LL,Pf,H) :- proof([Pf,N],predecessors,[]),
	get_first_point([Pf,N],PL,LL,H),!.

get_first_point(H,PL,_,H) :- member(H,PL),!.
get_first_point(H,_,LL,H) :- proof(H,control,status(subproof(Pf))),
	member([Pf|_],LL),!.
get_first_point(H,PL,LL,H1) :- proof(HH,predecessors,[H]),
	get_first_point(HH,PL,LL,H1),!.
get_first_point(_,PL,LL,_) :- ilf_serv_error("Could not find common predecessor for nodes %w and proofs %w",[PL,LL]),fail.

collect_clauses([P|PL],P) :- collect_clauses(PL,P),!.
collect_clauses([P|PL],H) :- 
	H=[Pf,_],
	gen_hdl(Pf,PN),
	retract(proof(H,predecessors,Pred)),
	assert(proof(H,predecessors,[PN])),
	assert(proof(PN,predecessors,Pred)),
	proof(P,contents,C),assert(proof(PN,contents,C)),
	proof(P,status,S),assert(proof(PN,status,S)),
	proof(P,control,Co),assert(proof(PN,control,Co)),
	rm_pos(P,[PN]),!,
	collect_clauses(PL,H).
collect_clauses([],_).


get_multiple_clauses(L) :- setof(R,gives_multiple_clauses(R),L).

gives_multiple_clauses(R) :- clausify_rule(R,_,_),
	proof(P1,control,R),
	proof(P2,control,R),
	not P1=P2.



remove_by_rule(R) :- rm_by_rule(R),!.

rm_by_rule(L) :- make_tmp(P,with_rule(L,P)),
	bagof(P,tmp(P),PL),
	collect_proof_pars,
	length(PL,N),
	(ilf_state(ilf_serv,on);thermo(N)),
	rm_pos_l(PL),!.
rm_by_rule(_L).

make_tmp(_,_C) :- retract_all(tmp(_)),fail.
make_tmp(X,C) :- C,assert(tmp(X)),fail.
make_tmp(_,_).

with_rule(L,P) :- proof(P,control,rule(L1,_)),sublist(L1,L).

remove_by_contents(L) :- ilf_serv_log((
	write("\nRemoving lines with contents in "),
	write(L),
	nl
	)),fail.
remove_by_contents(L) :- proof([Pf,global],goal,_),
	proof([Pf,N],contents,C),
	not proof([Pf,N],control,axiom(_)),
	member(C1,L),
	instance(C,C1),!,
	ilf_warning(("Cannot remove outermost line at %w by contents.\n",[[Pf,N]])),!.
remove_by_contents(R) :- rm_by_contents(R),!.

rm_by_contents(L) :- make_tmp(P,with_contents(L,P)),
	bagof(P,tmp(P),PL),
	collect_proof_pars,
	length(PL,N),
	(ilf_state(ilf_serv,on);thermo(N)),
	rm_pos_l(PL),!.
rm_by_contents(_L).

with_contents(L,P) :- proof(P,contents,C),
	once((
		member(C1,L),instance(C,C1)
	)).

sublist([],_).
sublist([E|L],L1) :- (not not member(E,L1)),sublist(L,L1),!.

rm_pos(P) :- proof(P,status,subproof(Pf)),
	proof_pars(Pf,_,_,_,L),
	rm_pos(P,L),
	(ilf_state(ilf_serv,on);write("+")),!.
rm_pos(P) :- proof(P,control,rule(_,L)),
	rm_pos(P,L),
	(ilf_state(ilf_serv,on);write("+")),!.
rm_pos(_) :- (ilf_state(ilf_serv,on);write("-")),!.

rm_pos_l([P|L]) :- rm_pos(P),rm_pos_l(L),!.
rm_pos_l([]).

rm_pos(P,L) :- retract(used_for(P,Q)),
	once((
		retract(proof(Q,control,rule(R,A))),
		change_pos_lst(P,L,A,A1),
		change_rule_lst(P,L,R,R1),
		assert(proof(Q,control,rule(R1,A1))),
		make_new_used(Q,L)
	)),fail.
rm_pos(P,L) :- retract(proof_pars(A,B,C,D,E)),
	once((
		change_pos_lst(P,L,E,E1),
		assert(proof_pars(A,B,C,D,E1))
	)),fail.
rm_pos(P,_) :- retract(proof(Q,predecessors,[P])),
	proof(P,predecessors,V),
	assert(proof(Q,predecessors,V)),
	(proof(P,status,subproof(Pf)) -> 
	    rm_subproof(Pf)
	; true),
	retract_all(proof(P,_,_)),!.
rm_pos(P,_) :- proof(P,predecessors,[_]),
	(proof(P,status,subproof(Pf)) -> 
	    rm_subproof(Pf)
	; true),
	retract_all(proof(P,_,_)),!.
rm_pos([Pf,_],_) :- retract(proof(H,status,subproof(Pf))),
	assert(proof(H,status,proved)),
	retract(proof(H,control,rule(R,L))),
	assert(proof(H,control,rule([empty_subproof(R)],L))),
	rm_subproof(Pf),!.

rm_pos_l([P|PL],L) :- rm_pos(P,L),rm_pos_l(PL,L),!.
rm_pos_l([],_).

make_new_used(Q,[P|L]) :- assert(used_for(P,Q)),
	make_new_used(Q,L),!.
make_new_used(_,[]).


used_in_subproof(Pf,Pred) :- retract_all(used_pf(_)),
	retract_all(used_subpf(_)),
	make_used_pf(Pf),
	(setof(H,used_pf(_,H),Pred);Pred=[]),
	retract_all(used_pf(_)),
	retract_all(used_subpf(_)),!.


/* remove_duplicate keeps only the first occurence of a formula proved several times */


remove_duplicate :- rem_dupli.

rem_dupli :- collect_proof_pars,
	setval(line_stack_size,0),
	make_line_stack,
	getval(line_stack_size,N),
	(ilf_state(ilf_serv,on);thermo(N)),
	rem_duplicate,!.

make_line_stack :- proof([Pf,global],goal,_),
	last_in_proof(Pf,H0),
	retract_all(line_stack(_)),
	make_line_stack(H0),!.

make_line_stack(H) :-
	asserta(line_stack(H)),
	incval(line_stack_size),
	fail.
make_line_stack(H) :- previous_line(H,H1),!,
	make_line_stack(H1),!.
make_line_stack(_).

previous_line(H,H1) :- proof(H,status,subproof(Pf)),
	last_in_proof(Pf,H1),!.
previous_line(H,H1) :- proof(H,predecessors,[H1]),!.
previous_line([Pf,_],H1) :- skip_subproof(Pf,H1),!.

skip_subproof(Pf,H1) :- proof([Pf1,N],status,subproof(Pf)),
	(
	proof([Pf1,N],predecessors,[H1])
	;
	skip_subproof(Pf1,H1)
	),!.


rem_duplicate :- retract_all(proof_lines(_,_)),fail.
rem_duplicate :- proof(H,control,axiom(_)),
	once((
	        not(line_stack(H)),
	        proof(H,contents,C),
		remove_alls(C, C0),
	        assert(proof_lines(C0,H))
	)),fail.
 
rem_duplicate :- retract(line_stack(H)),
	do_rem_duplicate(H),
	fail.
 
rem_duplicate :- retract_all(proof_lines(_,_)).
 
get_duplicate(C,H) :- numbervars(C,1,_),
	get_one_duplicate(C,H),!.

get_one_duplicate(C,H) :-
	proof_lines(C,H),
		not (			% Faelle duerfen nicht entfernt werden
		H=[Pf,_],
		proof(HH,status,subproof(Pf)),
		proof(HH,control,R),
		case_rule(R)
	),!.
% speziell fuer Tableaux - 3TaP
get_one_duplicate(C,H) :- same_signed(C,C1),proof_lines(C1,H),!.

do_rem_duplicate(H) :- proof(H,contents,C),
	remove_alls(C, C0),
	numbervars(C0,1,_),
	do_rem_duplicate(H,C0),!.

do_rem_duplicate(H,C) :- get_duplicate(C,H1),!,
% Formel ist schon da 
	(ilf_state(ilf_serv,on);write(+)),
	rm_pos(H,[H1]),
	proceed_duplicate(H),!.
do_rem_duplicate(H,C) :- 
% Sonst abspeichern 
	asserta(proof_lines(C,H)),
	(ilf_state(ilf_serv,on);write(*)),
	proceed_duplicate(H),!.

proceed_duplicate([Pf,_]) :- 
	line_stack([Pf,_]),!.
proceed_duplicate([Pf,_]) :- retract_all(proof_lines(_,[Pf,_])),!.


/* change_pos(P,L) entfernt Position P und setzt Referenzen auf L */


change_pos(P,_) :- once((
	retract(proof(Q,predecessors,[P])),
	proof(P,predecessors,Pred),
	assert(proof(Q,predecessors,Pred))
	)),
	fail.
change_pos(P,_) :- retract_all(proof(P,_,_)),fail.
change_pos(P,L) :- proof(Q,control,rule(R,Pos)),
	change_pos_lst(P,L,Pos,Pos1),
	change_rule_lst(P,L,R,R1),
	assert(pf_chg(Q,control,rule(R1,Pos1))),fail.
change_pos(_,_) :- retract(pf_chg(Q,Key,Val)),
	retract_all(proof(Q,Key,_)),
	assert(proof(Q,Key,Val)),
	fail.
change_pos(_,_).

new_readies :- proof(_,status,subproof(Pf)),
	retract_all(proof([Pf,global],control,ready)),
	assert(proof([Pf,global],control,ready)),fail.
new_readies.

change_pos_lst(P,L,[P|Rest],List1) :-
	change_pos_lst(P,L,Rest,List2),
	strict_union(L,List2,List1),!.
change_pos_lst(P,L,[E|Rest],[E|List]) :- change_pos_lst(P,L,Rest,List),!.
change_pos_lst(_,_,[],[]).

change_rule_lst(P,L,[X|RL],[X|LL]) :- var(X),!,change_rule_lst(P,L,RL,LL),!.
change_rule_lst(P,L,[P|RL],LL) :- change_rule_lst(P,L,RL,L1),
	append(L,L1,LL),!.
change_rule_lst(P,L,[R|RL],[R1|RL1]) :- R=..[Op|Arg],
	change_rule_lst(P,L,Arg,Arg1),
	R1=..[Op|Arg1],
	change_rule_lst(P,L,RL,RL1),!.
change_rule_lst(_,_,[],[]).

make_used_pf(Pf) :- proof([Pf,_],status,subproof(SPf)),
	assert(used_subpf(SPf)),
	make_used_pf(SPf),
	fail.
make_used_pf(Pf) :- proof([Pf,_],control,rule(_,Pred)),make_used_hdl(Pred),fail.
make_used_pf(_).

make_used_hdl([[Pf,_H]|L]) :- used_subpf(Pf),!,make_used_hdl(L),!.
make_used_hdl([H|L]) :- assert(used_pf(H)),make_used_hdl(L),!.
make_used_hdl([]).

/* Begin remove_duplicate_cases */
remove_duplicate_cases :- collect_proof_pars,fail.
remove_duplicate_cases :- proof(H,control,rule([case(_)|_],_)),
	duplicate_case(H,H1),
	H=[PfH,_],
	proof(HPf,status,subproof(PfH)),
	rm_pos(H,[H1]),
	reduce_case_control(HPf,H1),
	fail.
remove_duplicate_cases :- clean_reduced_cases.

clean_reduced_cases :- proof(H,control,rule([reduced_case(_)],_)),
	proof(H,status,S),
	clean_reduced_case_with_status(H,S),fail.
clean_reduced_cases.

clean_reduced_case_with_status(H,subproof(Pf)) :- 
	setof([Pf,N],C^proof([Pf,N],contents,C),CL),
	clean_reduced_case(H,CL),!.
clean_reduced_case_with_status(H,proved) :-
	clean_reduced_case(H,[]),!.
clean_reduced_case_with_status(H,S) :- ilf_serv_error("Cannot clean reduced case %w with status %w.",[H,S]).

clean_reduced_case(H,[]) :- retract(proof(H,status,_)),
	assert(proof(H,status,proved)),
	retract(proof(H,control,rule([reduced_case(N)],L))),
	assert(proof(H,control,rule([reduced_case(0,N)],L))),!.
clean_reduced_case(H,[HC]) :- proof(HC,status,subproof(Pf)),
	retract(proof(H,status,_)),
	assert(proof(H,status,subproof(Pf))),
	retract(proof(H,control,rule([reduced_case(N)],L))),
	strict_remove(HC,L,L1),
	proof(HC,control,rule(_,LC)),
	strict_union(L1,LC,L2),
	assert(proof(H,control,rule([reduced_case(1,N)],L2))),
	retract_all(proof(HC,_,_)),!.
clean_reduced_case(H,_) :- 
	retract(proof(H,control,rule([reduced_case(N)],L))),
	assert(proof(H,control,rule([reduced_case(2,N)],L))),!.
	
reduce_case_control(HPf,H1) :- 
	retract(proof(HPf,control,rule([reduced_case(N)],L))),
	L=[C|L1],
	strict_remove(H1,L1,L2),
	(N1 is N+1),
	assert(proof(HPf,control,rule([reduced_case(N1)],[C,H1|L2]))),!.
reduce_case_control(HPf,H1) :- 
	retract(proof(HPf,control,rule(_,L))),
	L=[C|L1],
	strict_remove(H1,L1,L2),
	assert(proof(HPf,control,rule([reduced_case(1)],[C,H1|L2]))),!.

duplicate_case(H,H1) :-
	proof(H,contents,C),
	numbervars(C,1,_),
	proof(H1,contents,C),
	block_1_usable(H1,H),!.
	
/* End remove_duplicate_cases */

/* raise_small_cases/1 Eliminiert kleine Unterbeweise von contradiction */

raise_small_cases(N) :- ilf_serv_log(printf("Raising cases with less than %w lines.",[N])),fail.
raise_small_cases(_) :- collect_proof_pars,fail.
raise_small_cases(N) :- small_contra_case(N,HH),
	raise_contra_case(HH),fail.
raise_small_cases(_).

small_contra_case(N,[HH1,HH2]) :- case_contra_proof(Pf),
	once((
		setof([Pf,NN],C^proof([Pf,NN],contents,C),[H1,H2]),
		proof(H1,status,subproof(Pf1)),
		proof(H2,status,subproof(Pf2)),
		proof_pars(Pf1,_,_,G1,E1),
		proof_pars(Pf2,_,_,G2,E2),
		is_small_case(N,[H1,G1,E1],[H2,G2,E2],[HH1,HH2])
	)).

case_contra_proof(Pf) :- translit(contradiction,Contra),
	case_rule(R),
	proof(H,control,R),
	proof(H,status,subproof(Pf)),
	once(proof(H,contents,Contra);proof([Pf,_],contents,Contra)).

case_rule(rule([_,ilf_case],_)).
case_rule(rule([cut(_)|_],_)).
case_rule(rule([case],_)).

is_small_case(N,[H1,G1,_E1],[H2,G2,E2],[H2,H1]) :- G2 < N,G2 < G1,
	not member(H1,E2),!.
is_small_case(N,[H1,G1,E1],[H2,_G2,_E2],[H1,H2]) :- G1 < N, not member(H2,E1),!.
	
raise_contra_case([H1,H2]) :- H2=[Pf,_],
	proof(H0,status,subproof(Pf)),
	H0=[Pf0,_],
	gen_hdl(Pf0,HN2),
	proof(H2,control,rule(_,A2)),
	assert(proof(HN2,control,rule([indirect],A2))),
	proof(H2,contents,C2),
	assert(proof(HN2,contents,C2)),
	proof(H2,status,S2),
	assert(proof(HN2,status,S2)),
	retract_all(proof(H2,_,_)),
	retract(proof(H0,predecessors,Pred)),
	assert(proof(HN2,predecessors,Pred)),
	gen_hdl(Pf0,HN1),
	assert(proof(HN1,predecessors,[HN2])),
	assert(proof(H0,predecessors,[HN1])),
	case_justify(H0,J),
	append(J,[HN2],JN),
	assert(proof(HN1,control,rule([tautology],JN))),
	assert(proof(HN1,status,proved)),
	proof(H1,status,subproof(Pf1)),
	proof(H1,contents,CH1),
	get_the_dual(CH1,CA),
	assert(proof(HN1,contents,CA)),
	ass_list(Pf1,AL),
	rm_pos_l(AL,[HN1]),
	proof([Pf1,NX],predecessors,[]),
	raise_contra_case_below(H0,[Pf1,NX]),!.

get_the_dual(C,D) :- proof([_,global],system,L),member(three_tap,L),!,
	get_signed_dual(C,D),!.
get_the_dual(C,D) :- dualize(C,D).

get_signed_dual(C,D) :- translit(not,SNeg),C=..[SNeg,D],!.
get_signed_dual(C,D) :- translit(fSign,FSign),C=..[FSign,CC],
	translit(tSign,TSign),
	D=..[TSign,CC],!.
get_signed_dual(C,D) :- translit(tSign,TSign),C=..[TSign,CC],
	translit(fSign,FSign),
	D=..[FSign,CC],!.
get_signed_dual(C,D) :- translit(not,SNeg),D=..[SNeg,C],!.

case_justify(H,[C]) :- proof(H,control,rule([_,ilf_case],[C|_])),!.
case_justify(_,[]).

% Aufsammeln der obersten assumptions

ass_list(Pf,AL) :- proof([Pf,N],predecessors,[]),
	proof([Pf,N],status,assumption(_)),
	ass_below([Pf,N],AL),!.
ass_list(_,[]).

ass_below(H,[H|AL]) :- proof(H,status,assumption(_)),
	proof(H1,predecessors,[H]),
	ass_below(H1,AL),!.
ass_below(_,[]).

raise_contra_case_below(H0,HX) :- translit(false,Contra),
	proof(HX,contents,Contra),
	proof(HX,control,R),
	proof(HX,status,SX),
	retract(proof(H0,control,_)),
	assert(proof(H0,control,R)),
	retract(proof(H0,status,_)),
	assert(proof(H0,status,SX)),
	retract_all(proof(HX,_,_)),!.
raise_contra_case_below([Pf,N0],HX) :- proof(HX,status,S),!,
	proof(HX,contents,CX),
	proof(HX,control,RX),
	proof(HXX,predecessors,[HX]),
	gen_hdl(Pf,HY),
	rm_pos(HX,[HY]),
	assert(proof(HY,contents,CX)),
	assert(proof(HY,control,RX)),
	assert(proof(HY,status,S)),
	retract(proof([Pf,N0],predecessors,Pred)),
	assert(proof([Pf,N0],predecessors,[HY])),
	assert(proof(HY,predecessors,Pred)),
	raise_contra_case_below([Pf,N0],HXX),!.

/* End raise_small_cases/1 */

/* make_top_subproofs generates top level subproofs for formulas which are referenced several times. Use move_into_subproof to fill subproofs and remove trivial subproofs */


times_referenced(H,N) :- 
	bagof(H,P^R^PRefs^(proof(P,control,rule(R,PRefs)),member(H,PRefs)),PL),length(PL,N),!.
times_referenced(_,0).
top_references(L) :- bagof(N-H,R^A^(proof(H,status,proved),proof(H,control,rule(R,A)),times_referenced(H,N)),L1),keysort(L1,L2),reverse(L2,L),!.
top_references([]).
make_top_subproofs :- top_references(L),make_subproofs(L),!.
make_top_subproofs(Used) :- top_references(L),make_subproofs(L,Used),!.

make_subproofs([]) :-!,write("Proofs made\n").
make_subproofs([N-[Pf,_]|L]) :- N<5,!,last_in_proof(Pf,H),make_subproof(H),write("Proofs made\n").
make_subproofs([N-H|L]) :- make_subproof(H),make_subproofs(L).

make_subproofs([],_) :-!,write("Proofs made\n").
make_subproofs([N-[Pf,_]|L],Used) :- N<Used,!,last_in_proof(Pf,H),make_subproof(H),write("Proofs made\n").
make_subproofs([N-H|L],Used) :- make_subproof(H),make_subproofs(L,Used).

make_subproof(H) :- retract(proof(H,status,proved)),
	gen_hdl(NN),
	assert(proof(H,status,subproof(NN))),
	retract(proof(H,control,R)),
	assert(proof(H,control,rule([direct],[[NN,1]]))),
	PN=[NN,1],
	assert(proof(PN,predecessors,[])),
	assert(proof(PN,status,proved)),
	assert(proof(PN,control,R)),
	proof(H,contents,F),
	assert(proof(PN,contents,F)),!.

/* move_into_subproof verlegt Formeln die keine Annahmen sind und nur in einem Unterbeweis benutzt werden an den Anfang dieses Unterbeweises. */


move_into_subproof :- collect_proof_pars,
	repeat,mv_into_subproof,!.

mv_into_subproof :- 
	proof([Pf,global],goal,_),
	first_proof_line(Pf,H),
	mv_into_subproof(H).

mv_into_subproof(H) :- proof(H,status,proved),
	setof(Pf,only_in_subproof(H,Pf),[Pf1]),
	mv_into_subproof(H,Pf1),!,fail.
mv_into_subproof(H) :- next_line(H,H1),!,
	mv_into_subproof(H1),!.
mv_into_subproof(_).

mv_into_subproof(H,Pf) :-
	retract(proof([Pf,N],predecessors,[])),
	gen_hdl(NN),
	assert(proof([Pf,N],predecessors,[[Pf,NN]])),
	assert(proof([Pf,NN],predecessors,[])),
	change_refs(H,[Pf,NN]),
	retract(proof(H,contents,F)),
	assert(proof([Pf,NN],contents,F)),
	retract(proof(H,status,S)),
	assert(proof([Pf,NN],status,S)),
	retract(proof(H,control,C)),
	assert(proof([Pf,NN],control,C)),
	retract(proof(H,predecessors,P)),
	retract(proof(H1,predecessors,[H])),
	assert(proof(H1,predecessors,P)),
	retract(proof_pars(Pf,In_Tiefe,Hat_Tiefe,Groesse,ExtRefs)),
	Groesse1 is Groesse+1,
	C=..[_,_,Arg],
	strict_remove(H,ExtRefs,ExtRefs1),
	strict_union(Arg,ExtRefs1,ExtRefs2),
	assert(proof_pars(Pf,In_Tiefe,Hat_Tiefe,Groesse1,ExtRefs2)),
	change_used(H,[Pf,NN]),!.

change_used(H1,H2) :- retract(used_for(H1,H3)),
	once((
		change_refs(H1,[H3],H2),
		assert(used_for(H2,H3))
	)),fail.
change_used(H1,H2) :- retract(used_for(H3,H1)),assert(used_for(H3,H2)),fail.
change_used(_,_).


only_in_subproof([Pf,N],_) :- used_for([Pf,N],[Pf,_]),!,fail.
only_in_subproof(H,Pf) :- proof_pars(Pf,_I,_T,_G,E),member(H,E).


move_lines :-
	collect_proof_pars,
	% get size of the proof:
	proof([Pf,global],goal,_),
	proof_pars(Pf,_,_,Size,_),

	nl, write(move_lines_size_is(Size)), nl,

	(       Size > 160 ->	
						% block.pro uses predicate_size
						% of proof/3 > 500 [cw]
	        mv_lines
	;
	        move_lines_fd).


% move_lines schneller machen

mv_lines :-
	% collect_proof_pars, -  this is now done by move_lines
	retract_all(to_ins(_)),
	fail.
mv_lines :- proof([Pf,global],goal,_),
	proof([Pf,_N],status,subproof(_Pf1)),
	mv_lines(Pf),!.

mv_lines(Pf) :- proof([Pf,_],status,subproof(Pf1)),mv_lines(Pf1),fail.
mv_lines(Pf) :- last_in_proof(Pf,H),
	note_to_ins(H),
	setof([Pf,N],to_ins([Pf,N]),L),
	(
	ilf_state(ilf_serv,on)
	;
	length(L,NL),
	NL1 is NL - 2,
	thermo(NL1)
	),
	retract(to_ins(H)),
	mv_lines(Pf,H,HH),
	add_remaining_lines(Pf,HH,HHH),
	assert(proof(HHH,predecessors,[])),!.

add_remaining_lines(Pf,H,HH) :- retract(to_ins([Pf,N])),
	assert(proof(H,predecessors,[[Pf,N]])),
	(ilf_state(ilf_serv,on);write("*")),
	add_remaining_lines(Pf,[Pf,N],HH),!.
add_remaining_lines(_,H,H).

mv_lines(Pf,H,HH) :- proof(H,status,subproof(Pf1)),
	proof(H,control,rule(_,LR)),
	proof_pars(Pf1,_,_,_,Ext),
	append(LR,Ext,L),!,
	mv_lines(Pf,H,L,HH),!.
mv_lines(Pf,H,HH) :- (proof(H,control,rule(_,L));L=[]),
	mv_lines(Pf,H,L,HH),!.

mv_lines(Pf,H1,[H|L],H2) :- H \= [Pf,_],!,mv_lines(Pf,H1,L,H2),!.
mv_lines(Pf,H1,[H|L],H2) :- proof(H,status,assumption(_)),!,
	mv_lines(Pf,H1,L,H2),!.
mv_lines(Pf,H1,[H|L],H2) :- used_for(H,HH),to_ins(HH),!,
	mv_lines(Pf,H1,L,H2),!.
mv_lines(Pf,H1,[H|L],H2) :- proof([Pf,N],status,subproof(Pf1)),
	to_ins([Pf,N]),
	proof_pars(Pf1,_,_,_,Ext),
	member(H,Ext),
	mv_lines(Pf,H1,L,H2),!.
mv_lines(Pf,H1,[H|L],H2) :- 
	to_ins(H),
	assert(proof(H1,predecessors,[H])),
	(ilf_state(ilf_serv,on);write("*")),
	retract(to_ins(H)),!,
	mv_lines(Pf,H,HH),
	mv_lines(Pf,HH,L,H2),!.
mv_lines(Pf,H1,[_H|L],H2) :- mv_lines(Pf,H1,L,H2),!.
mv_lines(_Pf,H1,[],H1).

note_to_ins(H) :- assert(to_ins(H)),fail.
note_to_ins(H) :- proof(H,predecessors,[H1]),note_to_ins(H1).
note_to_ins([Pf,_]) :- retract_all(proof([Pf,_],predecessors,_)).


/*
% move_lines mit Chi-Funktion stillgelegt
move_lines :- collect_proof_pars,fail.
move_lines :- make_chi,fail.
move_lines :- proof([PfHdl,global],goal,_),
	proof([PfHdl,_],status,subproof(Pf)),
	move_lines(Pf).

*/


move_lines(Pf) :- last_block_line(Pf,H),
	move_lines_dn(H),!.

move_lines_dn([Pf,NN]) :-
	proof([Pf,N],predecessors,[]),
	move_lines([Pf,N],[Pf,NN]),fail.
move_lines_dn(H) :- proof(H,status,subproof(Pf)),move_lines(Pf),fail.
move_lines_dn(H) :- proof(H,predecessors,[H1]),move_lines_dn(H1),fail.
move_lines_dn(_).


move_lines(H,H) :- write(H),nl,!.
move_lines(H1,H) :- proof(H2,predecessors,[H1]),
	move_lines(H1,H2,H3,H),
	move_lines(H3,H),!.

move_lines(_H1,H,H,H) :- !.
move_lines(H1,H2,H2,_H) :- used_for(H1,H2),!.
move_lines(H1,H2,H2,_H) :- proof(H2,status,subproof(Pf)),
	proof_pars(Pf,_,_,_,L),member(H1,L),!.
move_lines(H1,H2,H2,_H) :- proof(H1,status,assumption(_)),!.
move_lines(H1,H2,H2,_H) :- chi(H1,Chi1),chi(H2,Chi2),
	Chi2 =< Chi1,!.
move_lines(H1,H2,H1,_H) :- write("."),retract(proof(H1,predecessors,V)),
	assert(proof(H1,predecessors,[H2])),
	retract(proof(H2,predecessors,_)),
	assert(proof(H2,predecessors,V)),
	retract(proof(H3,predecessors,[H2])),
	assert(proof(H3,predecessors,[H1])),!.

make_chi :- retract_all(chi(_,_)),fail.
make_chi :- proof(H,contents,_),make_chi(H),fail.
make_chi.

make_chi(H) :- proof(H,status,subproof(Pf)),
	proof_pars(Pf,_,_,S,_),
	Wt is S+1,
	get_in(H,A),
	get_out(H,F),
	Chi is (A-F)/Wt,
	assert(chi(H,Chi)),!.
make_chi(H) :- get_in(H,A),get_out(H,F),Chi is A - F,
	assert(chi(H,Chi)),!.

get_in(H,A) :- bagof(Q,used_line(Q,H),UsedFor),
	length(UsedFor,A),!.
get_in(_H,0).

used_line(Q,H) :- used_for(Q,H),
	is_line(Q).

is_line([Pf,_]) :- proof([Pf,global],goal,_),!,fail.
is_line(Q) :- proof(Q,control,axiom(_)),!,fail.
is_line(_).

get_out(H,F) :-
	bagof(R,used_for(H,R),UsedTo),
	length(UsedTo,F),!.
get_out(_H,0).


% Verschieben 
move_lines_fd :- ilf_serv_log(write("Moving lines to appropriate places.\n")),fail.
move_lines_fd :- proof([PfHdl,global],goal,_),
	proof([PfHdl,_],status,subproof(Pf)),
	move_lines_fd(Pf).

move_lines_fd(Pf) :- last_block_line(Pf,H),
	all_lines_fd(H,H),!.

all_lines_fd(A,A) :- 
	proof(A,status,subproof(Pf)),!,
	move_lines_fd(Pf),
	(
	proof(A,predecessor,[P]),
	all_lines_fd(P,A)
	;
	true
	),!.
all_lines_fd(A,A) :- proof(A,predecessors,[P]),
	all_lines_fd(P,A),!.
all_lines_fd(P,A) :-proof(P,predecessors,[Q]),
	move_line_fd(P,A),
	all_lines_fd(Q,A),!.
all_lines_fd(_P,_A).

last_block_line(Pf,H) :- proof([Pf,N],predecessors,[]),
	last_block_line(Pf,N,H).

last_block_line(Pf,N,H) :- proof([Pf,M],predecessors,[[Pf,N]]),
	last_block_line(Pf,M,H),!.
last_block_line(Pf,N,[Pf,N]).

move_line_fd(Quelle,Ziel) :- 
	bagof(H,used_for(Quelle,H),L),
	move_line_fd(Quelle,Quelle,L,Ziel),!.
move_line_fd(Quelle,_Ziel) :- 
	ilf_serv_log((
		write("ILF Warning: Line "),
		write(Quelle),
		write(" not used\n")
	)),
	once((
		ilf_state(ilf_serv,on)
		;
		write("Remove?\n"),
		read(y)
	)),
	proof(Quelle,predecessors,P),
	retract(proof(H,predecessors,[Quelle])),
	assert(proof(H,predecessors,P)),
	retract_all(proof(H,_,_)),!.

move_line_fd(Quelle,Ziel,L,Ziel) :- ins_before(Quelle,L,Ziel),!.
move_line_fd(Quelle,Akt,L,Ziel) :- next_usable_line(Akt,L,NAkt),
	move_line_fd(Quelle,NAkt,L,Ziel),!.
move_line_fd(Quelle,Akt,L,_Ziel) :- ins_after(Quelle,L,Akt),!.

next_usable_line(Akt,L,[Pf,H]) :- 
	proof(NAkt,predecessors,[Akt]),
	proof(NAkt,status,subproof(Pf)),
	proof([Pf,H],predecessors,[]),
	block_usable([Pf,H],L),!.
next_usable_line(Akt,L,NAkt) :- proof(NAkt,predecessors,[Akt]),
	block_usable(NAkt,L),!.

block_usable(N,[E|L]) :- block_1_usable(N,E),block_usable(N,L),!.
block_usable(_,[]).

block_1_usable(N,N) :- !,fail.
block_1_usable(N,E) :- proof(E,predecessors,[N]),!.
block_1_usable(N,E) :- proof(E,predecessors,[E1]),!,block_1_usable(N,E1).
block_1_usable(N,[PF,_]) :- proof(E1,status,subproof(PF)),
	block_1_usable(N,E1).

ins_before(Ins,_,Ins) :- !.
ins_before(Ins,NodeL,[Pf,H]) :- gen_hdl(Pf,NH),
	proof(Ins,control,rule(_,_)),
	retract(proof([Pf,H],predecessors,L)),
	assert(proof([Pf,H],predecessors,[NH])),
	retract(proof(Ins,predecessors,PIns)),
	(
	retract(proof(Q,predecessors,[Ins])),
	assert(proof(Q,predecessors,PIns))
	;
	true
	),
	assert(proof(NH,predecessors,L)),
	copy_node(Ins,NH,status),
	copy_node(Ins,NH,contents),
	copy_node(Ins,NH,control),
	change_refs(Ins,NodeL,NH),
	!.

ins_after(Ins,_,Ins) :- !.
ins_after(Ins,L,P) :- proof(Q,predecessors,[P]),
	ins_before(Ins,L,Q),!.
ins_after(Ins,L,[Pf,_]) :- proof(Q,status,subproof(Pf)),
	ins_before(Ins,L,Q),!.

gen_hdl(H) :- repeat,gensym("hdl",H),not proof([_,H],_,_),!.
gen_pf_hdl(Pf) :- repeat,gensym("pfhdl",Pf),not proof([Pf,_],_,_),!.

gen_hdl(Pf,[Pf,H]) :- gensym("hdl",H),
	not proof([Pf,H],_,_),!.

copy_node(N1,N2,Key) :- retract(proof(N1,Key,Val)),assert(proof(N2,Key,Val)),!.
copy_node(_,_,_).

change_refs(H,NH) :- bagof(HH,
	PL^R^(proof(HH,control,rule(R,PL)),member(H,PL)),
	HL),
	change_refs(H,HL,NH),!.
change_refs(_,_).

change_refs(Ins,[N|NodeL],NH) :- retract(proof(N,control,rule(R,L))),
	change_pos_lst(Ins,[NH],L,L1),
	assert(proof(N,control,rule(R,L1))),
	change_refs(Ins,NodeL,NH).
change_refs(_,[],_).

change_refs_l(Handles, H) :-
	member(HQ, Handles),
	change_refs(HQ, H),
	fail.
change_refs_l(_, _).

/* collect_proof_pars/0 erzeugt proof_pars/5 (exported in block) mit
	proof_pars(Pf,In_Tiefe,Hat_Tiefe,Groesse,ExtRefs)
   collect_proof_pars/0,2 ist als Tool implementiert und sucht proof/3
   in dem Modul, aus dem es aufgerufen wurde */

collect_proof_pars(Module) :- 
	% Initialisierung 
	retract_all(proof_pars(_,_,_,_,_)),
	retract_all(used_for(_,_)),
	call(proof([PfHdl,global],goal,_), Module),
	% Start 
	collect_proof_pars(PfHdl,0, Module),
	!.

collect_proof_pars(Pf,D1, Module) :- 
	call(proof([Pf,_],status,subproof(Pf1)), Module),
	D2 is D1+1,
	collect_proof_pars(Pf1,D2, Module),
	fail.
collect_proof_pars(Pf,D1, Module) :- 
	bagof([D,S,ER], is_proof_pars(Pf,D,S,ER,Module), L),
	make_proof_pars(Pf,D1,L,0,0,[]),!.

is_proof_pars(Pf,D,S,ER, Module) :- 
	call(proof([Pf,H],status,subproof(Pf1)), Module),
	proof_pars(Pf1,_,D,S,ER),
	call(proof([Pf,H],control,rule(_,Ref)), Module),
	make_used_for([Pf,H],Ref).
is_proof_pars(Pf,0,1,ER, Module) :- 
	call((
		proof([Pf,H],status,proved),
		proof([Pf,H],control,rule(_,ER))
	     ), Module),
	make_used_for([Pf,H],ER).
is_proof_pars(Pf,0,1,[], Module) :-
	call(proof([Pf,_H],status,assumption(_)), Module).
	
make_proof_pars(Pf,D1,[[D,S,ER]|L],D0,S0,ER0) :-
	D =< D0,!,
	S1 is S0+S,
	append(ER,ER0,ER1),
	make_proof_pars(Pf,D1,L,D0,S1,ER1).
make_proof_pars(Pf,D1,[[D,S,ER]|L],_D0,S0,ER0) :-
	S1 is S0+S+1,
	append(ER,ER0,ER1),
	make_proof_pars(Pf,D1,L,D,S1,ER1).
make_proof_pars(Pf,D1,[],D,S,ER) :-
	DD is D+1,
	(setof(H,H1^(member(H,ER),not (H=[Pf,H1])),ER1)
	;
	ER1=[]),
	assert(proof_pars(Pf,D1,DD,S,ER1)),!.
	
make_used_for(H,[H1|L]) :- 
	(used_for(H1,H);assert(used_for(H1,H))),
	make_used_for(H,L),!.
make_used_for(_,[]).


/* Erkennen trivialer Unterbeweise:
Typ 1: indirekt, Laenge 3, kein echter Unterbeweis
Typ 2: Direkt, Laenge 1
Typ 3: Indirekt, Laenge 3, direkter Unterbeweis
Typ 4: Indirekt, Laenge 3, indirekter Unterbeweis
*/


trivial_subproof((H/I)) :- proof(H,control,rule(R,[[Pf1,N1],[Pf1,N2]])),
	(R=[indirect];R=[in(not)]),
	proof([Pf1,N2],predecessors,[[Pf1,N3]]),
	proof([Pf1,N3],predecessors,[[Pf1,N1]]),
	proof([Pf1,N3],control,rule(_,L)),
	(not member([Pf1,N1],L)),
	trivial_ind_type([Pf1,N3],I),
	proof([Pf1,N3],contents,H3),
	proof(H,contents,HH),
	ilf_state(occur,O,on),
	once((
		unify(H3,HH),
		ilf_state(occur,_,O)
		;
		ilf_state(occur,_,O),fail
	)).
trivial_subproof((H/2)) :- proof(H,control,rule([direct],[H1])),
	proof(H1,predecessors,[]).

trivial_ind_type(H,1) :- not proof(H,status,subproof(_)),!.
trivial_ind_type(H,3) :- proof(H,control,rule([direct],_)),!.
trivial_ind_type(H,4) :- proof(H,control,rule([R],_)),(R=indirect;R=in(not)),!.

remove_trivial_subproofs :- ilf_serv_log(write("\nRemoving trivial subproofs\n")),fail.
remove_trivial_subproofs :- proof([Pf,global],goal,_),
	first_proof_line(Pf,H),
	remove_trivial_subproofs(H),!.

%
% remove_trivial_subproofs :- setof(H,trivial_subproof(H),L),
% 	collect_proof_pars,
%	hide_subproof_l(L),!.
% remove_trivial_subproofs :-
%       ilf_serv_log(write("There are no trivial subproofs to hide.\n")).
%

remove_trivial_subproofs(H) :- 
	once((
		proof(H,status,subproof(_Pf)),
		is_trivial_subproof(H,Typ),
		remove_trivial_subproof(H,Typ)
	)),fail.
remove_trivial_subproofs(H) :- next_line(H,H1),remove_trivial_subproofs(H1),!.
remove_trivial_subproofs(_).


is_trivial_subproof(H,[d,1]) :- proof(H,control,rule([direct],[P])),
	proof(P,predecessors,[]),!,contents_variant(H,P).
is_trivial_subproof(H,[d,2]) :- proof(H,control,rule([direct],[P])),
	proof(P,predecessors,[P1]),
	proof(P1,predecessors,[]),!,contents_variant(H,P).
is_trivial_subproof(H,[ind,2]) :- proof(H,control,rule(R,[_Ass,Cont|_])),
	(R=[indirect];R=[in(not)];R=[indirect_all(_)]),
	proof(Cont,predecessors,[P]),
	proof(P,predecessors,[]),!,
	contents_variant(P,H).
is_trivial_subproof(H,[ind,3]) :- proof(H,control,rule(R,[Ass,Cont|_])),
	(R=[indirect];R=[in(not)];R=[indirect_all(_)]),
	proof(Cont,predecessors,[P]),
	proof(P,predecessors,[Ass]),!,
	contents_variant(P,H),
	proof(P,status,subproof(_)),
	!.
is_trivial_subproof(H,[d,1]) :- proof(H,control,rule([direct_all(_)],[P])),
	proof(P,predecessors,[]),!.

remove_trivial_subproof(H,[T,L]) :- ilf_serv_log((
	write("Removing "),write(T),write("irect subproof with length "),
	write(L),write(" at "),write(H),nl
	)),fail.
% Ueberpruefen, ob am aeussersten Beweis Ersetzung moeglich ist: 
remove_trivial_subproof([Pf,N],T) :- proof([Pf,global],goal,_),
	not_removable([Pf,N],T),
	ilf_serv_log((
		write("Cannot remove outer subproof\n")
	)),!.
remove_trivial_subproof(H,[d,1]) :- 
	retract(proof(H,control,rule(_,[P]))),
	(proof(P,control,rule(R,L)) ->
	    assert(proof(H,control,rule(R,L)))
	; true),
	retract(proof(H,status,_)),
	(proof(P,status,S) ->
	    assert(proof(H,status,S))
	; true),
	retract_all(proof(P,_,_)),!.
remove_trivial_subproof(H,[d,2]) :-
	retract(proof(H,control,rule(_,[P]))),
	proof(P,predecessors,[P1]),
	gen_hdl(N1),
	H=[Pf,_],
	retract(proof(H,predecessors,PH)),
	assert(proof(H,predecessors,[[Pf,N1]])),
	assert(proof([Pf,N1],predecessors,PH)),
	proof(P1,contents,C1),
	assert(proof([Pf,N1],contents,C1)),
	(proof(P1,status,S) ->
	    assert(proof([Pf,N1],status,S))
	; true),
	(proof(P1,control,Co) ->
	    assert(proof([Pf,N1],control,Co))
	; true),
	change_refs(P1,[Pf,N1]),
	proof(P,control,rule(R,L)),
	assert(proof(H,control,rule(R,L))),
	retract(proof(H,status,_)),
	proof(P,status,SP),
	assert(proof(H,status,SP)),
	P=[PP,_],
	retract_all(proof([PP,_],_,_)),
	!.
remove_trivial_subproof(H,[ind,2]) :-
	retract(proof(H,control,rule(_,[_,PC]))),
	proof(PC,predecessors,[P]),
	(proof(P,control,rule(R,L)) ->
	    assert(proof(H,control,rule(R,L)))
	; true),
	retract(proof(H,status,_)),
	(proof(P,status,S) ->
	    assert(proof(H,status,S))
	; true),
	PC=[PP,_],
	retract_all(proof([PP,_],_,_)),!.
remove_trivial_subproof(H,[ind,3]) :- 
	proof(H,control,rule(RH,[Ass,Cont])),
	proof(Cont,predecessors,[P]),
	proof(P,control,rule([direct],[[Pf,N]])),
	gen_hdl(HA),
	retract(proof([Pf,N1Pf],predecessors,[])),
	assert(proof([Pf,N1Pf],predecessors,[[Pf,HA]])),
	assert(proof([Pf,HA],predecessors,[])),
	proof(Ass,contents,CA),
	assert(proof([Pf,HA],contents,CA)),
	proof(Ass,status,SAss),
	assert(proof([Pf,HA],status,SAss)),
	gen_hdl(HC),
	last_in_proof(Pf,NNPf),
	assert(proof([Pf,HC],predecessors,[NNPf])),
	translit(contradiction,Contradiction),
	assert(proof([Pf,HC],contents,Contradiction)),
	proof(Cont,status,SC),
	assert(proof([Pf,HC],status,SC)),
	(proof(Cont,control,R) ->
	    (    R=rule(RR,L),
	         change_pos_lst(P,[[Pf,N]],L,L1),
	         R1=rule(RR,L1)
	     ;   R1=R
	    ),
	    assert(proof([Pf,HC],control,R1))
	;   true
	),
	retract(proof(H,status,_)),
	assert(proof(H,status,subproof(Pf))),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule(RH,[[Pf,HA],[Pf,HC]]))),
	Cont=[PP,_],
	retract_all(proof([PP,_],_,_)),
	change_refs(Ass,[Pf,HA]),!.
remove_trivial_subproof(H,[ind,3]) :- 
	proof(H,control,rule(RH,[Ass,Cont])),
	proof(Cont,predecessors,[P]),
	proof(P,control,rule(RX,_)),
	proof_type(RX,indirect),
	proof(P,status,subproof(Pf)),
	gen_hdl(HA),
	retract(proof([Pf,N1Pf],predecessors,[])),
	assert(proof([Pf,N1Pf],predecessors,[[Pf,HA]])),
	assert(proof([Pf,HA],predecessors,[])),
	proof(Ass,contents,CA),
	assert(proof([Pf,HA],contents,CA)),
	proof(Ass,status,SAss),
	assert(proof([Pf,HA],status,SAss)),
	last_in_proof(Pf,NNPf),
	retract(proof(H,status,_)),
	assert(proof(H,status,subproof(Pf))),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule(RH,[[Pf,HA],NNPf]))),
	Cont=[PP,_],
	retract_all(proof([PP,_],_,_)),
	change_refs(Ass,[Pf,HA]),!.

remove_trivial_subproof(_H,_S) :- ilf_serv_log(write("Not successful\n")).

remove_last_directs :- bagof(H,last_direct(H),HL),
	collect_proof_pars,
	remove_last_direct_l(HL),!.
remove_last_directs.

last_direct(H) :- proof(H,control,rule([direct],[P])),
	once((
		not proof(_,predecessors,[H]),
		H=[Pf,_],
		not proof([Pf,global],goal,_),!,
		contents_variant(H,P)
	)).

remove_last_direct_l([H|HL]) :- remove_last_direct(H),
	(last_direct(H) -> HL1=[H|HL];HL1=HL),
	remove_last_direct_l(HL1),!.
	
remove_last_direct(H) :-
	proof(H,status,subproof(Pf)),
	proof([Pf,N],predecessors,[]),
	proof(H,control,rule(_,[P])),
	remove_last_direct(H,[Pf,N],P),!.

remove_last_direct(H,P,P) :- proof(P,control,rule(R,Arg)),
	retract(proof(H,control,_)),
	retract_all(used_for(_,H)),
	make_used_for(H,Arg),
	assert(proof(H,control,rule(R,Arg))),
	proof(P,status,S),
	retract(proof(H,status,_)),
	asserta(proof(H,status,S)),
	retract_all(proof(P,_,_)),!.
remove_last_direct(H,HP,P) :-
	H=[Pf,_],gen_hdl(Pf,HN),
	proof(HP,contents,C),
	assert(proof(HN,contents,C)),
	proof(HP,control,rule(R,Arg)),
	assert(proof(HN,control,rule(R,Arg))),
	make_used_for(HN,Arg),
	proof(HP,status,S),
	assert(proof(HN,status,S)),
	(S=subproof(_) -> retract(proof(HP,status,_)),
		assert(proof(HP,status,proved));true),
	retract(proof(H,predecessors,Pred)),
	assert(proof(HN,predecessors,Pred)),
	assert(proof(H,predecessors,[HN])),
	proof(HP1,predecessors,[HP]),
	rm_pos(HP,[HN]),
	remove_last_direct(H,HP1,P),!.


not_removable(H,[d,1]) :- !,
	proof(H,control,rule([direct],[P])),
	not proof(P,status,subproof(_)),!.
not_removable([_Pf,_N],[d,2]) :- !.
not_removable(H,[ind,2]) :-
	proof(H,control,rule(_,[_,PC])),
	proof(PC,predecessors,[P]),
	not proof(P,status,subproof(_)),!.
not_removable(_H,[ind,3]) :- !,fail.


contents_variant(H1,H2) :- proof(H1,contents,F1),proof(H2,contents,F2),!,
	numbervars(F1,1,N),numbervars(F2,1,N),F1=F2.

proof_type([indirect],indirect) :- !.
proof_type([in(not)],indirect) :- !.
proof_type([direct],direct) :- !.
proof_type(T,unknown) :- 
	ilf_serv_error((
		write("Ilf ERROR: Unknown proof type "),
		write(T),
		nl
	)),!.


hide_subproof_l([H|L]) :- hide_subproof(H),hide_subproof_l(L),!.
hide_subproof_l([]) :- new_readies.

hide_subproof(H/1) :- retract(proof(H,status,subproof(Pf))),
	proof([Pf,N1],predecessors,[]),
	proof([Pf,N2],predecessors,[[Pf,N1]]),
	proof([Pf,N2],control,R),
	asserta(proof(H,status,proved)),
	retract_all(proof(H,control,_)),
	asserta(proof(H,control,R)),
	retract_all(proof([Pf,_],_,_)),!.
hide_subproof(H/2) :- proof(H,status,subproof(Pf1)),
	proof([Pf1,N1],status,subproof(Pf2)),!,
	retract(proof(H,status,subproof(_))),
	asserta(proof(H,status,subproof(Pf2))),
	proof([Pf1,N1],control,R),
	retract(proof(H,control,_)),
	asserta(proof(H,control,R)),!.
hide_subproof(H/2) :- hide_subproof(H/1).
hide_subproof(H/3) :- 
	retract(proof(H,status,subproof(Pf1))),
	proof([Pf1,P],status,subproof(Pf2)),
	proof([Pf1,A],predecessors,[]),
	proof([Pf1,C],predecessors,[[Pf1,P]]),
	gen_hdl(HA),
	proof([Pf1,A],contents,As),
	assert(proof([Pf2,HA],contents,As)),
	proof([Pf1,A],status,SAs),
	assert(proof([Pf2,HA],status,SAs)),
	assert(proof([Pf2,HA],predecessors,[])),
	retract(proof([Pf2,N21],predecessors,[])),
	assert(proof([Pf2,N21],predecessors,[[Pf2,HA]])),
	proof([Pf1,P],control,rule([direct],L)),
	gen_hdl(HG),
	last_in_proof(Pf2,H2),
	proof([Pf1,P],contents,G),
	assert(proof([Pf2,HG],contents,G)),
	assert(proof([Pf2,HG],status,proved)),
	assert(proof([Pf2,HG],control,rule([since],L))),
	assert(proof([Pf2,HG],predecessors,[H2])),
	gen_hdl(HC),
	translit(contradiction,Contradiction),
	assert(proof([Pf2,HC],contents,Contradiction)),
	assert(proof([Pf2,HC],status,proved)),
	proof([Pf1,C],control,R),
	assert(proof([Pf2,HC],control,R)),
	assert(proof([Pf2,HC],predecessors,[Pf2,HG])),
	retract_all(proof([Pf1,_],_,_)),
	assert(proof(H,status,subproof(Pf2))),
	change_refs([Pf1,A],[Pf2,HA]),
	!.
hide_subproof(H/4) :-
	retract(proof(H,status,subproof(Pf1))),
	proof([Pf1,P],status,subproof(Pf2)),
	proof([Pf1,A],predecessors,[]),
	gen_hdl(HA),
	proof([Pf1,A],contents,As),
	assert(proof([Pf2,HA],contents,As)),
	proof([Pf1,A],status,SAs),
	assert(proof([Pf2,HA],status,SAs)),
	assert(proof([Pf2,HA],predecessors,[])),
	retract(proof([Pf2,N21],predecessors,[])),
	assert(proof([Pf2,N21],predecessors,[[Pf2,HA]])),
	proof([Pf1,P],control,R),
	retract(proof(H,control,_)),
	assert(proof(H,control,R)),
	retract_all(proof([Pf1,_],_,_)),
	assert(proof(H,status,subproof(Pf2))),
	change_refs([Pf1,A],[Pf2,HA]),
	!.
hide_subproof(X) :- ilf_serv_error((
	write("Ilf ERROR: "),
	write(hide_subproof(X)),
	nl
	)),fail.

remove_unused :- ilf_serv_log(write("\nRemoving unused formulas\n")),fail.
remove_unused :- proof([Pf,global],goal,_),
	last_in_proof(Pf,Thm),
	retract_all(used_proof_line(_)),
	assert(used_proof_line(Thm)),
	remove_unused(Thm),
	(ilf_state(ilf_serv,on);nl),!.

remove_unused(none) :- !.
remove_unused(H) :- used_proof_line(H),!,
	retract_all(used_proof_line(H)),
	(proof(H,control,rule(_,L)) ->
	    make_used_proof_line(L)
	; true),
	get_prev_line(H,H1),
	remove_unused(H1),!.
remove_unused(H) :- proof(H,status,subproof(Pf)),!,
	rm_subproof(Pf),
	get_prev_line(H,H1),
	rm_line(H),
	remove_unused(H1),!.
remove_unused(H) :- 
	get_prev_line(H,H1),!,
	rm_line(H),
	remove_unused(H1),!.
remove_unused(H) :- rm_line(H),!.

rm_line(H) :-
	retract(proof(H1,predecessors,[H])),
	proof(H,predecessors,PH),
	assert(proof(H1,predecessors,PH)),
	proof(H,contents,F),
	ilf_serv_log((
		write("Removing "),
		write(F),
		write(" at "),
		write(H),nl
	)),
	retract_all(proof(H,_,_)),!.
rm_line(H) :- proof(H,contents,F),
	ilf_serv_log((
		write("Removing "),
		write(F),
		write(" at "),
		write(H),nl
	)),
	retract_all(proof(H,_,_)),!.

rm_subproof(Pf) :- proof([Pf,_],status,subproof(Pf1)),rm_subproof(Pf1),fail.
rm_subproof(Pf) :- retract_all(proof([Pf,_],_,_)),
	retract_all(used_for(_,[Pf,_])),!.

get_prev_line(H,H1) :- proof(H,status,subproof(Pf)),last_in_proof(Pf,H1),!.
get_prev_line(H,H1) :- proof(H,predecessors,[H1]),!.
get_prev_line([Pf,_],H1) :- proof(HH,status,subproof(Pf)),
	get_prev_up(HH,H1),!.
get_prev_line(_,none).

get_prev_up(H,H1) :- proof(H,predecessors,[H1]),!.
get_prev_up([Pf,_],H1) :- proof(HH,status,subproof(Pf)),
	get_prev_up(HH,H1),!.

make_used_proof_line([E|L]) :- assert(used_proof_line(E)),
	make_used_proof_line(L).
make_used_proof_line([]).

% is_lemma/1 ueberprueft ob Zeile Lemma oder Theorem ist 
is_lemma([Pf,_]) :- proof([Pf,global],goal,_),!.

subproof_to_lemma(Hdl) :- proof(Hdl,status,subproof(Pf)),
	proof_pars(Pf,_,_,_,RL),
	retract(proof(Hdl,status,_)),
	asserta(proof(Hdl,status,proved)),
	retract_all(proof(Hdl,control,_)),
	proof([BP,global],goal,_),
	ass_contents_l(RL,RL1,CL),
	asserta(proof(Hdl,control,rule([lemma],[[BP,lemma(Pf)]|RL1]))),
	assert(used_for([BP,lemma(Pf)],Hdl)),
	proof(Hdl,contents,F),
	make_lemma_fla(RL1,CL,F,RL2n,RL2p,CL2n,CL2p,F1),
	ilf_state(occur,S,on),
	add_n_ass(Pf,RL2n,CL2n,RL2,AL,Rule,RL2p,CL2p),
	ilf_state(occur,_,S),
	chg_refs_in_subproof_l(Pf,RL2,AL),
	lemma_ins_pt(BP,HBP),
	retract(proof(HBP,predecessors,PHBP)),
	asserta(proof(HBP,predecessors,[[BP,lemma(Pf)]])),
	asserta(proof([BP,lemma(Pf)],predecessors,PHBP)),
	asserta(proof([BP,lemma(Pf)],contents,F1)),
	asserta(proof([BP,lemma(Pf)],status,subproof(Pf))),
	asserta(proof([BP,lemma(Pf)],control,Rule)),
	!.

make_lemma_fla(RL1,CL1,F,RL1,[lemma],CL1n,[F],F1) :- 
	(
	log_op(F,_),(not F=not(_))
	;
	F=..[Op|_],
	translit(IOp,Op),
	not IOp=Op,
	not IOp=not
	),!,
	serv_negate_l(CL1,CL1n),
	serv_list_fmla(CL1,[F],F1),!.
make_lemma_fla(RL1,CL1,F,RL2n,RL2p,CL2n,CL2p,F1) :- serv_negate_l(CL1,CL1N),
	make_lemma_fla1([lemma|RL1],[F|CL1N],RL2p,RL2n,CL2p,CL2n),
	serv_list_fmla(CL2n,CL2p,F1).

make_lemma_fla1([H|RL1],[NotG|CL1],RL2p,[H|RL2n],CL2p,[G|CL2n]) :- 
	translit(not,Not),
	NotG=..[Not,G],
	!,
	make_lemma_fla1(RL1,CL1,RL2p,RL2n,CL2p,CL2n),!.
make_lemma_fla1([H|RL1],[G|CL1],[H|RL2p],RL2n,[G|CL2p],CL2n) :- !,
	make_lemma_fla1(RL1,CL1,RL2p,RL2n,CL2p,CL2n),!.
make_lemma_fla1([],[],[],[],[],[]).


/* Regel A1,...,An,not(A1'),...,not(Am') => not(B), so A1,...,B,...,An -> A1';...;Am' */


add_n_ass(Pf,[lemma|RL2n],[C|CL2n],RL2,AL,rule([indirect],[[Pf,HPf],[Pf,H1]|AL]),RL2p,CL2p) :- translit(contradiction,Contradiction),
	proof([Pf,H1],contents,Contradiction),
	proof([Pf,HPf],contents,FF),unify(C,FF),!,
	add_n_ass(Pf,RL2n,CL2n,RL2,AL,_,RL2p,CL2p),!.
add_n_ass(Pf,[lemma|RL2n],[C|CL2n],RL2,AL,rule([indirect],[HA,HC|AL]),RL2p,CL2p) :- !,
	last_in_proof(Pf,Hc),
	% Wenn Ziel nicht da, so als bewiesen dahintersetzen 
	translit(not,Not),
	(
	NotFF=..[Not,FF],
	proof([Pf,Hdl],contents,NotFF),unify(C,FF),Hc1=Hc
	;
	gen_hdl(Hdl),
	NotC=..[Not,C],
	asserta(proof([Pf,Hdl],contents,NotC)),
	asserta(proof([Pf,Hdl],status,proved)),
	proof(HPf,status,subproof(Pf)),
	(proof(HPf,control,rule(_,Args));Args=[]),
	asserta(proof([Pf,Hdl],control(propositional_logic,Args))),
	asserta(proof([Pf,Hdl],predecessors,[Hc])),
	Hc1=[Pf,Hdl]
	),
	% Negiertes Ziel annehmen 
	gen_hdl(HAS),
	HA=[Pf,HAS],
	asserta(proof(HA,contents,C)),
	asserta(proof(HA,status,assumption([]))),
	gen_hdl(HCS),
	HC=[Pf,HCS],
	translit(contradiction,Contradiction),
	asserta(proof(HC,contents,Contradiction)),
	asserta(proof(HC,status,proved)),
	asserta(proof(HC,control,rule([in(contradiction)],[[Pf,Hdl],HA]))),
	add_n_ass(Pf,RL2n,CL2n,RL2,AL,_,RL2p,CL2p),!.
add_n_ass(Pf,[R|RL2n],[C|CL2n],[R|RL2],[HH|AL],Rule,RL2p,CL2p) :-
	gen_hdl(Hdl),
	HH=[Pf,Hdl],
	asserta(proof(HH,contents,C)),
	asserta(proof(HH,status,assumption([]))),
	retract(proof([Pf,H1],predecessors,[])),
	asserta(proof([Pf,H1],predecessors,[HH])),
	asserta(proof(HH,predecessors,[])),
	add_n_ass(Pf,RL2n,CL2n,RL2,AL,Rule,RL2p,CL2p),!.
add_n_ass(Pf,[],[],RL,AL,Rule,RL2p,CL2p) :- !,
	add_p_ass(Pf,RL2p,CL2p,RL,AL,Rule),!.
add_n_ass(_Pf,R,C,_,_,_,_,_) :- 
	ilf_serv_error((
		write("ILF ERROR: add_n_ass:"),
		write(R),nl,write(C),nl
	)),fail.


/* Regel A1,...,An,not(A1'),...,not(Am') => B, so A1,...,An -> A1';...;B;..;Am' */


add_p_ass(Pf,[lemma|RL2p],[C|CL2p],RL2,AL,rule([indirect],[[Pf,HPf],[Pf,H1]|AL])) :- 
	translit(contradiction,Contradiction),
	proof([Pf,H1],contents,Contradiction),
	translit(not,Not),
	NotFF=..[Not,FF],
	proof([Pf,HPf],contents,NotFF),unify(C,FF),!,
	add_p_ass(Pf,RL2p,CL2p,RL2,AL,_),!.
add_p_ass(Pf,[lemma|RL2p],[C|CL2p],RL2,AL,rule([direct],[[Pf,HPf]|AL])) :- 
	proof([Pf,HPf],contents,FF),unify(C,FF),!,
	(proof([Pf,HPf1],predecessors,[[Pf,HPf]]) -> 
	    rm_proof_at([Pf,HPf1])
	; true),
	add_p_ass(Pf,RL2p,CL2p,RL2,AL,_),!.
add_p_ass(Pf,[lemma|_RL2p],[C|_CL2p],RL2,AL,rule([direct],[[Pf,Hdl]|AL])) :- !,
	last_in_proof(Pf,Hc),
	gen_hdl(Hdl),
	asserta(proof([Pf,Hdl],contents,C)),
	asserta(proof([Pf,Hdl],status,proved)),
	proof(HPf,status,subproof(Pf)),
	(proof(HPf,control,rule(_,Args));Args=[]),
	asserta(proof([Pf,Hdl],control(propositional_logic,Args))),
	asserta(proof([Pf,Hdl],predecessors,[Hc])),
	add_p_ass(Pf,_RL2n,_CL2n,RL2,AL,_),!.
add_p_ass(Pf,[R|RL2n],[C|CL2n],[R|RL2],[HH|AL],Rule) :-
	gen_hdl(Hdl),
	HH=[Pf,Hdl],
	translit(not,Not),
	NotC=..[Not,C],
	asserta(proof(HH,contents,NotC)),
	asserta(proof(HH,status,assumption([]))),
	retract(proof([Pf,H1],predecessors,[])),
	asserta(proof([Pf,H1],predecessors,[HH])),
	asserta(proof(HH,predecessors,[])),
	add_p_ass(Pf,RL2n,CL2n,RL2,AL,Rule),!.
add_p_ass(_Pf,[],[],[],[],_) :- !.
add_p_ass(_Pf,R,C,_,_,_) :- 
	ilf_serv_error((
		write("ILF ERROR: add_p_ass:"),
		write(R),nl,write(C),nl
	)),fail.

rm_proof_at([Pf,H]) :- once(proof([Pf,H1],predecessors,[[Pf,H]])),
	rm_proof_at([Pf,H1]),fail.
rm_proof_at(H) :- proof(H,status,subproof(Pf)),
	proof([Pf,H1],predecessors,[]),
	rm_proof_at([Pf,H1]),fail.
rm_proof_at(H) :- retract_all(proof(H,_,_)).


chg_refs_in_subproof_l(Pf,[R|RL],[A|AL]) :- chg_refs_in_subproof(Pf,R,A),
	chg_refs_in_subproof_l(Pf,RL,AL).
chg_refs_in_subproof_l(_,[],[]).

chg_refs_in_subproof(Pf,R,A) :- retract(used_for(R,[Pf,H])),
	once((
		retract(proof([Pf,H],control,rule(Rule,L))),
		change_pos_lst(R,[A],L,L1),
		asserta(proof([Pf,H],control,rule(Rule,L1))),
		assert(used_for(A,[Pf,H]))
	)),fail.
chg_refs_in_subproof(Pf,R,A) :- proof([Pf,_],status,subproof(Pf1)),
	chg_refs_in_subproof(Pf1,R,A),fail.
chg_refs_in_subproof(_,_,_).

	
lemma_ins_pt(BP,H) :- proof([BP,H1],predecessors,[]),
	lemma_ins_pt1([BP,H1],H),!.

lemma_ins_pt1(HH,H) :- 
	proof(HH1,predecessors,[HH]),
	lemma_ins_pt1(HH1,H),!.
lemma_ins_pt1(HH,HH).

ass_contents_l([H|HL],PL,CL) :- proof(H,control,axiom(_)),
	ass_contents_l(HL,PL,CL),!.
ass_contents_l([H|HL],PL,CL) :- is_lemma(H),
	ass_contents_l(HL,PL,CL),!.
ass_contents_l([H|HL],[H|PL],[C|CL]) :- proof(H,contents,C),
	ass_contents_l(HL,PL,CL),!.
ass_contents_l([],[],[]).

reduce_depth :- write("Reducing proof depth to ? (Number.)\n"),
	read(N),number(N),
	reduce_depth(N),!.

reduce_depth(N) :- ilf_serv_log((
	write("\nReducing proof depth to "),
	write(N),
	nl
	)),
	collect_proof_pars,
	fail.
reduce_depth(N) :- proof([Pf,global],goal,_),
	proof_pars(Pf,_,D,_,_),D1 is D-1,
	D1 =< N,
	ilf_serv_log((
		write("Proof depth is "),
		write(N),nl
	)),!.
reduce_depth(N) :- reduce_depth1(N),
	ilf_serv_log(
		write("Lemma generated\n")
	),
	collect_proof_pars,
	reduce_depth(N).
reduce_depth(_) :- 
	ilf_serv_log(
		write("No appropriate lemma found.\n")
	),!.

reduce_depth1(N) :- 
	bagof((DD,D2,Pf1),lemma_cand(N,DD,Pf1,D2),L),
	sort(0,>=,L,[(_,_,Pf0)|_]),
	proof(H,status,subproof(Pf0)),
	subproof_to_lemma(H).

lemma_cand(N,DD,Pf,D2) :- proof_pars(Pf,D1,D2,_,Ext),D2 =< N, N < D1, DD is D1+D2,length(Ext,LExt),LExt < 4.

rew_neg_clauses :- ilf_serv_log(write("Rewriting negative clause heads\n")),fail.
rew_neg_clauses :- neg_clause_template(T,T1),retract(proof(P,contents,T)),
	assert(proof(P,contents,T1)),fail.
rew_neg_clauses :- translit(false,False),
	translit('->',Imp),
	translit(not,Not),
	I=..[Imp,F,False],
	retract(proof(H,contents,I)),
	(F=..[Not,FF] -> NotF=FF;
	NotF=..[Not,F]),
	assert(proof(H,contents,NotF)),fail.
rew_neg_clauses.

neg_clause_template(imp(tSign(A),contradiction),fSign(A)).
neg_clause_template(imp(fSign(A),contradiction),tSign(A)).
neg_clause_template(I,NotF) :- 
		translit(false,False),
		translit('->',Imp),
		translit(not,Not),
		I=..[Imp,F,False],
		(F=..[Not,FF] -> NotF=FF;
		NotF=..[Not,F]).

/* unique_references/0 verhindert, dass Referenzen doppelt genannt werden */


unique_references :- retract_all(the_references(_,_,_)),fail.
unique_references :- retract(proof(H,control,rule(R,A))),
	make_unique1(A,A1),
	assert(the_references(H,R,A1)),
	fail.
unique_references :- retract(the_references(H,R,A)),
	assert(proof(H,control,rule(R,A))),
	fail.
unique_references.

/*********************************************
	Universeller Abschluss aller Formeln
*********************************************/

allcloseForms :-
	write("Universal Closure\n"),
 	proof([Pf,N],predecessors,_),
	once((
		retract(proof([Pf,N],contents,Contents)),
		a_close(Contents,NewCont),
		assert(proof([Pf,N],contents,NewCont)),
		write("*")
	)),
	fail.
allcloseForms.

/* Integriert die aktuelle Theorie in proof/3 */


make_proof_theory :- setof([H,Name],proof(H,control,axiom(Name)),AxList),
	make_proof_theory_l(AxList),
	make_proof_theory_h,
	assert(proof([ilftheory,equality],status,theory(equality))),!.

make_proof_theory_l([[H,ref]|AxList]) :- 
	retract_all(proof(H,predecessors,_)),
	assert(proof(H,predecessors,[[ilftheory,equality]])),
	make_proof_theory_l(AxList),!.
make_proof_theory_l([[H,sym]|AxList]) :-
	retract_all(proof(H,predecessors,_)),
	assert(proof(H,predecessors,[[ilftheory,equality]])),
	make_proof_theory_l(AxList),!.
make_proof_theory_l([[H,trans]|AxList]) :-
	retract_all(proof(H,predecessors,_)),
	assert(proof(H,predecessors,[[ilftheory,equality]])),
	make_proof_theory_l(AxList),!.
make_proof_theory_l([[H,split(_,_)]|AxList]) :-
	retract_all(proof(H,predecessors,_)),
	assert(proof(H,predecessors,[[ilftheory,equality]])),
	make_proof_theory_l(AxList),!.
make_proof_theory_l([[H,Name]|AxList]) :- 
	setof(T,in_theory(T,Name),TL),
	make_ax_pred(H,TL),
	make_proof_theory_l(AxList),!.
make_proof_theory_l([_|AxList]) :- make_proof_theory_l(AxList),!.
make_proof_theory_l([]).

make_ax_pred(H,TL) :- add_1(ilftheory,TL,L),
	retract_all(proof(H,predecessors,_)),
	assert(proof(H,predecessors,L)),!.
	
add_1(H,[E|L],[[H,E]|L1]) :- add_1(H,L,L1),!.
add_1(_,[],[]). 

make_proof_theory_h :- setof(T,theory(T),TL),
	make_proof_theory_h_l(TL),!.

make_proof_theory_h_l([T|TL]) :- 
	assert(proof([ilftheory,T],status,theory(T))),
	(setof(T1,subtheory(T1,T),TTL);TTL=[]),
	add_1(ilftheory,TTL,TTL1),
	assert(proof([ilftheory,T],predecessors,TTL1)),
	make_proof_theory_h_l(TL),!.
make_proof_theory_h_l([]).

proof_subtheory([H|_],T) :- proof(H,status,theory(T)),!.
proof_subtheory([H|_],T) :- proof(H,predecessors,HL),proof_subtheory(HL,T),!.
proof_subtheory([_|HL],T) :- proof_subtheory(HL,T),!.


first_proof_line(Pf,H) :- 
	proof([Pf,N],predecessors,[]),
	first_proof_line(Pf,N,H),!.
first_proof_line(Pf,_) :- ilf_serv_error((
	write("Ilf ERROR: No line in proof "),
	write(Pf),
	write(" with empty predecessor list\n")
	)),fail.

first_proof_line(Pf,N,H) :-
	proof([Pf,N],status,subproof(Pf1)),!,
	first_proof_line(Pf1,H),!.
first_proof_line(Pf,N,[Pf,N]).


next_line(Node1,Node2) :- 
	% Nachfolger existiert im selben Teilbeweis 
	proof(Node3,predecessors,[Node1]),
	% Sonderbehandlung wenn Teilblock 
	lookup(Node3,Node2),!.
% Sonst zurueck zum Oberbeweis 
next_line([Pf,_],Node2) :- proof(Node2,status,subproof(Pf)),
	!.

lookup(Node1,Node2) :- 
	% Erste Zeile finden wenn Teilbeweis 
	proof(Node1,status,subproof(Pf)),
	proof([Pf,H],predecessors,[]),
	lookup([Pf,H],Node2).
% Sonst aendert sich nichts 
lookup(Node,Node).

block_top :- write("Tools for Block Proofs 1.68 (12/12/98) installed\n").


:- block_top.

/*OTTER */

/* ##########                   O2BL                      ########### */

/* O2BL uebersetzt otter-Beweise in den Blockkalkuel, dazu muss proof/3 
   im current_input/output_module vorhanden sein. 
   Nach Ausfuehrung des Praedikates (kann dauern!) steht ein Blockbeweis 
   als proof/3 zur Verfuegung  */ 


:- dynamic                   % local in "O2BL"
	ax_count/1,
	ax_handle/2,
	goal_handle/2,
	node_count/1,
	proofhandle/1,
	oproof/3.


o2bl :-
    o_ini,
    o_dupli_proof,
	spy_ilf,
    o_construct_ini,
    o_construct_ax,
    o_construct_proof,
    o_construct_po,
    retract(proof([X,global],goal,H)),
    e_close(H,H1),
    asserta(proof([X,global],goal,H1)),
    false2contra,
	o_deny,
    !.


/* "Aufraeumen" */


o_ini:-
    retract_all(oproof(_,_,_)),
    retract_all(proofhandle(_)),
    retract_all(node_count(_)),
    retract_all(ax_count(_)),
    retract_all(ax_handle(_,_)),
    !.


/* Kopieren von proof/3 in oproof/3, das Proofhandle steht danach als
   proofhandle/1 zur Verfuegung. node_count/1 gibt die Nummer des zuletzt
   gefundenen Knotens an, ax_count/1 die Nummer des zuletzt gefundenen
   Axioms (dabei wird beruecksichtigt, dass die Handle fuer Axiome 
   ggf. die Form ax(Nr) haben */


o_dupli_proof:-
    once((
	proof([PH,_],_,_),
	assert(proofhandle(PH))
    )), fail.
o_dupli_proof:-
    assert(ax_count(1)),
    assert(node_count(1)),
    retract(proof([PH,NH],Y,Z)),
    once((
	count_nodes(NH),
	AxH=NH,
	count_ax(AxH,Y,Z),
	assert(oproof([PH,NH],Y,Z))
    )),
    fail.
o_dupli_proof :- proofhandle(PH),
	assert(oproof([PH,global],control,ready)),
	assert(oproof([PH,global],system,otter)),!.

count_nodes(NH) :-
    number(NH),
    % AxH is abs(NH),
    count(node_count,NH).
count_nodes(_NH).

count_ax(ax(NH),status,axiom(_)) :-
    count(ax_count,NH).
count_ax(NH,status,axiom(_)) :-
    count(ax_count,NH).
count_ax(_,_,_).

count(Pred,H) :-
    number(H),
    Old=..[Pred,Max],
    call(Old),
    Max<H,
	functor(Term,Pred,1),
    retractall(Term),
    New=..[Pred,H],
    assert(New).
count(_,_).


/* Konstruktion des Anfanges: 
   Das Ziel wird durch einen indirekten Beweis der Zielklausel bewiesen.
   Als Ziel wird dabei entweder das Axiom mit Namen goal oder das
   Axiom mit der groessten Nummer angesehen. */


o_construct_ini :-
    proofhandle(PH),
    get_system(PH,System1),
    strict_union(System1,[ilf],System2),
    assert(proof([PH,global],system,System2)),
    assert(proof([PH,global],status,proved)),
    assert(proof([PH,global],control,ready)),
   o_preserve_global_controls,
    (
	 oproof([PH,GoalH],status,axiom(goal))
    ;
     ax_count(N),
     (GoalH=ax(N), 
      oproof([PH,GoalH],status,axiom(_))
      ;
      GoalH=N
     )
    ),
    oproof([PH,GoalH],contents,NGoal),
    a_close(NGoal,A_ClosedGoal),	
    assert(proof([PH,1],contents,A_ClosedGoal)),
	assert(proof([PH,global],goal,A_ClosedGoal)),
    assert(proof([PH,1],predecessors,[])),
    assert(proof([PH,1],status,subproof(sub(PH,1)))),
    node_count(Last),    		 
    assert(proof([PH,1],control,rule([indirect],[[sub(PH,1),GoalH],[sub(PH,1),Last]]))),
    o_negate(A_ClosedGoal,NegA_ClosedGoal),
    assert(proof([sub(PH,1),GoalH],contents,NegA_ClosedGoal)),
    assert(proof([sub(PH,1),GoalH],predecessors,[])),
    assert(proof([sub(PH,1),GoalH],status,assumption([]))),
    assert(goal_handle([PH,GoalH],[sub(PH,1),GoalH])),
    setval(o2bl_last_line,GoalH),
    !.

/* o_deny/0 changes reference of negated goal with new constants to assumption of subproof */
o_deny :- proof(PD,control,rule([deny(_)],[_])),
	proof(_, control, rule([indirect], [AssH|_])),
	retract(proof(PD,control,_)),
	assert(proof(PD,control,rule([let],[AssH]))),fail.
o_deny.

o_negate(not(X),X) :- !.
o_negate((X,Y),(NotX;NotY)) :- !, o_negate(X,NotX), o_negate(Y,NotY).
o_negate((X;Y),(NotX,NotY)) :- !, o_negate(X,NotX), o_negate(Y,NotY).
o_negate(ex(X,F),all(X,NotF)) :- !, o_negate(F,NotF).
o_negate(all(X,F),ex(X,NotF)) :- !, o_negate(F,NotF).
o_negate(X,not(X)).


/* Die in der Liste angegebenen global controls werden in den Blockbeweis
   uebernommen. */


o_preserve_global_controls :-
     oproof([PH,global],control,Control),
     once(member(Control,[
	 goal_name(_),               
	 used_goal(_),
	 constants(_)
     ])),
     assert(proof([PH,global],control,Control)),
     fail.
o_preserve_global_controls.


/* Nach den Regeln des Blockkalkuels muss jedes Axiom seinen eigenen
   Teilbeweis haben.  Fuer den Aufbau der Verweise wird das Praedikat
   ax_handle(altesHandle,neuesHandle) aufgebaut. Nachdem alle Axiome 
   konstruiert sind, wird das  negierte Ziel als Axiom entfernt und 
   ax_handle entsprechend veraendert. */


o_construct_ax :-
    oproof([PH,H],status,axiom(Name)),
    once((
	(H=ax(N) ; H=N), 
	HH=[ax(PH,N),0],
	oproof([PH,H],contents,Ax),
	assert(proof(HH,contents,Ax)),
	assert(proof(HH,predecessors,[])),
	assert(proof(HH,status,proved)),
	assert(proof(HH,control,axiom(Name))),
	assert(ax_handle([PH,H],HH))
    )),
    fail.
o_construct_ax :-
    goal_handle(Old,New),
    retract(ax_handle(Old,New1)),
    retract_all(proof(New1,_,_)),
    fail.
o_construct_ax :-
    retract(goal_handle(Old,New)),
    assert(ax_handle(Old,New)).


/* Der Blockbeweis besteht aus den gleichen Zeilen wie der urspruengliche
   Otter-Beweis ohne die Axiome.
   Die otter-Status-Informationen ("justification list") werden dabei
   in rule-controls umgesetzt (stat2ctl/2). */


o_construct_proof :-
    setval(o2bl_line_count,0),
    node_count(Last),
	oproof([PH,Count],contents,Contents),
	once((
		oproof([PH,Count],status,Status),
		not (Status=axiom(_)),
		incval(o2bl_line_count),
		stat2ctl([PH,Count],Status,Control),
		assert(proof([sub(PH,1),Count],contents,Contents)),
		getval(o2bl_last_line,LastLine),
		setval(o2bl_last_line,Count),
		assert(proof([sub(PH,1),Count],predecessors,[[sub(PH,1),LastLine]])),
		assert(proof([sub(PH,1),Count],status,proved)),
		assert(proof([sub(PH,1),Count],control,Control)),
		(
		 oproof([PH,Count],control,proof_object([Job,po(N)])),
		 assert(proof([sub(PH,1),Count],control,proof_object([po(Job),N])))
		 ;
		 true
		)
    )),
    Count=Last,
    translit(contradiction,Contradiction),
    retract(proof([sub(PH,1),Last],contents,_)),
    assert(proof([sub(PH,1),Last],contents,Contradiction)).


/* stat2ctl/3,4 wandelt die Status-Informationen des otter-Beweises
   ("justification list") in control-Informationen fuer den Blockbeweis.  */
/* Changed after putting rule geration into convert.pl */
% stat2ctl(_,_,_) :- spy_ilf,fail.
% stat2ctl(_,rule([intro],[[1,ax(N)]]),rule([intro],[[ax(1,N),0]])) :- !.
stat2ctl(_,rule([intro],[OldH]),rule([intro],[NewH])) :- ax_handle(OldH,NewH),!.
stat2ctl(_,rule(R,P),rule(R,P1)) :- setof([sub(1,1),N],member([1,N],P),P1),!.
stat2ctl(_,rule(R,_),rule(R,[])) :- !.

stat2ctl(H,Status,rule(Rules,Handles)) :-
    stat2ctl(H,Status,Rules,Handles,_).
stat2ctl(H,Status,rule(unknown)) :-
    writeln("Warning: unknown status `%' for node %",[Status,H]).        

stat2ctl(_,[],[],[],[]).
stat2ctl(NH,[clausify|Status],[clausify|Rules],[AxH|Handles],[]) :-
    (oproof(NH,predecessors,[OAxH]) ; oproof(NH,predecessors,[_,OAxH])),
    ax_handle(OAxH,AxH),
    stat2ctl(NH,Status,Rules,Handles,_).
stat2ctl(NH,[intro|Status],[intro|Rules],[AxH|Handles],[]) :-
    (oproof(NH,predecessors,[OAxH]) ; oproof(NH,predecessors,[_,OAxH])),
    ax_handle(OAxH,AxH),
    stat2ctl(NH,Status,Rules,Handles,_).
stat2ctl(_NH,[[flip,Param]],[flip(Param)],[],[]).

stat2ctl(NH,[[H|Params1]|Status],Rules,[[sub(PH,1),H]|Handles],Params) :-
    proofhandle(PH),
    stat2ctl(NH,Status,Rules,Handles,Params0),
    append(Params1,Params0,Params).
stat2ctl(NH,[H|Status],Rules,[[sub(PH,1),H]|Handles],[1|Params]) :-
    number(H),
    proofhandle(PH),
    stat2ctl(NH,Status,Rules,Handles,Params).
stat2ctl(NH,[RuleOp|Status],[Rule|Rules],Handles,[]) :-
	atom(RuleOp),!,
    proofhandle(PH),
    stat2ctl(NH,Status,Rules,Handles,Params),
    Rule=..[RuleOp,Params].
% For Prover9
stat2ctl(NH,[Rule|Status],[Rule|Rules],Handles,[]) :-
    proofhandle(PH),
    stat2ctl(NH,Status,Rules,Handles,Params).


/* o_construct_po/0 uebernimmt die (evtl. vorhandenen) Proof-Objekte in
   einen separaten Blockbeweis (Proof-Handle = po(Block-Proof-Handle)).
   Die Anpassung der proof_object-Controls ist schon in o_construct_proof
   passiert. */


o_construct_po :-
   oproof([Job,po(N)],control,proof_object),
   once((
       oproof([Job,po(N)],status,Status),
       oproof([Job,po(N)],contents,Contents),
       oproof([Job,po(N)],predecessors,Pred),
       po_new_handle([Job,po(N)],NewH),
       po_stat2ctl([Job,po(N)],Status,Control),
       po_new_pred(Pred,NewPred),
       assert(proof(NewH,status,proved)),
       assert(proof(NewH,control,Control)),
       assert(proof(NewH,contents,Contents)),
       assert(proof(NewH,predecessors,NewPred))
   )),
   fail.
o_construct_po :- 
    proof(_,control,proof_object(_)),
    po2subproof.
o_construct_po.

po_new_handle([Job,po(N)],[po(Job),N]) :- !.
po_new_handle(H,_) :-
    writeln("Warning: unknown proof object handle `%'.",[H]),
    !, fail.

po_stat2ctl([_Job,_],input,rule(input)).
po_stat2ctl([Job,_],instantiate(N,SubstList),
	            rule(instantiate(SubstList),[[po(Job),N]])).
po_stat2ctl([Job,_],merge(N,NLit),rule(merge(NLit),[[po(Job),N]])).
po_stat2ctl([Job,_],resolve(N1,NLit1,N2,NLit2),
		    rule(resolve(NLit1,NLit2),[[po(Job),N1],[po(Job),N2]])).

po_stat2ctl([Job,_],flip(N,NLit),rule(flip(NLit),[[po(Job),N]])).
po_stat2ctl([Job,_],paramod(N1,NLits1,N2,NLits2),rule(paramod(NLits1,NLits2),[[po(Job),N1],[po(Job),N2]])).

po_stat2ctl(H,Status,_) :-
    writeln("Warning: unknown proof object status `%' (node %)",[Status,H]),
    !, fail.

po_new_pred([],[]).
po_new_pred([P],[PP]) :- po_new_handle(P,PP).


/* po2subproof/0 fuegt die Proof-Objekte als Unterbeweise in einen
   Blockbeweis ein. Wenn einer Zeile des Blockbeweises genau ein
   Proofobjekt entspricht, wird auf die Einfuegung verzichtet. */


po2subproof :-
    proof([sub(Job,1),N],status,proved),
    po2subproof([sub(Job,1),N]),
    fail.    
po2subproof :-
    retract_all(proof(_,control,proof_object(_))).


po2subproof(H) :-
    proof(H,control,proof_object(POH)), 
    !,
    proof_objects(POH,[POH],POL),
    (length(POL,1)
     ;
     po2subproof(H,POL,[],1)
    ),
    !.
po2subproof(H) :- 
    writeln("Warning: No proof object for node %",[H]).


proof_objects(H,L,LL) :-
    proof(H,predecessors,[Pred]),
    not(proof(_,control,proof_object(Pred))),
    proof_objects(Pred,[Pred|L],LL).
proof_objects(_H,L,L). 


po2subproof(H,[],LastPO,_) :-
    H=[sub(Job,_),N],
    retract(proof(H,status,proved)),
    retract(proof(H,control,rule(_,_))),
    assert(proof(H,status,subproof(sub(Job,po(N))))),
    assert(proof(H,control,rule([direct],LastPO))).
po2subproof([sub(Job,_),N],[POH|R],Pred,PON) :- 
    proof(POH,contents,C),
    proof(POH,control,rule(Rule,Handles)),
    HH=[sub(Job,po(N)),PON],
    handle_po2bl([sub(Job,po(N)),PON],POH,Handles,BHandles),
    assert(proof(HH,contents,C)),
    assert(proof(HH,status,proved)),
    assert(proof(HH,control,rule([Rule],BHandles))),
    assert(proof(HH,predecessors,Pred)),
    PON1 is PON+1,
    po2subproof([sub(Job,_),N],R,[HH],PON1).


handle_po2bl(_,_,[],[]).
handle_po2bl(HNew,HOld,[H|R],[BH|BR]) :- 
    proof(BH,control,proof_object(H)),
    handle_po2bl(HNew,HOld,R,BR).
handle_po2bl([sub(Job,po(N)),N0],[_,PON0],[[_,PON1]|R],[[sub(Job,po(N)),N1]|BR]) :- 
    N1 is PON1-PON0+N0, 
    handle_po2bl([sub(Job,po(N)),N0],[_,PON0],R,BR).

false2contra :- 
	retract(proof(H,contents,false)),
	assert(proof(H,contents,contradiction)),
	fail.
false2contra.


/* ##########          ENDE     O2BL                      ########### */

/* ##########		Aufbereitung von Otter-Block-Beweisen   ########### */
/***************************************************************************
	Zusammenfassen der Modus-Ponens-Resolutionen in den Unterbeweisen
***************************************************************************/


:- dynamic                  % local in "Aufbereitung von Otter-Block-Beweisen"
	has_subst/2,
	is_unique_tmp/2.

rm_ModPon :- 
	clausifyAxs,
	nl,
	proof([Pf,global],goal,_),
	proof([Pf,_],status,subproof(Pf1)),!,
	setof(Pf2,N^proof([Pf1,N],status,subproof(Pf2)),PfL),
	rm_ModPon_l(PfL),
	remove_by_rule([mp(_,_)]),
	!.
rm_ModPon.


rm_ModPon_l(L) :- 
	write("Removing 'Modus Ponens'-resolutions\n"),
	rm_MP_l(L),!.

rm_MP_l([Pf|L]) :- rm_MP(Pf),write(*),rm_MP_l(L),!.
rm_MP_l([]).

rm_MP(Pf) :- 
	last_in_proof(Pf,[Pf,N]),
	(last_MP_in_proof([Pf,N],[Pf,N1]) ->		
	    proof([Pf,N1],predecessors,[[Pf,N2]]),
	    rm_MP(Pf,N2)
	; true).
rm_MP(_).


/* Letzte MP-Res. des Unterbeweises wird zur zusammengefassten Resolution */


last_MP_in_proof([Pf,N],[Pf,N1]) :-
	(	
	once(proof([Pf,N],control,rule([resolve(_,_)],[Ref1,Ref2]))),
	( is_posLit(Ref1) ; is_posLit(Ref2) ),
	N1=N
	;
	proof([Pf,N],predecessors,[Pre]),
	last_MP_in_proof(Pre,[Pf,N1])
	),!.


/* MP-Resolutionen: eine der Referenzen ist pos. Lit. */


rm_MP(Pf,N) :-
	once(
		proof([Pf,N],control,rule([resolve(_,_)],[Ref1,Ref2])),
		( (is_posLit(Ref1) ; is_posLit(Ref2))  ->
			retract(proof([Pf,N],control,rule([resolve(R1,R2)],[Ref1,Ref2]))),
			assert(proof([Pf,N],control,rule([mp(R1,R2)],[Ref1,Ref2])))
		;       true
		)    
	    ),
	proof([Pf,N],predecessors,[[Pf,N1]]),
	rm_MP(Pf,N1),
	!.
rm_MP(Pf,N) :-
	proof([Pf,N],predecessors,[[Pf,N1]]),
	rm_MP(Pf,N1),
	!.
rm_MP(_,_).


is_posLit([Pf,N]) :-
	once((
		proof([Pf,N],contents,Clause),
		splitLits(Clause,NLitsL,PLitsL)
	)),
	NLitsL=[],
	PLitsL=[_].
	


/******************************************** 
	Klausifizierung der Axiome
********************************************/


clausifyAxs :-
	write("'Clausify' axioms\n"),
	(
	proof([sub(Job,N),ax(AH)],predecessors,_) ;
	proof([ax(Job,AN),NH],predecessors,_)
	),
	once((
		( H=[sub(Job,N),ax(AH)] ; H=[ax(Job,AN),NH] ),
		retract(proof(H,contents,Contents)),
		clausify(Contents,NewCont),
		assert(proof(H,contents,NewCont)),
		write("*")
	)),
	fail.
clausifyAxs.


clausify(all(Formula), all(Clause)) :-
	clausify((Formula) , Clause),
	!.

clausify(forall(Formula), forall(Clause)) :-
	clausify((Formula) , Clause),
	!.

clausify(ex(Formula), ex(Clause)) :-
	clausify((Formula) , Clause),
	!.

clausify(exists(Formula), exists(Clause)) :-
	clausify((Formula) , Clause),
	!.

clausify(true->(Formula) , Clause) :- 
	clausify((Formula),Clause),
	!.

clausify((Formula)->false , Clause) :-
	negForm(Formula,NegForm),
	clausify(NegForm,Clause),
	!.

clausify((Form1)->(Form2) , Clause1;Clause2) :-
	negForm(Form1,NegForm1),
	clausify((NegForm1),Clause1),
	clausify((Form2),Clause2),
	!.
	
clausify((Form1)';'(Form2) , Clause1;Clause2) :-
	clausify((Form1),Clause1),
	clausify((Form2),Clause2),
	!.

clausify((Form1)','(Form2) , Clause1;Clause2) :-
	negForm(Form1,NegForm1),
	negForm(Form2,NegForm2),
	clausify((NegForm1),Clause1),
	clausify((NegForm2),Clause2),
	!.

clausify(not(Formula) , Clause) :-
	log_op(Formula,_),
	negForm(Formula,NegForm),
	clausify((NegForm),Clause),
	!.

clausify(Term,Term).


negForm(not(X),X).
negForm((X,Y),(NotX;NotY)) :- negForm(X,NotX), negForm(Y,NotY).
negForm((X;Y),(NotX,NotY)) :- negForm(X,NotX), negForm(Y,NotY).
negForm(ex(X,F),all(X,NotF)) :- negForm(F,NotF).
negForm(all(X,F),ex(X,NotF)) :- negForm(F,NotF).
negForm(exists(X,F),forall(X,NotF)) :- negForm(F,NotF).
negForm(forall(X,F),exists(X,NotF)) :- negForm(F,NotF).
negForm(X,not(X)).		


/* Variablen werden (konsistent innerhalb eines Unterbeweises) in v1, v2, ...
   umnummeriert */
   
 


rename_vars :- proof([Pf,global],goal,_),
	proof([Pf,_],status,subproof(Pf1)),!,
	setof(Pf2,N^proof([Pf1,N],status,subproof(Pf2)),PfL),
	rename_vars_l(PfL),
	nl,
	!.


rename_vars_l(L) :- 
	write("Rename variables\n"),
	ren_vars_l(L),!.

ren_vars_l([Pf|L]) :- ren_vars(Pf),write(*),ren_vars_l(L),!.
ren_vars_l([]).

ren_vars(Pf) :- 
	last_in_proof(Pf,[Pf,N]),
	get_vars([Pf,N],VarList),
	length(VarList,Length),
	varList2substList(VarList,SubstList,Length),
	ren_vars([Pf,N],SubstList).
ren_vars(_).


varList2substList([],[],_).
varList2substList([Var|VarList],[[Var,NewVar]|SubstList],Length) :-
	length(VarList,VarListLength),
	Pos is Length - VarListLength,
	integer_atom(Pos,Ext),
	concat_atoms('v',Ext,NewVar),
	varList2substList(VarList,SubstList,Length).


ren_vars([Pf,N],Subst) :- 
	once((
		(Subst=[_|_],
		retract(proof([Pf,N],contents,F)),
		substitute(F,FF,U,is_vn(U),Subst),
		assert(proof([Pf,N],contents,FF))
		;
		true)
	)),
	once((
		(Subst=[_|_],
		retract(proof([Pf,N],control,rule([instantiate(S)],Refs))),
		substitute(S,SS,U,is_vn(U),Subst),
		assert(proof([Pf,N],control,rule([instantiate(SS)],Refs)))
		;
		true)
	)),
	proof([Pf,N],predecessors,[[Pf,N1]]),
	ren_vars([Pf,N1],Subst),!.
ren_vars(_,_).


/*************************************************************************/
/* Beseitigung der Substitutionen in den Unterbeweisen, die von Proof Objects stammen */
/* Idee: Die Unterbeweise werden von unten nach oben abgearbeitet */
/* Zu jeder Zeile wird die dort gueltige Substitution in has_subst/2 notiert, soweit sie eindeutig war */
/* Wenn Die Zeile nicht mit instantiate erhalten wurde, so wird die Substitution dort ausgefuehrt */
/* In diesem Fall ergibt sich die Substitution durch Ueberlagerung der Substitutionen der Zeilen, fuer die die gegebene Zeile gebraucht wird */
/* Bei Zeilen die Instantiate enthalten wird die Substitution wie eben ermittelt, aber noch mit dem Argument von instantiate verkettet */


rm_instantiation :- proof([Pf,global],goal,_),
	proof([Pf,_],status,subproof(Pf1)),!,
	collect_proof_pars,	% Erzeugt hier used_for/2 
	setof(Pf2,N^proof([Pf1,N],status,subproof(Pf2)),PfL),
	rm_instantiation_l(PfL),
	remove_by_rule([instantiate(_)]),
	nl,
	local_constants,	% Aktualisieren der lokalen Konstanten
	!.


rm_instantiation_l(L) :- 
	write("Removing instances\n"),
	rm_inst_l(L),!.

rm_inst_l([Pf|L]) :- rm_inst(Pf),write(*),rm_inst_l(L),!.
rm_inst_l([]).

rm_inst(Pf) :- retract_all(has_subst(_,_)),
	last_in_proof(Pf,[Pf,N1]),	% Die Unterbeweise werden jeweils von unten nach oben abgearbeitet
	rm_inst(Pf,N1).
rm_inst(_) :-
	retract_all(has_subst(_,_)).


/* Fuer Zeile mit instantiate */


rm_inst(Pf,N) :- 
	once((
		proof([Pf,N],control,rule([instantiate(S)],[[Pf1,_]])),
		(Pf1=Pf ->
		    get_subst(Pf,N,Subst),
		    add_subst(Subst,S,Subst1),
		    assert(has_subst([Pf,N],Subst1)) 
		; true
		)
	)),
	proof([Pf,N],predecessors,[[Pf,N1]]),
	rm_inst(Pf,N1),!.
rm_inst(Pf,N) :- 
	once((
		get_subst(Pf,N,Subst),
		assert(has_subst([Pf,N],Subst)),
		(Subst=[_|_],
		retract(proof([Pf,N],contents,F)),
		substitute(F,FF,U,is_vn(U),Subst),
		assert(proof([Pf,N],contents,FF))
		;
		true)
	)),
	proof([Pf,N],predecessors,[[Pf,N1]]),
	rm_inst(Pf,N1),!.
rm_inst(_,_).


get_subst(Pf,N,Subst) :- 
	setof(S,N1^(
		used_for([Pf,N],[Pf,N1]),has_subst([Pf,N1],S)
	),SL),
	make_unique(SL,Subst),!.
get_subst(_Pf,_N,[]).

make_unique([S],S) :- !.
make_unique(SL,Subst) :- unique_tmp_l(SL),
	setof([V1,V2],retract(is_unique_tmp(V1,V2)),Subst).
make_unique(_SL,[]).

unique_tmp_l([S|SL]) :- unique_tmp(S),unique_tmp_l(SL),!.
unique_tmp_l([]) :- retract_all(is_unique_tmp(_,not_unique)).

unique_tmp([[V1,_]|S]) :- is_unique_tmp(V1,not_unique),!,
	unique_tmp(S),!.
unique_tmp([[V1,V2]|S]) :- is_unique_tmp(V1,V3),not V2=V3,
	retract_all(is_unique_tmp(V1,_)),
	assert(is_unique_tmp(V1,not_unique)),
	unique_tmp(S),!.
unique_tmp([[V1,V2]|S]) :- assert(is_unique_tmp(V1,V2)),
	unique_tmp(S),!.
unique_tmp([]).

add_subst(Subst,S,Subst1) :- setof([V1,V2],comp_subst(Subst,S,V1,V2),Subst1).
add_subst(_,_,[]).

comp_subst(S1,S2,V1,V2) :- member(subst(V1,V),S2),
	once((member([V,V2],S1);V2=V)).
comp_subst(S1,S2,V1,V2) :- member([V1,V2],S1),not member(subst(V1,_),S2).

is_vn(X) :- atom(X),name(X,VN),
	string_list(VN,[118|VNr]),string_list(VS,VNr),
	concat_string([VS, "."],VS1),
	term_string(T,VS1),number(T),!.


 
/****************************************************************
 Konvertierung von direkten Beweisen mit neg. Formel als Ergebnis
   in indirekte Beweise 
*****************************************************************/


conv_direct :- 
	write("Converting direct subproofs\n"),
	proof([sub(Job,M),PO],control,rule([Rule],_)),
	once((
		( Rule=direct ; Rule=direct_all(_) ),
		proof([sub(Job,M),PO],contents,not(_)),
		conv_dir([sub(Job,M),PO]),
		write("*")
	)),
	fail.
conv_direct :-
	remove_by_rule([obsolete_merge]).


conv_dir(Pf) :- 
	insert_ass(Pf),	% Einfuegen der proof/3-Praed. fuer Annahme 
	insert_contra(Pf),	% Letzte Zeile in Unterbew. wird Widerspruch 
	dir2indir(Pf),	% Regel 'direct` wird 'indirect` 
	rm_assumption(Pf).	% Entfernen der Annahme aus Beweiszeilen
conv_dir(_).


insert_ass(Pf) :-
	Pf=[sub(Job,_),PO],
	proof(Pf,contents,not(Formula)),
	assert(proof([sub(Job,po(PO)),ass],contents,Formula)),
	assert(proof([sub(Job,po(PO)),ass],status,assumption([]))),
	assert(proof([sub(Job,po(PO)),ass],predecessors,[])).
	


insert_contra(Pf) :-	
	Pf=[sub(Job,_),PO],
	last_in_proof(sub(Job,po(PO)),LastPO),
	(
	% 'merge' wird ueberfluessig 
	retract(proof(LastPO,control,rule([merge(_)],[Ref]))),
	assert(proof(LastPO,control,rule([obsolete_merge],[Ref]))),
	proof(LastPO,predecessors,[[Pf2]])
	;
	Pf2=LastPO
	),
	retract(proof(Pf2,contents,_)),
	assert(proof(Pf2,contents,contradiction)),
	retract(proof(Pf2,control,rule([_],RefL))),
	assert(proof(Pf2,control,rule([binary([1,1])],RefL))).


dir2indir(Pf) :-
	Pf=[sub(Job,_),PO],
	(
	retract(proof(Pf,control,rule([direct],[Pf1]))),
	assert(proof(Pf,control,rule([indirect],[[sub(Job,po(PO)),ass],Pf1])))
	;
	retract(proof(Pf,control,rule([direct_all(VL)],[Pf1]))),
	assert(proof(Pf,control,rule([indirect_all(VL)],[[sub(Job,po(PO)),ass],Pf1])))
	).


rm_assumption(Pf) :-
	Pf=[sub(Job,_),PO],
	proof(Pf,contents,Formula),
	last_in_proof(sub(Job,po(PO)),LastPO),
	rm_assumption(LastPO,Formula).
rm_assumption(_).

rm_assumption([Pf,N],Formula) :-
	once((
		retract(proof([Pf,N],contents,Cont)), %Entfernen der Teilformel 'Formula' aus 'Cont' 
		newCont(Formula,Cont,NewCont),
		assert(proof([Pf,N],contents,NewCont))
	)),
	proof([Pf,N],predecessors,[[Pf,N1]]),
	rm_assumption([Pf,N1],Formula).
rm_assumption([Pf,N],_Formula) :-
	retract(proof([Pf,N],predecessors,Pred)),
	assert(proof([Pf,N],predecessors,[[Pf,ass]])),
	assert(proof([Pf,ass],predecessors,Pred)),
	retract(proof([Pf,N],control,rule(_Rule,RefL))),
	assert(proof([Pf,N],control,rule([assumption],[[Pf,ass]|RefL]))).
rm_assumption(_,_).


newnCont(Formula, Form;Cont, NewCont) :-
	is_variant_of(Formula,Form),
	newCont(Formula, Cont, NewCont).
newCont(Formula, Cont;Form, NewCont) :-
	is_variant_of(Formula,Form),
	newCont(Formula, Cont, NewCont).
newCont(Formula, Cont1;Cont2, NewCont1;NewCont2) :-
	newCont(Formula, Cont1, NewCont1),
	newCont(Formula, Cont2, NewCont2).
newCont(_Formula, Cont, Cont).	

is_variant_of(Vari1,Vari2) :-
	var(Vari1), 
	var(Vari2), 
	!.
is_variant_of(Vari1,Vari2) :-
	not(var(Vari1)),
	not(var(Vari2)),
	Vari1=..[F1|ArgList1],
	Vari2=..[F2|ArgList2],
	F1=F2,
	is_lvariant_of(ArgList1,ArgList2),
	!.

is_lvariant_of([],[]).
is_lvariant_of([],_) :- fail, !.
is_lvariant_of(_,[]) :- fail, !.
is_lvariant_of([Arg1|ArgList1],[Arg2|ArgList2]) :-
	is_variant_of(Arg1,Arg2),
	is_lvariant_of(ArgList1,ArgList2),
	!.




/***************************************************************
	Gentzifizierung der Formeln (als Klauseln vorliegend)
***************************************************************/


gentzifyForms :-
	write("'Gentzify' formulas\n"),
	proof([Pf,N],predecessors,_),
	once((
		retract(proof([Pf,N],contents,Contents)),
		gentzify(Contents,NewCont),
		assert(proof([Pf,N],contents,NewCont)),
		write("*")
	)),
	fail.
gentzifyForms.


gentzify(all(Clause), all(Gentzen)) :-
	gentzify(Clause,Gentzen),
	!.

gentzify(forall(Clause), forall(Gentzen)) :-
	gentzify(Clause,Gentzen),
	!.

gentzify(ex(Clause), ex(Gentzen)) :-
	gentzify(Clause,Gentzen),
	!.

gentzify(exists(Clause), exists(Gentzen)) :-
	gentzify(Clause,Gentzen),
	!.

gentzify(Clause,Gentzen) :-
	% Aufsplitten der Literale in pos. und neg. 
	splitLits(Clause,NLitsL,PLitsL),
	(
	NLitsL=[], disjLits(PLitsL,DisjLits), Gentzen=(DisjLits)
	;
	PLitsL=[], disjLits(NLitsL,DisjLits), Gentzen=(DisjLits)
	;
	negLits(NLitsL,LitsL),
	conjLits(LitsL,ConjLits), disjLits(PLitsL,DisjLits), Gentzen=(ConjLits->DisjLits)
	),!.


splitLits(Clause1;Clause2, NLitsL,PLitsL) :-
	splitLits(Clause1,NLits1L,PLits1L),
	splitLits(Clause2,NLits2L,PLits2L),
	append(NLits1L,NLits2L,NLitsL),
	append(PLits1L,PLits2L,PLitsL).
splitLits(not Lit,[not Lit],[]).
splitLits(Lit,[],[Lit]).


negLits([not Lit|LitsL],[Lit|NegLitsL]) :-
	negLits(LitsL,NegLitsL).
negLits([Lit|LitsL],[not Lit|NegLitsL]) :-
	negLits(LitsL,NegLitsL).
negLits([],[]).

/* Literale werden disjunktiv bzw. konjunktiv verknuepft */


disjLits([Lit|LitsL],Lit;Lits) :-
	disjLits(LitsL,Lits).
disjLits([Lit],Lit).

conjLits([Lit|LitsL],Lit','Lits) :-
	conjLits(LitsL,Lits).
conjLits([Lit],Lit).
	

/*
/*****************************************************
	Aufzaehlen der lokalen Konstanten 
******************************************************/


local_constants :- 
	write("Get local constants\n"),
	proof([sub(Job,M),PO],control,rule([Rule],_)),
	once((
		( Rule=direct ; Rule=indirect ;
		  Rule=direct_all(_) ; Rule=indirect_all(_) ),
		report_constants([sub(Job,M),PO]),
		write("*")
	)),
	fail.
local_constants :-
	tmp2all.

tmp2all :-
	retract(proof(Pf,control,rule([direct_tmp(VarList)],Ref))),
	once(assert(proof(Pf,control,rule([direct_all(VarList)],Ref)))),
	fail.
tmp2all :-
	retract(proof(Pf,control,rule([indirect_tmp(VarList)],Ref))),
	once(assert(proof(Pf,control,rule([indirect_all(VarList)],Ref)))),
	fail.
tmp2all.
	


report_constants(Pf) :-
	proof(Pf,control,rule(_,[Rf])),
	get_vars(Rf,VarList),
	(
	retract(proof(Pf,control,rule([direct],Ref))),
	assert(proof(Pf,control,rule([direct_tmp(VarList)],Ref)))
	;
	retract(proof(Pf,control,rule([direct_all(_)],Ref))),
	assert(proof(Pf,control,rule([direct_tmp(VarList)],Ref)))
	;
	retract(proof(Pf,control,rule([indirect],Ref))),
	assert(proof(Pf,control,rule([indirect_tmp(VarList)],Ref)))
	;
	retract(proof(Pf,control,rule([indirect_all(_)],Ref))),
	assert(proof(Pf,control,rule([indirect_tmp(VarList)],Ref)))
	).
report_constants(_).	


get_vars(PH,VarList) :-
	proof(PH,contents,Cont),
	substitute(Cont,_,U,is_vn(U),Subst),
	varList(Subst,VL1),
	(
	proof(PH,predecessors,[Pre]), get_vars(Pre,VL2)
	;
	VL2=[]
	),
	append(VL1,VL2,VL),
	( 
	VL=[],VarList=VL
	;
	setof(Var,member(Var,VL),VarList)
	).


varList([],[]) :- !.
varList([X],[]) :-
	var(X),!.
varList([[V|_]],[V]) :- !.
varList([[V|_]|VL],[V]) :-
	var(VL),!.
varList([[V|_]|VL1],[V|VL2]) :-
	varList(VL1,VL2),!.


/************** Entfernen von merge ****************************/


remove_merge :- collect_proof_pars,fail.
remove_merge :- proof(P,control,rule([merge(_)],[S])),
	once((
		proof(S,control,rule(R,_)),
		rm_pos(S),
		retract(proof(P,control,rule(_,A))),
		assert(proof(P,control,rule(R,A)))
	)),
	fail.
remove_merge.


make_paramodulation_chains :- proof([Pf,global],goal,_),
	last_in_proof(Pf,H),
	collect_proof_pars,
	make_paramodulation_chains(H).

make_paramodulation_chains(H) :- 
	once((
		proof(H,control,rule([paramod([1,1],[1,N|_])],_)),
		proof(H,contents,(T1=T2)),
		change_para_side(N,(T1=T2),TL),
		make_paramodulation_chain(N,H,[],[],TL,H)
	)),fail.
make_paramodulation_chains(H) :- proof(H,status,subproof(Pf)),
	last_in_proof(Pf,HPf),
	make_paramodulation_chains(HPf),!.
make_paramodulation_chains(H) :- proof(H,predecessors,[H1]),
	make_paramodulation_chains(H1),!.
make_paramodulation_chains([Pf,_]) :- proof(H,status,subproof(Pf)),
	proof(H,predecessors,[HPf]),
	make_paramodulation_chains(HPf),!.
make_paramodulation_chains(_).

make_paramodulation_chain(N,H,HArg,HUsed,[T|EqL],HAkt) :- 
	proof(HAkt,control,rule([paramod([1,1],[1,N|_])],[H1,H2])),
	proof(H2,contents,C),
	change_para_side(_,C,[T,T3]),
	can_chain(H2,HAkt),
	proof(H2,control,rule(_,Arg0)),
	append(Arg0,[H1|HArg],HArg1),
	strict_remove(H2,HArg1,HArg2),
	make_paramodulation_chain(N,H,HArg2,[H2|HUsed],[T,T3|EqL],H2),!.
make_paramodulation_chain(N,H,HArg,HUsed,[T,TT|EqL],HAkt) :- 
	M is 3-N,
	proof(HAkt,control,rule([paramod([1,1],[1,M|_])],[H1,H2])),
	can_chain(H1,HAkt),
	can_chain(H2,HAkt),
	proof(H2,contents,C2),
	change_para_side(_,C2,[T2,TT]),
	proof(H1,contents,C1),
	change_para_side(_,C1,[T,T2]),
	proof(H1,control,rule(_,HArg1)),
	proof(H2,control,rule(_,HArg2)),
	append(HArg1,HArg,Arg1),
	append(HArg2,Arg1,Arg2),
	strict_remove(H1,Arg2,Arg3),
	strict_remove(H2,Arg3,Arg4),
	make_paramodulation_chain(_,H,Arg4,[H1,H2|HUsed],[T,T2,TT|EqL],H1),!.
make_paramodulation_chain(_,_,_,_,[_,_],_) :- !.
make_paramodulation_chain(_,H,HArg,HUsed,EqL,_) :- 
	retract(proof(H,contents,_)),
	assert(proof(H,contents,=(EqL))),
	make_unique1(HArg,HArg1),
	retract(proof(H,control,rule(_,_))),
	assert(proof(H,control,rule([paramodulation],HArg1))),
	destroy_l(HUsed),
	!.

change_para_side(2,(T1=T2),[T1,T2]) :- !.
change_para_side(1,(T1=T2),[T2,T1]).

can_chain(H,H0) :- H=[Pf,_],H0=[Pf,_],
	used_only_for(H,H0),!.

used_only_for(H,H0) :- used_for(H,H1),not H1=H0,!,fail.
used_only_for(_,_).


destroy_l([P|L]) :- destroy(P),destroy_l(L).
destroy_l([]).

destroy(P) :- retract(proof(P,predecessors,Pred)),
	retract(proof(Q,predecessors,[P])),
	assert(proof(Q,predecessors,Pred)),
	retract_all(proof(P,_,_)),!.


/* ##########	Ende	Aufbereitung von Otter-Block-Beweisen   ########### */


OTTER*/


/* ##########     Aufbereitung von Discountbeweisen   ############# */


/* Zusammenfassen von Gleichungen und Ungleichungen zu Ketten */


make_chains(Op) :- proof(H,control,rule([trans(Op)],Arg)),
	make_chains(Op,H,Arg),
	fail.
make_chains(_).

make_chains(Op,H) :- proof(H,control,rule([trans(Op)],Arg)),
	make_chains(Op,H,Arg).

make_chains :- setof(Op,H^A^proof(H,control,rule([trans(Op)],A)),OpL),
	make_chains_l(OpL),!.

make_chains_l([Op|L]) :- make_chains(Op),make_chains_l(L),!.
make_chains_l([]).

make_chains(Op,H,Arg) :- proof(H,contents,F),
	F=..[Op,A,E],
	get_chains(Op,A,E,Arg,FL,PL),
	get_break_points([E|FL],PL,BPL),
	make_chain_rules(Op,H,BPL),!.


/* get_chains baut die Listen der Positionen PL und der Terme FL der Kette in umgekehrter Reihenfolge auf */


get_chains(_Op,A,A,_Arg,[],[]) :- !.
get_chains(Op,A,B,Arg,[C|FL],[P|PL]) :- 
	F=..[Op,C,B],
	member(P,Arg),
	proof(P,contents,F),
	strict_remove(P,Arg,Arg1),
	get_chains(Op,A,C,Arg1,FL,PL),!.

get_break_points([F1,F2|FL],[P|PL],BPLX) :- 
	get_break_points(FL,PL,[F2,F1],[P],BPLX),!.

get_break_points([F1|FL],[P|PL],FL0,PL0,[[[F1|FL0],PL0]|BPLX]) :-
	chain_break_point(P,PL0),
	!,get_break_points([F1|FL],[P|PL],BPLX).
	
get_break_points([F1|FL],[P|PL],FL0,PL0,BPL) :- 
	get_break_points(FL,PL,[F1|FL0],[P|PL0],BPL),!.
get_break_points([],[],FL0,PL0,[[FL0,PL0]]).

chain_break_point(P,_) :- proof(P,status,subproof(_)),!.


/* Zusammenfassen */


% Wenn nur 2 Terme, so weiter
make_chain_rules(Op,H,[[[_,_],_]|BPL]) :- make_chain_rules(Op,H,BPL),!.
make_chain_rules(Op,H,[[FL,PL]|BPL]) :- rm_chain_members(PL,RL,Arg),
	strict_remove_l(PL,Arg,Arg1),
	make_1_chain(Op,H,FL,RL,Arg1),
	make_chain_rules(Op,H,BPL),!.
make_chain_rules(_,[]).

rm_chain_members([],[],[]) :- !.
rm_chain_members([P|PL],RL,Arg) :-
	proof(P,control,rule(RP,AP)),
	proof(P,predecessors,PPred),
	retract(proof(Q,predecessors,[P])),
	assert(proof(Q,predecessors,PPred)),
	retract_all(proof(P,_,_)),
	rm_chain_members(PL,RL1,Arg1),
	append(RP,RL1,RL),
	append(AP,Arg1,Arg),!.
rm_chain_members(PL,_,_) :- ilf_serv_error((
	write("Ilf ERROR in removing chain with positions "),
	write(PL),nl
	)),!.

make_1_chain(Op,P,FL,RL,Arg) :- retract(proof(P,control,_)),
	assert(proof(P,control,rule([chain(Op)|RL],Arg))),
	retract(proof(P,contents,_)),
	F=..[Op,FL],
	assert(proof(P,contents,F)),!.


/* ##########     Ende Aufbereitung von Discountbeweisen   ############# */



/*PAD

/* ############## Transformation von Modelleliminations-Beweisen, die von pad im Hintergrund erzeugt wurden #################### */

/* Einlesen von Hintergrundbeweisen und verbinden mit dem aktuellen Beweis */
/* Aufruf: bg2bl(StartJob) Entfernt auch Sorteninformationen. Benutzte Theorie muss geladen sein. Getestet mit Setheo */


% these predicates used here are not defined in the .pl files:
% rev/2, relation/2, function/2
% cw Tue Nov 12 14:21:20 1996


:- dynamic                  % local in "Transformation von
	                    % Modelleliminations-Beweisen, 
	                    % die von pad im Hintergrund erzeugt wurden"
	padpl/1,
	used_clause/4.


bg2bl(_) :- retract_all(padpl(_)),fail.
bg2bl(_) :- proof(H,contents,_F),assert(padpl(H)),fail.
bg2bl(_) :- put_proof(tmp),fail.
bg2bl(StartJob) :- 
	get_proof(StartJob),
	get_subproof_jobs(StartJob,JobFList),
	make_bl_proof(StartJob,JobFList),
	job_from_jobF(JobFList,JobList),
	get_proof(StartJob),
	remake_bg_proof(StartJob,JobList),
	add_clauses(StartJob),
	reload_proof_l(JobList),
	really_add_proof(StartJob,JobList),
	!.

get_subproof_jobs(StartJob,JobFList) :-
	get_proof(StartJob),
	setof((J/F),H^(
		proof(H,status,subproof(J)),
		proof(H,contents,F)
		),JobFList).

job_from_jobF([(J/_F)|L],[J|JL]) :- job_from_jobF(L,JL),!.
job_from_jobF([],[]).

remake_bg_proof(StartJob,[_]) :- retract_all(proof([StartJob,goal],_,_)),
	retract_all(proof([StartJob,global],goal,_)),!.
remake_bg_proof(StartJob,L) :- add_1(StartJob,L,JL),
	retract_all(proof([StartJob,goal],control,_)),
	assert(proof([StartJob,goal],control,rule([since],JL))),!.


make_bl_proof(StartJob,[(Job/G)|JL]) :-
	get_proof(Job),
	rm_exp_sort,
	check_me_proof,
	me2bl,
	remove_query,
	me_answers,
	proof([Pf,global],goal,_),
	proof([Pf,N],status,subproof(Pf1)),
	retract(proof([Pf,N],contents,_)),
	assert(proof([Pf,N],contents,G)),
	make_goal_ass(Pf1,G),
	remove_by_rule([insert,since]),
	remove_by_rule([contrapositive]),
	remove_unused,
%	convert_indirect,
	remove_duplicate,
	remove_trivial_subproofs,
%	move_into_subproof,
	move_lines,
	a_close_proof(Pf),
	connect_exp_bl(StartJob),
	term2string(Job,JobS),
	retract_all(proof([_,global],_,_)),
	concat_string(["a", JobS],F),
	put_proof(F),
	make_bl_proof(StartJob,JL),!.
make_bl_proof(StartJob,[_|JL]) :- make_bl_proof(StartJob,JL),!.
make_bl_proof(_,[]).


/* rm_exp_sort entfernt Sorteninformationen aus Beweis, Axiomen und Ziel */


n
rm_exp_sort :-
	proof([Job,global],system,[S]),
	rm_exp_sort(S,Job).

rm_exp_sort(setheo,Job) :-ilf_state(well_sorted,on),
	rm_sort_arg(Job),fail.
rm_exp_sort(setheo,Job) :- retract(proof([Job,global],goal,F)),
	rm_sort_arg_f(F,F1),
	assert(proof([Job,global],goal,F1)),!.
rm_exp_sort(komet,Job) :- rm_exp_sort(setheo,Job),!.
rm_exp_sort(Sys,Job) :-
	write("Ilf Warning: Cannot generate blockstructure for proof ilf."),
	write(Job),write(".out from system "),write(Sys),nl,!,fail.

rm_sort_arg(Job) :- setof(H,F^proof([Job,H],contents,F),L),
	rm_sort_arg_1(Job,L),!.

rm_sort_arg_1(Job,[H|_L]) :- 
 	once((	
 		retract(proof([Job,H],contents,F)),
		rm_sort_arg_f(F,F1),
		assert(proof([Job,H],contents,F1))
	)),
	fail.
rm_sort_arg_1(Job,[_|L]) :- rm_sort_arg_1(Job,L),!.
rm_sort_arg_1(_,[]).

rm_sort_arg_f(X,X) :- var(X),!.
rm_sort_arg_f(eqq(_,U1,V1),(U2=V2)) :-rm_sort_arg_t(U1,U2),
	rm_sort_arg_t(V1,V2),!.
rm_sort_arg_f(X,X) :- number(X),!.
rm_sort_arg_f(F,F1) :- F=..[Op|Arg],
	log_op(F,_),!,
	rm_sort_arg_f_l(Arg,Arg1),
	F1=..[Op|Arg1],!.
rm_sort_arg_f(F,F1) :- F=..[Op,_S|Arg],length(Arg,NArg),functor(FF,Op,NArg),
	relation(_,(FF :- B)),!,
	once((
	pad_body_list(B,BL)
	;
	BL=[]
	)),
	length(BL,N1),
	N1 = NArg,
	rm_sort_arg_t_l(Arg,Arg1),
	F1=..[Op|Arg1],!.
rm_sort_arg_f(F,F1) :- F=..[Op|Arg],
	rm_sort_arg_t_l(Arg,Arg1),
	F1=..[Op|Arg1],!.
rm_sort_arg_f(F,F).

rm_sort_arg_f_l([F|FL],[F1|FL1]) :- rm_sort_arg_f(F,F1),rm_sort_arg_f_l(FL,FL1),!.
rm_sort_arg_f_l([],[]).

rm_sort_arg_t(X,X) :- var(X),!.
rm_sort_arg_t(X,X) :- number(X),!.
rm_sort_arg_t(F,F1) :- F=..[Op,S|Arg],length(Arg,NArg),
	(
	S=skolem
	;
	functor(FF,Op,NArg),
	once((	function(_,((FF : _) :- B)),
	        pad_body_list(B,BL)
	        ;
	        function(_,(FF : _)),
	        BL=[]
	)),
	length(BL,N1),
	N1 = NArg
	),
	rm_sort_arg_t_l(Arg,Arg1),
	F1=..[Op|Arg1],!.
rm_sort_arg_t(F,F1) :- F=..[Op|Arg],
	rm_sort_arg_t_l(Arg,Arg1),
	F1=..[Op|Arg1],!.
rm_sort_arg_t(F,F).

rm_sort_arg_t_l([F|FL],[F1|FL1]) :- rm_sort_arg_t(F,F1),rm_sort_arg_t_l(FL,FL1),!.
rm_sort_arg_t_l([],[]).

pad_body_list((B1,B2),BL) :-
	pad_body_list(B1,B1L),
	pad_body_list(B2,B2L),
	append(B1L,B2L,BL),!.
pad_body_list(B,[B]).


/* make_goal_ass macht Axiome, die vom Ziel kommen zu Annahmen */


make_goal_ass(Pf,G) :-
	bagof([HH,I],Nr^retract(proof(HH,control,axiom(clause(goal(Nr),I)))),HL),
	retract(proof([Pf,H],predecessors,[])),
	gen_hdl(Pf,HH),
	ins_ass_l(HL,[Pf,H],HH,AL),
	ass_to_clause(Pf,HH),
	assert(proof(HH,predecessors,[])),
	assert(proof(HH,contents,not(G))),
	assert(proof(HH,status,assumption([]))),
	rev(AL,AAL),
	list_body(AAL,B),
	assert(proof([Pf,global],goal,(B -> G))).
make_goal_ass(_,_).

ins_ass_l([[Hd,I]|HL],[Pf,H],HH,[F|FL]) :-
	gen_hdl(Hdn), % Alles auf gleiches ProofHandle setzen 
	assert(proof([Pf,H],predecessors,[[Pf,Hdn]])),
	assert(proof([Pf,Hdn],status,proved)),
	assert(proof([Pf,Hdn],control,rule([clausify(I)],[HH]))),
	proof(Hd,contents,F),
	assert(proof([Pf,Hdn],contents,F)),
	change_refs(Hd,[Pf,Hdn]),
	retract_all(proof(Hd,_,_)),
	ins_ass_l(HL,[Pf,Hdn],HH,FL),!.
ins_ass_l([],H,HH,[]) :- assert(proof(H,predecessors,[HH])),!.

ass_to_clause(Pf,HH) :- retract(proof([Pf,N],status,assumption(_))),
	once((
		assert(proof([Pf,N],status,proved)),
		retract_all(proof([Pf,N],control,_)),
		assert(proof([Pf,N],control,rule([clausify(0)],[HH])))
	)),fail.
ass_to_clause(_,_).


/* connect_exp_bl stellt Verbindung von Klauseln zu Axiomen her */


connect_exp_bl(StartJob) :- 
	proof(H,control,axiom(clause(Name,K))),
	once((
		test_for_used(H),
		gen_hdl(Hn),
		change_refs(H,[StartJob,Hn]),
		proof(H,contents,F),
		assert(used_clause([StartJob,Hn],Name,F,K))
	)),
	fail.
connect_exp_bl(_) :- proof(H,control,axiom(clause(_,_))),
	retract_all(proof(H,_,_)),fail.
connect_exp_bl(_).

test_for_used(H) :- proof(_,control,rule(_,L)),
		member(H,L),!.

make_ax_cont(Name,Name) :- padpl(Name),!.
make_ax_cont(Name,Name) :- proof(Name,_,_),!.
make_ax_cont(Name,[ilfax,Name]) :- proof([ilfax,Name],contents,_),!.
make_ax_cont(Name,[ilfax,Name]) :- ax_name(Name,H,B,_),
	(translit(true,B),F=H;translit('->',Imp),F=..[Imp,B,H]),
	assert(proof([ilfax,Name],contents,F)),
	assert(proof([ilfax,Name],status,proved)),
	assert(proof([ilfax,Name],control,axiom(Name))),
	!.
make_ax_cont(Name,_) :- write("Pad ERROR: Axiom "),write(Name),
	write(" not found!"),fail.


add_clauses(StartJob) :- retract(proof([StartJob,N],predecessors,[])),
	add_next_clause([StartJob,N]),!.

add_next_clause(H) :- retract(used_clause(H1,Name,F,K)),
		(F=(F1 -> false) -> F2 = not(F1);F2=F),
		a_close(F2,F3),
		assert(proof(H1,contents,F3)),
		assert(proof(H1,status,proved)),
		make_ax_cont(Name,NeuName),
		assert(proof(H1,control,rule([clausify(K)],[NeuName]))),
		assert(proof(H,predecessors,[H1])),
		add_next_clause(H1),!.
add_next_clause(H) :- assert(proof(H,predecessors,[])),!.


reload_proof_l([J|JobList]) :- 
	term2string(J,JS),
	concat_string(["tmp/ilf.a", JS, ".out"],F),
	get_uih_file(F,File),compile(File),
	retract(proof(H,control,rule([expert(_System,J)],_))),
	last_in_proof(J,HJ),
	proof(HJ,control,Cl),
	proof(HJ,status,St),
	retract(proof(H,status,_)),
	assert(proof(H,control,Cl)),
	assert(proof(H,status,St)),
	retract_all(proof(HJ,_,_)),
	reload_proof_l(JobList),!.
reload_proof_l([]) :- concat_string(["tmp/ilf.tmp.out"],F),
	get_uih_file(F,File),compile(File).

really_add_proof(StartJob,JobList) :-
	retract(proof(H,control,rule([bg(_,StartJob)],_))),
	make_pair_list(StartJob,JobList,Arg),
	assert(proof(H,control,rule([direct],Arg))),
	retract(proof(H,status,_)),
	assert(proof(H,status,subproof(StartJob))),!.

make_pair_list(N,[E|L],[[N,E]|NL]) :- make_pair_list(N,L,NL),!.
make_pair_list(_,[],[]).


/* ############## Ende der Transformation von Beweisen, die von pad im Hintergrund erzeugt wurden #################### */

PAD*/

/* ##########     Transformation von Spass-Blockbeweisen   ######### */

%----------------------------------------------------------------------------
%
% Build a Block Structured Proof
%
%----------------------------------------------------------------------------

dynamic :- sk_functions/1, sk_predicates/1.

:- op(1110,xfy,<->).

ilf_build_bsp(PH):-
	(current_module(spass_parser) ->
	    true;
	    open_right_module("dedsys/spass/spass_parser.pl")
	),
	!,
	spass_filenames(PH, DFG_File, FlotterFile, OriginFile, OutputFile, NamesFile),
	ilf_build_bsp(PH, DFG_File, FlotterFile, OriginFile, OutputFile, NamesFile).

ilf_build_bsp(PH, DFG_File, FlotterFile, OriginFile, OutputFile, NamesFile):-
	spass_dfg_problem(DFG_File, problem(_,_, logical_part(symbol_list(DFG_Functions,
								          DFG_Predicates,_,_,_),
						              _,DFG_Formulae,_,_),_)),
	!,
	spass_flotter_problem(FlotterFile, problem(_,_, logical_part(symbol_list(FlotterFunctions,
								                 FlotterPredicates,_,_,_),
							             _,_,FlotterClauses,_),_)),
	!,

	subtract(FlotterFunctions, DFG_Functions, SkFunctions),
	subtract(FlotterPredicates, DFG_Predicates, SkPredicates),
	assert(sk_functions(SkFunctions)),
	assert(sk_predicates(SkPredicates)),

	spass_origin(OriginFile, Assocs),
	!,
	spass_output(OutputFile, proof(Proof)),
	!,
	spass_axiom_names(NamesFile, AxiomNames),

	ilf_select_axioms(DFG_Formulae, DFG_Axioms),
	ilf_select_conjecture(DFG_Formulae, DFG_Conjecture),

	ilf_build_bsp_problem(PH, DFG_Conjecture, DFG_Axioms, AxiomNames, Proof, Proof1),
	ilf_build_bsp_flotter_clauses(PH, DFG_Conjecture, FlotterClauses, Assocs, PL),

	ilf_build_bsp_input_lines([PH, spass], PL, Proof1, Assocs, Proof2, PL1),
	ilf_build_bsp_proof([PH, spass], PL1, Proof2),
	!,
	abolish(sk_functions/1),
	abolish(sk_predicates/1).

ilf_build_bsp_problem(PH, DFG_Conjecture, DFG_Axioms, AxiomNames, ProofIn, ProofOut):-
	ilf_formula(DFG_Conjecture, ILF_Formula),
	assert(proof([PH, global], system, [spass])),
	assert(proof([PH, global], status, proved)),
	assert(proof([PH, global], goal, ILF_Formula)),
	assert(proof([PH, global], control, ready)),

	ilf_declare_axioms(1, DFG_Axioms, AxiomNames),
	ilf_declare_external_axioms(1, ProofIn, ProofOut),

	ilf_build_proof_node([PH, conjecture],
			     [],
			     rule([indirect], [[[PH, spass], assumption],
					       [[PH, spass], contradiction]]),
			     DFG_Conjecture,
			     subproof([PH, spass])).

ilf_build_bsp_flotter_clauses(PH, DFG_Conjecture, FlotterClauses, assocs(AAssocs, CAssocs), LastPL):-
	ilf_select_axioms(FlotterClauses, FlotterAxioms),
	ilf_select_conjectures(FlotterClauses, FlotterAssumptions),

	ilf_declare_flotter_axioms([PH, spass], [], FlotterAxioms, AAssocs, PL1),
	ilf_declare_assumption([PH, spass], PL1, DFG_Conjecture, PL2),
	ilf_declare_flotter_assumptions([PH, spass], PL2, FlotterAssumptions, CAssocs, LastPL).

ilf_declare_axioms(_,[],[]).
ilf_declare_axioms(No, [Name : Axiom|Rest], []):-
	ilf_specify_name(Name, Name1),
	ilf_build_proof_node([axiom(No), 0], [], axiom(Name1), Axiom, proved),
	SNo is No + 1,
	ilf_declare_axioms(SNo, Rest, []).
ilf_declare_axioms(No, [_Name : Axiom|Rest], [AxiomName|AxiomNames]):-
	ilf_specify_name(AxiomName, AxiomName1),
	ilf_build_proof_node([axiom(No), 0], [], axiom(AxiomName1), Axiom, proved),
	SNo is No + 1,
	ilf_declare_axioms(SNo, Rest, AxiomNames).

ilf_declare_external_axioms(_, [], []).
ilf_declare_external_axioms(No, [ProofLine|ProofIn], ProofOut):-
	ProofLine = proof_line(structure_info(label(NH),
	                                      split_level(SptLevel),
                                              origin(rule(Rule), ref(Ref))),
                               Formula),
	Rule = 'Ext',
	SptLevel = 0,
	Ref = [],

	ilf_build_proof_node([axiom(external(No)), NH], [], axiom(external(No)), Formula, proved),
        SNo is No +1,
	ilf_declare_external_axioms(SNo, ProofIn, ProofOut),
	!.
ilf_declare_external_axioms(No, [ProofLine|ProofIn], [ProofLine|ProofOut]):-
	ilf_declare_external_axioms(No, ProofIn, ProofOut).

ilf_declare_flotter_axioms(_, PL, [], [], PL).
ilf_declare_flotter_axioms(PH, PL, [_Name : Axiom|Axioms], [[No, OriginNo]|Assocs], LastPL):-

	ilf_select_sk(Axiom, FList, PList),
	ilf_build_proof_node([PH, axiom(No)], PL,
			     rule([clausify(FList, PList)], [[axiom(OriginNo), 0]]),
			     Axiom,
			     proved),
	ilf_declare_flotter_axioms(PH, [[PH, axiom(No)]], Axioms, Assocs, LastPL).

ilf_declare_assumption(PH, PL, Conjecture, LastPL):-
	ilf_formula(Conjecture, ILF_Formula),
	ilf_negate(ILF_Formula, NegILF_Formula),
	NH = [PH, assumption],
	LastPL = [NH],
	assert(proof(NH, contents, NegILF_Formula)),
	assert(proof(NH, predecessors, PL)),
	assert(proof(NH, status, assumption([]))).

ilf_declare_flotter_assumptions(_, PL, [], [], PL).
ilf_declare_flotter_assumptions(PH, PL, [_Name : Assumption|Assumptions], [[No, OriginNo]|Assocs], LastPL):-
%Konsistenzbedingung:
	OriginNo = 1,

	ilf_select_sk(Assumption, FList, PList),
	ilf_build_proof_node([PH, assumption(No)], PL,
			     rule([clausify(FList, PList)], [[PH, assumption]]),
			     Assumption,
			     proved), 
	ilf_declare_flotter_assumptions(PH, [[PH, assumption(No)]], Assumptions, Assocs, LastPL).

ilf_specify_name(noname, []):-
	!.
ilf_specify_name(ax_name(Dom, Ax), dcln(Dom, Ax)):-
	!.
ilf_specify_name(Name, Name).

ilf_build_bsp_input_lines(PH, PL, ProofIn, assocs(AAssocs, CAssocs), ProofOut, LastPL):-
	ilf_declare_axiom_clauses(PH, PL, ProofIn, AAssocs, Proof1, PL1),
	ilf_declare_assumption_clauses(PH, PL1, Proof1, CAssocs, ProofOut, LastPL).

ilf_declare_axiom_clauses(_, PL, Proof, [], Proof, PL).
ilf_declare_axiom_clauses(PH, PL, [FirstLine|InList], [[No, _OriginNo]|Assocs], OutList, LastPL):-
	FirstLine = proof_line(structure_info(label(NH),
	                                      split_level(_),
                                              origin(rule(Rule), ref(Ref))),
                               _Formula),
	No < NH,

%Konsistenzbedingungen:
	Rule = 'Inp',
	Ref = [],

	ilf_declare_axiom_clauses(PH, PL, [FirstLine|InList], Assocs, OutList, LastPL).

ilf_declare_axiom_clauses(PH, PL, [FirstLine|InList], [[No, _OriginNo]|Assocs], OutList, LastPL):-
	FirstLine = proof_line(structure_info(label(NH),
	                                      split_level(_),
                                              origin(rule(Rule), ref(Ref))),
                               Formula),
%Konsistenzbedingungen:
	No = NH,
	Rule = 'Inp',
	Ref = [],

	ilf_formula(Formula, ILF_Formula),
	ilf_build_proof_node([PH, NH], PL, rule([Rule], [[PH, axiom(No)]]), ILF_Formula, proved),
	ilf_declare_axiom_clauses(PH, [[PH, NH]], InList, Assocs, OutList, LastPL).

ilf_declare_assumption_clauses(_, PL, List, [], List, PL).
ilf_declare_assumption_clauses(PH, PL, [FirstLine|InList], [[No, _OriginNo]|Assocs], OutList, LastPL):-
	FirstLine = proof_line(structure_info(label(NH),
	                                      split_level(_),
                                              origin(rule(Rule), ref(Ref))),
                               Formula),
%Konsistenzbedingungen:
	Rule = 'Inp',
	Ref = [],

	ilf_formula(Formula, ILF_Formula),
	ilf_build_proof_node([PH, NH], PL, rule([Rule], [[PH, assumption(No)]]), ILF_Formula, proved),
	ilf_declare_assumption_clauses(PH, [[PH, NH]], InList, Assocs, OutList, LastPL).

ilf_select_conjecture(Formulae, Conjecture):-
	ilf_select_conjectures(Formulae, [_Name: Conjecture]).

ilf_select_conjectures([],[]).
ilf_select_conjectures([formulae(conjectures,_, Conjectures)|_], Conjectures):-
	!.
ilf_select_conjectures([formulae(Type,_,_)|Rest], Conjectures):-
	Type \= conjectures,
	ilf_select_conjectures(Rest, Conjectures).

ilf_build_bsp_proof(PH, PL, Proof):-
	ilf_select_referred(Proof, RestProof),
	ilf_build_sequence(PH, PL, RestProof,[]).

ilf_build_sequence(PH, PL, [ProofLine|Proof], OutList):-
	ProofLine = proof_line(structure_info(label(NH),_,
					      origin(rule(Rule), ref(Ref))),
			       Formula),
	ilf_aint_splitpoint(_, ProofLine),
	ilf_aint_contradiction(Formula),

	ilf_ref_list(Ref, LRef),
	ilf_build_proof_node([PH, NH], PL, rule([Rule], LRef), Formula, proved),
	ilf_build_sequence(PH, [[PH, NH]], Proof, OutList),
	!.

ilf_build_sequence(PH, PL, [ProofLine|Proof], Proof):-
	ProofLine = proof_line(structure_info(label(_),
	                                      split_level(_),
                                              origin(rule(Rule), ref(Ref))),
                               Formula),
	ilf_is_contradiction(Formula),

	ilf_ref_list(Ref, LRef),
	ilf_build_proof_node([PH, contradiction], PL, rule([Rule], LRef), contradiction, proved),
	!.

ilf_build_sequence(PH, PL, [ProofLine|Proof], OutList):-
	ProofLine = proof_line(structure_info(label(NH1),
	                                      split_level(SptLevel1),
                                              origin(rule(Rule1), ref(Ref1))),
                               Formula1),
	ilf_is_splitpoint(RefLabel, ProofLine),

	ilf_ref_list(Ref1, LRef1),
	LRef1 = [Ref_bar],
	SubPH1 = [[PH, RefLabel], case1],
	SubPH2 = [[PH, RefLabel], case2],

	ilf_ref_formula(RefLabel, RefFormula),
	ilf_build_proof_node([PH, [RefLabel, split]], PL,
			     rule([split],
				  [Ref_bar, SubPH1, SubPH2]),
			     neg(RefFormula), subproof([PH, RefLabel])),

	ilf_build_proof_node(SubPH1, [],
			     rule([case],
			          [[SubPH1, NH1], [SubPH1, contradiction]]),
			     neg(Formula1), subproof(SubPH1)), 
	ilf_build_proof_node([SubPH1, NH1], [], rule([Rule1], LRef1), Formula1, assumption([])),
 	ilf_build_sequence(SubPH1, [[SubPH1, NH1]], Proof, OutList1),

	ilf_second_case([PH, RefLabel], [SubPH1], OutList1, [SecondCase|OutList2], PL1),
	SecondCase = proof_line(structure_info(label(NH2),
	                                       split_level(SptLevel2),
                                               origin(rule(Rule2),_)),
                                Formula2),
%Konistenzbedingungen:
	ilf_is_splitpoint(RefLabel, SecondCase),
	SptLevel1 = SptLevel2,

	ilf_build_proof_node(SubPH2, PL1,
			     rule([case],
				  [[SubPH2, NH2], [SubPH2, contradiction]]),
			     neg(Formula2), subproof(SubPH2)), 
	ilf_build_proof_node([SubPH2, NH2], [], rule([Rule2], LRef1), Formula2, assumption([])),
	ilf_build_sequence(SubPH2, [[SubPH2, NH2]], OutList2, OutList),

	ilf_build_proof_node([PH, contradiction], [[PH, [RefLabel, split]]],
			     rule([split_con],
			          [Ref_bar, [PH, [RefLabel, split]]]),
			     contradiction, proved).

ilf_second_case(PH, PL, [ProofLine|Proof], Proof, [[PH, NH]]):-
	ProofLine = proof_line(structure_info(label(NH),
	                                      split_level(_),
                                              origin(rule(Rule), ref(Ref))),
                               Formula),
	Rule = 'Spt',
	Ref = [_,_],
	ilf_ref_list(Ref, LRef),
	ilf_build_proof_node([PH, NH], PL, rule([case_conclusion], LRef), Formula, proved),
	!.
ilf_second_case(_, PL, Proof, Proof, PL).

ilf_build_proof_node(ID, PL, Control, Formula, Status):-
	ilf_formula(Formula, ILF_Formula),
        assert(proof(ID, predecessors, PL)),
	assert(proof(ID, contents, ILF_Formula)),
	assert(proof(ID, status, Status)),
	assert(proof(ID, control, Control)).

ilf_ref_list([],[]):-
	!.
ilf_ref_list([Ref|Rest], [[PH, Ref]|RestL]):-
	proof([PH, Ref], status,_),
	ilf_ref_list(Rest, RestL),
	!.
ilf_ref_list(X,X).

ilf_ref_formula(Ref, RefFormula):-
	proof([_, Ref], contents, RefFormula),
	!.
ilf_ref_formula(_, true).

ilf_formula(neg(true), contradiction):-
	!.
ilf_formula(neg(Formula), ClosedILF_Formula -> contradiction):-
	ilf_formula(Formula, ILF_Formula),
	a_close(ILF_Formula, ClosedILF_Formula),
	!.
ilf_formula(proof_clause(constraint(C), antecedent(A), succedent(S)), ILF_Formula):-
	collect_vars(C, A, S, Vars),
	create_vars(Vars, VarTup, _NewVars),

	append(C, A, N_Atoms),
	ilf_negate_atoms(N_Atoms, NegAtoms),
	append(NegAtoms, S, Atoms),
	ilf_disjoin_atoms(Atoms, SpassTerm),

	substitute(SpassTerm, VarTup, SpassTerm1),
	ilf_formula1(SpassTerm1, ILF_Formula),
	!.
ilf_formula(Formula, ILF_Formula):-
	ilf_formula1(Formula, ILF_Formula).

ilf_disjoin_atoms([], []).
ilf_disjoin_atoms([Atom], Atom):-
	!.
ilf_disjoin_atoms([Atom1, Atom2], or(Atom1, Atom2)):-
	!.
ilf_disjoin_atoms([Atom|Atoms], or(Atom, A_Term)):-
	ilf_disjoin_atoms(Atoms, A_Term). 

ilf_negate_atoms([Atom|Atoms], [not(Atom)|N_Atoms]):-
	ilf_negate_atoms(Atoms, N_Atoms).
ilf_negate_atoms([], []).

collect_vars(L1, L2, L3, Vars):-
	collect_vars1(L1, VarsL1),
	collect_vars1(L2, VarsL2),
	union(VarsL1, VarsL2, Vars1),
	collect_vars1(L3, VarsL3),
	union(Vars1, VarsL3, Vars).

collect_vars1([], []).
collect_vars1([Clause|T], Vars):-
	compound(Clause),
	collect_vars(Clause, Vars1),
	collect_vars1(T, Vars2),
	union(Vars1, Vars2, Vars),
	!.
collect_vars1([_Clause|T], Vars):-
	collect_vars1(T, Vars).

collect_vars(Term, Vars):-
	compound(Term),
	Term =.. [_Op|Args],	
	sumlist(collect_vars, Args, [], Vars),
	!.
collect_vars(Var, [Var]):-
	var(Var),
	!.
collect_vars(Quoted, [Quoted]):-
	open("", string, s),
	printf(s, "%w", [Quoted]),
	current_stream(VarString,_, s),
	close(s),
	term_string(Var, VarString),
	var(Var),
	!.
collect_vars(_,[]).

collect_vars(Term, AccIn, AccOut):-
	collect_vars(Term, Vars),
	union(AccIn, Vars, AccOut).

ilf_negate(not ILF_Formula, ILF_Formula):-
	!.
ilf_negate(ILF_Formula, not ILF_Formula).

ilf_select_sk(Term, FList, PList):-
	sk_functions(SkFunctions),
	sk_predicates(SkPredicates),
	ilf_select_sk_operators(SkFunctions, Term, FList),
	ilf_select_sk_operators(SkPredicates, Term, PList).

ilf_select_sk_operators(SkOperators, Term, OpList):-
	compound(Term),
	Term =.. [Operator|Arguments],
	length(Arguments, Arity),
	ilf_select_sk_operators(SkOperators, Operator/Arity, [], OpList1),
	sumlist(ilf_select_sk_operators(SkOperators), Arguments, OpList1, OpList).
ilf_select_sk_operators(_, Term, []):-
	var(Term),
	!.
ilf_select_sk_operators(_, Term, []):-
	number(Term),
	!.
ilf_select_sk_operators(SkOperators, Term, OpList):-
	atom(Term),
	ilf_select_sk_operators(SkOperators, Term/0, [], OpList).

ilf_select_sk_operators(_, Term, List, List):-
	var(Term),
	!.
ilf_select_sk_operators(SkOperators, Operator/Arity, List, List):-
	nonmember(Operator/Arity, SkOperators),
	!.
ilf_select_sk_operators(SkOperators, Operator/Arity, ListIn, ListOut):-
	member(Operator/Arity, SkOperators),
	union(ListIn, [Operator/Arity], ListOut),
	!.
ilf_select_sk_operators(SkOperators, Term, ListIn, ListOut):-
	ilf_select_sk_operators(SkOperators, Term, OpList),
	union(ListIn, OpList, ListOut).

/*  ############# Ende Transformation von Spass-Blockbeweisen ########### */


/* Aufbereitung von Protein-Beweisen, die mit ILF gefuehrt wurden */

?- dynamic
	factor_cut/2,
	red_cut/2.
	
pt2bl :- proof([Name,global],goal,_),
	retract_all(proof(_,_,_)),
	get_right_file("dedsys/protein/proteinproof.exe",PPfexe),
	concat_string(["tmp/ilf.",Name,".r"],FName),
	get_uih_file(FName,Infile),
	concat_string([Infile,".ax"],Ax),
	concat_string([PPfexe," ",Infile," > ",Ax],Cmd),
	system(Cmd),
	make_ko_ax(Ax),
	concat_string([Infile,".tree"],Tree),
	compile(Tree),!,
	make_pf3(N),find_factors,
	pc2bl,
	add_pt_ax,
	add_choice(N),
	remove_duplicate,
	raise_subproofs,
	remove_restarts,
	make_done,
	rm_pt_query,
	ass_once,
	!.

?- dynamic pt_ax/4, pt_goal/2, pt_clause/2.

make_ko_ax(File) :- retract_all(pt_ax(_,_,_,_)),
	retract_all(pt_goal(_,_)),
	current_op(P,A,'->'),
	op(100,fx,'->'),
	compile(File),
	op(P,A,'->'),
	read_ko_ax.

read_ko_ax :- repeat, not make_pt_ax,!.

make_pt_ax :- 
	retract(pt_clause(Nr,C)),
	pt_name(Nr,InTh,Name),
	pt2ilf(C,C1),
	(
	C=[query|_],assert(pt_goal(Nr,C1))
	;
	unique_name(Name,Name1),
	asserta(pt_ax(Nr,InTh,C1,Name1))
	),!.

unique_name(goal,goal(N)) :- pt_ax(_,_,_,goal(N1)),N is N1+1,!.
unique_name(goal,goal(1)) :- !.
unique_name(N,N).

pt2ilf([query|C],C1) :- pt2ilf_goal(C,C1),!.
pt2ilf([restart|C],C1) :- pt2ilf(C,C1),!.
pt2ilf(L,(B -> H)) :- append(L0,['->'(L1)],L),
	pt2ilf_body(L0,B),
	pt2ilf_head(L1,H),!.
pt2ilf(C,C1) :- pt2ilf_head(C,C1),!.

pt2ilf_goal([C],C1) :- pt2ilf_head([C],CC),
	(CC=not(C1);C1=not(C)),!.
pt2ilf_goal([C|CL],(C1,B)) :- pt2ilf_goal([C],C1),
	pt2ilf_goal(CL,B),!.
	
pt2ilf_head([C],not(CC1)) :- 
	C=..[Op|Arg],
	name(Op,[110,111,116,95|OpL1]),
	name(Op1,OpL1),
	CC1=..[Op1|Arg],!.
pt2ilf_head([C],C) :- !.
pt2ilf_head([C|CL],(C1;B)) :- pt2ilf_head([C],C1),pt2ilf_head(CL,B),!.
pt2ilf_head(C,C).

pt2ilf_body([C],C1) :- pt2ilf_head([C],C1),!.
pt2ilf_body([C|CL],(C1,H)) :- pt2ilf_head([C],C1),pt2ilf_body(CL,H),!.
pt2ilf_body(C,C).

?- dynamic(ptproof/3).

make_pf3(N) :- retract_all(ptproof(_,_,_)),
	trc(X,Y,Z),
	numbervars(trc(X,Y,Z),1,N1),
	(N is N1-1),
	make_pf3(trc(X,Y,Z),[]),!.

make_pf3(trc(C,info(Nr,R,A1,A2),L),PL) :-
	(
	C=..[Op|Arg],
	name(Op,[110,111,116,95|OpL1]),
	name(Op1,OpL1),
	CC1=..[Op1|Arg],
	CC=not(CC1)
	;
	CC=C
	),!,
	assert(ptproof([1,PL],contents,CC)),
	(PL=[_|PL1],Pred=[[1,PL1]];Pred=[]),!,
	assert(ptproof([1,PL],predecessors,Pred)),
	assert(ptproof([1,PL],control,rule(R,A2,A1))),
	(R=query,A1=0 -> write(Nr),nl;true),
	make_pf3_l(L,PL,1),!.
make_pf3(X,_) :- write("ERROR:"),write(X),!.

make_pf3_l([E|L],PL,N) :- make_pf3(E,[N|PL]),(N1 is N+1),make_pf3_l(L,PL,N1),!.
make_pf3_l([],_,_).

sort_pos_neg(P,PNL) :- 
	bagof(Q,ptproof(Q,predecessors,[P]),QL),
	pos_neg(QL,Pos,Neg),
	pt_sort(Pos,Neg,PNL),!.

get_pos_neg(P,Pos,Neg) :- 
	bagof(Q,ptproof(Q,predecessors,[P]),QL),
	pos_neg(QL,Pos,Neg),!.
get_pos_neg(_,[],[]).


pos_neg([Q|QL],Pos,[Q|Neg]) :- 
	need_subproof(Q),
	!,pos_neg(QL,Pos,Neg),!.
pos_neg([Q|QL],[Q|Pos],Neg) :- ptproof(Q,control,rule(R,_,_)),
	member(R,[ext,fact,red_cut,factor_cut,th_start,th_ext,th_fact]),!,pos_neg(QL,Pos,Neg),!.
pos_neg([],[],[]) :- !.
pos_neg([Q|_],[],[]) :- ptproof(Q,control,rule(R,_,_)),
	ilf_serv_error((write("Unknown rule "),write(R),nl)),!.

need_subproof(P) :- red_cut(_,P),!.
need_subproof(Q) :- ptproof(Q,control,rule(R,_,_)),
	member(R,[restart]),!.

find_factors :- retract_all(factor_cut(_,_)),
	retract_all(red_cut(_,_)),fail.
find_factors :- 
	ptproof(P,control,rule(factor_cut,0,N)),
	once((
		factored_with(P,N,Q),
		retract(ptproof(P,control,_)),
		assert(ptproof(P,control,rule(factor_cut,x,Q))),
		assert(factor_cut(P,Q))
	)),
	fail.
find_factors :- 
	ptproof(P,control,rule(red_cut,0,N)),
	number(N),
	once((
		red_with(P,Q),
		retract(ptproof(P,control,_)),
		assert(ptproof(P,control,rule(red_cut,0,Q))),
		assert(red_cut(P,Q))
	)),
	fail.
find_factors :- 
	ptproof(P,control,rule(red,0,_)),
	once((
		red_with(P,Q),
		retract(ptproof(P,control,_)),
		assert(ptproof(P,control,rule(red_cut,0,Q))),
		assert(red_cut(P,Q))
	)),
	fail.
find_factors :- 
	ptproof(P,control,rule(th_red,0,_)),
	once((
		red_with(P,Q),
		retract(ptproof(P,control,_)),
		assert(ptproof(P,control,rule(red_cut,0,Q))),
		assert(red_cut(P,Q))
	)),
	fail.
find_factors :- pt_before.

factored_with(P,N,Q) :- ptproof(P,contents,not(_)),!,
	factored_with(P,-,N,P,Q),!.
factored_with(P,N,Q) :- factored_with(P,+,N,P,Q),!.

factored_with(P,_,0,Q,Q) :- ptproof(P,contents,CP),ptproof(Q,contents,CQ),!,
	(CP=CQ
	;
	ilf_serv_error((
		write("ERROR: Cannot factor "),write(CP),
		write(" at "),write(P),
		write(" with "),write(CQ),
		write(" at "),write(Q),nl
	))
	),!.
factored_with(P,S,N,Q,QQ) :- get_next_aunt(Q,S,Q1),
	N1 is N-1,
	factored_with(P,S,N1,Q1,QQ),!.
factored_with(P,_,_,_,_) :- ilf_serv_error((
	write("ILF ERROR: No factor for node "),
	write(P),ptproof(P,contents,C),
	write(" with contents "),write(C),nl
	)),!.

get_next_aunt([N,[1|R]],S,Q) :- !,
	get_next_aunt([N,R],S,Q),!.
get_next_aunt([N,[K|R]],-,[N,[K1|R]]) :- K1 is K-1,
	ptproof([N,[K1|R]],contents,not(_)),
	!.
get_next_aunt([N,[K|R]],+,[N,[K1|R]]) :-
	K1 is K-1,
	not ptproof([N,[K1|R]],contents,not(_)),!.
get_next_aunt([N,[K|R]],S,Q) :- K1 is K-1,
	get_next_aunt([N,[K1|R]],S,Q),!.

red_with([1,P],[1,Q]) :- 
	ptproof([1,P],contents,CP),
	negLits([CP],[CQ]),
	is_tail(Q,P),
	ptproof([1,Q],contents,CQ),
	!.
red_with(P,_) :- ilf_serv_error((
	write("ILF ERROR: No reduction for node "),
	write(P),ptproof(P,contents,C),
	write(" with contents "),write(C),nl
	)),!.

is_tail(P,[_|P]).
is_tail(P,[_|Q]) :- is_tail(P,Q).

?- dynamic(pt_before/2).

pt_before :- retract_all(pt_before(_,_)),fail.
pt_before :- factor_cut([1,P],[1,Q]),
	sibling(Q,P,Q1,P1),
	assert(pt_before(Q1,P1)),fail.
pt_before.

sibling([N1|Q],P,[N1|Q],[N2|Q]) :- append(_,[N2|Q],P),!.
sibling([_|Q],P,Q1,P1) :- sibling(Q,P,Q1,P1),!.
/*
sibling([_|P],[N|P],[N|P]) :- !.
sibling(P,[_|Q],R) :- sibling(P,Q,R),!.
sibling(P,[],[]) :- write("ILF ERROR: Sibling of "),
	write(P),write(" not found\n"),fail.
*/

pc2bl :- retract_all(proof(_,_,_)),fail.
pc2bl :- 
	H=[0,0],
	setof(G,N^pt_goal(N,G),GL),
	list_head(GL,GB),
	e_close(GB,GE),
	assert(proof([0,global],goal,GE)),
	get_protein_theory(T),
	assert(proof([0,global],control,[protein_theory(T)])),
	assert(proof([0,global],system,[protein,ilf])),
	assert(proof(H,contents,query)),
	assert(proof(H,predecessors,[])),
	assert(proof(H,status,subproof(1))),
	assert(proof(H,control,rule([direct],[[1,[]]]))),
	assert(proof([1,[]],contents,query)),
	assert(proof([1,[]],predecessors,[])),
	pc2bl([1,[]]),
	!.

/* pc2bl(H1): H1 ist als Knoten mit contents und predecessor eingefuegt,
* Rechtfertigung muss noch aufgebaut werden
*/
pc2bl([N,P]) :- ptproof([_,P],control,R),
	pc2bl([N,P],R),!.

pc2bl([N,P],rule(query,_,NQ)) :-
	get_pos_neg([_,P],Pos1,Neg),
	pt_sort(Pos1,Neg,PNL),
	ins_pos_neg_l([N,P],PNL,Arg),
	assert(proof([N,P],control,rule([query],[[ax,NQ]|Arg]))),
	assert(proof([N,P],status,proved)),
	proof(H,status,subproof(N)),
	retract(proof(H,control,rule(_,Arg1))),
	(
	pt_goal(NQ,_),R=restart
	;
	R=indirect
	),
	assert(proof(H,control,rule([R],Arg1))),!.
pc2bl([N,P],rule(ext,C,A)) :- 
	get_pos_neg([_,P],Pos1,Neg),Neg=[],
	sort_pos(Pos1,[],[],Pos),
	ins_pos([N,P],Pos,Arg),
	assert(proof([N,P],control,rule([ext(C)],[[ax,A]|Arg]))),
	assert(proof([N,P],status,proved)),!.

pc2bl([N,P],rule(th_ext,C,A)) :- 
	get_pos_neg([_,P],Pos1,Neg),
	sort_pos(Pos1,[],[],Pos),
	ins_pos([N,P],Pos,LPos),
	ins_new_ind_l(Neg,[N,P],NPL),
	append(LPos,NPL,Arg),
	assert(proof([N,P],control,rule([th_ext(C)],[[ax,A]|Arg]))),
	assert(proof([N,P],status,proved)),!.
pc2bl(H,rule(th_start,C,A)) :- pc2bl(H,rule(th_ext,C,A)),!.
pc2bl([N,P],rule(ext,C,A)) :- 
	get_pos_neg([_,P],Pos1,Neg),
	sort_pos(Pos1,[],[],Pos),
	ins_pos([N,P],Pos,LPos),
	ins_new_ind_l(Neg,[N,P],NPL),
	append(LPos,NPL,Arg),
	assert(proof([N,P],control,rule([ext(C)],[[ax,A]|Arg]))),
	assert(proof([N,P],status,proved)),!.
pc2bl([N,P],rule(ext,C,A)) :- 
	get_pos_neg([_,P],Pos1,Neg),
	sort_pos(Pos1,[],[],Pos),
	ins_pos([N,P],Pos,LPos),
	ins_case([N,P],A,LPos,Neg,LNeg),
	append(LNeg,LPos,Arg),
	assert(proof([N,P],control,rule([case(C)],[[ax,A]|Arg]))),
	assert(proof([N,P],status,proved)),!.
pc2bl(H,rule(fact,_,A)) :-
	assert(proof(H,status,proved)),
	assert(proof(H,control,rule([since],[[ax,A]]))),!.
pc2bl(H,rule(th_fact,_,A)) :- pc2bl(H,rule(fact,_,A)),!.
pc2bl(H,rule(factor_cut,_,[_,A])) :-
	assert(proof(H,status,proved)),
	proof([N,A],_,_),
	assert(proof(H,control,rule([since],[[N,A]]))),!.
pc2bl(H,rule(red_cut,_,[_,A])) :-
	assert(proof(H,status,proved)),
	proof([_,A],status,subproof(Pf)),
	proof([Pf,N],predecessors,[]),
	assert(proof(H,control,rule([since],[[Pf,N]]))),!.
pc2bl(H,rule(red,_,[_,A])) :-
	assert(proof(H,status,proved)),
	proof([_,A],status,subproof(Pf)),
	proof([Pf,N],predecessors,[]),
	assert(proof(H,control,rule([since],[[Pf,N]]))),!.
pc2bl(_,rule(R,_,_)) :- ilf_serv_error((
	write("ILF ERROR: Unknown rule "),
	write(R),nl
	)),!.

ins_pos_neg_l(H,[(P/'+')|Pos],[H1|Arg]) :-
	ins_pos(H,[P],[H1]),!,
	ins_pos_neg_l(H,Pos,Arg),!.
ins_pos_neg_l(H,[(P/'-')|Pos],[H1|Arg]) :-
	ins_new_ind_l([P],H,[H1]),!,
	ins_pos_neg_l(H,Pos,Arg),!.
ins_pos_neg_l(_,[],[]).

ins_pos([N,P],[[_,Q]|Pos],[[N,Q]|Arg]) :-
	ptproof([_,Q],contents,C),
	assert(proof([N,Q],contents,C)),
	retract(proof([N,P],predecessors,Pred)),
	assert(proof([N,P],predecessors,[[N,Q]])),
	assert(proof([N,Q],predecessors,Pred)),
	pc2bl([N,Q]),!,
	ins_pos([N,P],Pos,Arg),!.
ins_pos(_,[],[]).

/* Bei [N,P] wird NP mit indirektem Beweis eingefuegt */
ins_ind([N,P],NP) :- ptproof([_,NP],control,rule(restart,_,_)),!,
	ptproof([_,NP],contents,NegC),
	(NegC=not(C);C=not(NegC)),
	assert(proof([N,NP],contents,NegC)),
	retract(proof([N,P],predecessors,Pred)),
	assert(proof([N,P],predecessors,[[N,NP]])),
	assert(proof([N,NP],predecessors,Pred)),
	gen_pf_hdl(Pf),
	assert(proof([N,NP],status,subproof(Pf))),
	ptproof([_,[K|NP]],control,rule(R,I,A)),
	assert(proof([Pf,[K|NP]],contents,contradiction)),
	assert(proof([Pf,0],contents,C)),
	assert(proof([Pf,0],status,assumption([]))),
	assert(proof([Pf,0],predecessors,[])),
	assert(proof([Pf,[K|NP]],predecessors,[[Pf,0]])),
	assert(proof([N,NP],control,rule([indirect],[[Pf,0],[Pf,[K|NP]]]))),
	pc2bl([Pf,[K|NP]],rule(R,I,A)),!.
ins_ind([N,P],NP) :-
	ptproof([_,NP],contents,NegC),
	(NegC=not(C);C=not(NegC)),
	assert(proof([N,NP],contents,NegC)),
	retract(proof([N,P],predecessors,Pred)),
	assert(proof([N,P],predecessors,[[N,NP]])),
	assert(proof([N,NP],predecessors,Pred)),
	gen_pf_hdl(Pf),
	assert(proof([N,NP],status,subproof(Pf))),
	ptproof([_,NP],control,rule(R,I,A)),
	assert(proof([Pf,NP],contents,NegC)),
	assert(proof([Pf,0],contents,C)),
	assert(proof([Pf,0],status,assumption([]))),
	assert(proof([Pf,0],predecessors,[])),
	assert(proof([Pf,NP],predecessors,[[Pf,0]])),
	assert(proof([Pf,1],contents,contradiction)),
	assert(proof([Pf,1],predecessors,[[Pf,NP]])),
	assert(proof([Pf,1],status,proved)),
	assert(proof([Pf,1],control,rule([in(contradiction)],[[Pf,0],[Pf,NP]]))),
	assert(proof([N,NP],control,rule([indirect],[[Pf,0],[Pf,1]]))),
	pc2bl([Pf,NP],rule(R,I,A)),!.


ins_new_ind_l([[_,NP]|Neg],[N,P],[[N,NP]|NegP]) :-
	ins_ind([N,P],NP),!,
	ins_new_ind_l(Neg,[N,P],NegP),!.
ins_new_ind_l([],_,[]).

ins_neg([N,P],[NP],[[N,NP]]) :- ins_ind([N,P],NP),!.
ins_neg(_,[],[]) :- !.
ins_neg(H,NL,_Arg) :- ilf_serv_error((
	write("ILF ERROR ins_neg with "),write((H,NL)),nl)).

pt_sort(Pos,Neg,PNL) :- pt_sort(Pos,Neg,[],[],[],PNL),!.

pt_sort([P|L],Neg,LPwait,LNwait,Ltmp,L1) :- pt_try_insert(P,'+',Ltmp,Ltmp1),
	pt_sort(L,Neg,LPwait,LNwait,Ltmp1,L1),!.
pt_sort([P|L],Neg,LPwait,LNwait,Ltmp,L1) :- 
	pt_sort(L,Neg,[P|LPwait],LNwait,Ltmp,L1),!.
pt_sort([],[P|L],LPwait,LNwait,Ltmp,L1) :- pt_try_insert(P,'-',Ltmp,Ltmp1),
	pt_sort([],L,LPwait,LNwait,Ltmp1,L1),!.
pt_sort([],[P|L],LPwait,LNwait,_Ltmp,L1) :- 
	pt_sort([],L,LPwait,[P|LNwait],_Ltmp1,L1),!.
pt_sort([],[],[],[],L,L1) :- rev(L,L1),!.
pt_sort([],[],LPwait,LNwait,Ltmp,L1) :- pt_sort(LPwait,LNwait,[],[],Ltmp,L1),!.

pt_try_insert([_,P],_,L,_) :- pt_before(Q,P),not member(([_,Q]/_),L),!,fail.
pt_try_insert(P,S,L,[(P/S)|L]).

sort_pos([P|L],Lwait,Ltmp,L1) :- try_insert(P,Ltmp,Ltmp1),
	sort_pos(L,Lwait,Ltmp1,L1),!.
sort_pos([P|L],Lwait,Ltmp,L1) :- sort_pos(L,[P|Lwait],Ltmp,L1),!.
sort_pos([],[],L,L1) :- rev(L,L1),!.
sort_pos([],Lwait,Ltmp,L1) :- sort_pos(Lwait,[],Ltmp,L1),!.

try_insert(P,L,_) :- pt_before(Q,P),not member(Q,L),!,fail.
try_insert(P,L,[P|L]).

add_pt_ax :- pt_ax(N,_,Ax,Name),assert(proof([ax,N],contents,Ax)),
	assert(proof([ax,N],control,axiom(Name))),
	assert(proof([ax,N],status,proved)),
	assert(proof([ax,N],predecessors,[])),
	fail.
add_pt_ax.

rm_pt_query :- 
	setof(G1,N^pt_goal(N,G1),GL),
	list_body(GL,G),
	e_close(G,GE),
	retract(proof([0,0],contents,_)),
	assert(proof([0,0],contents,GE)),!,
	change_pt_query.

change_pt_query :-
	collect_proof_pars, 
	pt_goal_clauses,
	!.

pt_goal_clauses :- 
	not (
	/*	proof([ax,N],control,axiom(goal))*/
	pt_goal(N,_),
	used_for([ax,N],H),not H=[1,[]]
	),!,
/* keine Zielklausel benutzt - nur fuer Ende */
	make_pt_direct,!.
pt_goal_clauses :- 
	pt_goal(N,_),
	used_for([ax,N],_),
	proof([ax,N],contents,C1),
	a_close(C1,C),
	add_pt_ass(C,N,_NN),
	fail.
pt_goal_clauses :- retract(proof(H,contents,query)),
	assert(proof(H,contents,contradiction)),fail.
pt_goal_clauses.

make_pt_direct :- retract(proof([0,0],control,rule([indirect_all(V)|L],A))),
	assert(proof([0,0],control,rule([direct_all(V)|L],A))),
	fail.
make_pt_direct :- 
/*	proof([ax,N],control,axiom(goal)),*/
	pt_goal(N,_),
	retract_all(proof([ax,N],_,_)),
	used_for([ax,N],H),
	proof(H,contents,query),
	rm_pos(H),
	fail.
make_pt_direct.

add_pt_ass(C,N,NN) :- gen_hdl(NN),
	assert(proof([1,NN],contents,C)),
	assert(proof([1,NN],status,assumption([]))),
	retract(proof([1,A],predecessors,[])),
	assert(proof([1,A],predecessors,[[1,NN]])),
	assert(proof([1,NN],predecessors,[])),
	change_used([ax,N],[1,NN]),
	retract(proof([0,0],control,rule(R,Arg))),
	assert(proof([0,0],control,rule(R,[[1,NN]|Arg]))),
	retract_all(proof([ax,N],_,_)),!.


get_arg_contents([A],G) :- proof(A,contents,G),!.
get_arg_contents([A|Arg],(G,GA)) :- proof(A,contents,G),
	get_arg_contents(Arg,GA),!.

get_pt_answer(exists(V,G),Arg,V) :- get_goal_list(G,GL),
	get_arg_list(Arg,ArgL),
	is_answer(ArgL,GL),!.
get_pt_answer(exists(V,G),Arg,V) :- get_arg_list(Arg,ArgL),
	ilf_serv_error((
		write("Ilf ERROR: I don't see that "),write(ArgL),
		write(" is a solution of "),
		write(G),nl
	)).

get_pt_answer(_,_,[]).

get_goal_list((A;_),L) :- get_goal_list(A,L).
get_goal_list((_;B),L) :- get_goal_list(B,L).
get_goal_list((A,B),L) :- get_goal_list(A,AL),get_goal_list(B,BL),
	append(AL,BL,L),!.
get_goal_list(A,[A]).

get_arg_list([A|AL],[C|CL]) :- proof(A,contents,C),get_arg_list(AL,CL),!.
get_arg_list([],[]).

is_answer([A|AL],L) :- member(A,L),is_answer(AL,L).
is_answer([],_).

/*
split_case(_,H,indirect) :- retract(proof(H,control,rule(_,Arg))),
	assert(proof(H,control,rule([indirect],Arg))),!.
split_case(Pf,H,case) :- proof(H,contents,CH),
	proof_pars(Pf,_,_,_,Ref),
	add_pf_ass(Pf,Ref,Ass,NAss,CL),
	proof([Pf0,global],goal,_),
	proof([Pf0,_],status,subproof(Pf1)),
	last_in_proof(Pf1,HQ),
	gen_hdl(NN),
	proof([Pf,NA],predecessors,[]),
	proof([Pf,NA],contents,CA),
	list_body([CA|CL],B),
	assert(proof([Pf1,NN],contents,(B -> query))),
	retract(proof(HQ,predecessors,Pred)),
	assert(proof(HQ,predecessors,[[Pf1,NN]])),
	assert(proof([Pf1,NN],predecessors,Pred)),
	(
	retract(proof(HQ,contents,(BQ -> Q))),
	assert(proof(HQ,contents,((CH,BQ) -> Q)))
	;
	retract(proof(HQ,contents,Q)),
	assert(proof(HQ,contents,(CH -> Q))),
	),
	proof(HQ,status,subproof(Pf2)),
	gen_hdl(As2),
	assert(proof([Pf2,As2],contents,CH)),
	assert(proof([Pf2,As2],status,assumption([]))),
	retract(proof([Pf2,N2],predecessors,[])),
	assert(proof([Pf2,N2],predecessors,[[Pf2,As2]])),
	assert(proof([Pf2,As2],predecessors,[])),
	retract(proof(H,control,rule(_,Arg))),
	assert(proof(H,control,rule([since],[[Pf2,As2]]))),
	change_in_subproof(Pf2,H,[Pf2,As2]),
	assert(proof([Pf1,NN],status,subproof(Pf))),
	append(NAss,Arg,Arg1),
	assert(proof([Pf1,NN],control,rule([protein_case],Arg1))),
	!.
*/
/* get_restarts(Pf,PL,CL) bestimmt die erste Folge von restart-Punkten im Beweis Pf */
get_restarts(Pf,PL,CL) :- proof([Pf,N],predecessors,[]),
	get_restarts1([Pf,N],PL,CL),!.

get_restarts1(H,PL,CL) :- proof(H,control,rule([restart],_)),
	do_get_restarts(H,PL,CL),!.
get_restarts1(H,PL,CL) :- proof(H1,predecessors,[H]),!,
	get_restarts1(H1,PL,CL),!.

/* Finden einer zusammenhaengenden Folge von restart-Punkten, die nicht mit since erledigt werden koennen */
do_get_restarts(H,[],[]) :- not proof(H,control,rule([restart],_)),!.
do_get_restarts(H,[],[]) :- proof(H,contents,C),
	proof(H1,contents,C),
	block_1_usable(H1,H),
	retract(proof(H,status,subproof(Pf))),
	ilf_serv_log((write("Removing subproof "),write(Pf),write(" below "),write(C),nl)),
	assert(proof(H,status,proved)),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule([since],[H1]))),
	rm_subproof(Pf),
	collect_proof_pars,!.
do_get_restarts(H,[H|PL],[C|CL]) :- proof(H,control,rule([restart],_)),
	proof(H,contents,C),!,
	proof(H1,predecessors,[H]),
	do_get_restarts(H1,PL,CL),!.
do_get_restarts(_,[],[]).

split_case(_,[],[]) :- !.
split_case(Pf,[H|PL],CL) :-
	proof([_,global],goal,G),
	gen_hdl(NEnd),
	assert(proof([Pf,NEnd],contents,G)),
	retract(proof(H,predecessors,Pred)),
	assert(proof(H,predecessors,[])),
	assert(proof([Pf,NEnd],predecessors,Pred)),
	case_top([Pf,NEnd]),
	gen_pf_hdl(NPf),
	assert(proof([Pf,NEnd],status,subproof(NPf))),
	list_body(CL,B),
	ins_basic_case(H,NPf,B,G,HNeu),
	ins_rest_cases([H|PL],NPf,CL,G,HCase),
	negLits(CL,CD),
	assert(proof([Pf,NEnd],control,rule([protein_case(CD)],[HNeu|HCase]))),!.

case_top([Pf,NEnd]) :- proof(H,status,subproof(Pf)),
	retract(proof(H,control,R)),
	(
	R=rule([direct_all(V)],_),RR=rule([direct_all(V)],[[Pf,NEnd]])
	;
	RR=rule([ilf_case,direct],[[Pf,NEnd]])
	),
	assert(proof(H,control,RR)),!.

ins_basic_case(H,NPf,B,G,[NPf,NN]) :-
	gen_hdl(NN),
	assert(proof([NPf,NN],contents,(B -> G))),
	gen_pf_hdl(CPf),
	assert(proof([NPf,NN],status,subproof(CPf))),
	assert(proof([NPf,NN],predecessors,[])),
	gen_hdl(CN),
	assert(proof([CPf,CN],contents,B)),
	assert(proof([CPf,CN],status,assumption([]))),
	assert(proof([CPf,CN],predecessors,[])),
	modify_basic_case(H,G,CPf,CN,CN),
	last_in_proof(CPf,HG),
	assert(proof([NPf,NN],control,rule([ilf_case,direct],[[CPf,CN],HG]))),!.

modify_basic_case([Pf0,N],G,Pf,LN,CN) :- 
	proof([Pf0,N],control,rule([restart],_)),
	assert(proof([Pf,N],control,rule([since],[[Pf,CN]]))),
	assert(proof([Pf,N],status,proved)),
	assert(proof([Pf,N],predecessors,[[Pf,LN]])),
	proof([Pf0,N],contents,C),
	assert(proof([Pf,N],contents,C)),
	change_pt_used([Pf0,N],[Pf,N]),
	proof([Pf0,N],status,subproof(PP)),
	assert(tmp(had_subproof([Pf0,N],PP))),
	retract_all(proof([Pf0,N],_,_)),!,
	proof(H,predecessors,[[Pf0,N]]),
	modify_basic_case(H,G,Pf,N,CN),!.
modify_basic_case(H,G,Pf,_,_) :- modify_basic_case(H,G,Pf),!.

modify_basic_case([Pf0,N],G,Pf) :- change_pt_used([Pf0,N],[Pf,N]),!,
	rename_line([Pf0,N],Pf),
	test_basic_end([Pf0,N],G,Pf),!.

test_basic_end(H,G,Pf) :- proof(H1,predecessors,[H]),!,
	modify_basic_case(H1,G,Pf),!.
test_basic_end([_,N],G,Pf) :- retract(proof([Pf,N],contents,done(Ans))),
	assert(proof([Pf,N],contents,G)),
	retract(proof([Pf,N],control,rule(_,Arg))),
	(G=exists(V,_),RR=rule([pt_answer(V,Ans)],Arg)
	;
	RR=rule([pt_answer([],Ans)],Arg)
	),
	assert(proof([Pf,N],control,RR)),!.
/* Wenn nicht mehr done dasteht, ist das Ende schon mal behandelt worden */
test_basic_end(_,_,_).

change_pt_used(H1,H2) :- retract(used_for(H1,H3)),
	once((
		change_refs(H1,[H3],H2),
		assert(used_for(H2,H3))
	)),fail.
change_pt_used(H1,H2) :- retract(used_for(H3,H1)),assert(used_for(H3,H2)),fail.
change_pt_used(_,_).

rename_line([Pf0,N],Pf1) :- retract(proof([Pf0,N],contents,C)),
	assert(proof([Pf1,N],contents,C)),
	retract(proof([Pf0,N],status,S)),
	assert(proof([Pf1,N],status,S)),
	retract(proof([Pf0,N],predecessors,[[_,NN]])),
	assert(proof([Pf1,N],predecessors,[[Pf1,NN]])),
	retract(proof([Pf0,N],control,R)),
	assert(proof([Pf1,N],control,R)),!.
rename_line(H,P) :- ilf_serv_error((
	write("ILF ERROR renaming "),
	write(H),write(" to "),write(P)
	)).

ins_rest_cases([H|PL],NPf,[not(C)|CL],G,[[NPf,NC]|HCase]) :-
	gen_hdl(NC),
	assert(proof([NPf,NC],contents,(C -> G))),
	last_in_proof(NPf,HL),
	assert(proof([NPf,NC],predecessors,[HL])),
	retract(tmp(had_subproof(H,Pf))),
	assert(proof([NPf,NC],status,subproof(Pf))),
	proof([Pf,NAss],predecessors,[]),
	last_in_proof(Pf,HL0),
	retract(proof(HL0,contents,done(Ans))),
	assert(proof(HL0,contents,G)),
	retract(proof(HL0,control,rule(_,Arg))),
	(G=exists(V,_),RR=rule([pt_answer(V,Ans)],Arg)
	;
	RR=rule([pt_answer([],Ans)],Arg)
	),
	assert(proof(HL0,control,RR)),!,
	assert(proof([NPf,NC],control,rule([ilf_case,direct],[[Pf,NAss],HL0]))),!,
	ins_rest_cases(PL,NPf,CL,G,HCase),!.
ins_rest_cases([],_,_,_,[]).

remove_restarts :- setof(P,A^proof(P,control,rule([restart],A)),PL),
	remove_restarts(PL),!.
remove_restarts :- proof([Pf,global],goal,G),
	proof([Pf,N],status,subproof(_)),
	retract(proof([Pf,N],contents,_)),
	assert(proof([Pf,N],contents,G)),!.
	
remove_restarts(PL) :- collect_proof_pars,
	setof(AH,proof(AH,control,axiom(goal)),AHL),
	get_restart_lemmas(PL,AHL,Lemmas,Other),
	remove_goal_restarts(Other),
	subproof_to_lemma_l(Lemmas),
	!.

get_restart_lemmas([P|PL],AHL,[P|Lemmas],Other) :-
	proof(P,status,subproof(Pf)),
	proof_pars(Pf,_,_,_,ExtRefs),
	not (member(U,AHL),member(U,ExtRefs)),!,
	get_restart_lemmas(PL,AHL,Lemmas,Other),!.
get_restart_lemmas([P|PL],AHL,Lemmas,[P|Other]) :-
	get_restart_lemmas(PL,AHL,Lemmas,Other),!.
get_restart_lemmas([],_,[],[]).



/* Ende Fallunterscheidung */


add_choice(N) :- length(V,N),numbervars(V,1,_),
	proof([Pf,global],goal,_),
	proof([Pf,K],status,subproof(_)),
	retract(proof([Pf,K],control,rule(R,Arg))),
	(R=[direct],RR=[direct_all(V)]
	;
	RR=[indirect_all(V)]
	),
	assert(proof([Pf,K],control,rule(RR,Arg))),!.

get_protein_theory(T) :- setof(Name,Nr^C^Ax^Name^(pt_ax(Nr,Ax,C,Name),not Ax=0),T),!.
get_protein_theory([]).

/* make_appendix(Op,Pre,Post) stellt die Axiome deren Namen in L von
* proof([_,global,control,L) als Op(NamenListe) abgespeichert sind 
* als Klauseln in den Anhang.
* An pre_text wird das rulescript Pre angehaengt, nach "Appendix" wird das
* rule_script Post abgearbeitet
*/
make_appendix(Op,Pre,Post) :- F=..[Op,T],
	proof([Pf,global],goal,_),
	proof([Pf,global],control,L),
	member(F,L),!,
	collect_proof_pars,
	used_theory(T,TU),
	make_the_appendix(Pre,Post,TU),!.

used_theory([AxN|T],[AxN|TU]) :- 
	proof(Ax,control,axiom(AxN)),
	used_for(Ax,_),!,
	retract(proof(Ax,contents,C)),
	standard_sequence(C,C1),
	assert(proof(Ax,contents,C1)),
	used_theory(T,TU),!.
used_theory([_|T],TU) :- used_theory(T,TU),!.
used_theory([],[]).

standard_sequence((A -> false),C) :- !,
	body_list(A,AL),
	negLits(AL,ALD),
	split_neg_pos(ALD,LN,LP),
	list_ar_seq(LN,LP,C),!.
standard_sequence((true -> B),C) :- !,
	head_list(B,LB),
	split_neg_pos(LB,LN,LP),
	list_ar_seq(LN,LP,C),!.
standard_sequence((A -> B),C) :- body_list(A,AL),
	negLits(AL,ALD),
	head_list(B,BL),
	append(ALD,BL,L),
	split_neg_pos(L,LN,LP),
	list_ar_seq(LN,LP,C),!.
standard_sequence(A,C) :- standard_sequence((true -> A),C),!.

split_neg_pos([not(L)|CL],[L|CLN],CLP) :- split_neg_pos(CL,CLN,CLP),!.
split_neg_pos([L|CL],CLN,[L|CLP]) :- split_neg_pos(CL,CLN,CLP),!.
split_neg_pos([],[],[]).

list_ar_seq(LN,LP,C) :- list_seq(LN,LP,CC),
	(
	CC=..[':-',H,B],
	C='->'(B,H)
	;
	C=CC
	),!.
make_the_appendix(_,_,[]) :- !.
make_the_appendix(Pre,_Post,T) :-
	ilf_state(pre_text,Pr),!,
	body_list(Pr,PrL),
	append(PrL,Pre,BL),
	proof([Pf,global],goal,_),
	assert(proof([Pf,global],pre_text,BL)),
	ilf_state(post_text,Po),!,
	body_list(Po,PoL),
	make_theory_list(T,ST),
	append(["\n\n\\section*{Appendix}\n\n\\begin{itemize}"|ST],["\\end{itemize}\n\n"],ST0),append(PoL,ST0,ST1),
	assert(proof([Pf,global],post_text,ST1)),
	ilf_state(known_theory,KT),
	append(KT,T,KKT),
	ilf_state(known_theory,_,KKT),!.

make_theory_list([AxN|T],["\\item ",math(CAx),"\n\n"|ST]) :- 
	proof(Ax,control,axiom(AxN)),
	proof(Ax,contents,CAx),
	make_theory_list(T,ST),!.
make_theory_list([_|T],S) :- make_theory_list(T,S),!.
make_theory_list([],[]).

	
remove_goal_restarts(L) :- 
	proof([Pf0,global],goal,G),
	proof([Pf0,N],status,subproof(_Pf1)),
	retract(proof([Pf0,N],contents,_)),
	assert(proof([Pf0,N],contents,G)),
	rm_goal_restart_l(L),!.

rm_goal_restart_l([]) :- !.
rm_goal_restart_l(L) :-
        max_restart(L,H,L1),
	rm_goal_restart(H),
	rm_goal_restart_l(L1),!.

rm_goal_restart(H) :-
	NC=case(H),
/*Mit NC wird der neue Fall eingefuegt*/
	case_ins_point(H,HIP),
	make_otherwise(HIP,HI),
	HI=[PfI,_],
	retract(proof(HI,predecessors,Pred)),
	assert(proof(HI,predecessors,[[PfI,NC]])),
	assert(proof([PfI,NC],predecessors,Pred)),
	NA=claim(H),
/*Bei NA wird eingefuegt was benutzt werden kann, wenn der Fall erledigt ist*/
	proof(HI,status,subproof(Pfall)),
	after_last_ass(Pfall,[Pfall,Nall]),
	retract(proof([Pfall,Nall],predecessors,PredAll)),
	assert(proof([Pfall,Nall],predecessors,[[Pfall,NA]])),
	assert(proof([Pfall,NA],predecessors,PredAll)),
	proof(H,status,subproof(Pf)),
	proof_pars(Pf,_,_,_,ExtRefsH),
	ass_contents_l(ExtRefsH,RL1,CL),
	retract(proof(H,status,_)),
	assert(proof(H,status,proved)),
	retract(proof(H,control,rule(_,_Arg))),
	assert(proof(H,control,rule([case_result],[[Pfall,NA]|RL1]))),
	assert(used_for([Pfall,NA],H)),
	proof(H,contents,F),
	make_lemma_fla(RL1,CL,F,RL2n,RL2p,CL2n,CL2p,F1),
	ilf_state(occur,S,on),
	add_n_ass(Pf,RL2n,CL2n,RL2,AL,_Rule,RL2p,CL2p),
	ilf_state(occur,_,S),
	chg_refs_in_subproof_l(Pf,RL2,AL),
	assert(proof([Pfall,NA],contents,F1)),
	assert(proof([Pfall,NA],status,proved)),
	encode(NCS,NC),
	(assert(proof([Pfall,NA],control,rule([by_case(NCS)],[[PfI,NC]])))),
	(F= (not _NF)),
	proof([_,global],goal,G),
	assert(proof([PfI,NC],contents,(F1 -> G))),
/* NC als Argument von case angefuegt um es als label benutzen zu koennen */
	encode(NCS,NC),
	assert(proof([PfI,NC],control,rule([case([CL2n,CL2p],NCS)],[]))),
	assert(proof([PfI,NC],status,subproof(Pf))),
	assert(used_for([PfI,NC],[Pfall,NA])),!.


rm_goal_restart(H) :-
	NC=case(H),
/*Mit NC wird der neue Fall eingefuegt*/
	case_ins_point(H,HI),
	HI=[PfI,_],
	retract(proof(HI,predecessors,Pred)),
	assert(proof(HI,predecessors,[[PfI,NC]])),
	assert(proof([PfI,NC],predecessors,Pred)),
	NA=claim(H),
/*Bei NA wird eingefuegt was benutzt werden kann, wenn der Fall erledigt ist*/
	proof(HI,status,subproof(Pfall)),
	retract(proof([Pfall,Nall],predecessors,[])),
	assert(proof([Pfall,Nall],predecessors,[[Pfall,NA]])),
	assert(proof([Pfall,NA],predecessors,[])),
	proof(H,status,subproof(Pf)),
	proof_pars(Pf,_,_,_,ExtRefsH),
	ass_contents_l(ExtRefsH,RL1,CL),
	retract(proof(H,status,_)),
	assert(proof(H,status,proved)),
	retract(proof(H,control,rule(_,_Arg))),
	assert(proof(H,control,rule([case_result],[[Pfall,NA]|RL1]))),
	assert(used_for([Pfall,NA],H)),
	proof(H,contents,F),
	make_lemma_fla(RL1,CL,F,RL2n,RL2p,CL2n,CL2p,F1),
	ilf_state(occur,S,on),
	add_n_ass(Pf,RL2n,CL2n,RL2,AL,_Rule,RL2p,CL2p),
	ilf_state(occur,_,S),
	chg_refs_in_subproof_l(Pf,RL2,AL),
	assert(proof([Pfall,NA],contents,F1)),
	assert(proof([Pfall,NA],status,proved)),
	encode(NCS,NC),
	(assert(proof([Pfall,NA],control,rule([by_case(NCS)],[[PfI,NC]])))),
	(F= (not _NF)),
	proof([_,global],goal,G),
	assert(proof([PfI,NC],contents,G)),
/* [PfI,NC] als Argument von case angefuegt um es als label benutzen zu koennen */
	encode(NCS,NC),
	assert(proof([PfI,NC],control,rule([case([CL2n,CL2p],NCS)],[]))),
	assert(proof([PfI,NC],status,subproof(Pf))),
	assert(used_for([PfI,NC],[Pfall,NA])),!.

make_otherwise(HIP,HIP) :- proof(HIP,control,rule([case(otherwise,_)],_)),!.
make_otherwise(HI,HOtw) :-
	gen_pf_hdl(PfC),
	HOtw=[PfC,0],
	retract(proof(HI,status,subproof(Pf0))),
	assert(proof(HI,status,subproof(PfC))),		
	retract(proof(HI,control,rule(R,Arg0))),
	append(R,[ilf_case],R1),
	assert(proof(HI,control,rule(R1,[HOtw]))),
	proof([_,global],goal,G),
	assert(proof(HOtw,contents,G)),
	assert(proof(HOtw,status,subproof(Pf0))),
	assert(proof(HOtw,predecessors,[])),	
	assert(proof(HOtw,control,rule([case(otherwise,top)],Arg0))),
	!.


after_last_ass(Pf,H) :- proof([Pf,N],predecessors,[]),
	after_last_ass(Pf,N,H),!.

after_last_ass(Pf,N,H) :- proof([Pf,N],status,assumption([])),
	proof([Pf,N1],predecessors,[[Pf,N]]),
	after_last_ass(Pf,N1,H),!.
after_last_ass(Pf,N,[Pf,N]).

max_restart(L,H,L1) :- member(H,L),H=[_,P],
	strict_remove(H,L,L1),not (member([_,P1],L1),append(_,P1,P)),!.

case_ins_point([Pf,_],H) :- proof(H,status,subproof(Pf)),
	proof(H,control,rule([R|_],_)),
	member(R,[case(_,_),indirect_all(_),query]),!.
case_ins_point([Pf,_],H1) :- 
	proof(H,status,subproof(Pf)),
	case_ins_point(H,H1),!.
case_ins_point(_,_) :- ilf_serv_error(write("Case insertion point not found")).

/* Fallannahmen nur einmal auffuehren */
ass_once :-
	proof([Pf,global],goal,_),
	ass_once(Pf),
	!.

ass_once(Pf) :- 
	setof([Pf,N],R^L^A^X^proof([Pf,N],control,rule([case(R,L)|X],A)),PL),
	new_ass_case(PL).
ass_once(Pf) :- setof(Pf1,N^proof([Pf,N],status,subproof(Pf1)),PL),
	ass_once_l(PL),!.
ass_once(_).

ass_once_l([Pf|PL]) :- ass_once(Pf),ass_once_l(PL),!.
ass_once_l([]).

new_ass_case([H|L]) :- proof(H,control,rule([case(otherwise,_)|_],_)),!,
	new_ass_case(L),!.
new_ass_case([H|L]) :-
	proof(H,control,rule([case([P,N],_)|_],_)),
	proof(H,status,subproof(Pf1)),
	add_case_ass(Pf1,P,N,C),
	check_case_ass(Pf1,C),!,
	new_ass_case(L),!.
new_ass_case([]).

add_case_ass(_,[],[],[]) :- !.
add_case_ass(Pf,[C|Pos],Neg,[C/[Pf,PC]|L]) :- 
	add_case_ass(Pf,Pos,Neg,L),
	gen_hdl(PC),
	assert(proof([Pf,PC],contents,C)),
	assert(proof([Pf,PC],status,assumption([]))),
	retract(proof([Pf,NN],predecessors,[])),
	assert(proof([Pf,NN],predecessors,[[Pf,PC]])),
	assert(proof([Pf,PC],predecessors,[])),!.
add_case_ass(Pf,[],[C|Neg],[not(C)/[Pf,PC]|L]) :- 
	add_case_ass(Pf,[],Neg,L),
	gen_hdl(PC),
	assert(proof([Pf,PC],contents,not(C))),
	assert(proof([Pf,PC],status,assumption([]))),
	retract(proof([Pf,NN],predecessors,[])),
	assert(proof([Pf,NN],predecessors,[[Pf,PC]])),
	assert(proof([Pf,PC],predecessors,[])),!.

check_case_ass(Pf,C) :- proof([Pf,N],status,subproof(Pf1)),
	rm_double_case([Pf,N],C),
	check_case_ass1(Pf1,C),fail.
check_case_ass(_,_).

check_case_ass1(Pf,C) :- proof([Pf,N],status,assumption(_)),
	once((
		proof([Pf,N],contents,F),
		member((F/P),C),
		retract(proof([Pf,N],status,_)),
		assert(proof([Pf,N],status,proved)),
		assert(proof([Pf,N],control,rule([since],[P])))
	)),
	fail.
check_case_ass1(Pf,C) :- proof([Pf,N],status,subproof(Pf1)),
	rm_double_case([Pf,N],C),
	check_case_ass1(Pf1,C),fail.
check_case_ass1(_,_).

rm_double_case(H,C) :- retract(proof(H,control,rule([case([P,N],L)|R],A))),
	rm_from_case(P,N,C,P1,N1),
	assert(proof(H,control,rule([case([P1,N1],L)|R],A))),!.
rm_double_case(_,_).

rm_from_case([F|P],N,C,P1,N1) :- member(F/_,C),rm_from_case(P,N,C,P1,N1),!.
rm_from_case([F|P],N,C,[F|P1],N1) :- rm_from_case(P,N,C,P1,N1),!.
rm_from_case([],[F|N],C,P1,N1) :- member(not(F)/_,C),rm_from_case([],N,C,P1,N1),!.
rm_from_case([],[F|N],C,P1,[F|N1]) :- rm_from_case([],N,C,P1,N1),!.
rm_from_case([],[],_,[],[]).

remove_clearly :- ilf_state(known_theory,T),
	ax_name_list(T,TH),
	remove_clearly(TH,3).

ax_name_list([N|NL],[H|HL]) :- proof(H,control,axiom(N)),
	ax_name_list(NL,HL),!.
ax_name_list([_|NL],HL) :- ax_name_list(NL,HL),!.
ax_name_list([],[]).

remove_clearly(_,0) :- !.
remove_clearly(T,N) :- remove_clearly(T),N1 is N-1,remove_clearly(T,N1),!.
remove_clearly(_,_).

remove_clearly(T) :- 
	setof(H,proved_from(H,T),HL),
	collect_proof_pars,
	rm_clearly(HL),!.

proved_from(H,T) :- proof(H,control,rule(_,Arg)),sublist(Arg,T).

rm_clearly([H|HL]) :- rm_pos(H,[]),rm_clearly(HL),!.
rm_clearly([]).

raise_subproofs :- collect_proof_pars,fail.
raise_subproofs :- repeat,
	not((
	raisable_subproof(Pf),
	raise_subproof(Pf)
	)),!.

raisable_subproof(Pf) :- 
	proof(H,status,subproof(Pf)),
	proof(H,control,rule([indirect],_)),
	not (
		proof([Pf,N],status,assumption(_)),
		used_for([Pf,N],H1),
		not H1=H
	).

raise_subproof(Pf) :- subproof_ins_point(Pf,H),raise_subproof(Pf,H),!.

subproof_ins_point(Pf,H) :- proof_pars(Pf,_,_,_,ExtRefs),
	proof(H1,status,subproof(Pf)),
	proof(H1,contents,C),
	H1=[Pf1,_],
	proof(HH,status,subproof(Pf1)),
	proof(HH,contents,CC),
	ilf_serv_log((
		write("\nWarning: Indirect proof of "),
		write(C),
		write(" does not use assumption. Subsequent part of proof of "),
		write(CC),
		write(" will be eliminated.\n")
	)),
	last_ext_ref(H1,ExtRefs,H),!.

last_ext_ref([Pf,N],ExtRefs,H) :- member([Pf,_],ExtRefs),
	get_last_ref([Pf,N],ExtRefs,H),!.
last_ext_ref([Pf,_],ExtRefs,H) :- proof(H1,status,subproof(Pf)),
	last_ext_ref(H1,ExtRefs,H),!.

get_last_ref([Pf,N],ExtRefs,H) :- proof([Pf,NA],predecessors,[]),
	get_last_ref([Pf,NA],N,ExtRefs,_,H),!.

get_last_ref([_Pf,N],N,_,H,H) :- !.
get_last_ref(H,N,ExtRefs,_,HX) :- member(H,ExtRefs),!,
	proof(H1,predecessors,[H]),
	get_last_ref(H1,N,ExtRefs,H,HX),!.
get_last_ref(H,N,ExtRefs,H1,HX) :- proof(HH,predecessors,[H]),
	get_last_ref(HH,N,ExtRefs,H1,HX),!.
	
raise_subproof(Pf,_) :- 
		proof(H,status,subproof(Pf)),
		proof(H,control,rule(R,_)),
		not proof_type(R,indirect),
		proof(H,contents,C),
		ilf_serv_log((
			write("Warning: Contradiction in non-indirect proof of "),
			write(C),
			nl
		)),
		fail.

raise_subproof(Pf,H) :- proof(H1,predecessors,[H]),
	do_raise_subproof(Pf,H1),!.

do_raise_subproof(Pf,H1) :- proof(H1,status,subproof(Pf)),!,
	retract(proof(H1,control,rule(_,Arg))),
	assert(proof(H1,control,rule([direct],Arg))),
	rm_pos_below(H1,[H1]),!.
do_raise_subproof(Pf,H1) :-
/* Erst Pf bei H1 anhaengen und damit sichern */
	rm_useless_ass(Pf),
	retract(proof(HPf,status,subproof(Pf))),
	assert(proof(HPf,status,proved)),
	retract(proof(H1,status,S)),
	assert(proof(H1,status,subproof(Pf))),
	retract(proof(H1,contents,_)),
	assert(proof(H1,contents,contradiction)),
	retract(proof(H1,control,_)),
	last_in_proof(Pf,HC),
	assert(proof(H1,control,rule([direct],[HC]))),
	(S=subproof(Pf1) -> rm_subproof(Pf1);true),
	rm_pos_below(H1,[H1]),
	!.

rm_useless_ass(Pf) :-
	proof([Pf,N],predecessors,[]),
	rm_ass_from([Pf,N]),!.

rm_ass_from(H) :- proof(H,status,assumption(_)),
	proof(H1,predecessors,[H]),
	retract_all(proof(H,_,_)),
	rm_ass_from(H1),!.
rm_ass_from(H) :- retract(proof(H,predecessors,_)),
	assert(proof(H,predecessors,[])),!.
	
rm_pos_below(H,L) :- proof(H1,predecessors,[H]),
	rm_pos(H1,L),
	rm_pos_below(H,L),!.
rm_pos_below(_,_).

make_done :- 
	setof(H,A^C^P^L^proof(H,control,rule([case(C,P)|L],A)),HL),
	make_done_l(HL),!.
make_done.

make_done_l([H0|HL]) :-
	once((
		proof(H0,status,subproof(Pf)),
		last_in_proof(Pf,H)
	)),
	proof(H,control,rule(_,[HG|_])),
	proof(HG,control,axiom(goal)),
	proof(HG,contents,CG),
	head_list(CG,GL),
	serv_negate_l(GL,GLD),
	list_body(GLD,CD),
	e_close(CD,GE),
	make_done(H,HG,GE),!,
	make_done_l(HL).
make_done_l([_|HL]) :- make_done_l(HL),!.
make_done_l([]).

make_done(H,HG,GE) :- 
	proof(H,control,rule(R,Arg)),
	strict_remove(HG,Arg,Arg1),
	get_pt_answer(GE,Arg1,Ans),
	retract(proof(H,contents,_)),
	assert(proof(H,contents,done(Ans))),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule(R,Arg1))),
	H=[Pf,_],
	proof(HP,status,subproof(Pf)),
	retract(proof(HP,control,rule(RP,ArgP))),
	strict_union([H],ArgP,ArgP1),
	assert(proof(HP,control,rule(RP,ArgP1))),!.



/* ##########     Ende Aufbereitung von Proteinbeweisen   ############# */

/* Spezifisches fuer 3TAP */

:- dynamic(tap_sk/4).

get_tap_symb(_,"c").

tap_skolem_const :- ilf_serv_log(write("Calculating Skolem constants.")),fail.
tap_skolem_const :- get_uih_file("tmp/tap.texop",File),
	open(File,write,taptexop),fail.
tap_skolem_const :- printf(taptexop,"TEXOP\n",[]),fail.
tap_skolem_const :- proof([Pf,global],goal,_),
	proof([Pf,N],status,subproof(_)),
	tap_skolem_const([Pf,N]),!.

tap_skolem_const(H) :- proof(H,status,subproof(Pf)),
	proof([Pf,N],predecessors,[]),
	tap_skolem_const([Pf,N]),!.
tap_skolem_const(H) :- proof(H,control,rule([exists_right(SL)],[HH])),
	make_sk_texop(SL,SLL),
	get_var_subst(SLL,HH,SL1),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule([exists_right_ilf(SL1)],[HH]))),
	tap_skolem_cont(H),!.
tap_skolem_const(H) :- proof(H,control,rule([forall_right(SL)],[HH])),
	make_sk_texop(SL,SLL),
	get_var_subst(SLL,HH,SL1),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule([forall_right_ilf(SL1)],[HH]))),
	tap_skolem_cont(H),!.
tap_skolem_const(H) :- tap_skolem_cont(H).

tap_skolem_cont(H) :- proof(H1,predecessors,[H]),
	tap_skolem_const(H1).
tap_skolem_cont([Pf,_]) :- proof(H,status,subproof(Pf)),
	tap_skolem_cont(H).
tap_skolem_cont(_) :- 
	(get_uih_file(".ilferc",IE),exists(IE);get_right_file(".ilfrc",IE)),
	printf(taptexop,"END_TEXOP\nINCLUDE %w\n",[IE]),
	close(taptexop),retract_all(tap_sk(_,_,_,_)),
	get_uih_file("tmp/tap.texop",File),
	reload_texop(File).

make_sk_texop([(C : Typ)|L],[((C : Typ) - old)|CL]) :- tap_sk(C,Typ,_,_),
	make_sk_texop(L,CL),!.
make_sk_texop([(C : Typ)|L],[((C : Typ) - new)|CL]) :- 
	(tap_sk(_,Typ,Symb,N);(N=0,get_tap_symb(Typ,Symb))),
	(N1 is N+1),
	printf(taptexop,"struct\t1\t(%Dw) :- \"{%w}_{%w}\"\n",[(C : Typ),Symb,N1]),
	asserta(tap_sk(C,Typ,Symb,N1)),
	make_sk_texop(L,CL),!.
make_sk_texop([],[]).

get_var_subst(L,H,L1) :- proof(H,contents,C),
	squant_var(C,VL),
	get_the_subst(L,VL,L1),!.
get_var_subst(L,H,L1) :- ilf_error("get_var_subst(%w,%w,%w)\n",[L,H,L1]).

squant_var(fSign(ex(V,_)),V).
squant_var(tSign(all(V,_)),V).
squant_var(fSign(all(V,_)),V).
squant_var(tSign(ex(V,_)),V).

get_the_subst([E|L],[V : _|VL],[V -> E|L1]) :- get_the_subst(L,VL,L1),!.
get_the_subst([],[],[]).

same_signed(fSign(sneg(C)),tSign(C)).
same_signed(tSign(sneg(C)),fSign(C)).
same_signed(fSign(C),tSign(sneg(C))).
same_signed(tSign(C),fSign(sneg(C))).

/* End 3TAP */
/* Hyper */

hyper2bl :- proof([Pf,goal],contents,_),
	not proof([Pf,goal],predecessors,_),
	connect_incomplete_goal(Pf),fail.
hyper2bl :- hyper_answers,fail.
hyper2bl :- 
	proof([Pf,goal],contents,_),
	change_impossible(Pf),
	fail.
hyper2bl.

connect_incomplete_goal(Pf) :- get_last_node(Pf,H),
	assert(proof([Pf,goal],predecessors,[H])),
	assert(proof([Pf,goal],status,unproved)),
	setof([ax,N],C^proof([ax,N],contents,C),L), % Verhindern, dass verwendbare Formeln weggeworfen werden
	get_hyper_model([Pf,goal],Anc,Mod),
	append(L,Anc,L1),
	assert(proof([Pf,goal],control,rule([model],L1))),
	retract(proof([Pf,goal],contents,_)),
	assert(proof([Pf,goal],contents,ilf_model(Mod))),!.

get_hyper_model(H,[H1|UP],UC) :- proof(H,predecessors,[H1]),
	proof(H1,contents,C1),!,
	extend_hyper_model(H1,C1,UC,UC1),
	get_hyper_model(H1,UP,UC1).
get_hyper_model([Pf,_],UP,[Ass,UC]) :- proof([Pf1,N],status,subproof(Pf)),
	bagof(not(C),other_case([Pf1,N],C),CL),
	append(CL,UC1,UC),
	proof(H,status,subproof(Pf1)),
	get_hyper_model(H,UP,[Ass,UC1]).
get_hyper_model(_,[],[[],[]]).

extend_hyper_model(_,(_;_),UC,UC) :- !.
extend_hyper_model(H1,C1,[[C1|Ass],M],[Ass,M]) :- 
	proof(H1,status,assumption([])),!.
extend_hyper_model(_,C1,[Ass,[C1|Mod]],[Ass,Mod]).

other_case([Pf,N],C) :- proof([Pf,M],contents,(C -> _)),not M==N.

change_impossible(Pf) :- proof([Pf,goal],predecessors,[H]),
	proof(H,contents,contradiction),
	retract(proof(H,control,rule(_,Ref))),
	assert(proof(H,control,rule([impossible],Ref))),
	proof(H1,status,subproof(Pf)),
	retract(proof(H1,control,rule(R,Arg))),
	change_pos_lst([Pf,goal],[H],Arg,Arg1),
	assert(proof(H1,control,rule(R,Arg1))),
	retract_all(proof([Pf,goal],_,_)),!.
change_impossible(_).

impossible_case(Pf) :- retract_all(proof([Pf,goal],_,_)),
	proof(H,status,subproof(Pf)),
	retract(proof(H,control,_)),
	assert(proof(H,control,rule([impossible],[]))),
	!.

hyper_answers :- not proof([_,global],goal,exists(_,_)),!.
hyper_answers :- subst_goal_closed,raise_goal_closed,!.

subst_goal_closed :- proof(H,control,rule([goal_closed(Subst)],_)),
	subst_goal_closed(H,Subst),fail.
subst_goal_closed.

subst_goal_closed(H,Subst) :- retract(proof(H,contents,exists(V,C))),
	retract(proof(H,control,rule([goal_closed(_)],Ref))),
	make_equations(V,Subst,Eq),
	assert(proof(H,control,rule([goal_closed(Eq)],Ref))),
	V=Subst,
	assert(proof(H,contents,C)),!.

make_equations([X|V],[T|Subs],[X=T|L]) :- make_equations(V,Subs,L).
make_equations([],[],[]).

raise_goal_closed :- proof([Pf,global],goal,exists(V,_)),
	length(V,NV),
	proof([Pf,N],status,subproof(Pf1)),
	proof([Pf1,M],status,subproof(_)),
	raise_goal_closed([Pf1,M],NV,Sub),
	retract(proof([Pf,N],contents,C)),
	subst_ans(Sub,C,C1),
	assert(proof([Pf,N],contents,C1)),
	!.
raise_goal_closed :- ilf_error("raise_goal_closed failed").

raise_goal_closed(H,NV,Sub) :- hyper_subtree_ans(H,NV,LS),
	anti_unify_ans_l(LS,_,Sub),
	retract(proof(H,contents,C)),
	subst_ans(Sub,C,C1),
	assert(proof(H,contents,C1)),!.

hyper_subtree_ans(H,NV,LS) :- proof(H,control,rule(_,[_|Ref])),
	collect_subtree_ans_l(Ref,NV,LS).

collect_subtree_ans_l([H|Cases],NV,[S|LS]) :- collect_subtree_ans(H,NV,S),
	collect_subtree_ans_l(Cases,NV,LS).
collect_subtree_ans_l([],_,[]).

collect_subtree_ans(Case,NV,S) :- proof(Case,status,subproof(Pf)),
	collect_subtree_ans1(Case,Pf,NV,S),!.

collect_subtree_ans1(_Case,Pf,NV,S) :-
	proof([Pf,_],contents,contradiction),!,
	length(S,NV).
collect_subtree_ans1(_Case,Pf,NV,S) :- 
	proof([Pf,_],control,rule([model],_)),!,
	const_list(ilf_err,NV,S),!.
collect_subtree_ans1(Case,Pf,NV,S) :- proof([Pf,goal],status,subproof(_)), 
% eigentlichwird hier das letzte Element des Unterbeweises gesucht, so gehts schneller
	raise_goal_closed([Pf,goal],NV,S),
	retract(proof(Case,contents,(A -> C))),
	subst_ans(S,C,C1),
	assert(proof(Case,contents,(A -> C1))),
	!.
collect_subtree_ans1(Case,Pf,_NV,S) :- 
	proof([Pf,_],control,rule([goal_closed(Eq)],_)),
	eq2(Eq,S),
	retract(proof(Case,contents,(A -> C))),
	subst_ans(S,C,C1),
	assert(proof(Case,contents,(A -> C1))),
	!.

const_list(_,0,[]) :- !.
const_list(T,N,[T|L]) :- (N1 is N-1),const_list(T,N1,L),!.

eq2([_=T|L],[T|L1]) :- eq2(L,L1).
eq2([],[]).	

subst_ans(Sub,exists(V,C),C1) :- subst_ans_var(V,Sub,V1),
	substed_ans(V1,C,C1).
subst_ans(_,C,C).

/* anti_unify_ans_l antiunifiziert Liste von Termlisten */
anti_unify_ans_l([S|L],Sub0,Sub) :- 
	anti_unify_l(S,Sub0,Sub1),anti_unify_ans_l(L,Sub1,Sub).
anti_unify_ans_l([],L,L).

anti_unify_l([X|L],[X|Sub],[X|Sub1]) :- anti_unify_l(L,Sub,Sub1).
anti_unify_l([ilf_err|L],[_|Sub],[ilf_err|Sub1]) :- anti_unify_l(L,Sub,Sub1).
anti_unify_l([_|L],[_|Sub],[_|Sub1]) :- anti_unify_l(L,Sub,Sub1).
anti_unify_l([],[],[]).

subst_ans_var([X|V],[Y|Sub],[X|V1]) :- 
	(not not Y=ilf_err), % Y ist Variable oder ilf_err
	subst_ans_var(V,Sub,V1).
subst_ans_var([X|V],[X|Sub],V1) :- subst_ans_var(V,Sub,V1).
subst_ans_var([],[],[]).

substed_ans([],C,C).
substed_ans([X],C,ex(X,C)).
substed_ans(V,C,exists(V,C)).

get_last_node(Pf,H) :- proof([Pf,N],predecessors,[]),
	the_last_node([Pf,N],H).
the_last_node(H1,H) :- proof(H2,predecessors,[H1]),
	the_last_node(H2,H).
the_last_node(H,H).

elim_true_false :- retract(proof(H,contents,C)),elim_true_false(C,C1),
	assert(proof(H,contents,C1)),fail.
elim_true_false.

elim_true_false('<-'(C,true),C) :- !.
elim_true_false('<-'(false,C),not(C)) :- !.
elim_true_false('->'(true,C),C) :- !.
elim_true_false('->'(C,false),not(C)) :- !.
elim_true_false('<-'(H,B),'->'(B,H)) :- !.
elim_true_false(C,C).

raise_neg_cases :- ilf_serv_log(write("Raising contradictory cases.\n")),fail.
raise_neg_cases :- neg_cases(H,HN,HP),raise_neg_cases(H,HN,HP),fail.
raise_neg_cases.

neg_cases(H,HN,HP) :- case_rule(R),proof(H,control,R),proof(H,status,subproof(Pf)),
	setof([Pf,N],C^proof([Pf,N],contents,C),HL),
	split_pos_neg_cases(HL,HN,HP).

split_pos_neg_cases([H|HL],[H|HN],HP) :- 
	proof(H,status,subproof(Pf)),proof([Pf,_],contents,contradiction),
	split_pos_neg_cases(HL,HN,HP),!.
split_pos_neg_cases([H|HL],HN,[H|HP]) :- split_pos_neg_cases(HL,HN,HP),!.
split_pos_neg_cases([],[],[]).

raise_neg_cases(_,[],_) :- !.
raise_neg_cases(_,_,[]) :- !.
raise_neg_cases(H,HN,[_]) :- prepare_raise_neg_case(H,HA),
	raise_neg_case_l(HN,H,HA),raise_last_case(H,HA),!.
raise_neg_cases(H,HN,_) :- prepare_raise_neg_case(H,HA),raise_neg_case_l(HN,H,HA),!.

prepare_raise_neg_case(H,HA) :- H=[Pf,_],gen_hdl(Pf,HA),
	retract(proof(H,control,rule(R,[CD|Cases]))),
	asserta(proof(H,control,rule(R,[HA|Cases]))),
	proof(CD,contents,D),
	asserta(proof(HA,contents,D)),
	asserta(proof(HA,status,proved)),
	asserta(proof(HA,control,rule([resolve],[CD]))),
	retract(proof(H,predecessors,Pred)),
	asserta(proof(H,predecessors,[HA])),
	asserta(proof(HA,predecessors,Pred)),!.

raise_neg_case_l([HN|HNL],H,HA) :- raise_neg_case(HN,H,HA),raise_neg_case_l(HNL,H,HA),!.
raise_neg_case_l([],_,_).

raise_neg_case(HN,H,HA) :- H=[Pf,_],gen_hdl(Pf,HB),
	retract(proof(HA,predecessors,Pred)),
	asserta(proof(HA,predecessors,[HB])),
	asserta(proof(HB,predecessors,Pred)),
	proof(HN,status,subproof(PfN)),
	proof([PfN,A],status,assumption([])), % Annahme: Nur eine assumption und die kommt von case
	proof([PfN,A],contents,CA),
	dualize(CA,DA),
	asserta(proof(HB,contents,DA)),
	asserta(proof(HB,status,subproof(PfN))),
	proof(HN,control,rule(_,Ref)),
	asserta(proof(HB,control,rule([indirect],Ref))),
	retract(proof(HA,contents,CDis)),head_list(CDis,CDisL),
	strict_remove(CA,CDisL,CDisL1),list_head(CDisL1,CDis1),
	asserta(proof(HA,contents,CDis1)),
	retract(proof(HA,control,rule(R,CRef))),
	append(CRef,[HB],CRef1),
	asserta(proof(HA,control,rule(R,CRef1))),
	retract(proof(H,control,rule(RH,RefH))),
	strict_remove(HN,RefH,RefH1),
	asserta(proof(H,control,rule(RH,RefH1))),
	retract_all(proof(HN,_,_)),!.

raise_last_case(H,HA) :- retract(proof(H,control,rule(_,[HA,HC]))),
	proof(HC,status,subproof(PC)),
	proof([PC,NA],predecessors,[]),
	proof(HC,control,rule(_,Ref)),
	strict_remove([PC,NA],Ref,Ref1),
	asserta(proof(H,control,rule([direct],Ref1))),
	retract_all(proof(HC,_,_)),
	retract(proof(H,status,_)),
	assert(proof(H,status,subproof(PC))),
	
	change_pos([PC,NA],[HA]),!.
raise_last_case(H,HA) :- ilf_error("raise_last_case(%w,%w).\n",[H,HA]),!.

raise_contradictory_cases :- ilf_serv_log(writeln("Raising contradictions through cases.\n")),fail.
raise_contradictory_cases :- case_rule(R),
	proof(H,control,R),
	contradictory_case(H),ilf_serv_log(write(-H)),
	raise_contradictory_case(H),fail.
raise_contradictory_cases :- ilf_serv_log(nl).

contradictory_case(H) :- proof(H,contents,contradiction),!,fail.
contradictory_case(H) :- proof(H,status,subproof(Pf)),
	not (proof([Pf,_],status,subproof(Pf1)), 
		not proof([Pf1,_],contents,contradiction)),!.

raise_contradictory_case(H) :- proof(H,status,subproof(Pf)),
	retract(proof([Pf,N],contents,(A -> _))),
	assert(proof([Pf,N],contents,(A -> contradiction))),
	fail.
raise_contradictory_case(H) :- retract(proof(H,contents,_)),
	asserta(proof(H,contents,contradiction)),
	H=[Pf,_],raise_more_contradictory_cases(Pf),!.

raise_more_contradictory_cases(Pf) :- 
	once((proof([Pf1,_],status,subproof(Pf)),
		proof(H,status,subproof(Pf1))
	)),
	proof(H,control,R),case_rule(R),
	contradictory_case(H),
	raise_contradictory_case(H),!.
raise_more_contradictory_cases(_).

default_user_model([Ass,M],[Ass1,M1]) :- rev(Ass,Ass1),
	sort(M,MM),
	pred_into_model_l(MM,[],M1),!.

pred_into_model_l([A|M],M1,M2) :- pred_into_model(A,M1,M11),
	pred_into_model_l(M,M11,M2),!.
pred_into_model_l([],M,M).

pred_into_model(not(A),M1,M2) :- pred_into_model(neg,A,M1,M2).
pred_into_model(A,M1,M2) :- pred_into_model(pos,A,M1,M2).

pred_into_model(Sgn,A,[[T|R1]|M1],[[T|R2]|M1]) :- not not A=T,
	add_pred(Sgn,A,R1,R2),!.
pred_into_model(Sgn,A,[[T|R]|M1],[[T1|R1],[T|R]|M1]) :-
	functor(A,Op,NA),functor(T,_,NT),
	NA < NT,
	functor(T1,Op,NA),
	add_pred(Sgn,A,[[],[]],R1),!.
pred_into_model(Sgn,A,[E|M],[E|M1]) :- pred_into_model(Sgn,A,M,M1).
pred_into_model(pos,A,[],[[T,[A],[]]]) :- functor(A,Op,N),functor(T,Op,N).
pred_into_model(_,A,[],[[T,[],[A]]]) :- functor(A,Op,N),functor(T,Op,N).

add_pred(pos,A,[P,N],[P1,N]) :- append(P,[A],P1).
add_pred(_,A,[P,N],[P,N1]) :- append(N,[A],N1).
	
	
log_tmp_p3(T) :- concat_string(["tmp/ilf.",T,".out"],FS),
	get_uih_file(FS,F),open(F,write,p3file),fail.
log_tmp_p3(_) :- proof(H,K,V),printf(p3file,"proof(%DVw,%DVw,(%DVw)).\n",[H,K,V]),fail.
log_tmp_p3(_) :- close(p3file).



/* End Hyper */

/* Vollstaendiges Loeschen einer Theorie und rekursiv aller Zeilen, die nur Verweise auf diese Theorie benutzen */
erase_subtheory(_) :- collect_proof_pars,fail.
erase_subtheory(T) :- proof(H,control,axiom(N)),not not member(N,T),
	rm_ax(H),fail.
erase_subtheory(_) :- repeat, not rm_clearly,!.

rm_clearly :- proof(H,control,rule(_,[])),rm_pos(H).

rm_ax(H) :- retract(used_for(H,H1)),
	once((
		retract(proof(H1,control,rule(R,L))),
		strict_remove(H,L,L1),
		asserta(proof(H1,control,rule(R,L1)))
	)),fail.
rm_ax(H) :- retract_all(proof(H,_,_)).

:- import rm_all/2 from thman.

make_clauses_typed :- proof([Pf,global],goal,_),
	proof([Pf,_],status,subproof(Pf1)),
	proof([Pf1,N1],predecessors,[]),
	type_clauses_below([Pf1,N1]),!.

type_clauses_below(H) :- not proof(H,status,assumption(_)),
	retract(proof(H,contents,C)),
	make_clause_typed(C,C1),
	assert(proof(H,contents,C1)),fail.
type_clauses_below(H) :- proof(H,status,subproof(Pf)),
	proof([Pf,N],predecessors,[]),
	type_clauses_below([Pf,N]),fail.
type_clauses_below(H) :- proof(H1,predecessors,[H]),
	type_clauses_below(H1).
type_clauses_below(_).

make_clause_typed(C,C1) :- rm_all(C,D),
	clause_list(D,D1),
	extract_sort(D1,S,D2),
	quantify_typed(D2,S,C1),!.

clause_list((B -> H),[BL,HL]) :- body_list(B,BL),head_list(H,HL),!.
clause_list((C1;C2),[BL,HL]) :- clause_list(C1,[B1,H1]),clause_list(C2,[B2,H2]),
	append(B1,B2,BL),append(H1,H2,HL),!.
clause_list(not(X),[[X],[]]) :- !.
clause_list(X,[[],[X]]).

list_clause([[],H],D) :- list_head(H,D).
list_clause([[A],[]],not(A)) :- !.
list_clause([[A|BL],[]],(not(A);B)) :- list_clause([BL,[]],B).
list_clause([BL,HL],(B -> H)) :- list_body(BL,B),list_head(HL,H).

extract_sort([B,H],V1,[BS,H]) :- get_body_sort(B,BS,V),sort_var_sort(V,V1).

get_body_sort([B|BL],BB,[B|BV]) :- B=..[R,X|_],var(X),
	sort_pred(R),
	get_body_sort(BL,BB,BV),!.
get_body_sort([B|BL],BB,BV) :- functor(B,R,_),sort_pred(R),
	get_body_sort(BL,BB,BV),!.
get_body_sort([B|BL],[B|BB],BV) :- get_body_sort(BL,BB,BV),!.
get_body_sort([],[],[]).

sort_pred(R) :- atom_string(R,RS),
	(N is string_length(RS)-4),
	substring(RS,N,5,"_sort").

sort_var_sort(V,W) :- sort_var_sort(V,W,[]).
sort_var_sort([T|V],[T|W],VL) :- T=..[_,X|Arg],
	term_variables(Arg,AV),
	not((member(U,AV),not strict_member(U,VL))),
	sort_var_sort(V,W,[X|VL]),!.
sort_var_sort([T|V],W,VL) :- append(V,[T],V1),
	sort_var_sort(V1,W,VL).
sort_var_sort([],[],_).

quantify_typed(C,[T|VT],forall([X],(T -> D))) :- T=..[_,X|_],
	quantify_typed(C,VT,D).
quantify_typed(C,[],D) :- list_clause(C,D).

:- set_flag(syntax_option, not nested_comments). % debug


