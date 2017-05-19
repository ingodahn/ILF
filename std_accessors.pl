%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%
%%%% STANDARD ACCESSORS for restricted ILF version 2016
%%%%
%%%% Author: Wernhard
%%%%
%%%% Mon Feb 17 10:32:35 1997
%%%%
%%%% Default implementation for access predicates for proofs working on
%%%% a proof/3 predicate defined in module p3 (access_mode(std)).
%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(proof).

:- export
	get_proof/1,
	select_proof/0,
	present_proof/0,
	proof2ilf/0,
	put_proof/1,
	show_proof/0,
	undo/0,
	undo_enable/0.
/*	
:- import ilf_serv.
*/
:- import ilfsys.

:- import proof/3 from situation.

:- export 
	  access_mode/1,
	  current_access_mode/1,

	  line_id/2,
          line_proof/2,
          line_status/2,
          line_subproof/2,
	  line_predecessors/2,
	  line_successor/2,
	  line_contents/2,
	  line_control/2,
	  line_name/2,
	  line_declaration/2,
	  line_supers/2,

	  proof_id/2,
	  proof_lines/2,
	  proof_line/2,
	  proof_superline/2,
	  proof_firstline/2.


:-export                            %%  for now this is here          

	  install_p3_dynamic/1,
	  install_p3_module/1,
	  install_p3_compile/1,
	  install_p3_compile_term/1,

	  p3_assert/1,
          p3_asserta/1,
          p3_retract/1,
          p3_retract_all/1,
	  p3_listing/1.

:- setval(current_access_mode, none).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% 
%%%% READERS
%%%%

%%%
%%% In general they have this mode:
%%%
%%%   reader_predicate(+Object, ?Value)
%%%
%%% In general they are deterministic (for valid input).
%%% 
%%% Some accessors can fail for valid inputs. See comments to the
%%% individual accessors.
%%%
%%% Lines are represented by "line-handles", proofs by "proof-handles".
%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%
%%% <type>_id(+Object, ?Identifier)
%%%
%%% - Objects are (semantically) equal iff their Identifiers are
%%%   syntactical (ie. ==/2) [or variant/2]
%%% - Identifier can be printed. 
%%%
%%% [ - Identifier can be used wherever Object is used (except performance may
%%%     be poorer).]?
%%%

%%%%
%%%% LINE READERS (AND "TESTERS")
%%%%

line_id(Line, Line).

line_proof(Line, Proof) :-
	Line = [Proof,_].

line_status(Line, Status) :-
	proof(Line, status, Status),
	!. % blue

line_subproof(Line, Proof) :-
	%%
	%% Fails if line has no subproof.
	%%
	proof(Line, status, subproof(Proof)),
	!. % blue

line_predecessors(Line, Predecessors) :-
	%%
	%% Predecessors is [] or a singleton list.
	%%
	proof(Line, predecessors, Predecessors),
	!. % blue

line_successor(Line, Successor) :-
	%%
	%% Fails if Line has no Successor.
	%%
	proof(Successor, predecessors, [Line]),
	!. % blue

line_contents(Line, Contents) :-
	proof(Line, contents, Contents),
	!. % blue

line_control(Line, Control) :-
	%%
	%% Fails if line has no control, eg. if its status is assumption.
	%%
	proof(Line, control, Control),
	!. % blue

line_name(Line, Name) :-
	%%
	%% Fails if line has no name.
	%%
	proof(Line, name, Name),
	!. % blue

line_supers(Line, Proofs) :-
	%%
	%% +Line, -Proofs
	%%
	line_proof(Line, Proof),
	( proof_superline(Proof, Line1) ->
	  Proofs = [Proof|Proofs1],
	  line_supers(Line1, Proofs1)
        ; Proofs = []
        ).

line_declaration(Line, Declaration) :-
	%%
	%% Fails if line has no declaration, eg. if it is no definition
	%%
	proof(Line, declaration, Declaration),
	!. % blue

%%%%
%%%% PROOF READERS
%%%%

proof_id(Proof, Proof).

proof_lines(Proof, Lines) :-
	%%
	%% A proof has at least one line.
	%% Lines is a list of lines in the ordering determined by
	%% predecessors.
	%%
	Lines = [[Proof,Linespec]|Lines1],
	proof([Proof,Linespec], predecessors, []),
	!, % blue
	pl2([Proof,Linespec], Lines1).

pl2(Line, Lines) :-
	%% auxiliary predicate for proof_lines
	( proof(Line1, predecessors, [Line]) ->
	  Lines =  [Line1|Lines1],
	  pl2(Line1, Lines1)
        ; Lines = []).


proof_line(Proof, Line) :-
	%%
	%% A proof has at least one line.
	%%
        %% Enumerate lines of Proof in ordering determined by predecessors.
        %% 
	proof_firstline(Proof, Line1),
	ple(Line1, Line).

ple(Line, Line).
ple(Line, Line1) :-
	%% auxiliary predicate for proof_line
	line_successor(Line, Line2),
	ple(Line2, Line1).


proof_superline(Proof, Line) :-
	%%
	%% Line is the line of which Proof is a subproof.
	%% Fails if Proof is not a subproof.
	%%
	proof(Line, status, subproof(Proof)),
	!. % blue

proof_firstline(Proof, Line) :-
	proof([Proof, LH], predecessors, []),
	!, % blue
	Line = [Proof, LH].


:- setval(current_access_mode, std).
