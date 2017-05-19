/* 
 * @(#)proofout.pl	1.56 (07/29/98)
 *
 * Ausgabe von (Block-)Beweisen.
 *
 * basiert auf proof.pro 1.100 (05/21/96) 
 * Behandlung und Konvertierung des Praedikates proof/3
 * enthalten sind alle proof-related Funktionalitaeten von ILF
 * Modul ist Bestandteil des Vordergrundes
 * Autoren: Allner, Dahn, Wolf
 * (C) 1994
 * Portierung nach Eclipse Prolog: Honigmann
 */

:- module(proofout).

:- import ilf_state/2, 
	ilf_state/3, 
	ilf_debug/1,
	get_right_file/2,
	ilf_warning/2,
	spy_ilf/0
	from ilfsys.

:- import translit/2 from ilf_serv.

:- export
	load_subproof/1,
	article/1,
	articlehtml/0,
	articlehtml/1,
	articletex/0,
	articletex/1,
	block_lines/0,
	proof/1,
	proofhtml/0,
	proofhtml/1,
	prooftex/0,
	prooftex/1,
	show_proof/1,
	view_proof/1.

:- export
	blockproof_article/0,
	blockproof_article/1,
	blockproof_article/2,
	blockproof_article/3,
	blockproof_out/0,
	blockproof_out/1,
	blockproof_out/2,
	blockproof_out/3,
	blockproof_out/4,
	blockproof_out0/1,
	blockproof_out0/2,
	blockproof_out0/3,
	blockproof_out0/4,
	block_proof_out0/3,
	show_rule_list/3,
	show_rule_script/3.

:- export
	block_lines/0.

:- export list_p3/2.

:- export			  % from "Anzeige von Block-Beweisen im
				  % Standardformat im TreeViewer"
				  % seem not used anywhere else
	show_block_proof/0.
/*
	tvblck/1,
	proof_tex/0,
	verstecke_subproof/0,
	zeige_subproof/0,
	update_latex/0,
	hidden_proof/0,
	show_block_dependencies/0,
	show_block_dependencies_f/0
*/


:- begin_module(proofout).

:- import 
	collect_proof_pars/2,
	default_transformation/2,
	proof_pars/5,
	transform_proof/1
		from block.

:- import
	proof/3
		from situation.

:- import
	line_contents/2,
	line_control/2,
	line_predecessors/2,
	line_subproof/2,
	line_successor/2,
	proof_lines/2
		from proof.

:- import
	mode_specific/2,
	print_text/3
		from genout.

:- import
	body_list/2,
	mktemp/2
		from tools.

:- import get_attribute/2 from thman.

:- dynamic
	hidden/1,
	hidden_cache/2,
	ist_axiom/1,
	known_axiom/2,
	known_axiom_used/1,
	loeschen/1,
	possible_label/1,
	ref/3,
	since_label/2,
	test_test/0,
	test_test1/0,
	test_test2/0,
	test_test3/0,
	test_test4/0,
	test_test5/0,
	test_test6/0,
	test_test7/0,
	reihenfolge/3,
	reihenfolge2/2,
	reservation/2,
	rule_op_cache/3,
	skip/1,
	schonweg/2,
	schon_weg/1,
	used_constant/1,
	used_ref/1,
	verwendet_cache/2,
	verwendet_cache_temp/2,
	zahl/1.

:- 	make_local_array(current_mode, prolog),
 	make_local_array(current_handle, prolog),
 	make_local_array(firstup, prolog),
 	make_local_array(reihenfolge2, prolog).

/* Nutzerkommandos */
 
article(Mode) :- 
	blockproof_article(Mode),
	mode_specific(view, Mode).
articlehtml :- article(html).
articlehtml(File) :- blockproof_article(html, File).
articletex :- article(latex).
articletex(File) :- blockproof_article(latex, File).

proof(Mode) :-
	blockproof_out(Mode),
	mode_specific(view, Mode).
proofhtml :- proof(html).
proofhtml(File) :- blockproof_out(html, File).
prooftex :- proof(latex).
prooftex(File) :- blockproof_out(latex, File).

/* Beweisausgabe. */

blockproof_article :-
	ilf_state(out_mode, Mode),
	blockproof_article(Mode).
blockproof_article(Mode) :-
	ilf_state(default_proof_file, FileName),
	blockproof_article(Mode, FileName).
blockproof_article(Mode, Where) :-
	proof([Proof,global], goal, _),
	blockproof_article(Mode, Where, Proof).
blockproof_article(Mode, Where, Proof) :-
	blockproof_out(Mode, Where, Proof, true).

blockproof_out :-
	ilf_state(out_mode, Mode),
	blockproof_out(Mode).
blockproof_out(Mode) :-
	ilf_state(default_proof_file, FileName),
	blockproof_out(Mode, FileName).
blockproof_out(Mode, FileName) :-
	proof([Proof,global], goal, _),
	blockproof_out(Mode, FileName, Proof).
blockproof_out(Mode, FileName, Proof) :-
	blockproof_out(Mode, FileName, Proof, fail).

blockproof_out(Mode, FileName, Proof, Article) :-
	mode_specific(open_file(FileName, Stream), Mode),
	mode_specific(technical_header(Stream), Mode),
	get_title(Title),
	get_author(Author),
	mode_specific(title(Stream, Title, Author), Mode),
	blockproof_out0(Stream, Mode, Article, Proof),
	mode_specific(technical_trailer(Stream), Mode),
	close(Stream),
	!.
	
blockproof_out0(Stream) :-
	ilf_state(out_mode, Mode),
	blockproof_out0(Stream, Mode).
blockproof_out0(Stream, Mode) :-
	blockproof_out0(Stream, Mode, true).
blockproof_out0(Stream, Mode, Article) :-
	proof([Proof,global], goal, _),
	blockproof_out0(Stream, Mode, Article, Proof).

blockproof_out0(Stream, Mode, Article, Proof) :-
	setval(current_mode, Mode),
	/* No longer available in Eclipse
	ilf_state(occur, O, on),
	*/
	ilf_debug((write("Initializing "), flush(output))),
	clearall(Mode),
	compile_ilf_state(known_rules, known_rule),
	ilf_debug((write("done."), flush(output))),
	get_right_file("tmp",TempFileRoot),
	concat_string([TempFileRoot,"/.proofout"],TempFileTemplate),
	mktemp(TempFileTemplate, TempFileName),
	open(TempFileName, write, TempStream),
	print_text(Proof, abstract, TempStream, Mode),
	print_text(Proof, pre_text, TempStream, Mode),
	mode_specific(open_include(TempStream, ".types", VarTypeStream), Mode),
	proof_lines(Proof, HandleList),
	(Article ->
		print_blocklines(TempStream, Mode, HandleList)
		;
		mode_specific(open_include(
			TempStream, ".theory", TheoryStream), Mode),
%		hide_theory,
	        print_lemmata(TempStream, Mode, HandleList, MainProof),
	        print_theorem(TempStream, Mode, Proof, MainProof),
	        print_proof_begin(TempStream, Mode, Proof),
	        print_constants(TempStream, Mode, Proof),
		print_blocklines(TempStream, Mode, [MainProof]),
	        mode_specific(print_qed(TempStream), Mode),
		print_theory(TheoryStream, Mode),
		close(TheoryStream)
	),
	print_text(Proof, post_text, TempStream, Mode),
	close(TempStream),
	mode_specific(print_var_types(VarTypeStream), Mode),
	close(VarTypeStream),
	findall(H, (possible_label(H), retract(used_ref(H))), LabelList),
	findall(H, forward_ref(H), RefList),
	% ilfsys:spy_ilf,
	mode_specific(postprocess_file(TempFileName, LabelList, RefList, 
		PPPid, Output), Mode),
	repeat,
	(read_string(Output, "\n", _, Line) ->
		writeln(Stream, Line), 
		fail
		;
		true
	), !,
	close(Output),
	wait(PPPid, _),
	/* No longer supported in eclipse
	ilf_state(occur, _, O),
	*/
	!.

print_blocklines(_, _, []).
print_blocklines(Stream, Mode, [Handle|HandleList]) :-
	(
		print_blockline(Stream, Mode, Handle)
		;
		ilf_error("print_blockline(%Dw) failed", [Handle])
	),
	print_blocklines(Stream, Mode, HandleList).

print_blockline(_, _, Handle) :-
	skip(Handle),
	!.
print_blockline(Stream, Mode, Handle) :-
	rule_op(Handle, RuleList, Mode),
	!,
	make_reihenfolge2(Handle),
	exec_rule_list(Stream, Mode, Handle, RuleList),
	(verwendet(Handle, _) ; true), /* um sicherzustellen, dass 
					  verwendet_cache/2 existiert */
	make_reihenfolge2(Handle).
/* Default Subproof */
print_blockline(Stream, Mode, Handle) :-
	line_subproof(Handle, Proof),
	!,
	(proof_lines(Proof, HandleList) ->
		print_blocklines(Stream, Mode, HandleList)
		;
		ilf_debug(ilf_warning(
			"subproof lines not found for %Dw", [Handle]))
	),
	make_reihenfolge2(Handle),
	teste(proof, Handle),
	print_intro(Stream, Mode, Handle),
	loesche_test,
	open(_, string, RuleStream),
	print_rule(RuleStream, Mode, Handle),
	current_stream(RuleString, _, RuleStream),
	close(RuleStream),
	(RuleString="" ->
		print_formula(Stream, Mode, ".", Handle)
		;
		print_formula(Stream, Mode, ",", Handle),
		mode_specific(print_string(Stream, RuleString), Mode)
	),
	mode_specific(end_par(Stream), Mode).
/* Widerspruch */
print_blockline(Stream, Mode, Handle) :-
	translit(contradiction, Contradiction),
	line_contents(Handle, Contradiction),
	!,
	make_reihenfolge2(Handle),
	once(teste(proof, Handle)),
	print_contradiction(Stream, Mode, Handle),
	once(loesche_test).
/* Default */
print_blockline(Stream, Mode, Handle) :-
	make_reihenfolge2(Handle),
	teste(proof, Handle),
	print_intro(Stream, Mode, Handle),
	loesche_test,
	open(_, string, RuleStream),
	print_rule(RuleStream, Mode, Handle),
	current_stream(RuleString, _, RuleStream),
	close(RuleStream),
	(RuleString="" ->
		print_formula(Stream, Mode, ".", Handle)
		;
		print_formula(Stream, Mode, ",", Handle),
		mode_specific(print_string(Stream, RuleString), Mode)
	),
	mode_specific(print_string(Stream, "\n"), Mode).
	

make_reihenfolge2(Handle) :-
	reihenfolge2(Handle, _),
	!.
make_reihenfolge2(Handle) :-
	getval(reihenfolge2, N),
	N1 is N+1,
	setval(reihenfolge2, N1),
	assert(reihenfolge2(Handle, N)).

make_reihenfolge2_l([]).
make_reihenfolge2_l([Handle|HandleList]) :-
	make_reihenfolge2(Handle),
	make_reihenfolge2_l(HandleList).

reihenfolge2(_, Handle, N) :- reihenfolge2(Handle, N).

get_title(Title) :-
	ilf_state(proof_title, Title),
	!.
get_title("A Proof from Ilf").

get_author(Author) :-
	ilf_state(proof_author, Author),
	!.
get_author("The ILF Group").

forward_ref(Handle-Type-Name) :-
	used_ref(Handle),
	once((	
		ref(Handle, Type, Name)
		;
		ilf_warning("unresolved reference: %Dw", [Handle]),
		fail
	)).
	
/* print_text/4 gibt einen der definierbaren Texte (abstract, pre_text, ...)
   aus. Als erste wird ein global gesucht, das eine entsprechende Rulelist
   enthalten soll (Achtung: in der Rulelist sollten keine Befehle verwendet
   werden, die auf das aktuelle Handle zugreifen, da in dieser Situation
   kein aktuelles Handle definiert ist). Existiert ein solches global 
   nicht, wird print_text/3 aufgerufen. */

print_text(Proof, Item, Stream, Mode) :-
	ModeItem =.. [Item, Mode],
	proof([Proof, global], ModeItem, RuleList),
	!,
	exec_rule_list(Stream, Mode, [undefined,handle], RuleList),
	!.
print_text(Proof, Item, Stream, Mode) :-
	proof([Proof, global], Item, RuleList),
	!,
	exec_rule_list(Stream, Mode, [undefined,handle], RuleList),
	!.
print_text(_, Item, Stream, Mode) :-
	print_text(Item, Stream, Mode).

/* print_constants/3 gibt die Konstanten aus, die "eigentlich" Variablen
   sind. Die Verwendung von echten (Prolog-)Variablen scheitert hauptsaechlich 
   daran, dass es schwierig waere, die gleiche Variable in verschiedenen
   proof/3-Fakten zu haben. */

print_constants(_, _, _) :- 
	retract_all(used_constant(_)),
	fail.
print_constants(_, _, Proof) :- 
	/* Der alte Code und das Ilf-Server Manual haben unterschiedliche
	   Ansichten, wie die Konstanten angegeben werden */
	once((
		proof([Proof,global], control, constants(L))
		;
		proof([Proof,global], constants, L)
	)),
	make_used_constants(L). /* failed immer */
print_constants(Stream, Mode, _) :- 
	once((
 		used_constant((_ : T)),
 		setof(C,retract(used_constant((C : T))),CL),
 		mode_specific(print_constants(Stream, T, CL), Mode)
	)),
 	fail.
print_constants(Stream, Mode, _) :- 
	once((
		setof(H,retract(used_constant(H)),CL),
 		mode_specific(print_constants(Stream, CL), Mode)
	)),
	fail.
print_constants(_, _, _).
 
make_used_constants([C|L]) :- 
	assert(used_constant(C)),
 	make_used_constants(L),
	!.	

/* print_proof_begin/3 sucht evtl. fuer den Beweis benutzte Systeme heraus
   und ruft dann print_proof_begin/1 oder print_proof_begin/2 des Modus auf. */

print_proof_begin(Stream, Mode, Proof) :-
	proof([Proof,global], system, System),
	mode_specific(print_proof_begin(Stream, System), Mode),
	!.
print_proof_begin(Stream, Mode, _) :-
	mode_specific(print_proof_begin(Stream), Mode),
	!.

/* print_we/2,3 schreibt "We" ggf. mit einer Fussnote, die angibt, welche(s)
   System(e) den angegebenen Beweis geliefert haben. */
   
print_we(Stream, Mode, Proof) :-
	proof([Proof,global],system,System),
	!,
	mode_specific(print_we(Stream, System), Mode).
print_we(Stream, Mode, _) :-
	mode_specific(print_we(Stream), Mode).
 
/* Ausgabe eines Widerspruchs. Wenn sich der Widerspruch aus der 
   vorhergehenden Zeile und genau einer nicht recallten Zeile ergibt,
   wird "this contradicts ..." geschrieben, in allen anderen Faellen
   "... we have a contradiction.:"
   Im Prolog2-Code wurde im ersten Fall auch der verwendet/2-Fakt fuer
   die ausserhalb recall liegenden Zeile gestrichen - ist das notwendig? */

print_contradiction(Stream, Mode, Handle) :-		
	test_test4,		/* d.h. verwendet/2 mit der Vorgaenger- */
				/* Zeile wurde gestrichen ! */
	test_test1,		/* genau eine nicht recall'te Referenz */
	verwendet_list(Handle, [_]),
	print_references(Stream, Mode, Handle, "This contradicts ", ""),
	mode_specific(print_string(Stream, ".\n"), Mode),
	!.
print_contradiction(Stream, Mode, Handle) :-		
	print_intro(Stream, Mode, Handle),
	mode_specific(	
		print_string(Stream, " we have a contradiction.\n"), 
		Mode).

/* Ermitteln der Rulelist zu einem Handle. */

rule_op(Handle, RuleList, Mode) :-
	rule_op_cache(Handle, RuleList, Mode),
	!.
rule_op(Handle, RuleList, Mode) :-
	try_ruleop([Test|RuleList], Mode),
	ruletest(Handle, Test),
	assert(rule_op_cache(Handle, RuleList, Mode)),
	!.

try_ruleop(RuleList, Mode) :-
	mode_specific(ruleop(RuleList), Mode).
try_ruleop(RuleList, Mode) :-
	mode_specific(default_ruleop(RuleList), Mode).

ruletest(_, Test) :- 
	var(Test), 
	!.
ruletest(Handle, Test) :- 
	setval(current_handle, Handle), 
	call(Test).

/* Kommandos zum Schreiben der ruleops */

current_handle(Handle) :- 
	getval(current_handle, Handle), 
	!.
current_handle(Var) :- 
	var(Var), 
	!, 
	ilf_warning("current_handle not defined", []).

current_handle(Old, New) :-
	current_handle(Old),
	setval(current_handle, New).

control(Test) :- do_ruletest(control, Test).
control(Handle, Test) :- do_ruletest(Handle, control, Test).
status(Test) :- do_ruletest(status, Test).
status(Handle, Test) :- do_ruletest(Handle, status, Test).
contents(Test) :- do_ruletest(contents, Test).
contents(Handle, Test) :- do_ruletest(Handle, contents, Test).
name(Test) :- do_ruletest(name, Test).

do_ruletest(What, Test) :-
	getval(current_handle, Handle),
	do_ruletest(Handle, What, Test).

do_ruletest(Handle, What, Test) :-
	proof(Handle, What, Control),
	!,
	instance(Control, Test),
	Control=Test.
do_ruletest(_, _, []).

premises(Premises) :-
	getval(current_handle, Handle),
	premises(Handle, Premises).

premises(Handle, Premises) :-
	verwendet_list(Handle, Premises).

/* shift */
shift(Test, Shift) :- 
	getval(current_handle, Handle),
	shift(Test, Shift, Handle).

shift(Test, NoInteger, Handle) :-
	not integer(NoInteger),
	ilf_warning("Second argument is not an integer in %Dw", 
			[shift(Test, NoInteger, Handle)]),
	!,
	fail.
shift(Test, 0, Handle) :-
	getval(current_handle, Save),
	(ruletest(Handle, Test) -> Result=true; Result=fail),
	setval(current_handle, Save),
	!,
	Result.
shift(Test, Shift, Handle) :-
	Shift > 0,
	!,
	line_successor(Handle, Handle1),
	Shift1 is Shift-1,
	shift(Test, Shift1, Handle1).
shift(Test, Shift, Handle) :-
	Shift < 0,
	!,
	line_predecessors(Handle, [Handle1]),
	Shift1 is Shift+1,
	shift(Test, Shift1, Handle1).

/* find/4 */
   
find(Test, Pattern, What, List) :-
	getval(current_handle, Handle),
	find(Test, Pattern, What, List, Handle),
	setval(current_handle, Handle).

/* find/5 MUSS gelingen, ansonsten wird current_handle nicht ordentlich
   wiederhergestellt. */

find(Test, Pattern, What, List, Handle) :-
	copy_term(Test^Pattern^What, ThisTest^ThisPattern^ThisWhat),
	ruletest(Handle, ThisTest),
	!,
	findall(ThisWhat, ruletest(Handle, ThisPattern), WhatList),
	append(WhatList, List1, List),
	(line_successor(Handle, Handle1) ->
		find(Test, Pattern, What, List1, Handle1)
		;
		List1=[]
	).
find(_, _, _, [], _).

/* collect_formula/2 */

collect_formula(Handle, Test, HandleList) :-
	getval(current_handle, SaveHandle),
	collect_formula0(Handle, Test, HandleList),
	setval(current_handle, SaveHandle).

collect_formula0(Handle, Test, [Handle1|HandleList]) :-
	line_successor(Handle, Handle1),
	copy_term(Test, ThisTest),
	ruletest(Handle1, ThisTest),
	!,
	collect_formula0(Handle1, Test, HandleList).
collect_formula0(_, _, []).

/* Ausfuehren einer Rulelist. Manche Regeln (siehe formula/0) benutzen 
   auch das naechste Element der Liste, daher hat exec_rule zwei 
   RuleList-Argumente.  */

exec_rule_list(_, _, _, []) :-
	!,
	setval(firstup, off).
exec_rule_list(Stream, Mode, Handle, [Rule|RuleList]) :-
	once((
		exec_rule(Stream, Mode, Handle, Rule, RuleList, RuleList1)
		;
		ilf_warning("error executing '%Dw' for %Dw", [Rule, Handle]),
		RuleList1=RuleList
	)),
	exec_rule_list(Stream, Mode, Handle, RuleList1).

show_rule_script(Script, String, Mode) :-
	body_list(Script, List),
	show_rule_list(List, String, Mode).

show_rule_list(List, String, Mode) :-
	open(_, string, Stream),
	exec_rule_list(Stream, Mode, [undefined, handle], List),
	current_stream(String, _, Stream),
	close(Stream),
	!.

/* Variable -> Fehler! */
exec_rule(_, _, Handle, Var, RuleList, RuleList) :-
	var(Var),
	!,
	ilf_warning("variable %Dw in rulelist for %Dw ignored",
		    [Var, Handle]).
/* proof */
exec_rule(Stream, Mode, Handle, proof, RuleList, RuleList) :-
	!,
	retract_all(reihenfolge2(Handle, _)),
	(line_subproof(Handle, Proof) ->
		(proof_lines(Proof, HandleList) ->
			print_blocklines(Stream, Mode, HandleList)
			;
			ilf_debug(ilf_warning(
				"subproof lines not found for %Dw", [Handle]))
		)
		;
		ilf_warning("No subproof found for %Dw", [Handle])
	),
	make_reihenfolge2(Handle).
/* Strings */
exec_rule(Stream, Mode, _, String, RL, RL) :-
	string(String),
	!,
	check_firstup(Firstup),
	mode_specific(print_string(Stream, String, Firstup), Mode).
/* ref/1 */
exec_rule(Stream, Mode, _, ref(Handle), RL, RL) :-
	!,
	print_ref(Stream, Mode, Handle).
/* formula/1 */
exec_rule(Stream, Mode, _, formula(Handle), RL, RL) :-
	!,
	print_formula(Stream, Mode, "", Handle).
/* math/1 */
exec_rule(Stream, Mode, _, math(Formula), RL, RL) :-
	!,
	mode_specific(clear_varnumbers, Mode),
	check_firstup(Firstup),
	mode_specific(print_formula(Stream, Formula, Firstup, ""), Mode).
/* intro/0 */
exec_rule(Stream, Mode, Handle, intro, RL, RL) :-
	!,
	teste(Handle), 
	print_intro(Stream, Mode, Handle),
	loesche_test.
/* liste/0 */
exec_rule(Stream, Mode, Handle, liste, RL, RL) :-
	!,
	print_references(Stream, Mode, Handle, "", "by").
/* formula_ref/0 */
exec_rule(Stream, Mode, Handle, formula_ref, RL, RL) :-
	!,
	print_ref(Stream, Mode, Handle).
/* rules/0 */
exec_rule(Stream, Mode, Handle, rules, RL, RL) :-
	!,
	print_rule(Stream, Mode, Handle).
/* theorem/0 */
exec_rule(Stream, Mode, Handle, theorem, RL, RL) :-
	!,
	print_theorem(Stream, Mode, "Theorem", Handle, []). 
/* theorem/1 */
exec_rule(Stream, Mode, Handle, theorem(Type), RL, RL) :-
	!,
	print_theorem(Stream, Mode, Type, Handle, []). 
/* theorem/2 */
exec_rule(Stream, Mode, Handle, theorem(Type, Name), RL, RL) :-
	!,
	print_theorem(Stream, Mode, Type, Handle, Name). 
/* theorem/3 */
exec_rule(Stream, Mode, Handle, theorem(Type, Name, Script), RL, RL) :-
	!,
	open(_, string, S),
	body_list((Script, "."), RuleList),
	exec_rule_list(S, Mode, Handle, RuleList),
	current_stream(String, _, S),
	close(S),
	print_theorem_string(Stream, Mode, Type, String, Handle, Name). 
/* formula/0 */
exec_rule(Stream, Mode, Handle, formula, RL, RL1) :-
	!,
	get_punct(RL, String, Punct, RL1),
	print_formula(Stream, Mode, Punct, Handle),
	mode_specific(print_string(Stream, String), Mode).
/* collect_formula/1 */
exec_rule(Stream, Mode, Handle, collect_formula(Test), RL, RL1) :-
	!,
	get_punct(RL, String, Punct, RL1),
	collect_formula(Handle, Test, HandleList),
	print_formula_list(Stream, Mode, Punct, [Handle|HandleList]),
	mode_specific(print_string(Stream, String), Mode),
	make_reihenfolge2_l([Handle|HandleList]),
	mark_skip_l(HandleList).
/* we/0 */
exec_rule(Stream, Mode, Handle, we, RL, RL) :-
	!,
	line_subproof(Handle, Proof),
	print_we(Stream, Mode, Proof).
/* par/0 */
exec_rule(Stream, Mode, _, par, RL, RL) :-
	!,
	mode_specific(end_par(Stream), Mode).
/* firstup/0 */
exec_rule(_, _, _, firstup, RL, RL) :-
	!,
	setval(firstup, on).
/* hide/0,1 ignorieren */
exec_rule(_, _, _, hide, RL, RL) :- !.
exec_rule(_, _, _, hide(_), RL, RL) :- !.
/* label - im Moment nur fuer LaTeX! */
exec_rule(Stream, latex, Handle, label(What), RL, RL) :-
	assert(ref(Handle, What, [])),
	printf(Stream, "\\label{%w}", [Handle]).
/* unbekanntes Schluesselwort */
exec_rule(_, _, Handle, Unknown, RL, RL) :-
	ilf_warning("unknown keyword %Dw in rulelist for %Dw ignored",
		    [Unknown, Handle]).

get_punct([Next|RuleList], String, ".", RuleList) :-
	first_letter(Next, ".", String),
	!.
get_punct([Next|RuleList], String, ",", RuleList) :-
	first_letter(Next, ",", String),
	!.
get_punct(RuleList, "", "", RuleList).


/* Ausgabe einer Referenz. Wenn das referierte Object ueber ref/3 in eine
   bestimmte Kategorie faellt (z.B. Axiom, Lemma, o.ae.) und einen "Namen"
   (z.B. transitivity) hat, wird print_string_ref/3 des Modus benutzt.
   Ein Fakt fuer ref/3, aber kein Name fuehrt zum Aufruf von print_ref/4 
   des Modus. Ist kein Fakt fuer ref/3 da, wird print_ref/3 verwendet. 
   Die Zaehlung liegt immer in Verantwortung des Modus. Das Handle wird 
   immer dem Modus uebergeben (damit kann HTML z.B. einen Hyperlink auch
   vom Namen auf die entsprechende Stelle anbringen).  */

print_ref(Stream, Mode, Handle) :-
	ref(Handle, Type, []),
	!,
	check_firstup(Firstup),
	mode_specific(print_ref(Stream, Type, Handle, Firstup), Mode),
	!.
print_ref(Stream, Mode, Handle) :-
	ref(Handle, _, Name),
	!,
	show_fla(Name, NameS1, Mode),
	(check_firstup(on) ->
		mode_specific(firstup(NameS1, NameS), Mode)
		;
		NameS=NameS1
	),
	mode_specific(print_string_ref(Stream, NameS, Handle), Mode),
	!.
print_ref(Stream, Mode, Handle) :-
	(used_ref(Handle) ; assert(used_ref(Handle))),
	check_firstup(Firstup),
	mode_specific(print_ref(Stream, Handle, Firstup), Mode),
	!.

/* first_letter/3 gelingt, wenn das zweite Argument eine String der Laenge 1
   ist und die Verkettung des zweiten und des dritten Arguments gerade das
   erste Argument (das instantiiert sein muss) ergibt. */

first_letter(String, First, Rest) :-
	string(String),
	string_list(String, [FirstAscii|RestList]),
	string_list(First, [FirstAscii]),
	string_list(Rest, RestList).
	
goto_proof(Handle, [prolog(Call)|RuleListe], RuleList) :-
	setval(current_handle, Handle),
	once((call(Call) ; true)),
	goto_proof(Handle, RuleListe,RuleList).
goto_proof(_, [proof|RuleList], RuleList) :- !.
goto_proof(Handle, [_|RuleListe], RuleList) :-
	goto_proof(Handle, RuleListe,RuleList).
 
%% find_superproof([Proof, Handle], SuperHandle) :-
%% 	proof([Proof, Handle], predecessors, []),
%% 	proof(Handle1, status, subproof(Proof)),
%% 	not(schon_weg(Handle1)),
%% 	(
%% 		find_superproof(Handle1, SuperHandle)
%% 		;
%% 		SuperHandle=Handle1
%% 	).
%% 
/****************************************************************************
*
*	Die verschiedenen Einleitungen
*
*	Um zu wissen welche Formeln oder Axiome verwendet wurde, wird 
*	verwendet/2 benutzt (verwendet/2 entsteht aus proof(_,rule(_,Liste)).
*	Aus diesen Informationen erzeugt teste/3 die Fakten test_test[1-7]/0,
*	die hier benutzt werden. Zur Bedeutung von test_test[1-7]/0 siehe
*	teste/3 und die Kommentare direkt im Code von print_intro/3.
*
*	Fuer bekannt vorausgesetzte Axiome kann verwendet/2 geloescht werden
*	(ilf_state(known_theoy)).
*
*****************************************************************************/

print_intro(Stream, Mode, Handle) :-
	not(test_test), 
	test_test7,		/* es gibt Verweise ausserhalb von remember:
				   der Inhalt dieser Zeilen wird nach einem
				   "since" direkt angegeben */
	assert(test_test),	/* Flag: "since" wurde schon behandelt */
	once((			/* wenn es ausser den "since"-Zeilen noch 
				   andere Referenzen gibt, werden diese zuerst
				   ausgegeben */
		verwendet(Handle, Ref),
		not since_label(Handle, Ref),
		print_intro(Stream, Mode, Handle),
		mode_specific(print_string(Stream, "and since "), Mode),
		Punct = " "
		;
		test_test4,
		mode_specific(print_string(Stream, "Hence, since "), Mode),
		Punct = ", "
		;
		mode_specific(print_string(Stream, "Since "), Mode),
		Punct = " "
	)),
	print_since_lines(Stream, Mode, Handle, Punct),
	retract(test_test).
print_intro(Stream, Mode, _) :-
	not(test_test1),		/* verweist nur auf die genau davor */
	not(test_test2),		/* liegende Zeile */
	not(test_test3),
	not(test_test5),
	test_test4,
	mode_specific(print_string(Stream, "Hence "), Mode).
print_intro(Stream, Mode, _) :-
	not(test_test1),		/* alle Verweise innerhalb recall */
	not(test_test2),		/* aber nicht auf die genau davor */
	test_test3,			/* liegende Zeile */
	not(test_test4),
	not(test_test5),
	mode_specific(print_string(Stream, "Now "), Mode).
print_intro(Stream, Mode, _) :-
	not(test_test1),		/* alle Verweise innerhalb recall */
	not(test_test2),		/* und ein Verweis auf die genau */
	test_test3,			/* davor liegende Zeile */
	not(test_test5),
	mode_specific(print_string(Stream, "Therefore "), Mode).
print_intro(Stream, Mode, Handle) :-
	not(test_test2),		/* Verweis auf die davor liegende */
	not(test_test3),		/* Zeile und auf eine Zeile in einem */
	test_test4,			/* anderen subproof oder ausserhalb */
	test_test1,			/* von recall */
	print_references(Stream, Mode, Handle, "Hence by ").
print_intro(Stream, Mode, Handle) :-
	not(test_test2),		/* Verweis auf die davor liegende */
	not(test_test3),		/* Zeile und auf ein Axiom */
	test_test4,
	test_test5,
	print_references(Stream, Mode, Handle, "Hence by ").
print_intro(Stream, Mode, Handle) :-
	test_test1,			/* ein Verweis ausserhalb, alle */
	not(test_test2),		/* anderen innerhalb recall, aber */
	test_test3,			/* kein Verweis auf die unmittelbar */
	not(test_test4),		/* davorliegende Zeile. */
	print_references(Stream, Mode, Handle, "Now by ").
print_intro(Stream, Mode, Handle) :-
	test_test1,			/* ein Verweis ausserhalb, alle */
	not(test_test2),		/* anderen innerhalb recall (u.a. */
	test_test3,			/* die unmittelbar davor liegende) */
	print_references(Stream, Mode, Handle, "Therefore by ").
print_intro(Stream, Mode, Handle) :-
	test_test5,			/* Axiome und recall, kein Verweis */
	not(test_test2), 		/* auf die unmittelbar davor */
	test_test3,			/* liegende Zeile. */
	not(test_test4),
	print_references(Stream, Mode, Handle, "Now by ").
print_intro(Stream, Mode, Handle) :-
	test_test5,			/* Axiome und recall (u.a. die  */
	not(test_test2),		/* unmittelbar davor liegende Zeile. */
	test_test3,
	print_references(Stream, Mode, Handle, "Therefore by ").
print_intro(Stream, Mode, Handle) :-
	not(test_test1),		/* nur Axiome */
	not(test_test2),
	not(test_test3),
	not(test_test4),
	test_test5,
	print_references(Stream, Mode, Handle, "Because of ").
print_intro(Stream, Mode, Handle) :-
	not(test_test5),		/* Vorwaerts-Referencen und ein */
	test_test2,			/* Verweis ausserhalb recall */
	not(test_test3),
	not(test_test4),
	test_test1,
	print_references(Stream, Mode, Handle, "By ").
print_intro(Stream, Mode, Handle) :-
	not(test_test5),		/* genau ein Verweis ausserhalb */
	not(test_test2),		/* recall */
	not(test_test3),
	not(test_test4),
	test_test1,
	print_references(Stream, Mode, Handle, "By ").
print_intro(Stream, Mode, Handle) :-
	test_test5,			/* Axiome und genau ein Verweis */
	not(test_test2),		/* ausserhalb recall */
	not(test_test3),
	not(test_test4),
	test_test1,
	print_references(Stream, Mode, Handle, "By ").
print_intro(Stream, Mode, Handle) :-
	premises(Handle, []),
	mode_specific(print_string(Stream, "Clearly, "), Mode).
print_intro(_, _, _) :-
	setval(firstup, on).

/* Ausgabe des Contents einer Liste von Zeilen als Aufzaehlung lt.
   engl. Grammatik (>3 Glieder -> , auch vor and).
   Wird benutzt fuer die Ausgabe von 'since'. 
   Fuer 'since' gab es im Prolog2-Code ein auskommentiertes "by ..." 
   nach jeder Formel, ggf. muesste das noch ergaenzt werden. */

print_contents_list(Stream, Mode, [Hdl1, Hdl2, Hdl3]) :-
	!,
	print_formula_nolabel(Stream, Mode, ",", Hdl1),
	mode_specific(print_string(Stream, " "), Mode),
	print_formula_nolabel(Stream, Mode, ",", Hdl2),
	mode_specific(print_string(Stream, " and "), Mode),
	print_formula_nolabel(Stream, Mode, "", Hdl3).
print_contents_list(Stream, Mode, [Hdl1, Hdl2]) :-
	!,
	print_formula_nolabel(Stream, Mode, "", Hdl1),
	mode_specific(print_string(Stream, " and "), Mode),
	print_formula_nolabel(Stream, Mode, "", Hdl2).
print_contents_list(Stream, Mode, [Hdl1]) :-
	!,
	print_formula_nolabel(Stream, Mode, "", Hdl1).
print_contents_list(Stream, Mode, [Hdl1|HdlList]) :-
	print_formula_nolabel(Stream, Mode, ",", Hdl1),
	mode_specific(print_string(Stream, " "), Mode),
	print_contents_list(Stream, Mode, HdlList).

/* Ausgabe der "since"-Zeilen, die ausserhalb von remember liegen. */ 

print_since_lines(Stream, Mode, Handle, Punct) :-
	setof(X, since_label(Handle, X), SinceList),
	print_contents_list(Stream, Mode, SinceList),
	mode_specific(print_string(Stream, Punct), Mode).
print_since_lines(_, _, Handle, _) :-
	ilf_error("print_since_lines: %Dw", [Handle]).

/* Ausgabe der zum Beweis einer Zeile benutzen Formeln als Referenzen.
   print_references/4 wird von print_intro/3 aufgerufen, es druckt nur die
   Referenzen, die keine since_label/2 sind und gibt nach den Referenzen 
   noch ein Leerzeichen aus.
   Alle anderen werden vermutlich print_references/5 benutzen wollen. */

print_references(Stream, Mode, Handle, Intro) :-
	setof(X, (verwendet(Handle, X), not(since_label(Handle, X))), List),
	!,
	check_firstup(Firstup),
	mode_specific(print_string(Stream, Intro, Firstup), Mode),
	print_references_list(Stream, Mode, List, "by"),
	mode_specific(print_string(Stream, " "), Mode).
print_references(_, _, Handle, _) :-
	ilf_error("print_references/4: no references for %Dw", [Handle]).

print_references(Stream, Mode, Handle, Intro, By) :-
	setof(X, verwendet(Handle, X), List),
	!,
	check_firstup(Firstup),
	mode_specific(print_string(Stream, Intro, Firstup), Mode),
	print_references_list(Stream, Mode, List, By).
print_references(_, _, Handle, _, _) :-
	ilf_error("print_references/5: no references for %Dw", [Handle]).

print_references_list(Stream, Mode, [Handle1, Handle2, Handle3], By) :-
	!,
	print_ref(Stream, Mode, Handle1),
	mode_specific(print_string(Stream, ",  "), Mode),
	print_ref(Stream, Mode, Handle2),
	concat_string([", and ", By, " "], S),
	mode_specific(print_string(Stream, S), Mode),
	print_ref(Stream, Mode, Handle3).
print_references_list(Stream, Mode, [Handle1, Handle2], By) :-
	!,
	print_ref(Stream, Mode, Handle1),
	concat_string([" and ", By, " "], S),
	mode_specific(print_string(Stream, S), Mode),
	print_ref(Stream, Mode, Handle2).
print_references_list(Stream, Mode, [Handle], _) :-
	!,
	print_ref(Stream, Mode, Handle).
print_references_list(Stream, Mode, [Handle|HandleList], By) :-
	print_ref(Stream, Mode, Handle),
	mode_specific(print_string(Stream, ", "), Mode),
	print_references_list(Stream, Mode, HandleList, By).

/* Ausgabe der Regel(n) zu einer Zeile ("because of ..."). Wenn *alle*
   Regeln "bekannt" sind (d.h. es existiert je ein Fakt fuer known_rule/1),
   wird nichts ausgegeben. */

print_rule(_, _, Handle) :-
	line_control(Handle, rule(Rules, _)),
	all_rules_known(Rules),
	!.
print_rule(Stream, Mode, Handle) :-
	line_control(Handle, rule(Rules, _)),
	!,
	mode_specific(print_string(Stream, " because of "), Mode),
	mode_specific(print_formula(Stream, Rules, off,  "."), Mode).
print_rule(_, _, _).

all_rules_known([]).
all_rules_known([Rule|List]) :-
	not not known_rule(Rule),
	all_rules_known(List).

/* Ausgabe einer Formel mit Satzzeichen (kann auch "" sein) und mit
   der Moeglichkeit, ein Label zu setzen (die Entscheidung, ob tatsaechlich
   ein Label gesetzt wird, faellt erst im Postprocessing). Grundsaetzlich 
   werden vor Ausgabe einer Formel die Variablennamen zurueckgesetzt. */

print_formula(Stream, Mode, Punct, Handle) :-
	ref(Handle, _, _),
	!,
	print_formula_nolabel(Stream, Mode, Punct, Handle).
print_formula(Stream, Mode, Punct, Handle) :-
	assert(possible_label(Handle)),
	line_contents(Handle, Contents),
	check_firstup(Firstup),
	mode_specific(clear_varnumbers, Mode),
	punkt(Handle),
	mode_specific(
		print_formula(Stream, Contents, Firstup, Punct, Handle), 
		Mode),
	!.
print_formula(_, _, _, Handle) :-
	ilf_error("error writing formula for %Dw", [Handle]).

/* Ausgabe einer Liste von Formeln mit Satzzeichen und moeglichem Label
   (Anmerkungen siehe print_formula/4 */

print_formula_list(Stream, Mode, Punct, [Handle1, Handle2, Handle3]) :-
	!,
	print_formula(Stream, Mode, ",", Handle1),
	mode_specific(print_string(Stream, " "), Mode),
	print_formula(Stream, Mode, ",", Handle2),
	mode_specific(print_string(Stream, " and "), Mode),
	print_formula(Stream, Mode, Punct, Handle3).
print_formula_list(Stream, Mode, Punct, [Handle1, Handle2]) :-
	!,
	print_formula(Stream, Mode, "", Handle1),
	mode_specific(print_string(Stream, " and "), Mode),
	print_formula(Stream, Mode, Punct, Handle2).
print_formula_list(Stream, Mode, Punct, [Handle]) :-
	!,
	print_formula(Stream, Mode, Punct, Handle).
print_formula_list(Stream, Mode, Punct, [Handle|HandleList]) :-
	print_formula(Stream, Mode, ",", Handle),
	mode_specific(print_string(Stream, " "), Mode),
	print_formula_list(Stream, Mode, Punct, HandleList).

/* Ausgabe einer Formel im laufenden Text garantiert *ohne* Label. */

print_formula_nolabel(Stream, Mode, Punct, Handle) :-
	mode_specific(clear_varnumbers, Mode),
	line_contents(Handle, Contents),
	check_firstup(Firstup),
	punkt(Handle),
	mode_specific(print_formula(Stream, Contents, Firstup, Punct), Mode).

/* Ausgabe einer Formel in einer bestimmten "Umgebung" (das sind in Latex
   Environments, in HTML selbstgebaute Konstruktionen). Formeln in Umgebungen
   koennen grundsaetzlich referenziert werden. Die Referenz besteht entweder
   aus dem angebenen Namen oder aus dem Namen der Umgebung mit einer
   laufenden Nummer (diese muß vom Modus verwaltet werden!).
   Grundsaetzlich werden vor Ausgabe einer Formel die Variablennamen 
   zurueckgesetzt. */

print_theorem(Stream, Mode, Env, Handle, Name) :-
	check_assert_ref(Handle, Env, Name),
	mode_specific(clear_varnumbers, Mode),
	line_contents(Handle, Formula),
	mode_specific(print_theorem(Stream, Env, Formula, Handle, Name), Mode).

print_theorem(Stream, Mode, Env, Formula, Handle, Name) :-
	check_assert_ref(Handle, Env, Name),
	mode_specific(clear_varnumbers, Mode),
	mode_specific(print_theorem(Stream, Env, Formula, Handle, Name), Mode).

print_theorem_string(Stream, Mode, Env, String, Handle, Name) :-
	check_assert_ref(Handle, Env, Name),
	mode_specific(print_theorem_string(Stream, Env, String, Handle, Name), Mode).

check_assert_ref(Handle, _, _) :-
	ref(Handle, _, _),
	once((
		ilf_warning("label %Dw multiply defined", [Handle]),
		retract_all(ref(Handle, _, _))
	)),
	fail.
check_assert_ref(Handle, Env, Name) :-
	assert(ref(Handle, Env, Name)).

/* Liefert den aktuellen Wert der firstup-Variable und setzt sie zurueck. */
check_firstup(Firstup) :-
	getval(firstup, Firstup),
	setval(firstup, off).

/* blocklines_done/1 erzeugt fuer die 
/**************************************************************************
*
*	Test fuer die Einleitung
*
*	1 : Abstand > recall(2)
*	    ODER
*	    Abstand > 1 und beide nicht im gleichen Subproof
*	2 : Abstand negativ
*	3 : 1 < Abstand < recall(2)+1 UND beide im gleichen Subproof
*	4 : Abstand = 1
*	5 : Abstand = 0 Fall nicht in reihenfolge2 enthalten, daher Axiom
*	6 : Situation 1 mehr als einmal
*	7 : Termtiefe <= 1 
*	    UND Abstand = 0 (Axiom)
*		ODER
*		Abstand > remember(6) 
*	    	ODER
*	    	Abstand > 2*recall
*
****************************************************************************/

teste([Name, X]) :- teste(proof, [Name, X]).
teste(Proof, [Name, X]):- teste(Proof,Name,X).

teste(Proof,Name,X):-
	once(liste_test_vorgaenger([Name,X],Proof)).
	
liste_test_vorgaenger(Handle, Proof) :-
	verwendet(Handle, Handle1),
	once((
		reihenfolge2(Proof, Handle, Z0)
		;
		ilf_error("reihenfolge2(%Dw) undefined", [Handle]),
		getval(reihenfolge2, Z0)
	)),
	once((
		reihenfolge2(Proof, Handle1, Z1),
		Z is Z0-Z1
		;
		Z is 0
	)),
	once(auswerten_test(Handle, Handle1, Z)),
	fail.
liste_test_vorgaenger([_,_],_).
	
auswerten_test(Handle, Handle1, Z) :-
	line_contents(Handle1, F),
	term_depth_less(F, 1),
	(
		Z = 0
		;
		ilf_state(remember,R),
		Z>R
		;
		not(ilf_state(remember,_)),
		ilf_state(recall,E),
		Z>(E+E)
		;
		not(ilf_state(remember,_)),
		not(ilf_state(recall,_)),
		Z>6
	),
	assert_or_fail(since_label(Handle, Handle1)),
	assert_or_fail(test_test7).
auswerten_test(_, _, Z) :-
	(
		ilf_state(recall,R),
		Z>R
		;
		not(ilf_state(recall,_Re)),
		Z>2
	),
	test_test1,
	assert_or_fail(test_test6).
auswerten_test(_, _, Z) :- 
	(
		ilf_state(recall,R),
		Z>R
		;
		not(ilf_state(recall,_Re)),
		Z>2
	),
	assert_or_fail(test_test1).
auswerten_test(_, _, Z) :-
	Z<0,
	assert_or_fail(test_test2).
auswerten_test([Proof, Handle], [Proof, Handle1], Z) :-
	(
		ilf_state(recall,R),
		Z<(R+1),
		Z>1
		;
		not(ilf_state(recall,R)),
		Z=2
	),
	retract_all(verwendet_cache([Proof, Handle], [Proof, Handle1])),
	assert_or_fail(test_test3).
auswerten_test(_, _, Z) :-
	(
		ilf_state(recall,R),
		Z<(R+1),
		Z>1
		;
		not(ilf_state(recall,R)),
		Z=2
	),
	(
		assert_or_fail(test_test1)
		;
		test_test1,
		assert_or_fail(test_test6)
	).
auswerten_test(Handle, Handle1, 1) :-
	retract_all(verwendet_cache(Handle, Handle1)),
	assert_or_fail(test_test4).
auswerten_test(_, _, 0) :-
	assert_or_fail(test_test5).
auswerten_test([_Name,_X],[_Name1,_Y],_Z).

assert_or_fail(X) :- not(X), assert(X).

assert_once(X) :- call(X), !.
assert_once(X) :- assert(X).

/************************************************************************
 *									*
 *	Regeln								*
 *									*
 *	zum Einfuegen von Teilbeweisen					*
 *									*
 ************************************************************************/

load_subproof(SubPfhdl):-
	get_error_handler(64, Old, _),
	(
		set_error_handler(64, true/0)
		;
		set_error_handler(64, Old),
		fail
	),
	get_proof(SubPfhdl),
	!,
	set_error_handler(64, Old),
	top_retract(proof([SubPfhdl,global],goal,_)),
	!.
			
/* Aus den ilf_states know_rules und known_theory werden zum einfacheren
   Zugriff Praedikate know_rule/known_axiom erzeugt. */

compile_ilf_state(IlfState, Pred) :-
	ilf_state(IlfState, Val),
	(length(Val, _) -> ValList=Val ; ValList=[Val]),
	once(make_call_list(Pred, ValList, CallList0)),
	setof(X, member(X, CallList0), CallList),
	compile_term(CallList),
	!.
compile_ilf_state(_, Pred) :-
	Call=..[Pred, _],
	compile_term([Call :- fail]).

make_call_list(_, [], []) :- !.
make_call_list(Pred, [X|L], [Call|CallL]) :-
	Call=..[Pred, X],
	make_call_list(Pred, L, CallL).

/* Die eigentliche Ausgabe der Theorie erfolgt erst *nach* der Ausgabe
   des Beweises unter Benutzung des dann vorhandenen used_ref/1.
   Vor der Ausgabe des Beweises werden die Axiome mittels skip/1 vor
   print_blockline/3 versteckt und die Handle der "bekannten" Axiome 
   (ilf_state known_theory) ermttelt. */

hide_theory :-
	once(compile_ilf_state(known_theory, known_axiom)),
	fail.
hide_theory :-
	proof(Handle, control, axiom(Name)),
	assert(skip(Handle)),
	once(known_axiom(Name)),
	assert(known_axiom(Handle, Name)),
	fail.
hide_theory.
	
mark_skip_l([]).
mark_skip_l([Handle|HandleList]) :-
	assert(skip(Handle)),
	mark_skip_l(HandleList).

/* Ausgabe der Theorie.   
   Zunaechst werden die Namen der durch known_axiom (erzeugt aus dem ilf_state
   known_theory) aufgelisteten und im Beweis benutzten Theorien (Domains)
   ausgegeben.
   Danach kommen alle Axiome, die im Beweis benutzt wurden (verwendet_cache/2)
   und die nicht bekannt sind (known_axiom/1). Durch ist_axiom/2 wird 
   vermieden, dass Axiome doppelt ausgegeben werden. */

print_theory(Stream, Mode) :-
	print_known_theory(Stream, Mode),
	print_axioms(Stream, Mode).

print_known_theory(Stream, Mode) :- 
	setof(Theory, used_known_theory(Theory), KnownTheories),
	mode_specific(print_known_theory(Stream, KnownTheories), Mode).
print_known_theory(_, _).

used_known_theory(Theory) :-
	known_axiom_used(Theory-_),
	known_axiom(Theory-Var),
	var(Var),
	not var(Theory).

print_axioms(Stream, Mode) :-
	proof(Handle, control, axiom(AxName)),
	once(print_axiom(Stream, Mode, Handle, AxName)),
	fail.
print_axioms(_, _).

print_axiom(_, _, Handle, _) :-
	not verwendet_cache(_, Handle).
print_axiom(_, _, Handle, _) :- 
	ist_axiom(Handle).
print_axiom(Stream, Mode, Handle, AxName) :-
	print_theorem(Stream, Mode, "Axiom", Handle, AxName),
	assert(ist_axiom(Handle)).

%%conjecture_test("Conjecture") :-
%%	proof(Handle, status, Status),
%%	(var(Status) ->
%%		ilf_warning("%Dw: status is a variable.", [Handle])
%%		;
%%		test_conj(Status)
%%	),
%%	!.
%%conjecture_test("Theorem").
%%	
%%test_conj(proved) :- !, fail.
%%test_conj(assumption(_)) :- !, fail.
%%test_conj(subproof(_)) :- !, fail.
%%test_conj(axiom(_)) :- !, fail.
%%test_conj(lemma(_)) :- !, fail.
%%test_conj(theory(_)) :- !, fail.
%%test_conj(_).		

/* Neu! Fehlt noch: conjecture test. */

print_theorem(Stream, Mode, Proof, _) :-
	proof([Proof, global], goal, Formula),
	once(proof([Proof, global], name, Name) ; Name = []),
	punkt([Proof, theorem]),
	print_theorem(Stream, Mode, "Theorem", Formula, [Proof, theorem], Name).
		
/* Neu! */

print_lemmata(_, _, [MainProof], MainProof) :- !.
print_lemmata(Stream, Mode, [Lemma|HandleList], MainProof) :-
	skip(Lemma),
	!,
	print_lemmata(Stream, Mode, HandleList, MainProof).
print_lemmata(Stream, Mode, [Lemma|HandleList], MainProof) :-
	print_theorem(Stream, Mode, "Lemma", Lemma, []),
	print_proof_begin(Stream, Mode, Lemma),
	print_blocklines(Stream, Mode, [Lemma]),
	mode_specific(print_qed(Stream), Mode),
	print_lemmata(Stream, Mode, HandleList, MainProof).


/*************************************************************************
**								   	**
**	Die folgenden Regeln sind					**
**									**
**	zum Loeschen von Hilfsklauseln					**
**									**
*************************************************************************/

%%loesche_test:-
%%	retract_all(test_test1),
%%	retract_all(test_test2),
%%	retract_all(test_test3),
%%	retract_all(test_test4),
%%	retract_all(test_test5),
%%	retract_all(test_test6),
%%	retract_all(test_test7),
%%	retract_all(test_test).
%%
loesche_test:-
	clear(test_test1/0),
	clear(test_test2/0),
	clear(test_test3/0),
	clear(test_test4/0),
	clear(test_test5/0),
	clear(test_test6/0),
	clear(test_test7/0),
	clear(test_test/0).

clearall(Mode) :-
	loesche_test,
	clear(hidden/1),
	clear(hidden_cache/2),
	clear(ist_axiom/1),
	clear(known_axiom/2),
	clear(known_axiom_used/1),
	clear(loeschen/1),
	clear(possible_label/1),
	clear(ref/3),
	clear(reihenfolge/3),
	clear(reihenfolge2/2),
	clear(reservation/2),
	clear(rule_op_cache/3),
	clear(schonweg/2),
	clear(schon_weg/1),
	clear(since_label/2),
	clear(skip/1),
	clear(used_constant/1),
	clear(used_ref/1),
	clear(verwendet_cache/2),
	clear(verwendet_cache_temp/2),
	clear(zahl/1),
	setval(firstup, off),
	setval(reihenfolge2, 1),
	mode_specific(ini_varnames, Mode),
	mode_specific(clearall, Mode).

clear(Pred) :-
	current_predicate(Pred),
	!,
	abolish(Pred),
	dynamic(Pred).
clear(Pred) :-
	dynamic(Pred).

/* verwendet/2 und verwendet_list/2 geben die Information, welche Zeilen 
   fuer eine bestimmte Zeile benutzt werden. Das wird bei der Ausgabe der
   Einleitung benutzt und kann vom Benutzer ueber premises/1,2 abgefragt 
   werden. Dabei wird der ilf_state known_theory, die hide-Kommandos vom 
   Nutzer, ...  beruecksichtigt. */

:- mode verwendet(++, ?).
verwendet(H, H1) :-
	verwendet_cache_temp(H, HList),
	!,
	ilf_warning("cycle while trying to determine premises of %Dw", [H]),
	member(H1, HList).
verwendet(H, _) :-
	verwendet_cache(H, []),
	!,
	fail.
verwendet(H, H1) :-
	verwendet_cache(H, _),
	!,
	verwendet_cache(H, H1).
verwendet(H, H1) :-
	make_verwendet_cache(H),
	!,
	verwendet(H, H1).

:- mode verwendet_list(++, ?).
verwendet_list(H, HList) :-
	setof(H1, verwendet(H, H1), RefList),
	!,
	HList=RefList.
verwendet_list(_, []).

make_verwendet_cache(H) :-
	line_control(H, rule(_, List)),
	!,
	assert(verwendet_cache_temp(H, List)),
	check_reflist(H, List, RefList),
	(RefList == [] ->
		assert_once(verwendet_cache(H, []))
		;
		assert_verwendet_cache(H, RefList)
	),
	retract_all(verwendet_cache_temp(H,_)).
make_verwendet_cache(H) :-
	assert(verwendet_cache(H, [])).

assert_verwendet_cache(_, [] ) :- !.
assert_verwendet_cache(H, [Ref|RefList]) :- 
	assert_once(verwendet_cache(H, Ref)),
	assert_verwendet_cache(H, RefList).

check_reflist(H, Var, []) :- 
	var(Var), 
	!,
	ilf_warning("premise list of %Dw is a variable (ignored).", [H]). 
check_reflist(H, [Var|RefList], CheckedList) :- 
	var(Var), 
	!,
	ilf_warning("variable %w in premise list of %Dw (ignored).", [H, Var]), 
	check_reflist(H, RefList, CheckedList).
check_reflist(H, [H1|RefList], CheckedList) :- 
	known_axiom(H1, Name),
	!,
	assert_once(known_axiom_used(Name)),
	check_reflist(H, RefList, CheckedList).
check_reflist(H, [H1|RefList], CheckedList) :- 
	hidden(H1, HList),
	!,
	check_reflist(H, HList, CheckedList0),
	check_reflist(H, RefList, CheckedList1),
	append(CheckedList0, CheckedList1, CheckedList).
check_reflist(H, [H1|RefList], [H1|CheckedList]) :- 
	!,
	check_reflist(H, RefList, CheckedList).
check_reflist(_, [], []).

hidden(H, _) :-
	hidden_cache(H, no),
	!,
	fail.
hidden(H, HList) :-
	hidden_cache(H, HList),
	!.
hidden(H, HList) :-
	getval(current_mode, Mode),
	rule_op(H, RuleList, Mode),
	!,
	check_hidden(H, HList, RuleList),
	assert(hidden_cache(H, HList)),
	!,
	not HList == no.
hidden(H, [H]) :-
	assert(hidden_cache(H, no)),
	!,
	fail.

check_hidden(_, HiddenList, RuleList) :-
	member(hide(HiddenList), RuleList),
	!.
check_hidden(Handle, HiddenList, RuleList) :-
	member(hide, RuleList),
	!,
	verwendet_list(Handle, HiddenList).
check_hidden(_, no, _).
	
erzeuge_verwendet(Proof):-
	proof_lines(Proof, HandleList),
	erzeuge_verwendet_l(HandleList).

erzeuge_verwendet_l([]).
erzeuge_verwendet_l([Handle|HandeList]) :-
	once(verwendet(Handle, _) ; true),
	(line_subproof(Handle, SubProof) -> 
		erzeuge_verwendet(SubProof) 
		; 
		true 
	),
	erzeuge_verwendet_l(HandeList).

/* term_depth_less/2 ist wahr, wenn die Termtiefe des ersten Arguments
   kleiner oder gleich dem zweiten Argument ist. Dabei ist die Termtiefe
   einer Variablen, eines Atoms oder einer Zahl gleich 0 und die Termtiefe
   eines zusammengesetzten Terms gleich dem Maximum der Termtiefen seiner
   Argumente erhoeht um 1. */

term_depth_less(F,_N) :- var(F),!.
term_depth_less(F,_N) :- atomic(F),!.
term_depth_less(F,N) :- N > 0,F=..[_|Arg],
	N1 is N-1,
	term_depth_less_l(Arg,N1),!.

term_depth_less_l([E|Arg],N) :- term_depth_less(E,N),
	term_depth_less_l(Arg,N),!.
term_depth_less_l([],_).

/* punkt/1 gibt einen Punkt oder das uebergeben Handle auf stdout aus 
   (benutzt als Fortschrittsanzeige). */

punkt(Handle) :- ilf_state(debug, on), !, write(Handle), flush(output).
punkt(_) :- write("."), flush(output).

/*************************************************************************/
/* BLOCK LINES */
/*************************************************************************/
 
/* block_lines prints lines of block proof */

block_lines :- 
	% Initialisierung 
	proof([PfHdl,global],goal,_),
	first_proof_line(PfHdl,H),
	show_block_lines(H),!.


show_block_lines(Node) :- 
	% Anzeige 
	once(
	     ((    proof(Node,contents,F) ->
		   WriteF = yes
	      ;    WriteF = no
	      ),
	      (    proof(Node,status,S) -> 
		   WriteS = yes 
	      ;    WriteS = no
	      ),
	      (    proof(Node,control,R) ->
	           WriteR = yes 
	      ;    WriteR = no
	      ),
	      ilf_serv_log((write(Node),
	                    write(":"),
	                    (   WriteF = yes ->
 	                        printf("%Dw",[F])
	                    ;   write(" <*** Missing contents!>")
	                    ),
			    (   WriteS = yes -> 
	          	        write(" is "),
				write(S)
			    ;   write(" <*** Missing status!>")
			    ),
			    (   WriteR = yes ->
				write(" by "),
				write(R)
			    ;   true
			    ),
			    nl))
	    )),
	% Weiter 
	next_line(Node,Node1),
	show_block_lines(Node1).
% Abschluss
show_block_lines(_).


% next_line/2,  first_proof_line/2 are also defined in block.p.
% they are defined here too since they need to access the proof/3
% local to proofout and not proof/3 local to block.

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

/* Beweisausgabe mit Tex */

view_proof(Job) :- put_proof(view_tmp),
	get_proof(Job),
	proof([Pf,global],goal,_),
	proof([Pf,global],system,S),
	default_transformation(S,Transformation),
	transform_proof(Transformation),
	proof([Pf1,global],goal,_),
	proof([Pf1,global],system,S1), % Kann sich ja geaendert haben!
	(member(ilf, S1) ->
		once(ilf_state(out_mode, Mode) ; Mode=latex),
		proof(Mode)
		;
		ilf_warning("Proof %w is apparently not a block proof.",[Job])
	),get_proof(view_tmp),!.

/*************************************************************************/
/* Beweisausgabe in CSV-Datenbank mit Trennzeichen # 			 */

list_p3(Stream,lisp) :- printf(Stream,"(\n",[]),fail.
list_p3(Stream,Format) :- list_p3_lines(Stream,Format),fail.
list_p3(Stream,lisp) :- printf(Stream,")\n",[]),fail.
list_p3(_,_).

list_p3_lines(Stream,lisp) :- !,
	call(proof(H,K,V),p3),
	export_string(lisp,proof(H,K,V),S),
	printf(Stream,"%w\n",[S]),
	fail.
list_p3_lines(Stream,csv(Format)) :- !,
	standard_keys(L),
	print_csv_line(Stream,[block,line|L]),
	csv_block_lines(Stream,L,Format).
list_p3_lines(Stream,Format) :- call(proof(H,K,V),p3),
	export_string(Format,proof(H,K,V),S),
	printf(Stream,"%w.\n",[S]),
	fail.

standard_keys([contents,status,control,predecessors,name,declaration]).

print_csv_line(S,[X]) :- printf(S,"%Dw\n",[X]),!.
print_csv_line(S,[X|L]) :- printf(S,"%Dw#",[X]),
	print_csv_line(S,L),!.

csv_block_lines(S,H,Format) :- call(proof([Pf,global],goal,G),p3),
	export_string(Format,Pf,HS),
	export_string(Format,G,GS),
	(call(proof([Pf,global],system,Sys),p3),
	export_string(Format,Sys,SysS)
	;
	SysS=""),
	add_space([HS,global,GS,"",SysS],[block,line|H],SL),
	print_csv_line(S,SL),!,
	csv_block_proof(S,H,Format,Pf),!.

add_space([E|LL],[_|HL],[E|SL]) :- add_space(LL,HL,SL),!.
add_space([],[],[]).
add_space([],[_|HL],[""|SL]) :- add_space([],HL,SL),!.

csv_block_proof(S,H,Format,Pf) :- call(proof([Pf,N],predecessors,[]),p3),
	csv_one_line(S,H,Format,[Pf,N]),!.

csv_one_line(S,Head,Format,H) :- call(proof(H,status,subproof(Pf))),
	csv_block_proof(S,Head,Format,Pf),fail.
csv_one_line(S,Head,Format,H) :- 
	once((
		block_item(H,Head,Format,L),
		H=[H1,H2],
		export_string(Format,H1,SH1),
		export_string(Format,H2,SH2),
		print_csv_line(S,[SH1,SH2|L])
	)),fail.
csv_one_line(S,Head,Format,H) :- call(proof(H1,predecessors,[H])),
	!,csv_one_line(S,Head,Format,H1),!.
csv_one_line(_,_,_,_).

block_item(H,[K|Head],Format,[IS|L]) :- call(proof(H,K,I),p3),
	export_string(Format,I,IS),!,
	block_item(H,Head,Format,L),!.
block_item(H,[_|Head],Format,[""|L]) :- block_item(H,Head,Format,L),!.
block_item(_,[],_,[]).

export_string(ilf,H,S) :- termcanonic2string(H,S),!.
export_string(lisp,X,S) :- var(X),!,get_var_info(X,name,SS),
	concat_string(["?X",SS],S),!.
export_string(_,X,S) :- var(X),!,get_var_info(X,name,S),!.
export_string(prolog,all(X,H),S) :- get_attribute(X,A),
	get_var_info(X,name,SX),
	export_string(prolog,A,SA),
	export_string(prolog,H,SH),
	concat_string(["all(:(",SX,",",SA,"),",SH,")"],S),!.
export_string(prolog,ex(X,H),S) :- get_attribute(X,A),
	get_var_info(X,name,SX),
	export_string(prolog,A,SA),
	export_string(prolog,H,SH),
	concat_string(["ex(:(",SX,",",SA,"),",SH,")"],S),!.
export_string(prolog,[],"[]") :- !.
export_string(prolog,gives(D,T),S) :- D=..[Op|Arg],
	export_string(prolog,T,TS),
	(
	Arg=[],concat_string(["gives(",Op,",",TS,")"],S)
	;
	export_var_l(prolog,Arg,Arg1),
	concat_string(Arg1,Arg1S),
	concat_string(["gives(",Op,"(",Arg1S,"),",TS,")"],S)
	),!.
export_string(prolog,H,S) :- H=..[_],termcanonic2string(H,S),!.
export_string(prolog,H,S) :- H=..[Op|Arg],termcanonic2string(Op,OpS),
	export_string_l(prolog,Arg,ArgS),
	concat_string([OpS,"(",ArgS,")"],S),!.
export_string(lisp,all(X,H),S) :- get_attribute(X,A),
	get_var_info(X,name,SX),
	export_string(lisp,A,SA),
	export_string(lisp,H,SH),
	concat_string(["(|all| (|:| ?X",SX," ",SA,") ",SH,")"],S),!.
export_string(lisp,ex(X,H),S) :- get_attribute(X,A),
	get_var_info(X,name,SX),
	export_string(lisp,A,SA),
	export_string(lisp,H,SH),
	concat_string(["(|ex| (|:| ?X",SX," ",SA,") ",SH,")"],S),!.
export_string(lisp,[],"nil") :- !.
export_string(lisp,gives(D,T),S) :- D=..[Op|Arg],
	export_string(lisp,T,TS),
	(
	Arg=[],concat_string(["(gives ",Op," ",TS,")"],S)
	;
	export_var_l(lisp,Arg,Arg1),
	concat_string(Arg1,Arg1S),
	concat_string(["(gives (",Op," ",Arg1S,") ",TS,")"],S)
	),!.
export_string(lisp,[A|L],S) :- export_string_l(lisp,[A|L],SL),
	concat_string(["(",SL,")"],S),!.
export_string(lisp,H,S) :- atom(H),atom_string(H,SH),
	concat_string(["|",SH,"|"],S),!.
export_string(lisp,S,SS) :- string(S),term_string(S,SS),!.
export_string(lisp,N,NS) :- number(N),number_string(N,NS),!.
export_string(lisp,H,S) :- H=..[Op|Arg],atom_string(Op,OpS),
	export_string_l(lisp,Arg,ArgS),
	concat_string(["(|",OpS,"| ",ArgS,")"],S),!.

export_string_l(Format,[A],S) :- export_string(Format,A,S),!.
export_string_l(lisp,[A|L],S) :- export_string(lisp,A,SA),
	export_string_l(lisp,L,SL),
	concat_string([SA," ",SL],S),!.
export_string_l(Format,[A|L],S) :- export_string(Format,A,SA),
	export_string_l(Format,L,SL),
	concat_string([SA,",",SL],S),!.
export_string_l(_,[],"").

export_var_l(prolog,[X|L],["':'(",SX,",",ST,SC|SL]) :-
	get_attribute(X,T),export_string(prolog,T,ST),
	get_var_info(X,name,SX),
	(L=[],SC=")";SC="),"),
	export_var_l(prolog,L,SL),!.
export_var_l(lisp,[X|L],["(|:| ?X",SX," ",ST,SC|SL]) :-
	get_attribute(X,T),export_string(lisp,T,ST),
	get_var_info(X,name,SX),
	(L=[],SC=")";SC=") "),
	export_var_l(lisp,L,SL),!.
export_var_l(Format,[X|L],S) :- ilf_error("export_var_l: Type for %w not found\n",[X]),
	export_var_l(Format,L,S),!.
export_var_l(_,[],[]).

/* Ende Beweisausgabe in CSV-Datenbank mit Trennzeichen # 			 */

/*************************************************************************/
/* TREE VIEWER */
/*************************************************************************/

/* Anzeige von Beweisen im Standardformat im TreeViewer */

:- import 
	tree_read/1,
	tree_write/1,
	tree_writeq/1,
	tree_send/1
    from treecomm.
/* We don't use TreeViewer
:- dynamic                  % local in "Anzeige von Block-Beweisen im
	                    % Standardformat im TreeViewer"
	hidden/1,
	last_color/1,
	written/1,
	pf_send_tv/1,
	pf_unsend_tv/3.
*/
show_proof(Job) :-
	ilf_state(treeviewer, on),
	!,
	put_proof(view_tmp),
	get_proof(Job),
	get_flag(toplevel_module,Top),
	tv_the_proof(Top),
	get_proof(view_tmp),!.
show_proof(_) :-
	ilf_warning("Treeviewer is necessary for show_proof/1.", []).

tv_the_proof(Top) :- 
	call((
		proof([Pf,global],goal,_),
		proof([Pf,global],system,S)
	),Top),
	member(ilf,S),!,
	show_block_proof,!.
tv_the_proof(Top) :- 
	call((
		proof([Pf,global],goal,_),
		proof([Pf,global],system,S)
	),Top),
	member(three_tap,S),!,
	show_block_proof,!.
tv_the_proof(Top) :- 
	call((
		proof([Pf,global],goal,_),
		proof([Pf,global],system,S)
	),Top),
	member(hyper,S),!,
	show_block_proof,!.

tv_the_proof(Top) :- 
	call((
		proof([Pf,global],goal,_),
		proof([Pf,global],system,S)
	),Top),
	member(spass,S),!,
	transform_proof(sp2bl),
	show_block_proof,!.
tv_the_proof(Top) :-
	call(retract(proof([J1,global],goal,FF)),Top),
	call(assert(proof([main,global],goal,FF)),Top),
	call(assert(proof([main,main],contents,FF)),Top),
	connect_subproof([main,main],J1),
	tv_proof.

tv_proof :- get_flag(toplevel_module,Top),
	call(proof([main,global],goal,_),Top),!,
	tv_proof1.
tv_proof :- write("Ilf ERROR: No proof loaded in standard format!\n").

tv_proof1 :- tree_write(root([main,main])),fail.
tv_proof1 :- once((
		proof([main,main],contents,F),
		pf_detail_tv([main,main],F),
		retract_all(pf_send_tv(_)),
		retract_all(pf_unsend_tv(_,_,_)),
		assert(pf_send_tv([main,main]))
		)),fail.
tv_proof1 :- proof(Node,contents,F),pf_to_tv(Node,F).
tv_proof1 :- tree_write(call(gatherAll,[main,main])),fail.
tv_proof1 :- tree_write(call(listAll,[main,main])),fail.
tv_proof1 :- tree_write(update),fail.
tv_proof1 :- pf_unsend_tv(P,F,Q),write("Could not display edge "),
	write(P-(Q:F)),nl,fail.
tv_proof1.

pf_to_tv(Node,F) :- (proof(Node,predecessors,Pred);Pred=[]),!,
	pf_to_tv(Node,F,Pred),!,fail.

pf_to_tv(Node1,F,[Node2|Pred]) :- 
	pf_edge_tv1(Node1,F,Node2),pf_to_tv(Node1,F,Pred).
	
pf_edge_tv1(P,F,Q) :- pf_send_tv(Q),!,
	tree_writeq(new_edge(Q,P)),
	(pf_send_tv(P)
	;
	assert(pf_send_tv(P)),
	pf_detail_tv(P,F),
	pf_pending_tv(P)
	),!.
pf_edge_tv1(P,F,Q) :- assert(pf_unsend_tv(P,F,Q)),!.

pf_detail_tv(P,F) :- 
	show_fla(F, FS, text),
	tree_writeq(set_contents(P,FS)),
	(proof_shape(P,S),
	tree_writeq(set_shape(P,S))
	;
	true
	),
	!.

pf_pending_tv(P) :- retract(pf_unsend_tv(P0,F,P)),
	once((
		tree_writeq(new_edge(P,P0)),
		assert(pf_send_tv(P0)),
		pf_detail_tv(P0,F),
		pf_pending_tv(P0)
	)),
	fail.
pf_pending_tv(_).

proof_shape(Node,N) :- current_predicate(user_proof_shape/2),
	user_proof_shape(Node,N),!.
proof_shape(Node,2) :- proof(Node,status,subproof(_)),!.
proof_shape(Node,6) :- proof(Node,status,axiom(_)),!.
proof_shape(Node,1) :- proof(Node,status,assumption(_)),!.


ins_proof(Node) :- 
	proof(Node,status,subproof(SP)),atomic(SP),!,
	term_string(SP,JS),concat_string(["tmp/ilf.",JS,".out"],S),
	get_uih_file(S,File),!,
	(
	exists(File)
		;
	write("Ilf ERROR: File "),write(File),write(" not found!\n"),!,fail
	),!,
	get_flag(toplevel_module,Top),
	call((
		compile(File),
		(
		get_flag(proof/3,visibility,exported)
		;
		export(proof/3)
		)
	),Top),
	(
	get_flag(proof/3,visibility,imported)
	;
	import(from((proof/3),Top))
	),
	compile(File,Top),
	!.
ins_proof([P,H]) :- write("Ilf ERROR: Cannot load subproof in proof "),write(P),
	write(" at line "),write(H),write("!,\n"),!,fail.

connect_subproof(_,SP) :- 
	proof([SP,H],status,subproof(SSP)),
	connect_subproof([SP,H],SSP),
	fail.
connect_subproof(_,SP) :- proof([SP,H],contents,_),
	once((
		(top_retract(proof([SP,H],predecessors,L));L=[]),
		subproof_preds(_,L,L1),
		top_assert(proof([SP,H],predecessors,L1))
	)),
	fail.
connect_subproof([PfHdl,_],SP) :- new_ready(PfHdl),new_ready(SP).

subproof_preds(Node,[],[Node]) :- !.
subproof_preds(Node,L,L1) :- subproof_preds_1(Node,L,L1),!.

subproof_preds_1(Node,[Node1|L],[Node1|L1]) :-
	proof(Node1,_,_),!,
	subproof_preds_1(Node,L,L1),!.
subproof_preds_1(Node,[[Pf,_]|L],[Node1|L1]) :-
	proof(Node1,status,subproof(Pf)),
	subproof_preds_1(Node,L,L1),!.
subproof_preds_1([PfHdl,H],[[Pf,_]|L],[[PfHdl,pf(Pf)]|L1]) :-
	top_assert(proof([PfHdl,pf(Pf)],contents,subproof(Pf))),
	top_assert(proof([PfHdl,pf(Pf)],predecessors,[[PfHdl,H]])),
	subproof_preds_1([PfHdl,H],L,L1),!.
subproof_preds_1(_,[],[]).

new_ready(P) :- 
	get_flag(toplevel_module,Top),
	call(retract_all(proof([P,global],control,ready)),Top),
	call(assert(proof([P,global],control,ready)),Top),!.

expand_proof :-  make_subproof_menu(M),
	menu(_,"Subproof to expand:",M,S,_),
	!,
	ins_proof(S),
	tv_proof1,!.

make_subproof_menu(M) :- bagof(F-"@"-true-Node-"help",
		subproof_item(Node,F),
		M).

subproof_item(Node,F) :- proof(Node,status,subproof(_)),
	proof_leaf(Node),
	proof(Node,contents,F).
	
proof_leaf(Node) :- proof(_,predecessors,L),member(Node,L),!,fail.
proof_leaf(_).

hide_axioms :- proof(Node,status,axiom(_)),
	tree_writeq(call(hideThis,Node)),
	fail.
hide_axioms :- tree_write(update).

draw_axioms :- proof(Node,status,axiom(_)),
	tree_writeq(call(drawThis,Node)),
	fail.
draw_axioms :- tree_write(update).

hide_straights :-
	is_straight(Node),
	tree_writeq(call(hideThis,Node)),
	fail.
hide_straights :- tree_write(update).

draw_straights :- is_straight(Node),
	tree_writeq(call(drawThis,Node)),
	fail.
draw_straights :- tree_write(update).

is_straight(Node) :- proof(Node,contents,_),proof(Node,predecessors,[_]).

expand_prooftree :- tree_get_handle(Node),
	ins_proof(Node),
	tv_proof1,!.
/* Ende graphische Darstellung */

show_block_proof :- put_proof(view_tmp),
	proof([PfHdl,global],goal,G),
	tree_write(root(PfHdl)),
	block_root_shape(RSh),
	tree_write(set_shape(PfHdl,RSh)),
	abolish(last_color/1),
	assert(last_color([0,0,0])),

%	standard_vars(G,GG),
%	short_form(G,GG),
%	var_term_string(GG,GS),
	
	show_fla(G,GS,text),
	
	open(GS,string,str1),         % Laengenbegrenzung fuer Treeviewer
	read_string(str1,"",1000,GS1),
	close(str1),
	
	concat_string(["\"",GS1, "\""],GS2),
	tree_write(set_contents(PfHdl,GS2)),
	proof([PfHdl,H],predecessors,[]),HH=[PfHdl,H],
	show_block_proof(PfHdl,HH,[0,0,0]),
	tree_write(call(listAll,PfHdl)),
	tree_write(call(geometryScale,0:50)),
	tree_write(call(geometryRootRight,[])),
%	tree_write(fill_pulldown(graphic,"Transform",[[noconfirm,"To undo","undo_enable"],[noconfirm,"Undo","undo_show"],[separator],[noconfirm,"Make direct","tvblck(convert_indirect)"],[noconfirm,"No duplicates","tvblck(remove_duplicate)"],[noconfirm,"No trivials","tvblck(remove_trivial_subproofs)"],[noconfirm,"No unused","tvblck(remove_unused)"],[noconfirm,"Move into subproofs","tvblck(move_into_subproof)"],[noconfirm,"Reduce depth",tvblck(reduce_depth)]])),
%	tree_write(fill_pulldown(graphic,"Latex",[[noconfirm,"All","prooftex"],[noconfirm,"This","tex_tv_proof"],[noconfirm,"Explain","explain"]])),
	get_proof(view_tmp),
	!.


block_root_shape(7) :- proof(_,status,unproved),!.
block_root_shape(1) :- proof(_,status,tried),!.
block_root_shape(1) :- proof(_,status,untried),!.
block_root_shape(0).

tvblck(C) :- undo_enable,C,show_block_proof,!.

proof_tex:-hidden_proof,prooftex.

show_block_proof(PfHdl,H,C) :- show_block_node(PfHdl,H,C),fail.
show_block_proof(PfHdl,H,C) :- proof(H1,predecessors,[H]),
	show_block_proof(PfHdl,H1,C).
show_block_proof(_,_,_).

verstecke_subproof:-once(tree_write(get_handle)),
			once(tree_read(X)),
			proof(X,status,subproof(_)),
			assert(hidden(X)),
			tree_write(call(hideBelow,X)),
			tree_write(update).
	verstecke_subproof.

zeige_subproof:-once(tree_write(get_handle)),
			once(tree_read(X)),
			proof(X,status,subproof(_)),
			hidden(X),
			retract(hidden(X)),
			tree_write(call(drawBelow,X)),
			tree_write(update).
	zeige_subproof.



update_latex:-once(hidden_proof),once(tree_write(call(drawAll,[]))),fail.
update_latex:-hidden(X),once(tree_write(call(hideBelow,X))),fail.
update_latex:-tree_write(update).



hidden_proof:-erzeuge_knoten,
		hidden_proof1,
		loesche_knoten.


hidden_proof1:-proof([Pf,N],status,subproof(Pf1)),
			once(hidden_subproof(Pf1,O)),
			once((
			O=ok,
			 (
			 hidden([Pf,N])
			 ;
			 assert(hidden([Pf,N]))
			 )
			;
			 (
			 not(hidden([Pf,N]))
			 ;
			 retract(hidden([Pf,N]))
			 )
			)),
			fail.
hidden_proof1.

hidden_subproof(Pf,O):-once(proof([Pf,N],predecessors,[])),
			teste_knoten([Pf,N],O).
hidden_subproof(_,ok).

teste_knoten([Pf,N],O):-knoten(X,[Pf,N]),
			once(test_fuer_hidden([Pf,N],O2)),
			(not(O2=hidden),
			O=notok
			;
			once(teste_knoten(X,hidden)),
			fail
			).
teste_knoten([_,_],ok).

test_fuer_hidden([Pf,N],A4):-tree_write(get_handlestate([Pf,N])),tree_read(_),tree_read(_),tree_read(_),tree_read(A4),tree_read_weiter.
test_fuer_hidden([_,_],notok).

tree_read_weiter:-tree_read(A),
		(
		A=end
		;
		tree_read_weiter
		).



show_block_node(PfHdl,H,C) :- 
	once((
		tree_write(new_edge(PfHdl,H)),
		proof(H,contents,F),
		
%		standard_vars(F,FF),
%		short_form(F,FF),
%		var_term_string(FF,FS),
		show_fla(F,FS,text),

		open(FS,string,str1),      % Laengenbegrenzung fuer Treeviewer
		read_string(str1,"",1000,FS1),
		close(str1),
	
		concat_string(["\"" , FS1 , "\""],FS2),
		tree_write(set_contents(H,FS2)),
		get_color(C,Cl),
		tree_write(set_color(H,Cl))
	)),fail.
show_block_node(_,H,_) :- 
		proof(H,status,subproof(Pf1)),
		tree_write(set_shape(H,2)),
		(proof([Pf1,HH],predecessors,[]),[Pf1,HH]=H1,
		new_color(C1),
		show_block_proof(H,H1,C1)
		;
		true
		),!.
show_block_node(_,H,_) :- 
	proof(H,status,assumption(_)),
	tree_write(set_shape(H,6)),!.
show_block_node(_,H,_) :- proof(H,status,proved),
	translit(contradiction,Contradiction),
	proof(H,contents,Contradiction),
	tree_write(set_shape(H,3)),!.
show_block_node(_,H,_) :- proof(H,status,proved),
	tree_write(set_shape(H,0)),!.
show_block_node(_,H,_) :- proof(H,status,unproved),
	tree_write(set_shape(H,7)),!.
show_block_node(_,H,_) :- tree_write(set_shape(H,1)).

show_block_node(PfHdl,H,C) :- 
	once((
		tree_write(new_edge(PfHdl,H)),
		proof(H,contents,F),
		
%		standard_vars(F,FF),
%		short_form(F,FF),
%		var_term_string(FF,FS),
		show_fla(F,FS,text),

		open(FS,string,str1),      % Laengenbegrenzung fuer Treeviewer
		read_string(str1,"",1000,FS1),
		close(str1),
	
		concat_string(["\"" , FS1 , "\""],FS2),
		tree_write(set_contents(H,FS2)),
		get_color(C,Cl),
		tree_write(set_color(H,Cl))
	)),fail.
show_block_node(_,H,_) :- 
		proof(H,status,subproof(Pf1)),
		tree_write(set_shape(H,2)),
		(proof([Pf1,HH],predecessors,[]),[Pf1,HH]=H1,
		new_color(C1),
		show_block_proof(H,H1,C1)
		;
		true
		),!.
show_block_node(_,H,_) :- 
	proof(H,status,assumption(_)),
	tree_write(set_shape(H,6)),!.
show_block_node(_,H,_) :- proof(H,status,proved),
	translit(contradiction,Contradiction),
	proof(H,contents,Contradiction),
	tree_write(set_shape(H,3)),!.
show_block_node(_,H,_) :- proof(H,status,proved),
	tree_write(set_shape(H,0)),!.
show_block_node(_,H,_) :- proof(H,status,unproved),
	tree_write(set_shape(H,7)),!.
show_block_node(_,H,_) :- tree_write(set_shape(H,1)).

next_color([R,G,0],[R,G,15]).
next_color([R,0,15],[R,15,0]).
next_color([0,15,15],[15,0,15]).
next_color([15,15,15],[0,0,0]).

get_color([R,G,B],S) :- color_hex_code(R,RS),
	color_hex_code(G,GS),
	color_hex_code(B,BS),
	concat_string(["rgb:", RS, "/", GS, "/", BS],S), !.

color_hex_code(0,"0000").
color_hex_code(15,"ffff").

new_color(C) :- retract(last_color(CL)),
	next_color(CL,C),
	assert(last_color(C)),!.

var_term_string(T,S) :- open("",string,Stream),printf(Stream,"%Dw",[T]),
	get_stream_info(Stream,name,S),
	close(Stream),!.
	
/* Anzeige der logischen Abhaengigkeiten im TreeViewer */


show_block_dependencies :- tree_send(show_block_dependencies_f),!.

show_block_dependencies(F) :- tell(F),
	write("/ Input File for TreeViewer Ver. 1.2 or later /\n"),
	write("/* Generated by ILF "),
	date(Date),
	write(Date),
	show_block_dependencies_f,
	told,!.

show_block_dependencies_f :-
	write_dep_root_f,
	write_dep_graph_f,
	write_colors_f,
	write(call(gatherAll,proof)),nl,
	write(call(listAll,proof)),nl,
	write(update),nl,
	!.

write_dep_root_f :- 
		write(root(proof)),nl,
		write(set_info(proof,proof)),nl,
		write(new_edge(proof,axioms)),nl,
		write(set_info(axioms,axioms)),nl,
		!.

write_dep_graph_f :- retract_all(written(_)),
	retract_all(last_color(_)),
	assert(last_color([0,0,0])),
	fail.
write_dep_graph_f :- proof([Pf,global],goal,H),
	generate_var_name_struct(H,[],V),
	encode(HS,H,V),
	writeq(set_contents(proof,HS)),nl,
	proof([Pf,_],status,subproof(PP)),
	proof([PP,N],predecessors,[]),
	write_dep_graph_f([PP,N]),!.


write_dep_graph_f(H) :- written(H),!.
write_dep_graph_f(H) :- 
		proof(H,control,rule(_,L)),
		write_dep_graph_f_l(L),
		write_dep_graph_f(H,L),
		proof(H,contents,F),
		generate_var_name_struct(F,[],V),
		encode(FS,F,V),
		writeq(set_contents(H,FS)),nl,
		(proof(H,status,subproof(_)) -> 
		    writeq(set_shape(H,2)), nl
		; true
	        ),
		(translit(contradiction,F) ->
		    writeq(set_shape(H,3)),nl
		; true),
		assert(written(H)),
		(next_line(H,H1) -> 
		    write_dep_graph_f(H1)
		; true),
		!.
write_dep_graph_f(H) :- 
		proof(H,control,axiom(_)),
		proof(H,contents,F),
		generate_var_name_struct(F,[],V),
		encode(FS,F,V),
		writeq(new_edge(axioms,H)),nl,
		writeq(set_contents(H,FS)),nl,
		writeq(set_shape(H,6)),nl,
		assert(written(H)),
		!.
write_dep_graph_f(H) :- proof(H,status,assumption(_)),
		proof(H,contents,F),
		generate_var_name_struct(F,[],V),
		encode(FS,F,V),
		writeq(new_edge(proof,H)),nl,
		writeq(set_contents(H,FS)),nl,
		writeq(set_shape(H,1)),nl,
		assert(written(H)),
		next_line(H,H1),
		write_dep_graph_f(H1),!.
write_dep_graph_f(H) :- told,
	ilf_serv_error((
		write("ILF ERROR: Writing dependency graph failed at "),
		write(H),nl
		)),!,fail.

write_dep_graph_f_l([H|L]) :- write_dep_graph_f(H),write_dep_graph_f_l(L),!.
write_dep_graph_f_l([]).

write_dep_graph_f(H,[H1|L]) :- writeq(new_edge(H1,H)),nl,
	write_dep_graph_f(H,L),!.
write_dep_graph_f(_,[]).

write_colors_f :- proof([Pf,global],goal,_),
	proof([Pf,_],status,subproof(Pf1)),
	write_colors_f(Pf1).

write_colors_f(Pf1) :- new_color(C),get_color(C,Cl),
	proof([Pf1,N],predecessors,[]),
	write_colors_f([Pf1,N],Cl),!.


/* Wieder reinnehmen, wenn TV unquoted colors versteht
*
* write_colors_f(H,Cl) :- 
*	writeq(set_color(H,Cl)),nl,
*	fail.
*/


write_colors_f(H,Cl) :- 
	once((
		write("set_color("),
		writeq(H),
		write(","),
		write(Cl),
		write(")\n")
	)),
	fail.

write_colors_f(H,_C) :- proof(H,status,subproof(Pf)),
	write_colors_f(Pf),fail.
write_colors_f(H,C) :- proof(H1,predecessors,[H]),!,
	write_colors_f(H1,C),!.
write_colors_f(_,_).


/* Ende Anzeige der logischen Abhaengigkeiten im TreeViewer */

