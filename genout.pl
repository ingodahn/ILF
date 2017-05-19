/*
 * @(#)genout.pl	1.9 (02/10/98)
 *
 * "generische" Ausgaberoutinen
 * 
 * Ein "Ausgabe-Modus" ist ein Term, das eine eine bestimmte Art und
 * Weise der Ausgabe bezeichnet. Im Moment gibt es die Modi latex, html
 * und text.
 * genout stellt "abstracte"-Ausgabepraedikate (z.B. mode_specific/2, 
 * show_fla_body/3) bereit, auf die proofout, thout (und ggf. andere)
 * zugreifen koennen. Dabei werden die Modi erst dann geladen, wenn
 * zum ersten Mal auf sie zugegriffen wird.
 */

/* Hilfsmodule zum Abspeichern von tex_op/4. */

:- module(genout_user_texop).
:- export tex_op/4.

:- module(genout_default_texop).
:- export tex_op/4.

/* Hier beginnt der eigentliche genout-Modul. */

:- module(genout).

/* Fuer die Benutzung durch ILF */

:- export
	close_out_mode/1,
	close_out_modes/0,
	dict/0,
	dict/1,
	open_out_mode/1,
	open_out_modes/0,
	printtex/0,
	printtex/1,
	reload_default_texop/0,
	reload_default_texop/1,
	reload_texop/0,
	reload_texop/1,
	show_fla/3,
	viewtex/0,
	viewtex/1,
	viewhtml/0,
	viewhtml/1.

:- export
	mode_specific/2,
	print_text/3.
	
:- begin_module(genout).

:- import ilfsys.

:- import
	body_list/2
		from tools.

:- import
	pred_needs/2
		from outtools.

:- dynamic
	call_mode/1,
	call_tool/1,
	call_tool/2,
	temp_out_mode/1.

genout_top :-
	reload_default_texop,
	get_right_file("even.texop.pl",F),
	call(compile(F))@genout_user_texop,
	/*
	reload_texop,
	*/
	compile_mode_specific.

/* out_mode/1 gelingt fuer alle bekannten Output-Modi. Bekannt sind 
     - alle Modi, die durch gen_out_mode/1 gegeben sind
     - alle Modi, die der Nutzer durch open_out_mode/1 explizit geoeffnet
       und nicht durch close_out_mode/1 wieder geschlossen hat. */

out_mode(Mode) :- gen_out_mode(Mode).
out_mode(Mode) :- temp_out_mode(Mode).

gen_out_mode(dyna).
gen_out_mode(html).
gen_out_mode(latex).
gen_out_mode(mca).
gen_out_mode(text).
gen_out_mode(th_ilf).

/* Liste der von einem Modus bereitzustellenden Praedikate.
   outtools sollte fuer jedes dieser Praedikate eine Default-Implementation
   enthalten.   */

mode_needs(clear_varnumbers/0).
mode_needs(clearall/0).
mode_needs(default_ruleop/1).
mode_needs(end_par/1).
mode_needs(firstup/2).
mode_needs(hide_varnames/0).
mode_needs(ini_varnames/0).
mode_needs(open_file/2).
mode_needs(open_include/3).
mode_needs(postprocess_file/3).
mode_needs(postprocess_file/5).
mode_needs(print_constants/2).
mode_needs(print_formula/4).
mode_needs(print_formula/5).
mode_needs(print_known_theory/2).
mode_needs(print_proof_begin/1).
mode_needs(print_proof_begin/2).
mode_needs(print_qed/1).
mode_needs(print_ref/3).
mode_needs(print_ref/4).
mode_needs(print_string/2).
mode_needs(print_string/3).
mode_needs(print_string_ref/3).
mode_needs(print_text/3).
mode_needs(print_th_axiom/3).
mode_needs(print_th_domain/4).
mode_needs(print_th_func_declaration/3).
mode_needs(print_th_pred_declaration/2).
mode_needs(print_th_type_declaration/3).
mode_needs(print_theorem/5).
mode_needs(print_theorem_string/5).
mode_needs(print_var_types/1).
mode_needs(print_we/1).
mode_needs(print_we/2).
mode_needs(ruleop/1).
mode_needs(show_fla/2).
mode_needs(technical_header/1).
mode_needs(technical_trailer/1).
mode_needs(title/3).
mode_needs(view/0).
mode_needs(view/1).


/* Laden/Entladen der Modi */

for_all_modes(Pred) :-
	Pred =.. PredList,
	append(PredList, [Mode], CallList),
	Call =.. CallList,
	out_mode(Mode),
	once(Call),
	fail.
for_all_modes(_).

open_out_mode(Mode) :-
	open_out_mode0(Mode),
	compile_mode_specific,
	!.

open_out_mode0(Mode) :-
	(
		current_module(outtools)
		;
		open_right_module("pl/outtools.pl")
	),
	(
		gen_out_mode(Mode) 
		; 
		assert(temp_out_mode(Mode)),
		ilf_warning("%w is an unsupported output mode.", [Mode])
	),
	concat_string(["pl/", Mode, ".pl"], PlFile),
	/*
	open_right_module(PlFile),
	*/
	get_right_file(PlFile,ModeFile),
	compile(ModeFile),
	(
		current_module(Mode)
		;
		ilf_error("compiling %DQw has not created a module %w\n",
				[PlFile, Mode]),
		create_module(Mode)
	),
	compile_call_(Mode),
	!.

open_out_modes :- 
	for_all_modes(open_out_mode),
	compile_mode_specific,
	!.

close_out_mode(Mode) :-
	close_out_mode0(Mode),
	compile_mode_specific,
	!.

close_out_mode0(Mode) :-
	erase_module(Mode),
	(gen_out_mode(Mode) ; retract_all(temp_out_mode(Mode))),
	!.

close_out_modes :- for_all_modes(close_out_mode).

compile_mode_specific :-
	bagof(Call, get_mode_specific(Call), Calls),
	/*
	printf("%w",[Calls]),
	*/
	compile_term(Calls).

get_mode_specific(Call) :-
	out_mode(Mode),
	get_mode_specific0(Mode, Call).
get_mode_specific((
	mode_specific(Call, Unknown) :-
		ilf_error("%Dw: unknown output mode for '%Dw'.\n", 
			  [Unknown, Call]),
		!,
		fail
  )).

get_mode_specific0(Mode, (
	mode_specific(Call, Mode) :- 
		!, 
		Call_
  )) :-
	current_module(Mode),
	!,
	concat_atom(['call_', Mode], CallPred),
	Call_=..[CallPred, Call].
get_mode_specific0(Mode, (
	mode_specific(Call, Mode) :-
		!,
		open_out_mode(Mode),
		Call_
  )) :-
	concat_atom(['call_', Mode], CallPred),
	Call_=..[CallPred, Call],
	compile_term([Call_ :- fail]).

/* Erzeugen des call_mode/1 Praedikats, das von mode_specific aufgerufen wird.
   search_preds/1 findet alle notwendigen Praedikate (was notwendig ist, wird
   durch mode_needs/1 und pred_needs/2 bestimmt) und erzeugt einen Fakt fuer
     - call_mode/1, wenn das Praedikat im Modus-eigenen Modul definiert ist
     - call_tool/1, wenn das Praedikat nicht im Modus-eigenen Modul (folglich
       also in outtools) definert ist und nicht als tool implementiert ist
     - call_tool/2, wenn das Praedikat nicht im Modus-eigenen Modul (folglich
       also in outtools) definert ist und als tool implementiert ist (das
       zweite Argument ist dann der Name des Tool-Body)
   Diese Informationen werden ausgewertet und call_mode wird dementsprechend
   als call(..., mode) oder call(..., outtools) compiliert. */

compile_call_(Mode) :-
	current_module(Mode),
	!,
	search_preds(Mode),
	concat_atom(['call_', Mode], CallPred),
	bagof(Call, call_(Mode, CallPred, Call), Calls),
	compile_term(Calls).
compile_call_(_).

call_(Mode, CallPred, (Call_:-!,call(BodyCall,outtools))) :-
	call_tool(Pred/N, BodyPred/_),
	once((
		length(Args, N),
		Call=..[Pred|Args],
		append(Args, [Mode], BodyArgs),
		BodyCall=..[BodyPred|BodyArgs],
		Call_=..[CallPred, Call]
	)).
call_(_, CallPred, Call_) :-
	call_tool(Pred),
	construct_call_(outtools, CallPred, Pred, Call_).
call_(Mode, CallPred, Call_) :-
	call_mode(Pred),
	construct_call_(Mode, CallPred, Pred, Call_).
call_(Mode, CallPred, (Call_:-!,Warning,call(Call,Mode))) :-
	Warning=ilf_warning("??? %Dw for mode %Dw", [Call, Mode]),
	Call_=..[CallPred, Call].

construct_call_(Module, CallPred, Pred/N, (Call_:-!,call(Call,Module))) :-
	length(Args, N),
	Call=..[Pred|Args],
	Call_=..[CallPred, Call],
	!.
	
construct_tool_call_(Mode, CallPred, Pred/N, (Call_:-!,call(Call,outtools))) :-
	N1 is N-1,
	length(Args1, N1),
	append(Args1, Mode, Args),
	Call=..[Pred, Args],
	Call_=..[CallPred, Call],
	!.
	
search_preds(_) :-
	once((
		retract_all(call_mode(_)),
		retract_all(call_tool(_)),
		retract_all(call_tool(_, _))
	)),
	fail.
search_preds(Mode) :-
	mode_needs(Pred),
	search_pred(Pred, Mode),
	fail.
search_preds(Mode) :-
	call((
		current_predicate(Pred),
		get_flag(Pred, definition_module, outtools)
	), Mode),
	pred_needs(Pred, Pred1),
	search_pred(Pred1, Mode),
	fail.
search_preds(_).

search_pred(Pred, _) :- call_mode(Pred), !.
search_pred(Pred, _) :- call_tool(Pred), !.
search_pred(Pred, _) :- call_tool(Pred, _), !.
search_pred(texop/3, Mode) :-
	compile_texop(user, Mode),
	assert(call_mode(texop/3)),
	!.
search_pred(default_texop/3, Mode) :-
	compile_texop(default, Mode),
	assert(call_mode(default_texop/3)),
	!.
search_pred(ruleop/1, Mode) :-
	compile_ruleop(user, Mode),
	assert(call_mode(ruleop/1)),
	!.
search_pred(default_ruleop/1, Mode) :-
	compile_ruleop(default, Mode),
	assert(call_mode(default_ruleop/1)),
	!.
search_pred(Pred, Mode) :-
	pred_needs(Pred, Pred1),
	search_pred(Pred1, Mode),
	fail.
search_pred(Pred, Mode) :-
	call((
		current_predicate(Pred),
		(
			get_flag(Pred, definition_module, outtools)
			;
			get_flag(Pred, definition_module, Mode)
			;
			not get_flag(Pred, visibility, global)
		)
	), Mode),
	assert(call_mode(Pred)),
	!.
search_pred(Pred, _) :-
	call((
		get_flag(Pred, tool, on), 
		tool_body(Pred, BodyPred, outtools)
	), outtools),
	assert(call_tool(Pred, BodyPred)),
	!.
search_pred(Pred, _) :-
	assert(call_tool(Pred)),
	!.

/* Nutzerkommandos */

dict :- dict(latex).
dict(Mode) :- mode_specific(dict, Mode).
view(Mode) :- mode_specific(view, Mode).
view(Mode, File) :- mode_specific(view(File), Mode).
viewtex :- mode_specific(view, latex).
viewtex(File) :- mode_specific(view(File), latex).
viewhtml :- mode_specific(view, html).
viewhtml(File) :- mode_specific(view(File), html).

/* Gibt einen ueber ilf_state definierten Text aus.
   Der Modus muss ein Praedikat print_text/3 bereitstellen.
   Das Label wird auch dem Modus uebergeben, um ihm eine Sonderbehandlung
   fuer bestimmte Label (z. B. abstract) zu gestatten. Der Modus koennte
   z.B. auch entscheiden den Text nicht auszugeben, wenn er nur "" ist,
   oder er einem ueber Modus-spezifische Mittel (z.B. texop) definierten Text
   den Vorzug geben. */

print_text(_, _, Mode) :-
	once(mode_specific(clear_varnumbers, Mode)),
	fail.
print_text(Label, Stream, Mode) :-
	IlfState =.. [Label, Mode],
	ilf_state(IlfState, Text),
	mode_specific(print_text(Label, Stream, Text), Mode),
	!.
print_text(Label, Stream, Mode) :-
	ilf_state(Label, Text),
	mode_specific(print_text(Label, Stream, Text), Mode),
	!.
print_text(Label, Stream, Mode) :-
	mode_specific(print_text(Label, Stream, ""), Mode),
	!.

/* Umwandlung einer Formel in einen String. Dazu wird nach Herstellung
   der "short form" show_fla/2 des entsprechenden Modus aufgerufen.
   Um die "short form" herzustellen, wird das im ilf_state short_form
   angegebene Praedikat oder short_form/2 aus thman benutzt. */

show_fla(Formula, String, Mode) :- 
	mode_specific(show_fla(Formula, String), Mode).

/* {rule,tex,html,...}ops

   In genout liegen die vom Nutzer zu Beginn (oder per reload_texop)
   eingelesenen tex_op/4. Daraus werden (beim Start des Modus und nach
   jedem reload_texop) ruleop/1 und texop/3 in den einzelnen Modi erzeugt.
   Die Default-texops sind als default_texop/3 in jedem Modus definiert.
   Der Zugriff erfolgt ueber tex_op/3, op_texop/4 und try_texop/3 in
   outtools. */

texop_type(default, genout_default_texop, default_texop, default_ruleop).
texop_type(user, genout_user_texop, texop, ruleop).

/* (Nach)Laden von tex_op/4 aus .ilf(e)rc bzw. aus dem als Parameter
   uebergebenen Filenamen. */
 
reload_texop :-
	reload_texop0("", user).
 
reload_texop(FileName) :-
	reload_texop(FileName, user).

reload_default_texop :-
	get_right_file("default.texop.pl", FileName),
	reload_default_texop(FileName).

reload_default_texop(FileName) :-
	reload_texop(FileName, default).

reload_texop(FileName,TexopType) :- 
	texop_type(default, Module, _, _),
	call(compile(FileName)@Module).
/*
reload_texop(FileName, TexopType) :-
	concat_string([" -i ", FileName], Arg),
	reload_texop0(Arg, TexopType).
*/
reload_texop0(Arg, TexopType) :-
	get_right_file("bin/ilf", Ilf),
	get_uih_file("tmp/texop.pl", TexopFile),
	concat_string([Ilf, Arg, " -texop ", TexopFile], Cmd),
	sh(Cmd),
	load_texop(TexopType, TexopFile),
	compile_texop(TexopType),
	!.

load_texop :-
	get_uih_file("tmp/texop.pl", TexopFile),
	load_texop(user, TexopFile).

load_texop(TexopType, TexopFile) :-
	exists(TexopFile),
	!,
	texop_type(TexopType, Module, _, _),
	get_flag(variable_names, VariableNames),
	set_flag(variable_names, on),
	call(
		(
			compile_term(tex_op(_, _, _, _) :- fail),
			compile(TexopFile)
		),
		Module
	),
	set_flag(variable_names, VariableNames).
load_texop(_, TexopFile) :-
	ilf_error("%s does not exist.", [TexopFile]).
 
/* Erzeugen von texop/3 und ruleop/3 fuer die einzelnen Modi mit
   eingeschaltetem occur-Check. */

compile_texop(TexopType) :-
	for_all_modes(compile_texop(TexopType)),
	for_all_modes(compile_ruleop(TexopType)).

compile_texop(_, Mode) :-
	not (current_module(Mode)),
	!.
compile_texop(TexopType, Mode) :-
	texop_type(TexopType, TexopModule, TexopPred, _),
	%(current_predicate(tex_op/4) -> abolish(tex_op/4) ; true),
	% (import tex_op/4 from TexopModule),
	bagof(Texop, not_a_ruleop(TexopModule,TexopPred, Mode, Texop), Texops), 
	!,
	/* No longer available in Eclipse
	get_flag(occur_check, Occur),
	set_flag(occur_check, on),
	*/
	call(compile_term(Texops), Mode).
	/* Resetting occur check no longer available in Eclipse
	set_flag(occur_check, Occur).
	*/
compile_texop(TexopType, Mode) :-
	texop_type(TexopType, _, TexopPred, _),
	Texop =.. [TexopPred, _, _, _],
	call(compile_term(Texop :- fail), Mode).
 
not_a_ruleop(TexopModule,Pred, Mode, Texop) :-
	TexopModule:tex_op(Mode, Asso, Prec, Rule),
	Asso \= rule,
	check_texop(Mode, Asso, Prec, Rule),
	Texop =.. [Pred, Asso, Prec, Rule].

check_texop(_, Asso, _, Rule) :-
	xfy(Asso),
	!, 
	check_string(Asso, Rule).
check_texop(_, _, _, _).

xfy(xfy).  xfy(yfx).  xfy(xfx).
xfy(fx).   xfy(fy).
xfy(xf).   xfy(yf).

check_string(_, (_ :- text(String))) :- string(String), !.
check_string(_, (_ :- String)) :- string(String), !.
check_string(Asso, Texop) :-
	ilf_warning("%Qw: invalid texop for associativity %w", [Texop, Asso]),
	!,
	fail.

compile_ruleop(_, Mode) :-
	not (current_module(Mode)),
	!.
compile_ruleop(TexopType, Mode) :-
	texop_type(TexopType, TexopModule, _, RuleopPred),
	% (current_predicate(tex_op/4) -> abolish(tex_op/4) ; true),
	% (import tex_op/4 from TexopModule),
	bagof(Rule, Prec^(TexopModule:tex_op(Mode, rule, Prec, Rule)), TexopRules),
	!,
	transform_ruleop(RuleopPred, TexopRules, Rules),
	/* No longer available in Eclipse
	get_flag(occur_check, Occur),
	set_flag(occur_check, on),
	*/
	call(compile_term(Rules), Mode).
	/* resetting occur check no longer available in Eclipse
	set_flag(occur_check, Occur).
	*/
compile_ruleop(TexopType, Mode) :-
	texop_type(TexopType, _, _, RuleopPred),
	Ruleop =.. [RuleopPred, _],
	call(compile_term(Ruleop :- fail), Mode).
 
transform_ruleop(_, [], []).
transform_ruleop(RuleopPred, [Var|TexopRules], Rules) :-
	var(Var),
	ilf_warning("%Dw is a variable in %Dw", [Var, tex_op(rule, _, Var)]),
	!,
	transform_ruleop(RuleopPred, TexopRules, Rules).
transform_ruleop(RuleopPred, [Rule|TexopRules], [ruleop(Rule)|Rules]) :-
	length(Rule, _),
	!,
	transform_ruleop(RuleopPred, TexopRules, Rules).
transform_ruleop(RuleopPred, [Rule:-RuleListComma|TexopRules],
		 [Ruleop|Rules]) :-
	body_list(RuleListComma, RuleList),
	Ruleop =.. [RuleopPred, [control(Rule)|RuleList]],
	!,
	transform_ruleop(RuleopPred, TexopRules, Rules).
transform_ruleop(RuleopPred, [RuleLComma|TexopRules], [Ruleop|Rules]) :-
	body_list(RuleLComma, RuleL),
	Ruleop =.. [RuleopPred, RuleL],
	!,
	transform_ruleop(RuleopPred, TexopRules, Rules).

:- genout_top.
