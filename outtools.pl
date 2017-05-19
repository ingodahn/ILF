/*
 * @(#)outtools.pl	1.27 (02/25/98)
 *
 * Tool-Sammlung fuer die Ausgabe-Modi
 * 
 * Ein "Ausgabe-Modus" ist ein Term, das eine eine bestimmte Art und
 * Weise der Ausgabe bezeichnet. Im Moment gibt es die Modi latex, html
 * und text.
 * Dieser Modul dient als "Werkzeugkasten" zur Implementierung der 
 * konkreten Modi. genout verwaltet eine Liste von Praedikaten, die 
 * ein Modus zur Verfuegung stellen muss. Beim Laden eines Modus wird
 * ueberprueft, ob diese Praedikate dort bereits existieren, andernfalls
 * werden sie aus outtools importiert. 
 * Fast alle Praedikate hier sind als Tools implementiert, wodurch sie auf 
 * einfache Art ueber den Modus (=Module aus dem sie aufgerufen wurden)
 * informiert sind, in dem sie arbeiten.
 */

:- module(outtools).

/* Fuer die Benutzung durch ILF */

:- export
	pred_needs/2.
	
/* Nur fuer die Benutzung durch die Modi: */

:- export
	append_punct/3,
	apply_texop/2,
	apply_texop0/2,
	apply_texop0_list/3,
	clearall/0,
	clear_varnumbers/0,
	default_ruleop/1,
	default_texop/3,
	end_par/1,
	find_file/3,
	firstup/2,
	get_used_var_types/1,
	hide_varnames/0,
	ini_varnames/0,
	make_short_form/2,
	make_varname/3,
	math/2,
	new_typed_name/6,
	new_varname/4,
	open_file/2,
	open_include/3,
	postprocess_file/3,
	postprocess_file/5,
	print_formula/4,
	print_formula/5,
	print_string/2,
	print_string/3,
	print_string_ref/3,
	print_th_axiom/3,
	print_th_func_declaration/3,
	print_th_domain/3,
	print_th_domain/4,
	print_th_pred_declaration/2,
	print_th_type_declaration/3,
	print_theorem/5,
	print_theorem_string/5,
	print_text/3,
	print_text0/3,
	print_var_types/1,
	print_var_types/2,
	show_fla/2,
	show_fla/4,
	show_fla0/2,
	show_fla_list/5,
	show_fla0_list/3,
	show_item/3,
	show_type/2,
	tex_op/3,
	try_texop/3,
	varname_type_thman/2,
	view/0, 
	view/1, 
	write_ref_file/3.

:- import mktemp/2 from tools.

:- import get_right_file/2 from ilfsys.

:- tool(apply_texop/2, apply_texop_body/3).
:- tool(apply_texop0/2, apply_texop0_body/3).
:- tool(apply_texop0_list/3, apply_texop0_list_body/4).
:- tool(get_used_var_types/1, get_used_var_types_body/2).
:- tool(new_typed_name/6, new_typed_name_body/7).
:- tool(new_varname/4, new_varname_body/5).
:- tool(open_file/2, open_file_body/3).
:- tool(postprocess_file/3, postprocess_file_body/4).
:- tool(postprocess_file/5, postprocess_file_body/6).
:- tool(print_formula/4, print_formula_body/5).
:- tool(print_formula/5, print_formula_body/6).
:- tool(print_text/3, print_text_body/4).
:- tool(print_text0/3, print_text0_body/4).
:- tool(print_th_axiom/3, print_th_axiom_body/4).
:- tool(print_th_domain/4, print_th_domain_body/5).
:- tool(print_theorem/5, print_theorem_body/6).
:- tool(print_theorem_string/5, print_theorem_string_body/6).
:- tool(print_var_types/1, print_var_types_body/2).
:- tool(show_fla/2, show_fla_body/3).
:- tool(show_fla0/2, show_fla0_body/3).
:- tool(show_fla/4, show_fla_body/5).
:- tool(show_fla_list/5, show_fla_list_body/6).
:- tool(show_fla0_list/3, show_fla0_list_body/4).
:- tool(show_item/3, show_item_body/4).
:- tool(show_type/2, show_type_body/3).
:- tool(tex_op/3, tex_op_body/4).
:- tool(try_texop/3, try_texop_body/4).
:- tool(view/0, view_body/1).
:- tool(view/1, view_body/2).

:- begin_module(outtools).

:- lib(numbervars).
numbervars(X) :- numbervars(X, 0, _).

:- import 
	ilf_state/2,
	ilf_state/3
	from ilfsys.

:- import
	mode_specific/2
		from genout.

:- import
	get_attribute/2,
	contract_abbrevs/2,
	var_has_typterm/2
		from thman.

:- import	
	list_body/2,
	term2string/2
		from tools.


:- import
	show_rule_list/3,
	show_rule_script/3
		from proofout.

:- dynamic
	default_variable_name/1,
	hidden_used_var/3,
	last_varnumber/2, 
	subtype/3,
	type_varname_cache/5,
	used_var/3.

:- make_local_array(n).

outtools_top.

pred_needs(apply_texop/2, apply_texop0/2).

pred_needs(apply_texop0/2, concat_fla/2).
pred_needs(apply_texop0/2, show_fla/4).

pred_needs(apply_texop0_list/3, show_fla_list/5).

pred_needs(get_used_var_types/1, show_type/2).

pred_needs(new_varname/4, concat_fla/2).
pred_needs(new_varname/4, make_varname/3).
pred_needs(new_varname/4, new_typed_name/6).

pred_needs(open_file/2, file_extension/1).

pred_needs(postprocess_file/3, postprocess_file/5).

pred_needs(postprocess_file/5, write_ref_file/3).

pred_needs(print_th_domain/4, print_th_domain/3).

pred_needs(print_theorem/5, append_punct/3).
pred_needs(print_theorem/5, print_theorem_string/5).
pred_needs(print_theorem/5, show_fla/2).

pred_needs(print_text/3, print_text0/3).
pred_needs(print_text/3, show_item/3).

pred_needs(print_text0/3, end_par/1).

pred_needs(print_var_types/1, print_var_types/2).
pred_needs(print_var_types/1, get_used_var_types/1).

pred_needs(show_fla/2, clear_varnumbers/0).
pred_needs(show_fla/2, concat_fla/2).
pred_needs(show_fla/2, math/2).
pred_needs(show_fla/2, show_fla0/2).

pred_needs(show_fla/4, arg_sep/1).
pred_needs(show_fla/4, brackets/2).
pred_needs(show_fla/4, concat_fla/2).
pred_needs(show_fla/4, default_texop/3).
pred_needs(show_fla/4, list_brackets/2).
pred_needs(show_fla/4, new_varname/4).
pred_needs(show_fla/4, no_underscore/2).
pred_needs(show_fla/4, scope_brackets/2).
pred_needs(show_fla/4, texop/3).
pred_needs(show_fla/4, text/2).

pred_needs(show_fla0/2, apply_texop0/2).

pred_needs(show_fla_list/5, concat_fla/2).
pred_needs(show_fla_list/5, show_fla/4).

pred_needs(show_fla0_list/3, apply_texop0_list/3).

pred_needs(show_item/3, tex_op/3).

pred_needs(show_type/2, concat_fla/2).
pred_needs(show_type/2, math/2).
pred_needs(show_type/2, no_underscore/2).
pred_needs(show_type/2, tex_op/3).

pred_needs(tex_op/3, try_texop/3).

pred_needs(try_texop/3, texop/3).
pred_needs(try_texop/3, default_texop/3).

pred_needs(view/0, view/1).

/* Files */

/* Behandlung von uebergebenen Filenamen: Absolute Filenamen bleiben erhalten,
   relative Filenamen werden beim Anlegen (base_path/3) bzgl. $USERILFHOME/tmp
   interpretiert, beim Lesen (find_file/3) werden sie zunaechst bzgl.
   $USERILFHOME/tmp, dann bzgl. des aktuellen Directory gesucht.
   Zurueckgegeben wird im dritten Argument immer ein Pfad ohne Extension. */
 
base_path(FileName, Ext, Path) :-
	term2string(FileName, FileNameS1),
	tilde_expansion(FileNameS1, FileNameS),
	once(basename(FileNameS, Ext, BaseName)),
	uih_path(BaseName, Path).
 
basename(FileName, Ext, BaseName) :-
	append_strings(BaseName, Ext, FileName),
	!.
basename(FileName, _, FileName).
basename(FileName, _, BaseName) :-
	string_length(FileName, L),
	substring(FileName, Pos, 1, "."),
	(L1 is L - Pos),
	(Pos1 is Pos+1),
	substring(FileName, Pos1, L1, Ext),
	not substring(Ext, ".", _),
	LBaseName is Pos-1,
	substring(FileName, 1, LBaseName, BaseName),
	!.
 
uih_path(AbsPath, AbsPath) :-
	string_length(AbsPath) > 0,
	substring(AbsPath, "/", 1),
	!.
uih_path(BaseName, Path) :-
	concat_string(["tmp/", BaseName], RelPath),
	get_uih_file(RelPath, Path).
 
find_file(FileName, Ext, Path /* ohne Extension! */) :-
	term2string(FileName, FileNameS1),
	tilde_expansion(FileNameS1, FileNameS),
	basename(FileNameS, Ext, BaseName),
	find_path(BaseName, Ext, Path),
	!.
 
find_path(AbsPath, Ext, AbsPath) :-
	string_length(AbsPath) > 0,
	substring(AbsPath, "/", 1),
	!,
	concat_string([AbsPath, Ext], PathExt),
	exists(PathExt).
find_path(BaseName, Ext, Path) :-
	concat_string(["tmp/", BaseName], RelPath),
	get_uih_file(RelPath, Path),
	concat_string([Path, Ext], PathExt),
	exists(PathExt).
find_path(Path, Ext, Path) :-
	concat_string([Path, Ext], PathExt),
	exists(PathExt).
 
tilde_expansion(FileNameTilde, FileName) :-
	substring(FileNameTilde, "~", 1),
	!,
	concat_string(["csh -c 'echo ", FileNameTilde, "'"], Cmd),
	exec(Cmd, [null, Output], Pid),
	read_string(Output, "\n", _, FileName),
	close(Output),
	wait(Pid, 0).
tilde_expansion(FileName, FileName).
 
/* Oeffnet ein File mit dem uebergebenen Namen (ggf. plus der Endung .tex)
   und gibt den Stream zurueck */
 
open_file_body(FileName, Stream, Mode) :-
	mode_specific(file_extension(Ext), Mode),
	open_file(FileName, Stream, Ext).
 
open_file(FileName, Stream, Ext) :-
	base_path(FileName, Ext, Path),
	concat_strings(Path, Ext, PathExt),
	open(PathExt, write, Stream),
	!.
 
/* open_include/2 erzeugt einen (hoffentlich) eindeutigen Filenamen, schreibt 
   eine passend Include-Anweisung (die i.a. durch das Postprocessing wieder 
   aufgeloest wird) in den als erstes Argument uebergebenen String, oeffnet
   dieses File zum Schreiben und gibt den Stream im zweiten Argument wieder
   zurueck. */

:- mode open_include(++, -).
open_include(Stream, Base, IncludeStream) :-
	get_right_file("tmp",TempFileRoot),
	concat_string([TempFileRoot,"/", Base], TmpBase),
	mktemp(TmpBase, TmpFileName),
	os_file_name(TmpFileName,OSTmpFileName),
	printf(Stream, "\nilf_include %w\n", [OSTmpFileName]),
	open(TmpFileName, write, IncludeStream).

	
technical_header(_).
technical_trailer(Stream) :- write(Stream, "\n").

file_extension("").

postprocess_file_body(FileName, Pid, Out, Mode) :-
	mode_specific(postprocess_file(FileName, [], [], Pid, Out), Mode).

postprocess_file_body(FileName, LabelList, RefList, Pid, Out, Mode) :-
        concat_strings(FileName, ".ref", RefFileName),
        mode_specific(write_ref_file(LabelList, RefList, RefFileName), Mode),
        get_right_file("bin/ppout.pl", PPOut),
        concat_string(["perl ",PPOut, " -m ", Mode, " -r ", RefFileName, " ", FileName],
			Cmd),
        exec(Cmd, [null, Out, null], Pid),
        !.

write_ref_file(_, _, RefFile) :-
	open(RefFile, write, RefStream),
	writeln(RefStream, ""),
	close(RefStream).

view_body(Mode) :-
	ilf_state(default_proof_file, FileName),
	mode_specific(view(FileName), Mode).

view_body(FileName, Mode) :-
	mode_specific(file_extension(Ext), Mode),
        find_file(FileName, Ext, Path),
        concat_strings(Path, Ext, PathExt),
        open(PathExt, read, Stream),
        repeat,
        once(read_string(Stream, "\n", _, Line) ; true),
        (var(Line) ; write(Line), nl, fail),
        close(Stream),
        !.
	
clearall.

title(_, _, _).

/* Formelausgabe unter Beruecksichtigung der {tex,html}ops:
   show_fla/4 formatiert die als erstes Argument uebergebenen Formel gemaess
   den texop des Modus und gibt den resultierenden String als viertes Argument 
   zurueck.
   Das zweite Argument enthaelt Namen fuer die Variablen (in der Form
   [Var|VarName]) als mit einer Variablen abgeschlossenen Liste.
   Das dritte Argument ist die "auessere" Prioritaet, d.h. die Formel wird
   in Klammern eingeschlossen, wenn ihre Prioritaet (lt. texop bzw. Prolog)
   groesser oder gleich dem dritten Argument ist. */


/* Variablen */
show_fla_body(Fla,Var,_,FlaS, Mode) :-
	var(Fla),
	!,
	make_var_show(Fla, Var, FlaS, Mode),
	!.
/* texop(struct, ... */
show_fla_body(Fla,Var,Prio,FlaString, Mode) :-
	tex_op_body(struct,NPrio,(Fla :- Transcript), Mode),
	(
		Fla=..[_],
		NPrio1=0,
		Lbrack="",
		Rbrack=""
		;
		(
			number(NPrio),
			NPrio1=NPrio,
			get_brackets(Prio,NPrio1,Lbrack,Rbrack, Mode)
			;
			NPrio1=Prio,
			Lbrack="",
			Rbrack=""
		)
	),
	show_fla_script(Transcript,Var,NPrio1,String, Mode),
	mode_specific(concat_fla([Lbrack, String, Rbrack], FlaString), Mode),
	!.
/* Strings */
show_fla_body(Fla,_,_,Fla, _) :-
	string(Fla),
	!.
/* Atome */
show_fla_body([],_,_,FlaS, Mode) :-
	mode_specific(list_brackets(LBrack, RBrack), Mode),
	mode_specific(concat_fla([LBrack, RBrack], FlaS), Mode),
	!.
show_fla_body(Fla,_,_,FlaString, Mode) :-
	atom(Fla),
	!,
	atom_string(Fla,OpString),
	mode_specific(no_underscore(OpString,FlaString), Mode),
	!.
/* Zahlen */
show_fla_body(Fla,_,_,FlaS, _) :-
	number(Fla),
	number_string(Fla,FlaS),
	!.
/* (nichtleere) Listen */
show_fla_body([F|L],Var,_Prio,FlaS, Mode) :-
	current_op(CommaPrio,_,','),
	mode_specific(arg_sep(ArgSep), Mode),
	show_fla_list_body([F|L], ArgSep, Var, CommaPrio, ArgString, Mode),
	mode_specific(list_brackets(LBrack, RBrack), Mode),
	mode_specific(concat_fla([LBrack, ArgString, RBrack], FlaS), Mode),
	!.
/* texop(op, ... */
show_fla_body(Fla,Var,Prio,FlaString, Mode) :-
	Fla =..[Op|Arg],
	tex_op_body(op,NPrio,(Op :- (Prefix0,Separator0,Postfix0)), Mode),
	check_text(Prefix0, Prefix, Mode),
	check_text(Separator0, Separator, Mode),
	check_text(Postfix0, Postfix, Mode),
	(
		number(NPrio),
		NPrio1=NPrio,
		(
			length(Arg,0),
			Lbrack="",
			Rbrack=""
			;
			get_brackets(Prio,NPrio1,Lbrack,Rbrack, Mode)
		)
		;
		NPrio1=Prio,
		Lbrack="",
		Rbrack=""
	),
	show_fla_list_body(Arg,Separator,Var,NPrio1,ArgString, Mode),
	mode_specific(concat_fla([Lbrack, Prefix, ArgString, Postfix, Rbrack], 
				FlaString), Mode),
	!.
/* texop(xfx|xfy|yfx, ... */
show_fla_body(Fla,Var,Prio,FlaString, Mode) :-
	Fla=..[Op,Fla1,Fla2],
	xfy_texop(Asso, NPrio, Op :- OpString, Mode),
	name(Asso, [Asso1, _, Asso2]),
	new_prio(Asso1, NPrio, NPrio1),
	new_prio(Asso2, NPrio, NPrio2),
	show_fla_body(Fla1,Var,NPrio1,FlaString1, Mode),
	show_fla_body(Fla2,Var,NPrio2,FlaString2, Mode),
	get_brackets(Prio,NPrio,Lbrack,Rbrack, Mode),
	mode_specific(concat_fla(
		[Lbrack, FlaString1, " ", OpString, " ", FlaString2, Rbrack],
		FlaString), Mode),
	!.
/* texop(fx|fy, ... */
show_fla_body(Fla,Var,Prio,FlaString, Mode) :-
	Fla=..[Op,Fla1],
	fx_texop(Asso, NPrio, Op :- OpString, Mode),
	name(Asso, [_, Asso1]),
	new_prio(Asso1, NPrio, NPrio1),
	show_fla_body(Fla1, Var, NPrio1, FlaString1, Mode),
	get_brackets(Prio, NPrio, Lbrack, Rbrack, Mode),
	mode_specific(concat_fla(
		[Lbrack, OpString, " ", FlaString1, Rbrack], FlaString), Mode),
	!.
/* texop(xf|yf, ... */
show_fla_body(Fla,Var,Prio,FlaString, Mode) :-
	Fla=..[Op,Fla1],
	xf_texop(Asso, NPrio, Op :- OpString, Mode),
	name(Asso, [Asso1, _]),
	new_prio(Asso1, NPrio, NPrio1),
	show_fla_body(Fla1, Var, NPrio1, FlaString1, Mode),
	get_brackets(Prio, NPrio, Lbrack, Rbrack, Mode),
	mode_specific(concat_fla(
		[Lbrack, FlaString1, " ", OpString, Rbrack], FlaString), Mode),
	!.
/* Prolog Operatoren */
show_fla_body(Fla,Var,_,FlaString, Mode) :-
	Fla=..[Op|Arg],
	current_op(CommaPrio,_,','),
	mode_specific(arg_sep(ArgSep), Mode),
	show_fla_list_body(Arg, ArgSep, Var, CommaPrio, ArgString, Mode),
	atom_string(Op,OpString),
	mode_specific(no_underscore(OpString,OpString1), Mode),
	mode_specific(brackets(LBrack, RBrack), Mode),
	mode_specific(concat_fla(
		[OpString1, LBrack, ArgString, RBrack], FlaString), Mode),
	!.
/* Fehler! */
show_fla_body(Fla,_Var,_Prio,"", Mode) :-
	ilf_serv_error(ilf_error("%w: Error displaying formula \"%w\".",
				[Mode, Fla])).
 
/* show_fla_script/5 arbeitet einen Texop-Script (gegeben im ersten Argument)
   ab. Das zweite bis vierte Argument entsprechen dabei den Argumenten
   von show_fla. 
   Bei Bedarf koennte dieses Praedikat als tool-Body fuer ein exportiertes
   vierstelliges show_fla_script verwendet werden. */

show_fla_script(Var, _, _, "", _) :-
	var(Var),
	ilf_serv_error(
		ilf_error("Variable %w in tex_op script ignored.", [Var])
	),
	!.
show_fla_script((F1,F2),Vars,Prio,String, Mode) :-
	show_fla_script(F1,Vars,Prio,S1, Mode),
	show_fla_script(F2,Vars,Prio,S2, Mode),
	mode_specific(concat_fla([S1, S2], String), Mode),
	!.
show_fla_script(x(X),Vars,Prio,String, Mode) :-
	mode_specific(show_fla(X,Vars,Prio,String), Mode),
	!.
show_fla_script(x(X,T),Vars,Prio,String, Mode) :-
	set_default_varname(T),
	mode_specific(show_fla(X,Vars,Prio,String), Mode),
	reset_default_varname,
	!.
show_fla_script(y(X),Vars,Prio,String, Mode) :-
	Prio1 is Prio+1,
	mode_specific(show_fla(X,Vars,Prio1,String), Mode),
	!.
show_fla_script(y(X,T),Vars,Prio,String, Mode) :-
	Prio1 is Prio+1,
	set_default_varname(T),
	mode_specific(show_fla(X,Vars,Prio1,String), Mode),
	reset_default_varname,
	!.
show_fla_script(z(X),Vars,_,String, Mode) :-
	mode_specific(show_fla(X,Vars,2000,String), Mode),
	!.
show_fla_script(z(X,T),Vars,_,String, Mode) :-
	set_default_varname(T),
	mode_specific(show_fla(X,Vars,2000,String), Mode),
	reset_default_varname,
	!.
show_fla_script(text(Text),_,_,String, Mode) :-
	term2string(Text, TextS),
	mode_specific(text(TextS, String), Mode),
	!.
show_fla_script(t(X), Vars, _, String, Mode) :-
	var(X),
	get_attribute(X, Type),
	!,
	mode_specific(show_fla(Type, Vars, 2000, String), Mode),
	!.
show_fla_script(t(_), _, _, "", _) :-
	!.
show_fla_script(F,_,_,F,_) :-
	string(F),
	!.
show_fla_script(call(Var),_,_,"",_) :-
	var(Var),
	ilf_serv_error(
		ilf_error("call(%w) in tex_op script ignored.", [Var])
	),
	!.
show_fla_script(call(Call),_,_,"",_) :-
	call(Call),
	!.
show_fla_script(call(Call),_,_,"",_) :-
	ilf_serv_error(
		ilf_error("call(%w) in tex_op script failed.", [Call])
	),
	!.
show_fla_script(F, _, _, "", _) :-
	ilf_serv_error(ilf_error("Error in tex_op script \"%w\".", [F])),
	!.
 
/* show_fla_varname_script/7 arbeitet analog zu show_fla_script/5,
   beruecksichtigt aber die Schluesselwort varname/1 */

show_fla_varname_script((F1,F2), Vars, Prio, String, VarName, IgnoreNr, Mode) :-
	show_fla_varname_script(F1, Vars, Prio, S1, VarName, IgnoreNr, Mode),
	show_fla_varname_script(F2, Vars, Prio, S2, VarName, IgnoreNr, Mode),
	mode_specific(concat_fla([S1, S2], String), Mode),
	!.
show_fla_varname_script(varname(VarScript), Vars, _, "%v", VarName, _, Mode) :-
	(var(VarName) ->
		show_fla_script(VarScript, Vars, 2000, VarName, Mode)
		;
		ilf_error("more than one varname(_) in script", [])
	),
	!.
show_fla_varname_script(ignore_varnumber, _, _, "", _, true, _) :-
	!.
show_fla_varname_script(Script, Vars, Prio, String, _, _, Mode) :-
	show_fla_script(Script, Vars, Prio, String, Mode).


/* show_fla_list/5 gibt einen String aus, der aus den mittels show_fla
   umgewandelten Formeln des ersten Arguments, getrennt durch das als
   zweites Argument uebergebene Trennzeichen besteht. */

show_fla_list_body([Fla],_,Var,Prio,FlaS, Mode) :-
	show_fla_body(Fla,Var,Prio,FlaS, Mode),
	!.
show_fla_list_body([Fla|Flas],Separator,Var,Prio,AllS, Mode) :-
	mode_specific(show_fla(Fla,Var,Prio,FlaS), Mode),
	show_fla_list_body(Flas,Separator,Var,Prio,FlasS, Mode),
	mode_specific(concat_fla([FlaS, Separator, FlasS], AllS), Mode),
	!.
show_fla_list_body([],_,_,_,"",_).

/* Klammern werden auch bei gleichen Prioritaeten gesetzt.
   Um das auf der y-Seite des Operators zu verhindern, wird mittels
   new_prio/3 eine um eins groessere Prioritaet an die Unterformeln
   uebergeben. */
 
get_brackets(Prio, NPrio, "", "", _) :- 
	NPrio < Prio, !.
get_brackets(_, _, LBrack, RBrack, Mode) :-
	mode_specific(scope_brackets(LBrack, RBrack), Mode).
 
new_prio(0'y, X, Y) :- Y is X + 1.
new_prio(0'x ,X, X).

brackets("(", ")").
scope_brackets("(", ")").
list_brackets("[", "]").
arg_sep(", ").
no_underscore(X, X).
firstup(X, X).

concat_fla(List, String) :- concat_string(List, String).

/* apply_texop0(X,S) ist eine Abkuerzung for show_fla(X, _, 2000, S).
   apply_texop(X,S) schliesst das Ergebnis zusaetzliche in die
   mode-spezifischen Klammern fuer mathematischen Text ein.
   apply_texop0_list/3 ist analog eine Abkuerzung fuer show_fla_list/5.
   show_fla0/2 erzeugt vor dem Aufruf von apply_texop/2 die "short form",
   show_fla0_list/3 erzeugt die "short form" fuer alle Formeln der Liste
   und ruft dann apply_texop_list/3.
   show_fla/2 setzt die Variablennummerierung zurueck, ruft show_fla0/2
   und schliesst den Ergebnisstring in die mode-spezifischen Klammern 
   fuer mathematischen Text ein. */

apply_texop0_body(Fla, FlaS, Mode) :- 
	mode_specific(show_fla(Fla, _, 2000, FlaS), Mode).

apply_texop_body(Fla, FlaS, Mode) :- 
	apply_texop0_body(Fla, FlaS0, Mode), 
	mode_specific(math(Begin, End), Mode),
	mode_specific(concat_fla([Begin, FlaS0, End], FlaS), Mode).

apply_texop0_list_body(FlaL, Sep, String, Mode) :- 
	mode_specific(show_fla_list(FlaL, Sep,  _, 2000, String), Mode).

show_fla0_body(FlaLong, FlaS, Mode) :-
	make_short_form(FlaLong, Fla),
	mode_specific(apply_texop0(Fla, FlaS), Mode).

show_fla0_list_body(FlaLongL, Sep, String, Mode) :-
	make_short_form_list(FlaLongL, FlaL),
	mode_specific(apply_texop0_list(FlaL, Sep, String), Mode).

show_fla_body(Fla, FlaS, Mode) :-
	mode_specific(clear_varnumbers, Mode),
	mode_specific(show_fla0(Fla, FlaS0), Mode),
	mode_specific(math(Begin, End), Mode),
	mode_specific(concat_fla([Begin, FlaS0, End], FlaS), Mode).

make_short_form(Fla, ShortFla) :-
	ilf_state(short_form, ShortFormPred),
	ShortFormPred \== [],
	!,
	ShortFormCall=..[ShortFormPred, Fla, ShortFla],
	(
		call(ShortFormCall)
		;
		ilf_error("%Dw/2 failed for %Dw, using long form",
			[ShortFormPred, Fla]),
		ShortFla=Fla
	),
	!.
make_short_form(Fla, ShortFla) :-
	(
		contract_abbrevs(Fla, ShortFla)
		;
		ilf_error("contract_abbrevs/2 failed for %Dw, using long form",
			[Fla]),
		ShortFla=Fla
	),
	!.

make_short_form_list([], []) :- !.
make_short_form_list([Fla|R], [ShortFla|ShortR]) :-
	make_short_form(Fla, ShortFla),
	make_short_form_list(R, ShortR).

math("", "").

/* show_type wandelt einen (Typ-)Term in einen String unter Beruecksichtigung
   evtl. vorhandener tex_op(sort, ...). 
   muss geklaert werden: ist tex_op(sort,... fuer Domains oder Typen oder 
   beides? */

show_type_body(Type, TypeS, Mode) :-
	mode_specific(tex_op(sort, _, (Type:-Script)), Mode),
	!,
	mode_specific(clear_varnumbers, Mode),
	show_fla_script(Script, _, 2000, TypeS0, Mode),
	mode_specific(math(Begin, End), Mode),
	mode_specific(concat_fla([Begin, TypeS0, End], TypeS), Mode),
	!.
/* ?? Sollte man das versuchen ?? */
show_type_body(Type, TypeS, Mode) :-
	mode_specific(tex_op(struct, _, (Type:-Script)), Mode),
	!,
	ilf_warning("Typesetting type %Dw using texop(struct, ... in mode %w.",
		[Type, Mode]),
	mode_specific(clear_varnumbers, Mode),
	show_fla_script(Script, [], 2000, TypeS0, Mode),
	mode_specific(math(Begin, End), Mode),
	mode_specific(concat_fla([Begin, TypeS0, End], TypeS), Mode),
	!.
show_type_body(and([], Type), TypeS, Mode) :-
	mode_specific(show_fla(Type, TypeS), Mode),
	!.
show_type_body(and(AttrL, Type), TypeS, Mode) :-
	mode_specific(show_fla(Type, TypeS0), Mode),
	show_attr(AttrL, AttrS0, Mode),
	(AttrS0 == "" ->
		TypeS = TypeS0
		;
		mode_specific(no_underscore(" and ", And), Mode),
		mode_specific(concat_fla([AttrS0, And, TypeS0], TypeS), Mode)
	),
	!.
show_type_body(Type, SetS) :-
	ilf_error("%DQw is not a valid type, replaced by set.", [Type]),
	show_type(and([], set), SetS).

show_attr([in(_)|AttrL], AttrS, Mode) :-
	show_attr(AttrL, AttrS, Mode),
	!.
show_attr([Attr|AttrL], AttrS, Mode) :-
	show_attr(AttrL, AttrS0, Mode),
	(AttrS0 == "" ->
		sprintf(AttrS1, "%DQw", [Attr]),
		mode_specific(no_underscore(AttrS1, AttrS), Mode)
		;
		sprintf(AttrS1, "%DQw, ", [Attr]),
		mode_specific(no_underscore(AttrS1, AttrS2), Mode),
		concat_fla([AttrS2, AttrS0], AttrS)
	),
	!.
show_attr([], "", _).

/* show_item/3 liefert im dritten Argument entweder das Ergebnis eines 
   {tex,...}op-Scripts fuer das erste Argument oder (wenn ein {tex,...}op
   nicht existiert, das zweite Argument, abgearbeitet als Rule-Script. */

show_item_body(Item, _, String, Mode) :-
        mode_specific(ruleop([control(Item)|RuleList]), Mode),
	!,
	show_rule_list(RuleList, String, Mode),
        !.
show_item_body(Item, _, String, Mode) :-
        mode_specific(texop(struct, Prio, Item:-Script), Mode),
	!,
        (var(Prio) -> Prio=2000 ; true),
        show_fla_script(Script, _, Prio, String, Mode),
        !.
show_item_body(_, String, String, _) :-
	string(String),
	!.
show_item_body(_, Script, String, Mode) :-
	show_rule_script(Script, String, Mode),
	!.

/* {rule,tex,html,...}ops

   tex_op/3 ist ein Tool mit Toolbody tex_op_body/4. Diese Praedikat findet 
   einen texop, indem nacheinander texop/3 und default_texop/3 des
   jeweiligen Modus probiert werden. Wird ein texop gefunden, ohne dabei
   Variablen an Nicht-Variablen zu binden, ist diese Wahl endgültig.
   Wenn man Backtracking durch alle moeglichen texops braucht, muss man
   try_texop/3 (bzw. dessen Toolbody try_texop_body) verwenden.
   {xfy,fx,xf}_texop/4 sucht einen texop mit einer entsprechenden 
   Assoziativitaet.  Gibt es keinen entsprechenden texop, aber eine 
   Operatordeklaration, wird der Operator (als String) zurueckgegeben.
   Die Auswahl ist hier ebenfalls endgueltig. */

tex_op_body(Asso, Prec, Texop:-Rule, Mode) :-
	copy_term(Texop, TryTexop),
	try_texop_body(Asso, Prec, TryTexop:-Rule, Mode),
	instance(Texop, TryTexop),
	Texop=TryTexop,
	!.
 
try_texop_body(Asso, Prec, Texop, Mode) :-
	mode_specific(texop(Asso, Prec, Texop), Mode).
try_texop_body(Asso, Prec, Texop, Mode) :-
	mode_specific(default_texop(Asso, Prec, Texop), Mode).
 
xfy_texop(Asso, NPrio, (Op :- OpString), Mode) :-
	try_texop_body(Asso,Prio,(Op :- OpString0), Mode),
	xfy_op(Asso),
	(
		number(Prio),
		NPrio=Prio
		;
		NPrio=1300
	),
	check_text(OpString0, OpString, Mode),
	!.
xfy_texop(Asso, NPrio, (Op :- OpString), Mode) :-
	current_op(NPrio, Asso, Op),
	xfy_op(Asso),
	atom_string(Op, OpString0),
	mode_specific(no_underscore(OpString0, OpString), Mode),
	!.
 
xfy_op(xfy).
xfy_op(yfx).
xfy_op(xfx).

fx_texop(Asso, NPrio, (Op :- OpString), Mode) :-
	try_texop_body(Asso,Prio,(Op :- OpString0), Mode),
	fx_op(Asso),
	(
		number(Prio),
		NPrio=Prio
		;
		NPrio=1300
	),
	check_text(OpString0, OpString, Mode),
	!.
fx_texop(Asso, NPrio, (Op :- OpString), Mode) :-
	current_op(NPrio, Asso, Op),
	fx_op(Asso),
	atom_string(Op, OpString0),
	mode_specific(no_underscore(OpString0, OpString), Mode),
	!.
 
fx_op(fx).
fx_op(fy).

xf_texop(Asso, NPrio, (Op :- OpString), Mode) :-
	try_texop_body(Asso,Prio,(Op :- OpString0), Mode),
	xf_op(Asso),
	(
		number(Prio),
		NPrio=Prio
		;
		NPrio=1300
	),
	check_text(OpString0, OpString, Mode),
	!.
xf_texop(Asso, NPrio, (Op :- OpString), Mode) :-
	current_op(NPrio, Asso, Op),
	xf_op(Asso),
	atom_string(Op, OpString0),
	mode_specific(no_underscore(OpString0, OpString), Mode),
	!.
 
xf_op(xf).
xf_op(yf).

default_texop(_, _, _) :- fail.
default_ruleop(_) :- fail.

check_text(text(String), Text, Mode) :-
	!,
	mode_specific(text(String, Text), Mode).
check_text(String, String, _).

text(X, X).

print_constants(_, _).

/* print_theorem/5 gibt eine Formel in einer bestimmten Umgebung (im LaTeX-
   Sinn, z.B. eine theorem-Umgebung) aus. print_theorem_string/5 tut das
   gleiche mit einer bereits in einen String umgewandelten Formel. */

print_theorem_body(Stream, Env, Formula, Handle, Name, Mode) :-
	mode_specific(show_fla(Formula, FormulaS0), Mode),
	mode_specific(append_punct(FormulaS0, ".", FormulaS), Mode),
	mode_specific(
		print_theorem_string(Stream, Env, FormulaS, Handle, Name), 
		Mode).

print_theorem_string_body(Stream, Env, String, Handle, Name, Mode) :-
	show_fla(Env, EnvS, Mode),
	(Name = [] ->
		NameS = ""
		;
		show_fla(Name, NameS, Mode)
	),
	(NameS = "" ->
		printf(Stream, "%w %Dw:\n  %w\n", [EnvS, Handle, String])
		;
		printf(Stream, "%w %Dw:\n  %w\n", [EnvS, NameS, String])
	).

print_formula_body(Stream, Formula, _, Punct, Mode) :-
	mode_specific(show_fla(Formula, FormulaS), Mode),
	write(Stream, FormulaS),
	write(Stream, Punct).

print_formula_body(Stream, Formula, _, Punct, Label, Mode) :-
	mode_specific(show_fla(Formula, FormulaS), Mode),
	write(Stream, "\n"),
	write(Stream, Label),
	write(Stream, ": "),
	write(Stream, FormulaS),
	write(Stream, Punct).

print_ref(Stream, Ref, _) :-
	write(Stream, Ref).

print_ref(Stream, [], Ref, _) :-
	write(Stream, Ref).
print_ref(Stream, Type, Ref, _) :-
	printf(Stream, "%w %w", [Type, Ref]).

print_known_theory(_, _).

print_proof_begin(Stream) :-
        write(Stream, "Proof. ").
 
print_proof_begin(Stream, Systems) :-
        printf(Stream, "Proof%w. ", [Systems]).

print_we(Stream) :-
        write(Stream, "We ").
 
print_we(Stream, Systems) :-
        printf(Stream, "We %w ", [Systems]).

print_qed(Stream) :-
	write(Stream, "\nQED.\n").

end_par(Stream) :-
        write(Stream, "\n\n").

/* Stringausgabe */

print_string(Stream, String) :-
        write(Stream, String).

print_string(Stream, String, on) :-
        firstup(String, UpString),
        write(Stream, UpString).
print_string(Stream, String, _) :-
        write(Stream, String).

print_string_ref(Stream, String, _) :-
        write(Stream, String).

/* "Text"ausgabe.
   Gibt den uebergeben Text aus, ggf. in einer speziellen Umgebung (dazu
   muss der Modus print_text0/ neu definieren).
   Zuerst wird ueberprueft, ob Texops fuer das Item existieren. Ist
   dies der Fall, wird statt des uebergebenen Textes der durch show_fla_script
   aus dem gefundenen Script erzeugte (allerdings nicht im Math-Mode!)
   ausgegeben. Danach folgt ein Absatz. */

print_text_body(Item, Stream, String, Mode) :-
	mode_specific(show_item(Item, String, ItemString), Mode),
	mode_specific(print_text0(Item, Stream, ItemString), Mode),
        !.

print_text0_body(_, _, "", _) :-
        !.
print_text0_body(_, Stream, Text, Mode) :-
        write(Stream, Text),
	mode_specific(end_par(Stream), Mode).

/* Ausgabe der benutzten Variablen mit den zugehoerigen Typen */

print_var_types_body(Stream, Mode) :-
	mode_specific(get_used_var_types(TypeAndVarList), Mode),
	mode_specific(print_var_types(Stream, TypeAndVarList), Mode).

print_var_types(_, _).

/* Ausgabe des Domainnamen und -status fuer Theorie-Ausgabe. */

print_th_domain_body(Stream, _, Title, Status, Mode) :-
	mode_specific(print_th_domain(Stream, Title, Status), Mode).

print_th_domain(_, _, _).

/* Ausgabe der Definitionen fuer die Theorie-Ausgabe. */

print_th_func_declaration(_, _, _).
print_th_pred_declaration(_, _).
print_th_type_declaration(_, _, _).

/* Ausgabe eines Axioms (Name und Formel) fuer Theorie-Ausgabe. */

print_th_axiom_body(Stream, Name, Formula, Mode) :-
	show_fla(Formula, FormulaS, Mode),
	printf(Stream, "%w.\n%Dw.\n", [FormulaS, Name]).

append_punct(String, Punct, StringPunct) :-
	concat_string([String, Punct], StringPunct).

/* Behandlung der Variablennamen/-nummern
   basiert auf Teilen von tools.pro 1.19 (10/23/95) */
 
/* Bestimmung der Namen der Variablen.
   Zuerst wird ueberprueft, ob in der Liste VarNames bereits ein
   Element [Var|Name] enthalten ist; falls ja wird dieser Name zurueck-
   geliefert. Andernfalls wird ueber mode-spezifisches new_varname/4 ein 
   Name erzeugt, das Paar [Var|Name] in die Liste VarNames eingefuegt
   und FirstVarName zurueckgegeben (wenn der texop(reserve, ...) fuer
   den Typ der Variablen ein Teilskript varname(_) enthaelt, ist das
   Ergebnis dieses Teilscripts der VarName, das Ergebnis des gesamten
   Skripts der FirstVarName). */
 
make_var_show(Var, VarNames, VarName, Mode) :-
	make_var_show(Var, VarNames, VarNames, VarName, Mode).

make_var_show(Var, VarNames, X, FirstVarName, Mode) :-
	var(X),
	!,
	mode_specific(new_varname(VarNames, Var, FirstVarName, VarName), Mode),
	append_varname(X, Var, VarName),
	!.
make_var_show(Var, _, [[SameVar|VarName]|_], VarName, _) :-
	Var == SameVar,
	!.
make_var_show(Var, VarNames, [_|RVarNames], VarName, Mode) :-
	make_var_show(Var, VarNames, RVarNames, VarName, Mode),
	!.
make_var_show(Var, _, _, VarName, Mode) :-
	(get_attribute(Var, Type) ; Type = []),
	ilf_error("%w: error showing variable %w:%w", [Mode, Var, Type]),
	term2string(Var, VarName0),
	mode_specific(no_underscore(VarName0, VarName), Mode),
	!.
 
append_varname(X, Var, VarName) :-
	var(X),
	!,
	X=[[Var|VarName]|_].
append_varname([_|R], Var, VarName) :-
	append_varname(R, Var, VarName).

/* Zuruecksetzen aller Informationen ueber Variablen.
   Dieses Praedikat wird typischerweise vor der Ausgabe eines Dokuments
   (Theorie oder Beweis) aufgerufen. */

ini_varnames :-
	retract_all(used_var(_, _, _)),
	retract_all(hidden_used_var(_, _, _)),
	retract_all(subtype(_, _, _)),
	retract_all(type_varname_cache(_, _, _, _, _)),
	set_default_varname,
	clear_varnumbers.

/* "Verstecken" der seit dem letzen Aufruf von ini_varnames/0 bzw. 
   hide_varnames/0 angesammelten Informationen ueber benutzte Variablen.
   Dadurch werden diese Variablen beim naechsten Aufruf von get_used_var_type/1
   *nicht* mit zurueckgegeben.
   Das typische Anwendungsbeispiel ist die Ausgabe der Typvariablen fuer
   die Theorieausgabe. */

hide_varnames :-
	retract(used_var(X, Y, Z)),
	assert(hidden_used_var(X, Y, Z)),
	fail.
hide_varnames.
 
/* Loeschen der Informationen ueber die Variablennumerierung.
   Dieses Praedikat wird normalerweise vor jeder Formelausgabe aufgerufen. */

clear_varnumbers :-
	retract_all(last_varnumber(_,_)),
	default_variable_name(Name),
	assert(last_varnumber(Name, 0)),    /* default Name immer mit Index */
	!.
 
/* Der Default-Variablename wird durch den/die Fakt(en) fuer
   default_variable_name/1 gegeben. Weitere Variablennamen koennen als
   Default verwendet werden (der Typ wird in type_varname_cache/5 als []
   gespeichert), wenn dem keine Reservierungen und keine andere Verwendung
   seit dem letzten ini_varname/0 entgegenstehen. 
   default_varname/1 versucht sein Argument mit einem moeglichen Default-
   namen zu unifizieren. */

default_variable_name("X").

default_varname(VarName) :-
	var(VarName),
	!,
	(
		default_variable_name(VarName)
		;
		VarName = "X",
		ilf_error(
			"no default variable name defined. Will use \"X\"", []
		)
	),
	!.
default_varname(VarName) :-
	type_varname_cache([], VarName, [], _, _),
	!.
default_varname(VarName) :-
	not varname2type(VarName, _, _),
	assert(type_varname_cache([], VarName, [], _, _)),
	!.

/* Setzen des Default-Variablennamens (aufgerufen von ini_varnames/0).
   Wenn vorhanden und verschieden von [], wird der ilf_state 
   default_variable_name benutzt. Ansonsten werden der Reihe nach alle
   Buchstaben X, Y, Z, A, B, ..., W probiert. 
   Das Problem besteht darin, daß zum Zeitpunkt des Setzen des Default-
   Namens nicht ueberprueft werden kann, ob dieser evtl. mit einem
   reserve-Texop in Konflikt steht. Da aber (hoffentlich) auch Variablen
   in Beweisen bald alle einen Typ haben, wird sich dieses Problem mit
   der Zeit von selbst erledigen. */

set_default_varname :-
	retract_all(default_variable_name(_)),
	fail.
set_default_varname :-
	ilf_state(default_variable_name, DefaultName0),
	DefaultName0 \== [],
	term2string(DefaultName0, DefaultName),
	(varname2type(DefaultName, Type, _) ->
		ilf_warning(
	"Default variable name \"%w\" conflicts with reservation for type %w", 
			[DefaultName, Type]
		)
		;
		true
	),
	assert(default_variable_name(DefaultName)),
	!.
set_default_varname :-
	try_variable_name_from_list(["X", "Y", "Z"], DefaultName),
	assert(default_variable_name(DefaultName)),
	!.
set_default_varname :-
	try_variable_name("A", DefaultName),
	assert(default_variable_name(DefaultName)),
	!.
set_default_varname :-
	ilf_warning("Cannot select a default variable name: All letters are reserved. Will use \"X\".", []),
	assert(default_variable_name("X")),
	!.
 
try_variable_name_from_list([X|_], X) :-
	not varname2type(X, _, _),
	!.
try_variable_name_from_list([_|L], X) :-
	try_variable_name_from_list(L, X).
 
try_variable_name(X, X) :-
	not varname2type(X, _, _),
	!.
try_variable_name(A, X) :-
	string_list(A, [N]),
	N1 is N+1,
	N1 < 0'X,
	string_list(A1, [N1]),
	try_variable_name(A1, X).

/* set_default_varname/1 und reset_default_varname/0 werden benutzt, um
   die zweistelligen Varianten von x, y und z in struct-Skripten zu
   implementieren. Keine Tests auf moegliche Konflikte finden statt. */

set_default_varname(Var) :-
	var(Var),
	!,
	ilf_warning("default variable name %w should be a string.", [Var]),
	once(
		get_var_info(Var, name, NameA),
		atom_string(NameA, Name)
		;
		default_variable_name(Name)
		;
		Name = "X"
	),
	set_default_varname(Name),
	!.
set_default_varname(New) :-
	term2string(New, NewS),
	asserta(default_variable_name(NewS)),
	!.
 
reset_default_varname :-
	retract(default_variable_name(_)),
	default_variable_name(_),
	!.
reset_default_varname :-
	ilf_error("reset_default_varname called too often.", []),
	set_default_varname.
 
/* new_varname/4 erzeugt einen neuen Variablennamen. */

new_varname_body(Vars, Var, FirstVarS, VarS, Mode) :-
	split_varname(Var, OName, ONumber),
	once(get_attribute(Var, Type) ; Type = []),
	mode_specific(
		new_typed_name(Vars, Type, OName, FirstVar, Name, IgnoreNr), 
		Mode),
	(IgnoreNr ->
		new_varnumber(Type, Name, FirstVar, [], Number)
		;
		new_varnumber(Type, Name, FirstVar, ONumber, Number)
	),
	mode_specific(make_varname(Name, Number, VarS), Mode),
	insert_varname(FirstVar, VarS, FirstVarS),
	!.

:- mode new_typed_name_body(+, +, ?, -, -, -, ++).
new_typed_name_body(Vars, Type, VarName, FirstVarS, VarName, IgnoreNr, Mode) :-
	type2varname(Vars, Type, VarName, FirstVarS, IgnoreNr, Mode),
	!.
new_typed_name_body(Vars, Type, _, FirstVarS, VarName, IgnoreNr, Mode) :-
	type2varname(Vars, Type, VarName, FirstVarS, IgnoreNr, Mode),
	!.

split_varname(Var, BaseName, Number) :-
	get_var_info(Var, name, Name),
	not name(Name, [0'_|_]),
	!,
	atom_string(Name, NameS),
	split_varnameS(NameS, BaseName, Number).
split_varname(_, _, []).
 
split_varnameS(Name, BaseName, Number) :-
	string_length(Name, LName),
	substring(Name, Pos, 1, "_"),   /* substring/3 is not resatisfiable */
	(L is LName - Pos),
	(Pos1 is Pos+1),
	substring(Name, Pos1, L, NumberS),
	not substring(NumberS, "_", _),
	number_string(Number, NumberS),
	LBaseName is Pos-1,
	substring(Name, 1, LBaseName, BaseName),
	!.
split_varnameS(Name, Name, []).

:- mode new_varnumber(+, ++, ++, ++, -).
new_varnumber(Type, VarName, FirstVar, [], []) :-
	not(last_varnumber(VarName, _)),
	note_used_var(Type, VarName, FirstVar),
	assert(last_varnumber(VarName, 0)),
	!.
new_varnumber(_, VarName, _, [], VarNumber) :-
	retract(last_varnumber(VarName, N)),
	!,
	VarNumber is N+1,
	assert(last_varnumber(VarName, VarNumber)),
	!.
new_varnumber(_, VarName, _, VarNumber, VarNumber) :-
	last_varnumber(VarName, LastNumber),
	VarNumber > LastNumber,
	!,
	retract(last_varnumber(VarName, _)),
	assert(last_varnumber(VarName, VarNumber)).
new_varnumber(_, VarName, _, _, VarNumber) :-
	retract(last_varnumber(VarName, N)),
	!,
	VarNumber is N+1,
	assert(last_varnumber(VarName, VarNumber)),
	!.
new_varnumber(Type, VarName, FirstVar, VarNumber, VarNumber) :-
	note_used_var(Type, VarName, FirstVar),
	assert(last_varnumber(VarName, VarNumber)),
	!.

/* note_used_var/3 vermerkt, dass VarName als Name fuer Variablen des 
   angegeben Typs benutzt wurden. Es geht davon aus, dass verschiedene
   Typen verschiedene Variablennamen haben, daher wird der Typ (der natuerlich
   wieder Variablen enthalten kann) hier nicht speziell (copy_term usw.)
   behandelt. */

note_used_var(Type, VarName, FirstVar) :-
	hidden_used_var(Type, VarName, FirstVar),
	!.
note_used_var(Type, VarName, FirstVar) :-
	used_var(Type, VarName, FirstVar),
	!.
note_used_var(Type, VarName, FirstVar) :-
	assert(used_var(Type, VarName, FirstVar)).

/* Default-Implementation fuer make_varname/3
   Verbindet den Name und evtuelle Super-/Subscripte mit underscore */

make_varname(VarName/Index, [], VarNameS) :-
	!,
	concat_string([VarName, "_", Index], VarNameS).
make_varname(VarName/Index, VarNumber, VarNameS) :-
	!,
	concat_string([VarName, "_", Index, "_", VarNumber], VarNameS).
make_varname(VarName, [], VarName) :-
	!.
make_varname(VarName, VarNumber, VarNameS) :-
	!,
	concat_string([VarName, "_", VarNumber], VarNameS).

/* Einfuegen des Variablennamen (VarS) in den String, der beim ersten
   Auftreten der Variablen gedruckt wird. Als Platzhalter dient %v.
   [] als erstes Argument bedeutet, dass das erste Auftreten nicht
   gesondert behandelt wird. */

:- mode insert_varname(+, +, -).
insert_varname([], Var, Var) :- !.
insert_varname(FirstVar0, Var, FirstVar) :-
	substring(FirstVar0, "%v", Pos),
	!,
	L1 is Pos-1,
	N2 is Pos+2,
	L2 is string_length(FirstVar0)-Pos-1,
	substring(FirstVar0, 1, L1, FirstVar1),
	substring(FirstVar0, N2, L2, FirstVar2),
	concat_string([FirstVar1, Var, FirstVar2], FirstVar).
insert_varname(FirstVar, _, FirstVar).

/* Gibt eine Liste mit Elementen [Type, VarList] (VarList ist nur eine Liste
   der Stammnamen, die zu diesem Typ gehoeren) zurueck, die die seit dem
   letzten Aufruf von ini_varnames/0 bzw. hide_varnames/0 benutzten Variablen 
   beruecksichtigt. */

get_used_var_types_body(TypeVarList, Mode) :-
	bagof(Type-Var, used_type_var(Type, Var, Mode), TypeVarBag),
	!,
	setof(	[Type, VarL], 
		setof(Var, member(Type-Var, TypeVarBag), VarL), 
		TypeVarList),
	!.
get_used_var_types_body([], _).

used_type_var(Type, Var, Mode) :-
	used_var(InternalType, Var, FirstVar),
	InternalType \== [],
	FirstVar == [],
	mode_specific(show_type(InternalType, Type), Mode).	

/* varname2type/3 erwartet als erstes Argument einen Variablennamen
   als String. Das zweite Argument wird unifiziert mit einem Typ,
   fuer den der Variablenname (seit dem letzten Aufruf von ini_varnames)
   benutzt wurde bzw. fuer den der Name in thman reserviert ist.
   Default-Variablennamen lieferen dabei den Typ [] zurueck. */

?- mode varname2type(++, ?, ++).
varname2type(VarName, Type, Mode) :- 
	type_varname_cache(Type, VarName, _, _, Mode).
varname2type(VarName, Type, _) :- 
	atom_string(VarNameA, VarName),
	var_has_typterm(VarNameA, Type).
varname2type(VarName, [], _) :- 
	default_variable_name(VarName).

/* type2varname/6 erwartet als zweites Argument einen Typterm und 
   unifiziert das dritte Argument mit moeglichen Variablennamen fuer
   diesen Typ. (Falls der Typ [] sein sollte wird, mit dem Default-
   Variablennamen unifiziert).  Das erste Argument ist die (hinten 
   offene) Liste der bereits benannten Variablen (vgl. show_fla),
   das vierte Argument der String, der fuer das erste Auftreten
   der Variablen zu benutzen ist (oder [], wenn dort auch der normale
   Name verwendet werden soll; vgl. das Schluesselwort `varname' in 
   reserve-Texops) und das fuenfte Argument ist true/fail, je nachdem,
   ob bei der Ausgabe der Variable die Originalnummer berücksichtigt
   werden soll (vgl. das Schluesselwort `ignore_varnumber' in reserve-
   Texops).
   Wenn reserve-Texops vorhanden sind, werden diese ausgewertet, um
   den Variablennamen zu bestimmen. Danach werden Reservierungen in
   thman ausgewertet (in thman sind Reservierungen fuer Typen mit 
   Variablen verboten). Wenn dadurch kein Name gefunden werden kann,
   wird ein Default-Name bestimmt, der aus dem Typ-Term abgeleitet
   wird.
   Um die Abarbeitung zu beschleunigen werden die Namen ueber das
   dynamische Praedikat type_varname_cache/5 gecacht. Dabei werden
   Typvariablen ueber numbervars kodiert (d.h. zwei Typen werden
   als gleich betrachtet, wenn sie Varianten voneinander sind).
   Dieser Cache wird beim Aufruf von  ini_varnames/0 geloescht. */

?- mode type2varname(?, +, ?, ?, ?, ++).
type2varname(_, [], VarName, [], fail, _) :-
	default_varname(VarName),
	!.
type2varname(_, Type, VarName, FirstVarS, IgnoreNr, Mode) :-
	copy_term(Type, Type1),
	numbervars(Type1),
	type_varname_cache(Type1, VarName, FirstVarS, IgnoreNr, Mode),
	!.
type2varname(Vars, Type, VarName, FirstVarS, IgnoreNr, Mode) :-
	not var(Mode), 			/* ist das notwendig? TH */
	tex_op_body(reserve, _, Type:-VarNameScript, Mode),
	!,
	once((
		show_fla_varname_script(VarNameScript, Vars, 2000,
					FirstVarS0, VarName0, IgnoreNr0, Mode),
		(var(VarName0) ->
			VarName = FirstVarS0,
			FirstVarS = []
			;
			VarName = VarName0,
			FirstVarS = FirstVarS0
		),
		(var(IgnoreNr0) ->
			IgnoreNr = fail
			;
			IgnoreNr = IgnoreNr0
		)

	)),
	copy_term(Type, Type1),
	numbervars(Type1),
	assert(type_varname_cache(Type1, VarName, FirstVarS, IgnoreNr, Mode)).
type2varname(_, Type, VarName, [], fail,_) :-
	term_variables(Type, []),
	var_has_typterm(VarNameA, Type),
	atom_string(VarNameA, VarName),
	!,
	assert(type_varname_cache(Type, VarName, [], fail, _)).
type2varname(_, Type, VarName, [], fail, _) :-
	var(VarName),
        copy_term(Type, Type1),
	numbervars(Type1),
	make_varname_type_temp(VarName, Type1),
	assert(type_varname_cache(Type1, VarName, [], fail, _)).
	
/* Erzeugen eines Default-Variablennamen fuer einen bestimmten Typ 
   (in Abwesenheit eines reserve-Texops und einer Reservierung in thman).
   Achtung: die erzeugten Namen sind i.a. keine Prolog-Variablen mehr. */

make_varname_type_temp(VarName/Index, and(_, Type)) :-
	retract(subtype(Type, VarName, N)),
	!,
	Index is N+1,
	assert(subtype(Type, VarName, Index)).
make_varname_type_temp(VarName,  and(_, Type)) :-
	!,
	type2name(Type, VarName, Index),
	assert(subtype(Type, VarName, Index)).
make_varname_type_temp(VarName, Type) :-
	ilf_error("illegal type: %Dw.", [Type]),
	default_varname(VarName).

type2name(Type, Name, N) :-
	Type =.. [TypeBase|_],
	!,
	atom_string(TypeBase, TypeBaseS),
	type2name0(TypeBaseS, Name, N).
type2name(_, Name, N) :-
	type2name0("X", Name, N).

type2name0(Type, Name, 0) :-
	substring(Type, 1, L, Name),
	L > 0,
	not varname2type(Name, _, _),
	!.
type2name0(Type, Type, Index) :-
	setval(type_index, 1),
	repeat,
	getval(type_index, Index),
	N1 is Index+1,
	setval(type_index, N1),
	not varname2type(Type/Index, _, _),
	!.

:- outtools_top.
