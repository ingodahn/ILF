/* File errman.pl 1.3
 * checked in 11/20/98
 * Project: The ILF-Project
 * Author: Thomas Baar
 * Version for restricted ILF system 2016
 * 
 * Purpose: 
 *          This module (error-manager) is the module within to set
 *          error-handler, which should be valid all the time.
 *
 *          Furthermore this module provides possibilities to protocol and
 *          evaluate error-messages (and other).
 *          There is an stream error_report on which ILF write all
 *          protocols some events (f.i.ILF-ERROR messages and ILF-Warnings).
 *          The format of stream-messages is hidden in this module.
 *          There are tools to redirect and evaluate error_report - stream.
 *
 * Note: This module is loaded in forground in background - prolog of ILF.
 */

:- module(errman).


:- export
	adj_bg_def_errfile/1,
	adj_fg_def_errfile/1,
        adj_jobdep_errorfile/2,
        adj_jobdep_errorfile_l/2,
	evaluate_err_file/6,
        redirect_error_report/1,
	registrate_err/2,
	reset_error_report/0,
	save_error_report/0.

:- import
        rm_if_exists/1
                       from parasys.
:- import ilfsys.

?- begin_module(errman).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%   Start Redirection of error-handler for ILF    %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% During booting of ILF we call redirect_eclipse_error_handler what
% redirects some error_handlers for all modules.
% Redirection of error-handler is only possible in a global sense.

redirect_eclipse_error_handler:-
	set_error_handler(68,ilf_undef_handler/3),
	set_error_handler(70,ilf_undef_handler/3),
	set_error_handler(5,type_err_handler/3).

% The first clause avoid an recursive call of registrate_err
ilf_undef_handler(68,registrate_err(_,_), Module) :-
	printf(2, "ERROR !!!!!  registrate_err not defined in %w \n", [Module]),
        !, fail.
ilf_undef_handler(68,Goal,Module) :-
        functor(Goal,Op,N),
	open("",string, Str),
        write(Str, "WARNING "),
        write(Str, (Op/N)),
        write(Str, " is undefined in module "), writeln(Str, Module),
	current_stream(Msg,_,Str),
	close(Str),
	write(2, Msg),
	flush(2),
	registrate_err(168, [Msg]),
        !,fail.

% beim Fehlen von dynamischen Prozeduren wird nichts mehr ausgegeben
%             T,Baar
ilf_undef_handler(70,retract(Goal),Module) :-   % wenn retract aufgerufen und dyn. Praed. existiert nicht
        functor(Goal,Op,N),		    % schlaegt retract fehl	
	open("",string, Str),
        write(Str, "WARNING "),
        write(Str, (Op/N)),
        write(Str, " is not dynamic in module "), writeln(Str, Module),
	current_stream(Msg,_,Str),
	close(Str),
	write(2, Msg),	
	flush(2),
	registrate_err(170, [Msg]),
        !,fail.

ilf_undef_handler(70,retract_all(Goal),Module) :- % wenn retract_all aufgerufen wird und dyn. Praedikat ex. nicht
        functor(Goal,Op,N), 		      % gelingt retract_all  
	open("",string, Str),
        write(Str, "WARNING "),
        write(Str, (Op/N)),
        write(Str, " is not dynamic in module "), writeln(Str, Module),
	current_stream(Msg,_,Str),
	close(Str),
	write(2, Msg),	
	flush(2),
	registrate_err(170, [Msg]),
        !.

ilf_undef_handler(Err,Goal,Module) :- error(default(Err),Goal,Module).

% Error 5 in eclipse is type_error
type_err_handler(5,Goal,Module):-
	term_string(Goal,GoalS),
	open("",string, Str),
	write(Str, "ILF-ERROR: type error occurred in goal "),
	write(Str, GoalS), 
	write(Str, " in module "),
	writeln(Str, Module),
	current_stream(Msg,_,Str),
	close(Str),
	write(2, Msg),	
	flush(2),
	registrate_err(105, [Msg]),
	!,fail.
	


%%%%   End  Redirection of error-handler for ILF    %%%%%%%%%%%%%%%%%%%%

:- dynamic
        tmp_constr1/1,
	tmp_constr2/1,
        tmp_err_eval/4,
	tmp_err_occur/0,
        tmp_wait_reset_to/1.

errman_top:-
%	ilf_debug((print("ErrorManager 1.3 (11/20/98) installed"), nl)),
        redirect_eclipse_error_handler,
	rm_def_err_file,
	ini_error_report,
	!.


%%%%%%%  Start adjust-region   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adj_bg_def_errfile(FileN):-
	RootFileName = "tmp/.error_bg_file",
	get_uih_file(RootFileName, FileN),
	!.
adj_fg_def_errfile(FileN):-
	RootFileName = "tmp/.error_fg_file",
	get_uih_file(RootFileName, FileN),
	!.


adj_jobdep_errorfile(Job, File):-
	concat_string(["tmp/ilf.", Job, ".err"], RootF),
	get_uih_file(RootF, File),
	!.
adj_jobdep_errorfile_l([], []).
adj_jobdep_errorfile_l([Job|JobL], [File|FileL]):-
	adj_jobdep_errorfile(Job, File),
	adj_jobdep_errorfile_l(JobL, FileL).

%%%%%%%  End adjust-region   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%  Start error-stream setting and redirection  %%%%%%%%%%%%%%%%%

% rm_def_err_file deletes in the boot-phase the files to which
% the stream error_report connected as default.
rm_def_err_file:-
	current_module(exman),     % are we in background-prolog ?
	adj_bg_def_errfile(FileN),
	rm_if_exists(FileN),
	!.
rm_def_err_file:-                  % we are in foreground-prolog
	adj_fg_def_errfile(FileN),
	rm_if_exists(FileN),
	!.



ini_error_report:-
	(
	 current_module(exman),     % are we in background-prolog ?
	 adj_bg_def_errfile(FileN)
        ;
	 adj_fg_def_errfile(FileN)
        ),
	open(FileN, append, error_report),
	!.


% redirect_error_report(Str) redirects the stream error_report to Str.
% The current stream associated with error_report is store in a stack
% and reactivate, when reset_error_report occurs.

redirect_error_report(Str):-
	get_stream(error_report, StrOld),
	(retract(tmp_wait_reset_to(StreamStack)) ; StreamStack = []),
	assert(tmp_wait_reset_to([StrOld | StreamStack])),
	set_stream(error_report, Str),
	!.


% reset_error_report resets error_report to the first element
% in tmp_wait_reset_to - predicate (Stack of redirected Streams)
% and make it possible to redirect stream error_report once again

reset_error_report:-
	not (tmp_wait_reset_to([_|_])),
	ilf_error("reset_error_report: can't find tmp_wait_reset_to - fact or empty stack"),
	ini_error_report,
	!.
reset_error_report:-
	retract(tmp_wait_reset_to([StrOld|NewStack])),
	assert(tmp_wait_reset_to(NewStack)),
	set_stream(error_report, StrOld),
	!.

% save_error_report save the actual stream error_report in File and open
% error_report again
% So File exists and can be consulted.
save_error_report:-
	current_stream(File, _, error_report),
	flush(error_report),
	close(error_report),
	open(File, append, error_report),
	!.
save_error_report:-
	ilf_error(["save_error_report unexpected fails"]),
	close(error_report),
	ini_error_report.


%%%%%%%  End error-stream setting and redirection  %%%%%%%%%%%%%%%%%


%%%%%%%  Start error registration  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% registrate_err(No, List_of_Prop) should we call, if we can detect
% an unexpected situation (ilf_error, database is empty, etc)
% For full list of err-numbers see the end of this file.
% 
% 
% registrate_err write the error in a given format on error_report
% We add the Time and to List_of_Prop a unbounded tail Hole. So we can evaluate
% for one error-number not only one List_of_Prop's with a fixed length.
%
% registrate_err would be better implement as an eclipse-tool.
% But this would cause trouble in the booting-phase of ILF.
% We want to use registrate_err in ilfsys.pl (ilf_error - predicate).
% 
registrate_err(No, List_of_Prop):-
	get_flag(unix_time, UTime),
	append([UTime | List_of_Prop], _Hole, List1),
	write_canonical(error_report, error_occ(No, List1)),
	write(error_report, ".\n"),
	flush(error_report),
	!.

%%%%%%%  End  error registration  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Writing Report for the user     %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% How to interprete the items, which we have written earlier on error_report
% in the predicate registrate_err  ?
%


% evaluate_err_file(+Err_File, +ClassL, ?StartUT, ?EndUT, -ErrOccFlag, +OutSt) 
% consults an error file Err_File an write a report to OutStr
% The Flag ErrOccFlag detects, if an error of the desired classes occurs 
%
% evaluate_err_file searches all errors-messages in Err_File, which
% have a class in ClassL and occured between StartUT and EndUT and
% writes an human-readable report on OutStr
%
% The format of Err_File is determined in registrate_err, the format 
% of OutStr in err_write_report
evaluate_err_file(Err_File, ClassL, StartUT, EndUT, ErrOccFlag, OutStr):-
	clear_err_db,
	open(Err_File, read, Err_Stream),
	read_and_est_tmp_err_db(Err_Stream),
	close(Err_Stream),
	err_write_report(ClassL, StartUT, EndUT, OutStr),
	(tmp_err_occur, ErrOccFlag = yes ; ErrOccFlag = no),
	!.



%%%%%%%  Start error evaluation to dynamic database   %%%%%%%%%%%%%%%%%


clear_err_db:-
	retract_all(tmp_err_eval(_,_,_,_)),
        retract_all(tmp_err_occur).

% read_and_est_tmp_err_db(Stream) reads an error_report from Stream and generate
% tmp_err_eval facts in errman-module

read_and_est_tmp_err_db(Str):-
	repeat,
	read(Str, Item),
	(
	 Item = end_of_file
        ;
	 Item = error_occ(No, Li),
	 est_tmp_err_eval(No, Li),
	 fail
        ;
	 Item \= error_occ(_,_),
	 ilf_error("read_and_est_tmp_err_db: unexpected format of readed Item %w", [Item]),
         fail
        ),
	!.

% est_tmp_err_eval(No, Li) generates facts on which our evaluation-predicates
% are based.
% est_tmp_err_eval - is written for the format of fact, which are
% generate by registrate_err.
% Generally, est_tmp_err_eval adds error-class information and makes 
% the time of occurence explicit in the database. This information are
% needed to handle efficient with the dynamic facts.

est_tmp_err_eval(No, [ UTime | List_of_Prop]):-
	repeat,
	(
	 err_class(No, Class),
	 assert(tmp_err_eval(No, Class, UTime, List_of_Prop)),
	 fail
        ;
	 true
        ),
	!.

%%%%%%%  End  error evaluation to dynamic database   %%%%%%%%%%%%%%%%%


%%%%%%%  Start interpreting dynamic database and writing  for user  %%%%%


% err_write_report(ClassL, StartUT, EndUT, Stream) writes all errors
% which are members of a class matching with an element in ClassL in a
% special format on Stream. 
% Furthermore it detect only such error, which are occured between 
% unixtime StartUT and EndUT.
% Elements of ClassL, StartUT, EndUT can be (can contain) free variables.



err_write_report(ClassL, Start, End, Stream):-
	retract_all(tmp_constr1(_X1)),
	retract_all(tmp_constr2(_X2)),
	(var(Start) -> assert(tmp_constr1(_X1) :- true)
                       ;
		       assert(tmp_constr1(X1) :- Start =< X1)
        ),
	(var(End)  -> assert(tmp_constr2(_X2) :- true)
                       ;
		       assert(tmp_constr2(X2) :- X2 =< End)
        ),
	err_write_report1(ClassL, Stream).


err_write_report1([],_).
err_write_report1([Class | Tail], Str):-
	repeat,
	(
	 tmp_err_eval(No, Class, Ti, List_of_Prop),
	 once((
	       tmp_constr1(Ti),
	       tmp_constr2(Ti),
	       assert(tmp_err_occur),
	       err_write_msg(No, List_of_Prop, String),
	       writeln(Str, String)
	      )),
	 fail
        ;
	 true
        ),
%	printf(Str, "%% This were all errors which class matches which %w \n\n", [Class]),
        err_write_report1(Tail, Str).



%
% err_write_msg determines the format of output for the user
% 
%
% We interprete generated tmp_err_eval - facts.
% We have to be prepared, that the interpretation and length of List_of_Prop
% can be change in the future. 
% Therefore List_of_Prop has the form [a,c,v | Hole]

err_write_msg(No, List_of_Prop, String):-
	err_descr(No, DescrS),
	err_ana_prop(No, List_of_Prop, PropS),
	concat_string(["% Event ", No, " (", DescrS, ") : ", PropS], String).


%%%%%%%  End interpreting dynamic database and writing  for user  %%%%%




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Description of ilf-intern Errors (or Events)    %%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%  Description in natural language   %%%%%%%%%%%%%%%%%%%%%

%The first 100 intern-error-numbers are reservated  for new errors
err_descr( 1, " ilf-error occurrence  ").
err_descr( 2, " ilf-warning occurrence  ").
err_descr( 3, " ilf-database error ").
err_descr( 4, " error in background produced exit_block ").

% The intern-error-numbers greater than 100 are reserved for eclipse-errors
% occurences. If yue subtract from these intern-numbers 100 you will
% get the error number in the eclipse-error-table

err_descr(No, " eclipse-error handled in ILF "):-
	No > 100,
	!.
err_descr( No, ""):-
	ilf_warning("err_descr: can't find description for ilf_event with number %w", [No]).



%%%%%%%   Structuring of all errors in classes   %%%%%%%%%%%%%%%%

% err_class divide all error-numbers in classes. One error number can be 
% member of several classes.
% If the user want to have a error-report he can determine, which classes of
% errors(or events) should be occurc.
%
%
% currently we know the following classes
% err   -  error
% ie    -  ilf_error
% iw    -  warning
% db    -  database_errors
%

err_class(1, ie). 
err_class(1, err).
err_class(2, iw).
err_class(3, db).
err_class(4, err).
err_class(No, eclerr):- No > 100,!.


%%%%%%%%%  Interpretation of error-property-list  %%%%%%%%%%%%%%%%%%%%

% err_ana_prop(No, List_of_Prop, String) generates from List_of_Prop an human
% readable string String
% The length of List_of_Prop may be changed in future.

err_ana_prop(1, [Ilf_Err_Msg|_Hole], Ilf_Err_Msg):- !.
err_ana_prop(2, [Ilf_Warn_Msg|_Hole], Ilf_Warn_Msg):- !.
err_ana_prop(3, [Msg|_Hole], OutString):-
	concat_string([Msg, " Empty Database! Perhaps a syntax-error in the theory-file \n"], OutString),
	!.
err_ana_prop(4, [Msg |_Hole], OutString):-
	concat_string(["Unexpected error produced exit_block in ", Msg], OutString),
	!.
err_ana_prop(No, [Msg |_Hole], OutString):-
	No > 100,
	concat_string(["Handled error with message ",Msg], OutString),
	!.
err_ana_prop(_No,_, OutString):-
	concat_string(["Sorry, unexpected error detect in err_ana_prop"], OutString).

%%%%%%%  End  error-description     %%%%%%%%%%%%%%%%%



?- errman_top.





