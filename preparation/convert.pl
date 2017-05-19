/* Konverter fuer Otter-Files vom ILF-Server @(#)convert.pl	1.8 (3/19/98) */
/* Autor: dahn */

% :- lib(cio).
see(F) :- open(F,read,input).
seen :- close(input).

:- op(10,fx,'$').

:- dynamic(ax_name/2).
:- dynamic(proof/3).
:- dynamic(proof_object/3).
:- dynamic(proof_object/4).
:- dynamic(clause_info1/2).
:- dynamic(clause_info2/2).
:- dynamic(to_replace/2).
:- dynamic(last_handle/1).
:- dynamic(prolog_style_variables/0).

:- op(700,xfx,'!=').
spy_ilf.

convert :-
	make_work_file,
	otter_ops,
	get_ops,
	get_NONPROLOG,
	get_work_file("out",Outfile),
	open(Outfile,write,outfile),
	get_work_file("axn",Axn),
	see(Axn),
	get_otter_ax,
	put_ax_name,
	seen,
	get_work_file("opf.tmp.1",Tmpfile),
	see(Tmpfile),
	do_convert,
	seen,
	close(outfile),
	!.

otter_ops :- 
	op(500,xfy,+),
	op(500,xfx,-),
	op(700,xfx,'!='),
	op(400,xfy,*),
	op(400,xfx,'/').
	
get_ops :- 
	get_work_file("op",OpFile),
	open(OpFile, read, opStream),
	read_signature,
	close(opStream).
read_signature :- repeat,read(opStream,D),make_op(D),!.

/* Operator-Deklaration in *.op-File mit new_op() ! */
make_op(end_of_file) :- !.
make_op(new_op(P,A,Op)) :- op(P,A,Op),!,fail.
make_op(_) :- !,fail.


do_convert :- repeat,
	not((
		read_string("\n",_,Line),
		translate_string(Line,TLine),
		term_string(Term,TLine),
		do_convert(Term)
	)),
%	printf(outfile,"%MOQvDw.\n",[proof([1,global],control,ready)]),
	!.

translate_string(end_of_file,_) :- !,fail.
translate_string(S,TS) :- 
	tokenize_string(S,SL),
	replace_tokens(SL,SL1),
	SL1=[_,_|_],
	prolog_term(['.'],_,T,SL1,_),
	term_string(T,TS),
	!.

	
prolog_term(DelL,L,Rest) :- prolog_term(DelL,_,_,L,Rest).

prolog_term(DelL,Del,L,Rest) :- prolog_term(DelL,Del,_,L,Rest).

prolog_term(DelL,Del,T,L,Rest) :- prolog_term(DelL,Del,T,X-X,L,Rest).

prolog_term(DelL,Del,T,L-[],[Del|Rest],Rest) :- member(Del,DelL),!,
	concat_string(L,S),term_string(T,S).
prolog_term(DelL,Del,T,X-[" ",E," "|X1],[E|L],Rest) :- atom(E),current_op(_,_,E),!,
	prolog_term(DelL,Del,T,X-X1,L,Rest).
prolog_term(DelL,Del,T,X-[E|X1],[E|L],Rest) :- 
	prolog_term(DelL,Del,T,X-X1,L,Rest).


tokenize_stream(Stream,List) :- read_token(Stream,E,_),
	tokenize_stream(Stream,E,List).

tokenize_stream(_,end_of_file,[]) :- !.
tokenize_stream(Stream,E,[E|L]) :- tokenize_stream(Stream,L).

tokenize_string(S,L) :- open(S,string,Stream),tokenize_stream(Stream,L).


replace_tokens([-,>|TL],["'->'"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([<,-,>|TL],["'<->'"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([!,=|TL],["'!='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([<,=|TL],["'<='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([>,=|TL],["'>='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([=,=|TL],["'=='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([=,/,=|TL],["'=/='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([@,<|TL],["'@<'"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([@,>|TL],["'@>'"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([@,<,=|TL],["'@<='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([@,>,=|TL],["'@>='"|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens(['.'],['.']) :- !.
replace_tokens(['.'|TL],[#|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([T|TL],[T1|T1L]) :- to_replace(T,T1),
	replace_tokens(TL,T1L),!.
replace_tokens([T|TL],[T|TL1]) :- replace_tokens(TL,TL1),!.
replace_tokens([],['.']).


do_convert(proved) :-
	printf(outfile,"%MOQvDw.\n",[proof([1,global],control,proved)]),!.
/*
do_convert(used_formula(Handle,Reason,Fla)) :-
	translate_fla(Fla,FlaI),
	Handle=[NH|_],
	Handle1=[1,NH],
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,contents,FlaI)]),
	reaspred(Reason,Pred),
	pred_ax(Pred,FlaI,Pred1),
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,predecessors,Pred1)]),
	(Reason=[] -> Reason1=[intro];Reason1=Reason),
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,status,Reason1)]),
	!.
*/
do_convert(used_formula(Handle,Reason,Fla)) :-
	translate_fla(Fla,FlaI),
	Handle=[NH|_],
	Handle1=[1,NH],
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,contents,FlaI)]),
	(
	retract(last_handle(LH)),
	printf(outfile,"%w.\n",[proof(Handle1,predecessors,[LH])])
	;
	printf(outfile,"%w.\n",[proof(Handle1,predecessors,[])])
	),
	assert(last_handle(Handle1)),
	(
	Reason=[],
	is_ax(FlaI,[HAx]),
	Rule=rule([intro],[[1,HAx]])
	;
	reaspred(Reason,Refs),
	Rule=rule(Reason,Refs)
	),
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,status,Rule)]),
	!.

do_convert(proof_object(N,Art,Fla,_)) :- do_convert(proof_object(N,Art,Fla)),!.
do_convert(proof_object(N,Art,Fla)) :- spy_ilf,
	make_subst(Art,Art1),
	/*
	printf(outfile,"%MOQvDw.\n",[proof_object(N,Art1,Fla)]),
	*/
	po_fla2o_fla(Fla,Fla1),
	printf(outfile,"%MOQvDw.\n",[proof([1,po(N)],contents,Fla1)]),
	printf(outfile,"%MOQvDw.\n",[proof([1,po(N)],control,proof_object)]),
	S=..Art1,
	printf(outfile,"%MOQvDw.\n",[proof([1,po(N)],status,S)]),
	po_reaspred(Art1,Preds),
	printf(outfile,"%MOQvDw.\n",[proof([1,po(N)],predecessors,Preds)]),
	!.
do_convert(_).

po_fla2o_fla(X,X) :- atom(X),!.
po_fla2o_fla([X],X) :- atom(X),!.
po_fla2o_fla([Op|Args],F) :- atom(Op),!,po_fla2o_fla_l(Args,Args1),F=..[Op|Args1],!.
po_fla2o_fla(FL,FF) :- po_fla2o_fla_l(FL,FL1),make_clause(FL1,FF),!.

po_fla2o_fla_l([X|L],[F|LF]) :- po_fla2o_fla(X,F),!,po_fla2o_fla_l(L,LF).
po_fla2o_fla_l([],[]).

make_clause([F],F) :- !.
make_clause([F|FL],(F;FLF)) :- make_clause(FL,FLF).

po_reaspred([_],[]):-!.
po_reaspred([_,N|_],[[1,po(N)]]).

po_hdl(N,[M|L],[[N,po(M)]|L1]) :- po_hdl(N,L,L1).
po_hdl(_,[],[]).

/*
reaspred([],[]) :- !.
reaspred([N|Reas],[[1,N]|Pred]) :- number(N),!,
	reaspred(Reas,Pred),!.
reaspred([[N|_]|Reas],[[1,N]|Pred]) :- number(N),!,
	reaspred(Reas,Pred),!.
reaspred([_|Reas],Pred) :- reaspred(Reas,Pred),!.
*/
/*
reaspred([],[]) :- !.
reaspred([factor,[N|_]],[[1,N]]) :- !.
reaspred([hyper,N1,[N2|_]|_],[[1,N1],[1,N2]]) :- !.
reaspred([binary,[N1|_],[N2|_]],[[1,N1],[1,N2]]) :- !.
reaspred([para_into,[N1|_],[N2|_]|_],[[1,N1],[1,N2]]) :- !.
reaspred([para_from,[N1|_],[N2|_]|_],[[1,N1],[1,N2]]) :- !.
reaspred([back_demod,N1,demod,N2,N3|_],[[1,N1],[1,N2],[1,N3]]) :- !.
reaspred([copy,N,[flip,_]],[[1,N]]) :- !.
reaspred(Res,[]) :- printf("ERROR: Unknown reason %MOQvDw\n",[Res]).
*/
reaspred([],[]) :-!.
reaspred([assumption|Reas],Pred) :- reaspred(Reas,Pred).
reaspred([goal|Reas],Pred) :- reaspred(Reas,Pred).
reaspred([deny(N)|Reas],[[1,N]|Pred]) :- reaspred(Reas,Pred).
reaspred([copy(N)|Reas],[[1,N]|Pred]) :- reaspred(Reas,Pred).
reaspred([flip(_)|Reas],Pred) :- reaspred(Reas,Pred).
reaspred([rewrite([Fp|Args])|Reas],[[1,N]|Pred]) :- Fp=..[flapart,N|_],reaspred([rewrite(Args)|Reas],Pred).
reaspred([rewrite([Fp|Args])|Reas],[[1,N]|Pred]) :- Fp=[N|_],reaspred([rewrite(Args)|Reas],Pred).
reaspred([rewrite([])|Reas],Pred) :- reaspred(Reas,Pred).
reaspred([rewrite(flapart(N,_),flapart(N1,_))|Reas],[[1,N],[1,N1]|Pred]) :- reaspred(Reas,Pred).
reaspred([rewrite([N|_],[N1,_])|Reas],[[1,N],[1,N1]|Pred]) :- reaspred(Reas,Pred).
reaspred([back_rewrite(N)|Reas],[[1,N]|Pred]) :- reaspred(Reas,Pred).
reaspred([clausify(N)|Reas],[[1,N]|Pred]) :- reaspred(Reas,Pred).
reaspred([para(Fp1,Fp2)|Reas],[[1,N1],[1,N2]|Pred]):- Fp1=..[flapart,N1|_],Fp2=..[flapart,N2|_],reaspred(Reas,Pred).
reaspred([para([N1|_],[N2|_])|Reas],[[1,N1],[1,N2]|Pred]):- reaspred(Reas,Pred).
reaspred([xx(_)|Reas],Pred) :- reaspred(Reas,Pred).
reaspred([hyper(N1, _T1, N2, _T2)|Reas],[[1,N1],[1,N2]|Pred]) :- reaspred(Reas,Pred).
reaspred([resolve(N1, _T1, N2, _T2)|Reas],[[1,N1],[1,N2]|Pred]) :- reaspred(Reas,Pred).
reaspred(Res,[]):- printf("ERROR: Unknown reason %MOQvDw\n",[Res]).

is_ax(F,[ax(Nr)]) :- setval(ax_count,0),
	ax_name(Name,F1),incval(ax_count),
	variant(F,F1),!,
	getval(ax_count,Nr),
	Handle1=[1,ax(Nr)],
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,predecessors,[])]),
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,status,axiom(Name))]),
	printf(outfile,"%MOQvDw.\n",[proof(Handle1,contents,F1)]),!.
is_ax([],F,[unknown_axiom]) :- 
	printf("ILF Warning: Unknown axiom %w\n",[F]),!.

make_subst([instantiate,N,S],[instantiate,N,S1]) :- make_v_subst(S,S1),!.
make_subst(S,S).

make_v_subst([[V1,'.',V2]|VL],[[subst,V1,V2]|VL1]) :- make_v_subst(VL,VL1),!.
make_v_subst([],[]).

get_NONPROLOG :- 
	get_work_file("in",InFile),
	open(InFile,read,opNonprolog),
	read_nonprolog,
	close(opNonprolog).

read_nonprolog :- repeat,not (read_string(opNonprolog,"\n",_,Line),
	get_nonprolog(Line)),!.

/* read_string schlaegt fehl bei end_of_file) */
get_nonprolog(Line) :-
	string_length(Line,NL),
	11 < NL,
	extract_nonprolog(Line,NL).
get_nonprolog(_).

extract_nonprolog(Line,NL) :- 
	substring(Line,1,1,"%"),
	substring(Line,N,10,"NONPROLOG:"),
	N1 is N+10,
	N2 is (NL-N1)+1,
	substring(Line,N1,N2,S),!,
	make_nonprolog(S),!.
extract_nonprolog(Line,_) :- substring(Line,_,_,"set(prolog_style_variables"),
	assert(prolog_style_variables),!,fail.
	
make_nonprolog(S) :- tokenize_string(S,ST),make_to_replace(ST),!.

make_to_replace([S|SL]) :- atom_string(A,S),
	assert(to_replace(S,A)),
	make_to_replace(SL),!.
make_to_replace([]).

conv_vars :- 
	retract(proof(H,contents,S)),
	translate_fla(S,S1),
	assert(proof(H,contents,S1)),
	fail.
conv_vars :- retract(proof_object(N,R,F,_)),
	translate_fla(F,F1),
	assert(proof_object(N,R,F1)),
	fail.
conv_vars :- retract(proof_object(N,R,F)),
	translate_fla(F,F1),
	assert(proof_object(N,R,F1)),
	fail.
conv_vars.

translate_fla(H,H1) :- translate_fla(H,H1,_),!.

translate_fla(H,H1,V) :- otter_var(H),member((H,H1),V),!.
translate_fla(H,H,_) :- var(H),!.
translate_fla('$'(_),false,_) :- !.
translate_fla('!='(F1,F2),not(F11 = F22),V) :- translate_fla(F1,F11,V),
	translate_fla(F2,F22,V),!.
translate_fla(-(H),not(H1),V) :- translate_fla(H,H1,V),!.
translate_fla(|(H1,H2),(HH1;HH2),V) :- 
	translate_fla(H1,HH1,V),translate_fla(H2,HH2,V),!.
translate_fla(H,H1,V) :- H=..[Op|Arg],
	translate_fla_l(Arg,Arg1,V),
	H1=..[Op|Arg1],!.

translate_fla_l([H|HL],[H1|H1L],V) :- translate_fla(H,H1,V),
	translate_fla_l(HL,H1L,V),!.
translate_fla_l([],[],_).

otter_var(V) :- atom(V),
	not prolog_style_variables,
	atom_string(V,VS),
	string_list(VS,[X|_]),
	117 =< X,X =< 122,!.

get_otter_ax :- setval(cnt,1),repeat,
	not read_otter_ax,!.

read_otter_ax :- read_string(".",_,String),
	read_otter_ax(String),!.

read_otter_ax(String) :-
	translate_string(String,TString),
	term_string(Ax,TString),
	translate_fla(Ax,Ax1),
	readvar(input,X,L),
	check_for_vars(L),
	write_otter_ax(X,Ax1),!.

check_for_vars([[S|S]|L]) :- check_for_vars(L),!.
check_for_vars([]).

write_otter_ax(end_of_file,Ax) :- 
	printf("ILF ERROR: No name for axiom %w\n",[Ax]),!,fail.
write_otter_ax(Name,Ax) :- getval(cnt,N),
	printf(outfile,"otter_ax(%MOQvDw,%MOQvDw).\n",[N,Name]),
	assert(ax_name(Name,Ax)),
	incval(cnt),!.

put_ax_name :- printf(outfile,"?- io_module(axioms).\n",[]),fail.
put_ax_name :- 
	ax_name(N,A),
	printf(outfile,"ax_name(%MOQvDw,%MOQvDw,true,[]).\n",[N,A]),
	fail.
put_ax_name :- printf(outfile,"?- io_module(situation).\n",[]).

get_work_file(Relname,Absname) :-
	getval(work_file,WD),
	concat_string([WD,Relname],Absname),
	exists(Absname),!.

	/* Simplified for reduced ILF 2016 
make_work_file :- getenv("OUT",DirOut),
	string_length(DirOut,LOut),
	(LD is LOut - 3),
	substring(DirOut,1,LD,Dir),
	setval(work_file,Dir),
	!.
*/
/* pciwm11 und Toshiba
make_work_file :- setval(work_file,"//C/Users/dahn/CloudStation/ILF/Joao/preparation/OtterProof1.").

make_work_file :- setval(work_file,"//C/Users/dahn/CloudStation/ILF/Joao/preparation/JoaoProof.").
*/
make_work_file :- setval(work_file,"//C/Users/dahn/CloudStation/ILF/Joao/preparation/JoaoProof4.").

/* Lenovo
make_work_file :- setval(work_file,"//D/User/CloudStation/ILF/Joao/preparation/OtterProof1.").

make_work_file :- setval(work_file,"//D/User/CloudStation/ILF/Joao/preparation/JoaoProof.").

make_work_file :- setval(work_file,"//D/User/CloudStation/ILF/Joao/preparation/JoaoProof3.").
*/

/*	
translate_string(S1,S2) :- open(S1,string,Stream1),
	open(_,string,Stream2),
	translate_stream(Stream1,Stream2,0),
	current_stream(S2,string,Stream2).
*/
translate_stream(St1,St2,_) :- read_token(St1,T1,_),
	(
	T1=end_of_file
	;
	to_replace(T1,T2),
	printf(St2," %Qw",[T2]),
	at(St1,N1),
	translate_stream(St1,St2,N1)
	),!.
translate_stream(St1,St2,N) :- at(St1,N1),
	seek(St1,N),
	L is N1 - N,
	read_string(St1,"",L,S),
	printf(St2,"%w",[S]),
	translate_stream(St1,St2,N1),!.

