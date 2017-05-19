/*
:- dynamic proof/3,
	proof_object/3.
	*/
:- compile("OtterProof1.out").

po2proof(proof_object(N,Reason,Fla)):- 
	po_clause(Fla,F).
	assert(proof([1,po(N)],contents,F)),
	S=.. Reason,
	assert(proof([1,po(N)],status,S)).
	
po_clause([X],T):- po_term(X,T),!.
po_clause([X|T],(TX;TT)) :- po_term(X,TX),po_clause(T,TT),!.

po_term([Op|L],T) :- !,po_term_l(L,Args),T=..[Op|Args],!.
po_term(X,X).

po_term_l([],[]).
po_term_l([E|L],[T|LT]) :- po_term(E,T),po_term_l(L,LT).
