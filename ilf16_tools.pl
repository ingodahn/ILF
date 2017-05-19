indirect_direct :- 
	once(proof(P,status,subproof(PH))),
	unquantified_content(P,Goal),
	once(goal_in_proof(Goal,[PH,G])),
	ass_unused([PH,G]),
	make_direct_proof(P,PH,G),!.
	
indirect_direct :- writeln("Cannot convert into direct proof.").

goal_in_proof(Goal,[PH,G]) :- proof([PH,G],contents,GG),
	is_variant_of(GG,Goal),!.
goal_in_proof(LL=RR,[PH,G]) :- proof([PH,G],contents,GG),
	is_variant_of(GG,RR=LL),!.

unquantified_content(P,Goal) :- proof(P,contents,forall(_,Goal)),!.
unquantified_content(P,Goal) :- proof(P,contents,Goal).

ass_unused([PH,G]) :- proof([PH,Ass],predecessors,[]),!,
	dependant([PH,Ass],[[PH,Ass]],L),!,
	not member([PH,G],L).
	
/* dependant(P,L1,L2) - L2 is L1 augmented by all lines below P directly or indirectly depending upon lines in L1 */
dependant(P,L1,L2) :- proof(PP,predecessors,[P]),dependency(PP,L1,LL1),dependant(PP,LL1,L2).
dependant(_,L,L).

dependency(PP,L1,[PP|L1]) :- once(proof(PP,control,rule(_,RL))),member(X,L1),member(X,RL),!.
dependency(_,L,L).

make_direct_proof(P,PH,G) :- retract(proof(P,control,rule([indirect],_))),
	assert(proof(P,control,rule([direct],[[PH,G]]))),
	remove_unused,
	change_global(PH).

change_global(PH) :- once(proof([N,global],goal,_)),retract(proof([N,global],X,Y)),assert(proof([PH,global],X,Y)),fail.
change_global(_).