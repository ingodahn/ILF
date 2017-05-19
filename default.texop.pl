tex_op(latex, 'struct', _, ((not(X);Y) :- z(X)," \\rightarrow ",z(Y))).
tex_op(latex, 'xfy', 500, (';' :- "$ or $")).
tex_op(latex, 'xfy', 400, (',' :- "$ and $")).
tex_op(latex, 'yfx', 400, ('*' :- "\\cdot ")).
tex_op(latex, 'yf', 100, ('#' :- "^{\\prime} ")).
tex_op(latex, 'struct', 950, (all(X,Y) :- "$for all $",z(X),"$ $",z(Y))).
tex_op(latex, 'struct', _, (not(foralll(X,Y)) :- "$for some $",z(ilf_varlist(X)),z(not(Y)))).
tex_op(latex, 'struct', 950, (forall(X,Y) :- "$for all $",z(ilf_varlist(X)),"$ $",z(Y))).
tex_op(latex, 'struct', _, (ilf_varlist([X]) :- z(X))).
tex_op(latex, 'struct', _, (ilf_varlist([X|L]) :- z(X),"$, ",z(ilf_varlist(L)))).
tex_op(latex, 'struct', _, (contradiction :- "$we have a contradiction$")).
tex_op(latex, 'struct', _, (not(=(X,Y)) :- z(X)," \\neq ", z(Y))).
tex_op(latex, 'struct',_, (c1 :- "c_{1}")).
tex_op(latex, 'struct', _, (ax(1) :- "$associativity$")).
tex_op(latex, 'struct', _, (ax(2) :- "$right identitity$")).
tex_op(latex, 'struct', _, (ax(3) :- "$left identity$")).
tex_op(latex, 'struct', _, (ax(4) :- "$right inverse$")).
tex_op(latex, 'struct', _, (ax(5) :- "$left inverse$")).
tex_op(latex, 'struct', _, (ax(6) :- "$involution$")).
tex_op(latex, 'struct', _, (ax(7) :- "$anti-morphism$")).
tex_op(latex, 'struct', _, (ax(8) :- "$3-index free$")).
tex_op(latex, 'struct', _, (ax(9) :- "$2-commutativity$")).
tex_op(latex, 'struct', _, (ax(10) :- "$cubes commute$")).
/*
tex_op(latex, 'struct', _, ((X * (X * (X * X))) :- "(",z(X),")^{4}")).
*/
tex_op(latex, rule,_, (rule([indirect],Y) :- we, " show indirectly that ", formula, ".\n", proof,
        "Thus we have completed the proof of ", formula_ref, ".", par)).
tex_op(latex, rule,_, (rule([in(not)],_):-
        we, " show indirectly that ", formula, ".\n", proof,
        "Thus we have completed the proof of ", formula_ref, ".", par)).
tex_op(latex, rule,_,(rule([direct],_) :- premises([_]),
        we, " show directly that ", formula, ".\n", proof,
        "Thus we have completed the proof of ", formula_ref,".", par)).
tex_op(latex, rule,_,(rule([direct],_) :-
        we, " show directly that ", formula, ".\n", proof,
        intro, " we have completed the proof of ", formula_ref, ".", par)).
tex_op(latex, rule,_,((premises([]), not(status(assumption(_)))) :-
	"Clearly, ", formula, ".\n")).
tex_op(latex, rule,_,((not(control(rule(_,_))), not(status(assumption(_)))) :-
	"We still have to prove that ", formula, ".\n")).
tex_op(latex, rule,_, (rule([expert(System, _ )], _) :-
	intro, formula, " was proved by ", math(System), ".\n")).
tex_op(latex, rule,_, (status(assumption(_)),
	"Let us assume that ", collect_formula(status(assumption(_))), ".\n")).
tex_op(latex, rule,_, (rule([intro([])], Y) :- intro, formula,".\n")).
tex_op(latex, rule,_, (rule([factor([1, 2])], Y) :- intro, "$ using factoring we get $",formula,".\n")).
tex_op(latex, rule,_, (rule([hyper([X1, X2])], Y) :- intro, "$ with hyperresolution we get $",formula,".\n")).
tex_op(latex, rule,_, (rule([hyper([1, 1]), factor_simp([])], Y) :- intro, "$ with hyperresolution and simplification we obtain $",formula,".\n")).
tex_op(latex, rule,_, (rule([binary([1, 1])], Y) :- intro, "$ with binary resolution we have $",formula,".\n")).
tex_op(latex, rule,_, (rule([let],Y) :- intro, "$ let us assume that $",formula,".\n")).
