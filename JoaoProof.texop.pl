tex_op(latex, 'xfy', 500, (';' :- "$ or $")).
tex_op(latex, 'xfy', 400, (',' :- "$ and $")).
tex_op(latex, 'yfx', 400, ('*' :- "\\cdot ")).
tex_op(latex, 'struct', 950, (all(X,Y) :- "$for all $",z(X),"$ $",z(Y))).
tex_op(latex, 'struct', 950, (forall(X,Y) :- "$for all $",z(ilf_varlist(X)),"$ $",z(Y))).
tex_op(latex, 'struct', _, (contradiction :- "$we have a contradiction$")).
tex_op(latex, 'struct', _, (not(=(X,Y)) :- z(X)," \\neq ", z(Y))).
tex_op(latex, 'struct',_, ((al1*a) :- "A")).
tex_op(latex, 'struct',_,((al1*(a*X)) :- "A \\cdot ",z(X))).
tex_op(latex, 'struct',_, (br1 :- "br_{1}")).
tex_op(latex, 'struct',_, (ar1 :- "ar_{1}")).
tex_op(latex, 'struct',_, (al1 :- "al_{1}")).
tex_op(latex, 'struct',_, (ar2 :- "ar_{2}")).
tex_op(latex, 'struct',_, (al2 :- "al_{2}")).
tex_op(latex, 'struct', _, (ax(1) :- "$associativity$")).
tex_op(latex, 'struct', _, (ax(2) :- "l-$identity$")).
tex_op(latex, 'struct', _, (ax(3) :- "l$ doesn't change product of $l-$terms$")).
tex_op(latex, 'struct', _, (ax(4) :- "l-$factors commute$")).
tex_op(latex, 'struct', _, (ax(5) :- "l$ of left factor doesn't change $l$-product$")).
tex_op(latex, 'struct', _, (ax(6) :- "$right factor inherits $l")).
tex_op(latex, 'struct', _, (ax(7) :- "r-$identity$")).
tex_op(latex, 'struct', _, (ax(8) :- "r$ doesn't change product of $r-$terms$")).
tex_op(latex, 'struct', _, (ax(9) :- "r-$factors commute$")).
tex_op(latex, 'struct', _, (ax(11) :- "$left factor inherits $r")).
tex_op(latex, 'struct', _, (ax(12) :- "l$ doesn't change $r-$terms$")).
tex_op(latex, 'struct', _, (ax(13) :- "r$ doesn't change $l-$terms$")).
tex_op(latex, 'struct', _, (ax(14) :- "ar_{1}$ right introduces $l$ for $a")).
tex_op(latex, 'struct', _, (ax(15) :- "ar_{2}$ right removes $l$ for $a")).
tex_op(latex, 'struct', _, (ax(16) :- "al_{1}$ left introduces $r$ for $a")).
tex_op(latex, 'struct', _, (ax(17) :- "al_{2}$ left removes $r$ for $a")).
tex_op(latex, 'struct', _, (ax(18) :- "br_{1}$ right introduces $l$ for $b")).
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
