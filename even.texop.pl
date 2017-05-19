texop(latex,struct,_,(proof_author :- "$OTTER and ILF$")).
tex_op(latex, 'struct', _, (proof_title :- "$Twice the same number is even$")).
tex_op(latex, struct,_,(even(X) :- z(X),"$ is even$")).
tex_op(latex, struct,_,(odd(X) :- z(X),"$ is odd$")).
