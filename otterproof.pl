proof([2,global], control, proved).
proof([2,1], contents, even((A + B)); not(even(A)); not(even(B))).
proof([2,1], predecessors, []).
proof([2,1], status, []).
proof([2,2], contents, even((A + B)); not(odd(A)); not(odd(B))).
proof([2,2], predecessors, []).
proof([2,2], status, []).
proof([2,3], contents, not(even((a + a)))).
proof([2,3], predecessors, []).
proof([2,3], status, []).
proof([2,4], contents, even((A + A)); not(even(A))).
proof([2,4], predecessors, [[2,1]]).
proof([2,4], status, [factor, [1, 1, 2]]).
proof([2,5], contents, even((A + A)); not(odd(A))).
proof([2,5], predecessors, [[2,2]]).
proof([2,5], status, [factor, [2, 1, 2]]).
proof([2,6], contents, even(A); odd(A)).
proof([2,6], predecessors, []).
proof([2,6], status, []).
proof([2,7], contents, even(A); even((A + A))).
proof([2,7], predecessors, [[2,5], [2,6]]).
proof([2,7], status, [hyper, 5, [6, 2]]).
proof([2,9], contents, even((A + A))).
proof([2,9], predecessors, [[2,4], [2,7]]).
proof([2,9], status, [hyper, 4, [7, 1], factor_simp]).
proof([2,10], contents, false).
proof([2,10], predecessors, [[2,9], [2,3]]).
proof([2,10], status, [binary, [9, 1], [3, 1]]).
/* Additions */
proof([2,global],system,otter).
proof([2,ax(ev_ax)],contents,(not even(X) ; not even(Y) ; even(X + Y))).
proof([2,ax(ev_ax)],status,axiom(1)).
proof([2,ax(ev_ax)],predecessors,[]).
proof([2,ax(odd_ax)],contents,(not odd(X) ; not odd(Y) ; even(X + Y))).
proof([2,ax(odd_ax)],status,axiom(2)).
proof([2,ax(odd_ax)],predecessors,[]).
proof([2,ax(even_or_odd)],contents,(even(X) ; odd(X))).
proof([2,ax(even_or_odd)],status,axiom(3)).
proof([2,ax(even_or_odd)],predecessors,[]).
proof([2,ax(goal)],contents,(not even(a+a))).
proof([2,ax(goal)],status,axiom(goal)).
proof([2,ax(goal)],predecessors,[]).
proof([2,global],goal,even(a+a)).
/* Moved from end of file to make clauses consecutive */
proof([2,global], control, ready).
proof_object(1, [input], [[not, [even, v0]], [not, [even, v1]], [even, [+, v0, v1]]]).
proof_object(2, [input], [[not, [odd, v0]], [not, [odd, v1]], [even, [+, v0, v1]]]).
proof_object(3, [input], [[not, [even, [+, [a], [a]]]]]).
proof_object(4, [instantiate, 1, [[subst, v0, v1]]], [[not, [even, v1]], [not, [even, v1]], [even, [+, v1, v1]]]).
proof_object(5, [merge, 4, [2]], [[not, [even, v1]], [even, [+, v1, v1]]]).
proof_object(6, [instantiate, 5, [[subst, v1, v0]]], [[not, [even, v0]], [even, [+, v0, v0]]]).
proof_object(7, [instantiate, 2, [[subst, v0, v1]]], [[not, [odd, v1]], [not, [odd, v1]], [even, [+, v1, v1]]]).
proof_object(8, [merge, 7, [2]], [[not, [odd, v1]], [even, [+, v1, v1]]]).
proof_object(9, [instantiate, 8, [[subst, v1, v0]]], [[not, [odd, v0]], [even, [+, v0, v0]]]).
proof_object(10, [input], [[even, v0], [odd, v0]]).
proof_object(11, [instantiate, 9, [[subst, v0, v64]]], [[not, [odd, v64]], [even, [+, v64, v64]]]).

