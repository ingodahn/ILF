proof([1, global], goal, even(a + a)).
proof([1, global], system, [otter, ilf]).
proof([1, global], status, proved).
proof([1, global], control, ready).
proof([1, 1], contents, even(a + a)).
proof([1, 1], predecessors, []).
proof([1, 1], status, subproof(sub(1, 1))).
proof([1, 1], control, rule([indirect], [[sub(1, 1), ax(4)], [sub(1, 1), 10]])).
proof([sub(1, 1), ax(4)], contents, not even(a + a)).
proof([sub(1, 1), ax(4)], predecessors, []).
proof([sub(1, 1), ax(4)], status, assumption([])).
proof([ax(1, 1), 0], contents, not even(_632) ; not even(_640) ; even(_632 + _640)).
proof([ax(1, 1), 0], predecessors, []).
proof([ax(1, 1), 0], status, proved).
proof([ax(1, 1), 0], control, axiom(ev_ax)).
proof([ax(1, 2), 0], contents, not odd(_632) ; not odd(_640) ; even(_632 + _640)).
proof([ax(1, 2), 0], predecessors, []).
proof([ax(1, 2), 0], status, proved).
proof([ax(1, 2), 0], control, axiom(odd_ax)).
proof([ax(1, 3), 0], contents, even(_630) ; odd(_630)).
proof([ax(1, 3), 0], predecessors, []).
proof([ax(1, 3), 0], status, proved).
proof([ax(1, 3), 0], control, axiom(even_or_odd)).
proof([sub(1, 1), 1], contents, not even(_632) ; not even(_640) ; even(_632 + _640)).
proof([sub(1, 1), 1], predecessors, [[sub(1, 1), ax(4)]]).
proof([sub(1, 1), 1], status, proved).
proof([sub(1, 1), 1], control, rule([intro([])], [[sub(1, 1), ax(1)]])).
proof([sub(1, 1), 2], contents, not odd(_632) ; not odd(_640) ; even(_632 + _640)).
proof([sub(1, 1), 2], predecessors, [[sub(1, 1), 1]]).
proof([sub(1, 1), 2], status, proved).
proof([sub(1, 1), 2], control, rule([intro([])], [[sub(1, 1), ax(2)]])).
proof([sub(1, 1), 3], contents, not even(a + a)).
proof([sub(1, 1), 3], predecessors, [[sub(1, 1), 2]]).
proof([sub(1, 1), 3], status, proved).
proof([sub(1, 1), 3], control, rule([intro([])], [[sub(1, 1), ax(4)]])).
proof([sub(1, 1), 4], contents, not even(_632) ; even(_632 + _632)).
proof([sub(1, 1), 4], predecessors, [[sub(1, 1), 3]]).
proof([sub(1, 1), 4], status, proved).
proof([sub(1, 1), 4], control, rule([factor([1, 2])], [[sub(1, 1), 1]])).
proof([sub(1, 1), 5], contents, not odd(_632) ; even(_632 + _632)).
proof([sub(1, 1), 5], predecessors, [[sub(1, 1), 4]]).
proof([sub(1, 1), 5], status, proved).
proof([sub(1, 1), 5], control, rule([factor([1, 2])], [[sub(1, 1), 2]])).
proof([sub(1, 1), 6], contents, even(_630) ; odd(_630)).
proof([sub(1, 1), 6], predecessors, [[sub(1, 1), 5]]).
proof([sub(1, 1), 6], status, proved).
proof([sub(1, 1), 6], control, rule([intro([])], [[sub(1, 1), ax(3)]])).
proof([sub(1, 1), 7], contents, even(_630) ; even(_630 + _630)).
proof([sub(1, 1), 7], predecessors, [[sub(1, 1), 6]]).
proof([sub(1, 1), 7], status, proved).
proof([sub(1, 1), 7], control, rule([hyper([1, 2])], [[sub(1, 1), 5], [sub(1, 1), 6]])).
proof([sub(1, 1), 9], contents, even(_630 + _630)).
proof([sub(1, 1), 9], predecessors, [[sub(1, 1), 7]]).
proof([sub(1, 1), 9], status, proved).
proof([sub(1, 1), 9], control, rule([hyper([1, 1]), factor_simp([])], [[sub(1, 1), 4], [sub(1, 1), 7]])).
proof([sub(1, 1), 10], predecessors, [[sub(1, 1), 9]]).
proof([sub(1, 1), 10], status, proved).
proof([sub(1, 1), 10], control, rule([binary([1, 1])], [[sub(1, 1), 9], [sub(1, 1), 3]])).
proof([sub(1, 1), 10], contents, contradiction).
proof([po(1), 1], status, proved).
proof([po(1), 1], control, rule(input)).
proof([po(1), 1], contents, [[not, [even, v0]], [not, [even, v1]], [even, [+, v0, v1]]]).
proof([po(1), 1], predecessors, []).
proof([po(1), 2], status, proved).
proof([po(1), 2], control, rule(input)).
proof([po(1), 2], contents, [[not, [odd, v0]], [not, [odd, v1]], [even, [+, v0, v1]]]).
proof([po(1), 2], predecessors, []).
proof([po(1), 3], status, proved).
proof([po(1), 3], control, rule(input)).
proof([po(1), 3], contents, [[not, [even, [+, [a], [a]]]]]).
proof([po(1), 3], predecessors, []).
proof([po(1), 4], status, proved).
proof([po(1), 4], control, rule(instantiate([[subst, v0, v1]]), [[po(1), 1]])).
proof([po(1), 4], contents, [[not, [even, v1]], [not, [even, v1]], [even, [+, v1, v1]]]).
proof([po(1), 4], predecessors, [[po(1), 1]]).
proof([po(1), 5], status, proved).
proof([po(1), 5], control, rule(merge([2]), [[po(1), 4]])).
proof([po(1), 5], contents, [[not, [even, v1]], [even, [+, v1, v1]]]).
proof([po(1), 5], predecessors, [[po(1), 4]]).
proof([po(1), 6], status, proved).
proof([po(1), 6], control, rule(instantiate([[subst, v1, v0]]), [[po(1), 5]])).
proof([po(1), 6], contents, [[not, [even, v0]], [even, [+, v0, v0]]]).
proof([po(1), 6], predecessors, [[po(1), 5]]).
proof([po(1), 7], status, proved).
proof([po(1), 7], control, rule(instantiate([[subst, v0, v1]]), [[po(1), 2]])).
proof([po(1), 7], contents, [[not, [odd, v1]], [not, [odd, v1]], [even, [+, v1, v1]]]).
proof([po(1), 7], predecessors, [[po(1), 2]]).
proof([po(1), 8], status, proved).
proof([po(1), 8], control, rule(merge([2]), [[po(1), 7]])).
proof([po(1), 8], contents, [[not, [odd, v1]], [even, [+, v1, v1]]]).
proof([po(1), 8], predecessors, [[po(1), 7]]).
proof([po(1), 9], status, proved).
proof([po(1), 9], control, rule(instantiate([[subst, v1, v0]]), [[po(1), 8]])).
proof([po(1), 9], contents, [[not, [odd, v0]], [even, [+, v0, v0]]]).
proof([po(1), 9], predecessors, [[po(1), 8]]).
proof([po(1), 10], status, proved).
proof([po(1), 10], control, rule(input)).
proof([po(1), 10], contents, [[even, v0], [odd, v0]]).
proof([po(1), 10], predecessors, []).
proof([po(1), 11], status, proved).
proof([po(1), 11], control, rule(instantiate([[subst, v0, v64]]), [[po(1), 9]])).
proof([po(1), 11], contents, [[not, [odd, v64]], [even, [+, v64, v64]]]).
proof([po(1), 11], predecessors, [[po(1), 9]]).
