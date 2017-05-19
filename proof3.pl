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
proof([ax(1, 1), 0], contents, not even(_1374) ; not even(_1382) ; even(_1374 + _1382)).
proof([ax(1, 1), 0], predecessors, []).
proof([ax(1, 1), 0], status, proved).
proof([ax(1, 1), 0], control, axiom(ev_ax)).
proof([ax(1, 2), 0], contents, not odd(_1374) ; not odd(_1382) ; even(_1374 + _1382)).
proof([ax(1, 2), 0], predecessors, []).
proof([ax(1, 2), 0], status, proved).
proof([ax(1, 2), 0], control, axiom(odd_ax)).
proof([ax(1, 3), 0], contents, even(_1372) ; odd(_1372)).
proof([ax(1, 3), 0], predecessors, []).
proof([ax(1, 3), 0], status, proved).
proof([ax(1, 3), 0], control, axiom(even_or_odd)).
proof([sub(1, 1), 1], contents, not even(_1374) ; not even(_1382) ; even(_1374 + _1382)).
proof([sub(1, 1), 1], predecessors, [[sub(1, 1), ax(4)]]).
proof([sub(1, 1), 1], status, proved).
proof([sub(1, 1), 1], control, rule([intro([])], [[sub(1, 1), ax(1)]])).
proof([sub(1, 1), 2], contents, not odd(_1374) ; not odd(_1382) ; even(_1374 + _1382)).
proof([sub(1, 1), 2], predecessors, [[sub(1, 1), 1]]).
proof([sub(1, 1), 2], status, proved).
proof([sub(1, 1), 2], control, rule([intro([])], [[sub(1, 1), ax(2)]])).
proof([sub(1, 1), 3], contents, not even(a + a)).
proof([sub(1, 1), 3], predecessors, [[sub(1, 1), 2]]).
proof([sub(1, 1), 3], status, proved).
proof([sub(1, 1), 3], control, rule([intro([])], [[sub(1, 1), ax(4)]])).
proof([sub(1, 1), 4], contents, not even(_1374) ; even(_1374 + _1374)).
proof([sub(1, 1), 4], predecessors, [[sub(1, 1), 3]]).
proof([sub(1, 1), 4], status, proved).
proof([sub(1, 1), 4], control, rule([factor([1, 2])], [[sub(1, 1), 1]])).
proof([sub(1, 1), 5], contents, not odd(_1374) ; even(_1374 + _1374)).
proof([sub(1, 1), 5], predecessors, [[sub(1, 1), 4]]).
proof([sub(1, 1), 5], status, proved).
proof([sub(1, 1), 5], control, rule([factor([1, 2])], [[sub(1, 1), 2]])).
proof([sub(1, 1), 6], contents, even(_1372) ; odd(_1372)).
proof([sub(1, 1), 6], predecessors, [[sub(1, 1), 5]]).
proof([sub(1, 1), 6], status, proved).
proof([sub(1, 1), 6], control, rule([intro([])], [[sub(1, 1), ax(3)]])).
proof([sub(1, 1), 7], contents, even(_1372) ; even(_1372 + _1372)).
proof([sub(1, 1), 7], predecessors, [[sub(1, 1), 6]]).
proof([sub(1, 1), 7], status, proved).
proof([sub(1, 1), 7], control, rule([hyper([1, 2])], [[sub(1, 1), 5], [sub(1, 1), 6]])).
proof([sub(1, 1), 9], contents, even(_1372 + _1372)).
proof([sub(1, 1), 9], predecessors, [[sub(1, 1), 7]]).
proof([sub(1, 1), 9], status, proved).
proof([sub(1, 1), 9], control, rule([hyper([1, 1]), factor_simp([])], [[sub(1, 1), 4], [sub(1, 1), 7]])).
proof([sub(1, 1), 10], predecessors, [[sub(1, 1), 9]]).
proof([sub(1, 1), 10], status, proved).
proof([sub(1, 1), 10], control, rule([binary([1, 1])], [[sub(1, 1), 9], [sub(1, 1), 3]])).
proof([sub(1, 1), 10], contents, contradiction).
