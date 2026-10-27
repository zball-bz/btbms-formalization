"""Python port of BTBM.ts (ne-rewritten@88df798) for bounded experiments.

Expr = tuple of columns; column = tuple of entries; entry = (parent, height).
Python tuple comparison is exactly the paper's syntax order (proper prefix smaller,
entries by parent then height), and relative keys use (mark, value, height) triples.
"""
import sys

sys.setrecursionlimit(10000)


def to_height(e, r):
    return tuple(tuple(((0, p) if p < r else (1, p - r)) + (to_height(h, r),) for p, h in col) for col in e)


def has_next_layer(e):
    return len(e) > 0 and len(e[-1]) > 0


def next_layer(e):
    return e[-1][-1][1]


def tail_layer(e):
    return -1 if not has_next_layer(e) else 1 + tail_layer(next_layer(e))


def skip(e, n):
    for _ in range(n):
        e = next_layer(e)
    return e


def tail(e, tl):
    left, cur = 0, e
    for _ in range(tl):
        left += len(cur)
        cur = next_layer(cur)
    return left + len(cur) - 1


def root(e, tl):
    return skip(e, tl)[-1][-1][0]


def root_layer(e, r):
    cur, left, layer = e, 0, 0
    while True:
        if r < left + len(cur):
            return layer, r - left
        left += len(cur)
        cur = next_layer(cur)
        layer += 1


def ascend_replace(e, r, diff, tl, new_tail):
    res = []
    for i, col in enumerate(e):
        if tl == 0 and i == len(e) - 1:
            res.extend(new_tail)
        else:
            rc = []
            for j, (v, h) in enumerate(col):
                ntl = tl - 1 if (tl is not None and i == len(e) - 1 and j == len(col) - 1) else None
                rc.append((v + diff if v >= r else v, ascend_replace(h, r, diff, ntl, new_tail)))
            res.append(tuple(rc))
    return tuple(res)


def is_special(e, tl):
    if tl == 0:
        return False
    cur, left = e, 0
    for _ in range(tl):
        left += len(cur)
        cur = next_layer(cur)
    if len(cur[-1]) != 1:
        return False
    v, h = cur[-1][0]
    return len(h) == 0 and v == left - 1


def expand_special(e, tl, n):
    col = e[-1]
    v, h = col[-1]
    rc = list(col[:-1])
    if tl > 1:
        rc.append((v, expand_special(h, tl - 1, n)))
    else:
        ne = (v, h[:-1])
        if not rc:
            rc.append(ne)
        rc.extend([ne] * n)
    return e[:-1] + (tuple(rc),)


def appending_start(col_root, r, col_tail, t):
    hr = [to_height(h, r) for _, h in col_root]
    ht = [to_height(h, t) for _, h in col_tail[:-1]]
    ir = it = 0
    while ir != len(hr) and it != len(ht):
        x, y = hr[ir], ht[it]
        if x >= y:
            it += 1
        if x <= y:
            ir += 1
    return ir


class Undefined(Exception):
    pass


def FS(e, n):
    if len(e) == 0:
        return e
    tl = tail_layer(e)
    if tl < 0:
        return e[:-1]
    if is_special(e, tl):
        return expand_special(e, tl, n)
    t = tail(e, tl)
    r = root(e, tl)
    r_layer, ri = root_layer(e, r)
    e_root = skip(e, r_layer)
    col_root = e_root[ri]
    e_tail = skip(e_root, tl - r_layer)
    col_tail = e_tail[-1]
    app = appending_start(col_root, r, col_tail, t)
    new_tail = ()
    for j in range(n, 0, -1):
        new_col = list(ascend_replace((col_tail[:-1],), r, (j - 1) * (t - r), None, ())[0])
        if ri != len(e_root) - 1:
            nt1 = ascend_replace(e_root[ri + 1:], r, j * (t - r), tl - r_layer, new_tail)
            for k in range(app, len(col_root)):
                v, h = col_root[k]
                new_col.append((v, ascend_replace(h, r, j * (t - r), None, ())))
            new_tail = (tuple(new_col),) + nt1
        else:
            if app == len(col_root):
                raise Undefined(e)
            for k in range(app, len(col_root)):
                v, h = col_root[k]
                last = k == len(col_root) - 1
                new_col.append((v, ascend_replace(h, r, j * (t - r), tl - r_layer - 1 if last else None,
                                                  new_tail if last else ())))
            new_tail = (tuple(new_col),)
    return ascend_replace(e, 0, 0, tl, new_tail)


def seed(m):
    if m == 0:
        return ((),)
    col = ((m - 1, ()),)
    for i in range(m - 1, 0, -1):
        col = ((i - 1, (col,)),)
    return ((), col)


def word(e, d=0):
    out = []
    for col in e:
        if not col:
            out.append((2 * d, 0, 0))
            continue
        for k, (p, h) in enumerate(col):
            out.append((2 * d, 1, p) if k == 0 else (2 * d + 1, 0, p))
            out.extend(word(h, d + 1))
    return out


def mu(e):
    return len(word(e))


def size(e):
    """ordinary (column) plus entry vertices"""
    return sum(1 + sum(1 + size(h) for _, h in col) for col in e)


def show(e):
    def col(c):
        return '(' + ','.join(str(p + 1) + ('^' + show(h) if h else '') for p, h in c) + ')' if c else '(0)'
    return ''.join(col(c) for c in e)
