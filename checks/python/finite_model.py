"""Independent immutable model of paper §§1–3, written by Codex.

A forest is a tuple of columns, a column a tuple of (parent, height) entries.
Tuple ordering implements the paper's recursive lexicographic order. This is a
paper transcription, not copied TypeScript: step intentionally stays partial
on the empty forest. It is used only on nonempty V,I inputs by these workers.
"""

import itertools

EMPTY = ()


def h(forest, host):
    """Relative height key, using one fixed host throughout all descendants."""
    return tuple(
        tuple(((0, p) if p < host else (1, p - host), h(height, host))
              for p, height in column)
        for column in forest
    )


def shift(forest, root, delta):
    return tuple(
        tuple((p + (delta if p >= root else 0), shift(height, root, delta))
              for p, height in column)
        for column in forest
    )


def ar(forest, root, delta, depth, replacement):
    """Shift and replace one rightmost-route column; never shift replacement."""
    if depth == 0:
        return shift(forest[:-1], root, delta) + replacement
    parent, height = forest[-1][-1]
    changed_entry = (
        parent + (delta if parent >= root else 0),
        ar(height, root, delta, depth - 1, replacement),
    )
    changed_column = shift((forest[-1][:-1],), root, delta)[0] + (changed_entry,)
    return shift(forest[:-1], root, delta) + (changed_column,)


def seed(depth):
    forest = ()
    for parent in reversed(range(depth)):
        forest = (((parent, forest),),)
    return ((),) + forest


def scan(source, query):
    """Raw simultaneous-equality two-cursor scan; returns the source cursor."""
    i = j = 0
    while i < len(source) and j < len(query):
        x, y = source[i], query[j]
        i += x <= y
        j += x >= y
    return i


def reduce(letters):
    out = []
    for letter in letters:
        while out and out[-1] < letter:
            out.pop()
        out.append(letter)
    return tuple(out)


def step(forest, parameter):
    if not forest:
        raise ValueError("empty forest has no paper operation")
    if not forest[-1]:
        return forest[:-1]
    route, owners = [forest], []
    terminal = len(forest) - 1
    while route[-1][-1][-1][1]:
        owners.append(terminal)
        height = route[-1][-1][-1][1]
        route.append(height)
        terminal += len(height)
    query = route[-1][-1][:-1]
    root = route[-1][-1][-1][0]
    depth = len(route) - 1
    if depth > 0 and not query and root == owners[-1]:
        def special(current, remaining):
            column = current[-1]
            parent, height = column[-1]
            if remaining == 1:
                result = column[:-1] + ((parent, height[:-1]),) * (
                    parameter + (len(column) == 1)
                )
            else:
                result = column[:-1] + ((parent, special(height, remaining - 1)),)
            return current[:-1] + (result,)
        return special(forest, depth)

    for root_depth, current in enumerate(route):
        start = 0 if root_depth == 0 else owners[root_depth - 1] + 1
        if start <= root < start + len(current):
            break
    index = root - start
    root_column = current[index]
    delta = terminal - root
    cursor = scan(tuple(h(height, root) for _, height in root_column),
                  tuple(h(height, terminal) for _, height in query))
    unconsumed = root_column[cursor:]
    replacement = ()
    for phase in range(parameter, 0, -1):
        head = shift((query,), root, (phase - 1) * delta)[0] + tuple(
            (p, shift(height, root, phase * delta)) for p, height in unconsumed
        )
        if index < len(current) - 1:
            replacement = (head,) + ar(current[index + 1:], root, phase * delta,
                                       depth - root_depth, replacement)
        else:
            if not unconsumed:
                raise ValueError("empty owner-root suffix")
            last = (head[-1][0], ar(unconsumed[-1][1], root, phase * delta,
                                   depth - root_depth - 1, replacement))
            replacement = (head[:-1] + (last,),)
    return ar(forest, 0, 0, depth, replacement)


def word(forest, depth=0):
    out = []
    for column in forest:
        if not column:
            out.append((2 * depth, 0, 0))
        for index, (parent, height) in enumerate(column):
            out.append((2 * depth + (index > 0), int(index == 0), parent))
            out.extend(word(height, depth + 1))
    return tuple(out)


def mu(forest):
    return len(word(forest))


def prefix(forest, length):
    out = []
    for column in forest:
        if length <= 0:
            break
        if not column:
            out.append(())
            length -= 1
            continue
        retained = []
        for parent, height in column:
            if length <= 0:
                break
            length -= 1
            size = mu(height)
            retained.append((parent, prefix(height, min(length, size))))
            length -= size
        out.append(tuple(retained))
    return tuple(out)


def profile(forest):
    if not forest:
        return (-1, 0)
    depth = 0
    while forest[0][0][1]:
        forest = forest[0][0][1]
        depth += 1
    parent = forest[0][0][0]
    multiplicity = sum(1 for _ in itertools.takewhile(
        lambda entry: entry[0] == parent, forest[0]))
    return (depth, multiplicity)


def properties(forest, wanted="VIHASP"):
    """Report finite invariant failures; heights satisfying I have legal profiles."""
    errors = []

    def walk(current, stack, owners):
        for column in current:
            number = len(stack)
            visible = stack + [column]
            if "H" in wanted and tuple(sorted(column, reverse=True)) != column:
                errors.append(("H", number, column))
            boundary, start = (), number - 1
            for index, (parent, height) in enumerate(column):
                if "V" in wanted and not 0 <= parent < number:
                    errors.append(("V", number, parent))
                if "A" in wanted:
                    vertex, seen = start, []
                    while vertex != parent and 0 <= vertex < len(stack) and vertex not in seen:
                        seen.append(vertex)
                        source = tuple(h(child, vertex) for _, child in stack[vertex])
                        cursor = scan(source, boundary)
                        vertex = stack[vertex][cursor][0] if cursor < len(source) else -1
                    if vertex != parent:
                        errors.append(("A", number, index, parent, start, boundary, seen))
                for owner, upper in owners:
                    if parent == owner:
                        if "S" in wanted and not h(height, number) < h(upper, owner):
                            errors.append(("S", number, index, owner, height, upper))
                        if "P" in wanted and not profile(height) < profile(upper):
                            errors.append(("P", number, index, owner, height, upper))
                if height:
                    if "I" in wanted and any(not col or col[0][0] < number for col in height):
                        errors.append(("I", number, height))
                    # A failed I test suffices to reject a malformed height in these checks.
                    if all(height):
                        walk(height, visible, owners + [(number, height)])
                boundary = reduce(boundary + (h(height, number),))
                start = parent
            stack = visible

    walk(forest, [], [])
    return errors


def caps(forest):
    """All upward pointer-valid caps at all cuts, closing outer context."""
    def visit(current, start):
        for index, column in enumerate(current):
            number = start + index
            for cut in range(len(column) + 1):
                lower = column[cut][0] + 1 if cut < len(column) else 0
                for parent in range(lower, number):
                    yield current[:index] + (column[:cut] + ((parent, ()),),)
            for entry, (parent, height) in enumerate(column):
                for cap in visit(height, number + 1):
                    yield current[:index] + (column[:entry] + ((parent, cap),),)
    yield from visit(forest, 0)


def pretty(forest):
    return "".join("(" + ",".join(
        str(parent) + ("^" + pretty(height) if height else "")
        for parent, height in column) + ")" for column in forest)
