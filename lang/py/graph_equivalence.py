"""Compare encoded Python object graphs. This function is interpreted by Lean.

Snapshots are scalars or [roots, nodes]. An edge is [scalar_type, value] or
["ref", node_index]; a node is [runtime_type, ordered_labels, edges].
The snapshot adapter is in object_snapshot.py, outside the interpreted subset.
"""


def same_snapshot(left, right):
    # Scalars take this path without allocating or traversing a graph.
    if type(left) != type(right):
        return False
    if type(left) != list:
        return left == right

    pending_left = left[0]
    pending_right = right[0]
    if len(pending_left) != len(pending_right):
        return False
    seen_left = []
    seen_right = []
    cursor = 0
    while cursor < len(pending_left):
        a = pending_left[cursor]
        b = pending_right[cursor]
        if a[0] != b[0]:
            return False
        if a[0] == "ref":
            found = False
            index = 0
            while index < len(seen_left):
                if a[1] == seen_left[index]:
                    if b[1] != seen_right[index]:
                        return False
                    found = True
                else:
                    if b[1] == seen_right[index]:
                        return False
                index = index + 1
            if not found:
                seen_left = seen_left + [a[1]]
                seen_right = seen_right + [b[1]]
                node_left = left[1][a[1]]
                node_right = right[1][b[1]]
                if node_left[0] != node_right[0]:
                    return False
                if node_left[1] != node_right[1]:
                    return False
                if len(node_left[2]) != len(node_right[2]):
                    return False
                pending_left = pending_left + node_left[2]
                pending_right = pending_right + node_right[2]
        else:
            if a[1] != b[1]:
                return False
        cursor = cursor + 1
    return True
