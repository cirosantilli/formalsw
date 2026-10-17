"""Explicit observation boundary for graph_equivalence.same_snapshot.

Exact int/bool/str/bytes/None, list/tuple/dict/bytearray, and ordinary instances are supported.
Never invoke user equality or getters. Unsupported objects raise TypeError.
The adapter is executable Python; it is not a model of arbitrary CPython heaps.
"""

from lang.py.graph_equivalence import same_snapshot
import types


# Retain classes so saved snapshots cannot confuse a reused CPython id with the
# original class. Keys are builtin integers; metaclass hash/equality never runs.
_classes = {}


def _type_identity(cls):
    address = id(cls)
    _classes[address] = cls
    return address


def _namespace(cls):
    # Calling type.__getattribute__ would still invoke metaclass descriptors.
    return type.__dict__["__dict__"].__get__(cls)


def _mro(cls):
    return type.__dict__["__mro__"].__get__(cls)


def _scalar(value):
    cls = type(value)
    return cls is int or cls is bool or cls is str or cls is bytes or cls is type(None)


def snapshot_roots(roots):
    """Observe roots together, preserving cross-root aliases and dictionary order."""
    nodes = []
    objects = []  # Retain objects so ids cannot be reused during traversal.
    addresses = {}

    def edge(value):
        if _scalar(value):
            return [type(value).__name__, value]
        address = id(value)
        if address not in addresses:
            addresses[address] = len(objects)
            objects.append(value)
        return ["ref", addresses[address]]

    root_edges = [edge(value) for value in roots]
    cursor = 0
    while cursor < len(objects):
        value = objects[cursor]
        cls = type(value)
        if cls is list or cls is tuple or cls is bytearray:
            node = [cls.__name__, [], [edge(item) for item in value]]
        elif cls is dict:
            children = []
            for key, item in value.items():
                children.extend([edge(key), edge(item)])
            node = ["dict", [], children]
        else:
            # Inspect type dictionaries directly; do not call metaclass hooks.
            mro = _mro(cls)
            if len(mro) != 2 or mro[1] is not object:
                raise TypeError("unsupported snapshot: inherited or builtin object")
            namespace = _namespace(cls)
            if any(name in namespace for name in
                   ("__slots__", "__getattribute__", "__getattr__")):
                raise TypeError("unsupported snapshot: slots or custom attribute access")
            for name, member in namespace.items():
                if name not in ("__dict__", "__weakref__") and any(
                    "__get__" in _namespace(base)
                    for base in _mro(type(member))
                ):
                    # Ordinary methods are never invoked by this observation.
                    if type(member) is not types.FunctionType:
                        raise TypeError("unsupported snapshot: attribute descriptor")
            descriptor = namespace.get("__dict__")
            if type(descriptor) is not types.GetSetDescriptorType or descriptor.__objclass__ is not cls:
                raise TypeError("unsupported snapshot: nonstandard instance dictionary")
            fields = object.__getattribute__(value, "__dict__")
            if type(fields) is not dict or any(type(key) is not str for key in fields):
                raise TypeError("unsupported snapshot: nonstandard instance fields")
            # Class identity, not merely a potentially duplicated class name.
            node = [["object", _type_identity(cls)], list(fields), [edge(v) for v in fields.values()]]
        nodes.append(node)
        cursor += 1
    return [root_edges, nodes]


def snapshot(value):
    """Scalars need no graph allocation; encode other reachable state."""
    if _scalar(value):
        return value
    return snapshot_roots([value])


def equivalent(left, right):
    """Stored-state equivalence, independent of overridable Python __eq__."""
    return same_snapshot(snapshot(left), snapshot(right))


def equivalent_roots(left, right):
    """Include result, caller-owned inputs, and relevant globals in root order."""
    return same_snapshot(snapshot_roots(left), snapshot_roots(right))
