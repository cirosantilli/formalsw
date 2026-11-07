"""
Generate runtime BigO obligations with mandatory size-dependent primitive costs.
"""

import ast
import json
import re

from lang.py.global_inputs import annotation_kind, global_input_names
from lang.py.contracts import heap_input_name, reference_kind


def absolute_argument(node, name):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "abs" and len(node.args) == 1 and not node.keywords
            and isinstance(node.args[0], ast.Name) and node.args[0].id == name)


def integer_argument_measure(expression, integers):
    """Recognize an auxiliary integer's magnitude; other inputs stay quantified."""
    if len(integers) != 1:
        return None
    try:
        node = ast.parse(expression, mode="eval").body
    except SyntaxError:
        return None
    if (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and absolute_argument(node.left, integers[0].arg)
            and isinstance(node.right, ast.Constant) and type(node.right.value) is int
            and node.right.value == 1):
        return "input.2.natAbs + 1"
    return None


def nested_list_measure(expression, name, values):
    """Recognize row count or total rows and cells without evaluating Python."""
    try:
        node = ast.parse(expression, mode="eval").body
    except SyntaxError:
        node = None

    def length_of(node, variable):
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "len" and not node.keywords and len(node.args) == 1
                and isinstance(node.args[0], ast.Name) and node.args[0].id == variable)

    if length_of(node, name):
        return f"{values}.length"
    if (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and length_of(node.left, name) and isinstance(node.right, ast.Call)
            and isinstance(node.right.func, ast.Name) and node.right.func.id == "sum"
            and not node.right.keywords and len(node.right.args) == 1
            and isinstance(node.right.args[0], ast.GeneratorExp)):
        generator = node.right.args[0]
        if len(generator.generators) == 1:
            loop = generator.generators[0]
            if (isinstance(loop.target, ast.Name) and isinstance(loop.iter, ast.Name)
                    and loop.iter.id == name and not loop.ifs and not loop.is_async
                    and length_of(generator.elt, loop.target.id)):
                return f"FormalSW.PyAst.HeapCalls.Runtime.NestedIntList.size {values}"
    raise ValueError(f"runtime BigO nested lists require n = len({name}) or "
                     f"n = len({name}) + sum(len(row) for row in {name})")


def nested_list_input_family(function, arguments, args, conditions):
    """Use a canonical heap containing an outer list and one object per row."""
    lists = [argument for argument in arguments if annotation_kind(argument.annotation) == "list[list[int]]"]
    integers = [argument for argument in arguments if annotation_kind(argument.annotation) == "int"]
    if len(lists) != 1 or len(integers) > 1 or len(lists) + len(integers) != len(arguments):
        raise ValueError("runtime BigO nested inputs support one list[list[int]] and at most one int argument")
    if len(args) != 2:
        raise ValueError("runtime BigO nested lists require an explicit size binding")
    family = "List (List Int) × Int" if integers else "List (List Int)"
    values = "input.1" if integers else "input"
    size = integer_argument_measure(args[1], integers) or nested_list_measure(args[1], lists[0].arg, values)
    heap = f"(FormalSW.PyAst.HeapCalls.Runtime.NestedIntList.heap {values})"
    replacements = {lists[0].arg: "(0 : Nat)", heap_input_name(function): heap}
    if integers:
        replacements[integers[0].arg] = "input.2"
    predicate = " ∧ ".join(f"({condition})" for condition in conditions) or "True"
    predicate = re.sub(r"«([^»]+)»", lambda match: replacements.get(match[1], match[0]), predicate)
    inputs = ", ".join(".ref 0" if argument is lists[0] else ".scalar (.int input.2)"
                       for argument in arguments)
    return (
        f"(fun {'input' if integers else '_'} : {family} => [{inputs}]) (fun input : {family} => {heap})",
        f"(fun (input : {family}) => {predicate})" if conditions else "(fun _ => True)",
        f"(fun input : {family} => {size})",
    )


def integer_list_measure(expression, name, values):
    """Recognize list length or total integer encoding size without evaluating Python."""
    if re.fullmatch(rf"len\(\s*{re.escape(name)}\s*\)", expression):
        return f"{values}.length"
    try:
        node = ast.parse(expression, mode="eval").body
    except SyntaxError:
        node = None
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "sum" and len(node.args) == 1 and not node.keywords
            and isinstance(node.args[0], ast.GeneratorExp)):
        generator = node.args[0]
        if len(generator.generators) == 1:
            loop = generator.generators[0]
            element = generator.elt
            if (isinstance(loop.target, ast.Name) and isinstance(loop.iter, ast.Name)
                    and loop.iter.id == name and not loop.ifs and not loop.is_async
                    and isinstance(element, ast.BinOp) and isinstance(element.op, ast.Add)
                    and isinstance(element.left, ast.Constant) and type(element.left.value) is int
                    and element.left.value == 1 and isinstance(element.right, ast.Call)
                    and not element.right.args and not element.right.keywords
                    and isinstance(element.right.func, ast.Attribute)
                    and element.right.func.attr == "bit_length"
                    and isinstance(element.right.func.value, ast.Name)
                    and element.right.func.value.id == loop.target.id):
                return f"FormalSW.PyAst.IntegerListWork.size {values}"
    raise ValueError(f"runtime BigO list inputs require an explicit n = len({name}) or "
                     f"n = sum(1 + value.bit_length() for value in {name}) binding")


def list_input_family(function, arguments, args, conditions):
    """Quantify signed elements and an optional integer with an explicit size measure."""
    lists = [argument for argument in arguments if annotation_kind(argument.annotation) == "list[int]"]
    integers = [argument for argument in arguments if annotation_kind(argument.annotation) == "int"]
    if len(lists) != 1 or len(integers) > 1 or len(lists) + len(integers) != len(arguments):
        raise ValueError("runtime BigO list inputs support one list[int] and at most one int argument")
    name = lists[0].arg
    if len(args) != 2:
        raise ValueError(f"runtime BigO list inputs require an explicit n = len({name}) binding")
    family = "List Int × Int" if integers else "List Int"
    values = "input.1" if integers else "input"
    size = integer_argument_measure(args[1], integers) or integer_list_measure(args[1], name, values)
    heap = f"[.list ({values}.map (fun value => .scalar (.int value)))]"
    replacements = {name: "(0 : Nat)", heap_input_name(function): heap}
    if integers:
        replacements[integers[0].arg] = "input.2"
    predicate = " ∧ ".join(f"({condition})" for condition in conditions) or "True"
    # Substitute simultaneously: source argument names may occur in the new terms.
    predicate = re.sub(r"«([^»]+)»", lambda match: replacements.get(match[1], match[0]), predicate)
    inputs = ", ".join(".ref 0" if argument is lists[0] else ".scalar (.int input.2)"
                       for argument in arguments)
    return (
        f"(fun {'input' if integers else '_'} : {family} => [{inputs}]) (fun input : {family} => {heap})",
        f"(fun (input : {family}) => {predicate})" if conditions else "(fun _ => True)",
        f"(fun input : {family} => {size})",
    )


def integer_pair_input_family(function, arguments, args, conditions, heap):
    """Measure both signed inputs by magnitude, without executing size metadata."""
    names = [argument.arg for argument in arguments]
    expected = f"n = abs({names[0]}) + abs({names[1]}) + 1"
    if len(args) != 2:
        raise ValueError(f"runtime BigO integer pairs require {expected}")
    try:
        node = ast.parse(args[1], mode="eval").body
    except SyntaxError:
        node = None

    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and isinstance(node.right, ast.Constant) and type(node.right.value) is int
            and node.right.value == 1 and isinstance(node.left, ast.BinOp)
            and isinstance(node.left.op, ast.Add)
            and absolute_argument(node.left.left, names[0]) and absolute_argument(node.left.right, names[1])):
        raise ValueError(f"runtime BigO integer pairs require {expected}")
    replacements = {names[0]: "input.1", names[1]: "input.2", heap_input_name(function): "[]"}
    predicate = " ∧ ".join(f"({condition})" for condition in conditions) or "True"
    predicate = re.sub(r"«([^»]+)»", lambda match: replacements.get(match[1], match[0]), predicate)
    values = "[.scalar (.int input.1), .scalar (.int input.2)]" if heap else "[.int input.1, .int input.2]"
    inputs = f"(fun input : Int × Int => {values})" + (" (fun _ => [])" if heap else "")
    return (
        inputs,
        f"(fun input : Int × Int => {predicate})" if conditions else "(fun _ => True)",
        "(fun input : Int × Int => input.1.natAbs + input.2.natAbs + 1)",
    )


def global_heap_input_family(function, arguments, args, conditions, domains, globals_value):
    """
    Quantify the input, shared heap, and global values inside one runtime family.
    Independent references may alias; initializers never constrain entry state.
    """
    if len(arguments) != 1 or annotation_kind(arguments[0].annotation) != "int":
        raise ValueError("runtime BigO heap globals support one integer input on natural values")
    argument = arguments[0].arg
    if len(args) == 1:
        variable = argument
    elif len(args) == 2 and args[1].strip() == argument:
        variable = "n"
    else:
        raise ValueError("runtime BigO expects a bound and an optional n = input binding")
    globals_ = function.formalsw_globals
    if not heap_input_name(function) or globals_value is None:
        raise ValueError("runtime BigO heap globals require a reference global and a shared heap contract")
    scalar_types = {"int": "Int", "str": "String", "bytes": "List UInt8", "bool": "Bool"}
    types = ["Nat", "FormalSW.PyAst.Mutable.Heap"]
    for item in globals_:
        if reference_kind(item.kind):
            types.append("Nat")
        elif item.kind in scalar_types:
            types.append(scalar_types[item.kind])
        else:
            raise ValueError(f"runtime BigO does not support global type {item.kind}")
    family = " × ".join(types)
    names = [argument, heap_input_name(function), *global_input_names(function, globals_).values()]
    replacements = {}
    for index, name in enumerate(names):
        projection = "input" + ".2" * index + (".1" if index < len(names) - 1 else "")
        replacements[name] = f"({projection} : Int)" if index == 0 else projection

    def substitute(term):
        # Simultaneous substitution also handles source names such as `input`.
        return re.sub(r"«([^»]+)»", lambda match: replacements.get(match[1], match[0]), term)

    predicate = " ∧ ".join(f"({substitute(condition)})" for condition in (*domains, *conditions))
    parameter = variable if re.search(rf"\b{re.escape(variable)}\b", args[0]) else "_"
    return (
        f"(fun input : {family} => [.scalar (.int input.1)]) (fun input : {family} => input.2.1)",
        f"(fun input : {family} => {predicate})",
        f"(fun input : {family} => input.1) (fun {parameter} : Nat => {args[0]})",
        f"(globals := fun input : {family} => {substitute(globals_value)})",
    )


def runtime_complexity_type(namespace, function, args, conditions, *, heap=False,
                            memoized=False, globals_domain=(), globals_value=None):
    if memoized and heap:
        raise ValueError("runtime BigO does not yet model heap memoization")
    runtime = "MemoCalls" if memoized else "HeapCalls" if heap else "Calls"
    cache_names = f" {namespace}.module.memoizedFunctions" if memoized else ""
    args = list(args)
    arithmetic = "fixed"
    if args and args[-1].startswith("arithmetic="):
        arithmetic = args.pop().removeprefix("arithmetic=")
    if arithmetic not in {"fixed", "bits"}:
        raise ValueError("BigO arithmetic must be fixed or bits")
    arguments = [*function.args.posonlyargs, *function.args.args]
    if function.args.vararg or function.args.kwarg or function.args.kwonlyargs:
        raise ValueError("runtime BigO requires positional inputs")
    if any(re.search(r"\bcost\s*=", argument) for argument in args):
        raise ValueError("runtime BigO uses operation-specific costs; cost=steps and partial resource models are not supported")
    if getattr(function, "formalsw_globals", ()):
        if not heap:
            raise ValueError("runtime BigO global inputs require the heap interpreter")
        inputs, domain, measure, state = global_heap_input_family(
            function, arguments, args, conditions, globals_domain, globals_value)
        return (
            f"FormalSW.PyAst.HeapCalls.Runtime.IsBigO .{'word' if arithmetic == 'fixed' else 'bits'} {namespace}.module {json.dumps(function.name)}\n"
            f"  {inputs}\n"
            f"  {domain} {measure}\n"
            f"  {state}"
        )
    kinds = {annotation_kind(argument.annotation) for argument in arguments}
    if kinds & {"list[int]", "list[list[int]]"}:
        if not heap:
            raise ValueError("runtime BigO list inputs require the heap interpreter")
        family = nested_list_input_family if "list[list[int]]" in kinds else list_input_family
        inputs, domain, size = family(function, arguments, args, conditions)
        parameter = "n" if re.search(r"\bn\b", args[0]) else "_"
        return (
            f"FormalSW.PyAst.HeapCalls.Runtime.IsBigO .{'word' if arithmetic == 'fixed' else 'bits'} {namespace}.module {json.dumps(function.name)}\n"
            f"  {inputs}\n"
            f"  {domain} {size} (fun {parameter} : Nat => {args[0]})"
        )
    if len(arguments) == 2 and kinds == {"int"}:
        inputs, domain, size = integer_pair_input_family(function, arguments, args, conditions, heap)
        parameter = "n" if re.search(r"\bn\b", args[0]) else "_"
        return (
            f"FormalSW.PyAst.{runtime}.Runtime.IsBigO .{'word' if arithmetic == 'fixed' else 'bits'} {namespace}.module{cache_names} {json.dumps(function.name)}\n"
            f"  {inputs}\n"
            f"  {domain} {size} (fun {parameter} : Nat => {args[0]})"
        )
    if len(arguments) != 1 or annotation_kind(arguments[0].annotation) != "int":
        raise ValueError("runtime BigO supports one integer input on natural values, two signed integers, or a list with an optional int")
    argument = arguments[0].arg
    if len(args) == 1:
        variable = argument
    elif len(args) == 2 and args[1].strip() == argument:
        variable = "n"
    else:
        raise ValueError("runtime BigO expects a bound and an optional n = input binding")
    predicate = " ∧ ".join(f"({condition})" for condition in conditions) or "True"
    predicate = predicate.replace(f"«{argument}»", "(input : Int)")
    domain = f"(fun (input : Nat) => {predicate})" if conditions else "(fun _ => True)"
    parameter = variable if re.search(rf"\b{re.escape(variable)}\b", args[0]) else "_"
    inputs = "(fun input : Nat => [.scalar (.int input)]) (fun _ => [])" if heap else "(fun input : Nat => [.int input])"
    return (
        f"FormalSW.PyAst.{runtime}.Runtime.IsBigO .{'word' if arithmetic == 'fixed' else 'bits'} {namespace}.module{cache_names} {json.dumps(function.name)}\n"
        f"  {inputs}\n"
        f"  {domain} id (fun {parameter} : Nat => {args[0]})"
    )
