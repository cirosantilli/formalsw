"""
Generate runtime BigO obligations with mandatory size-dependent primitive costs.
"""

import json
import re

from lang.py.global_inputs import annotation_kind
from lang.py.contracts import heap_input_name


def list_input_family(function, arguments, args, conditions):
    """Quantify arbitrary signed elements and window sizes, measuring list length."""
    lists = [argument for argument in arguments if annotation_kind(argument.annotation) == "list[int]"]
    integers = [argument for argument in arguments if annotation_kind(argument.annotation) == "int"]
    if len(lists) != 1 or len(integers) > 1 or len(lists) + len(integers) != len(arguments):
        raise ValueError("runtime BigO list inputs support one list[int] and at most one int argument")
    name = lists[0].arg
    if len(args) != 2 or re.fullmatch(rf"len\(\s*{re.escape(name)}\s*\)", args[1]) is None:
        raise ValueError(f"runtime BigO list inputs require an explicit n = len({name}) binding")
    family = "List Int × Int" if integers else "List Int"
    values = "input.1" if integers else "input"
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
        f"(fun input : {family} => {values}.length)",
    )


def runtime_complexity_type(namespace, function, args, conditions, *, heap=False):
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
    if any(annotation_kind(argument.annotation) == "list[int]" for argument in arguments):
        if not heap:
            raise ValueError("runtime BigO list inputs require the heap interpreter")
        inputs, domain, size = list_input_family(function, arguments, args, conditions)
        parameter = "n" if re.search(r"\bn\b", args[0]) else "_"
        return (
            f"FormalSW.PyAst.HeapCalls.Runtime.IsBigO .{'word' if arithmetic == 'fixed' else 'bits'} {namespace}.module {json.dumps(function.name)}\n"
            f"  {inputs}\n"
            f"  {domain} {size} (fun {parameter} : Nat => {args[0]})"
        )
    if len(arguments) != 1 or annotation_kind(arguments[0].annotation) != "int":
        raise ValueError("runtime BigO supports one integer input on natural values, or a list[int] with an optional int")
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
    runtime = "HeapCalls" if heap else "Calls"
    inputs = "(fun input : Nat => [.scalar (.int input)]) (fun _ => [])" if heap else "(fun input : Nat => [.int input])"
    return (
        f"FormalSW.PyAst.{runtime}.Runtime.IsBigO .{'word' if arithmetic == 'fixed' else 'bits'} {namespace}.module {json.dumps(function.name)}\n"
        f"  {inputs}\n"
        f"  {domain} id (fun {parameter} : Nat => {args[0]})"
    )
