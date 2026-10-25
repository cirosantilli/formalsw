"""
Lower a guarded nonescaping closure group to private shared list cells.

The ordinary local-functions lowering remains the preferred path. This path
supports recursive/sibling direct calls and initialized owner data cells; it
does not represent general function values or escaping closures.
"""
import ast
import copy
import symtable

from lang.py.imports import bindings


def lower_closure_cells(module, outer, children, postponed, occupied):
    """Return fresh helpers and an owner body, or reject without changing inputs."""
    def reject(message):
        raise ValueError('local closure cells: ' + message)

    names = {child.name for child in children}
    if len(names) != len(children):
        reject('definitions must have distinct names')
    forbidden = (ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda, ast.Global,
                 ast.Yield, ast.YieldFrom, ast.Await, ast.NamedExpr, ast.Delete)
    if any(isinstance(node, forbidden) for node in ast.walk(outer)):
        reject('unsupported scope mutation, suspension, deletion, or nested scope')
    if any(isinstance(node, ast.FunctionDef) and node is not outer and node not in children
           for node in ast.walk(outer)):
        reject('definitions must be directly in the enclosing function body')
    reflective = {'eval', 'exec', 'locals', 'globals', 'vars', '__import__'}
    if any(isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
           and node.func.id in reflective for node in ast.walk(outer)):
        reject('dynamic scope inspection is unsupported')

    parameters = {arg.arg for arg in outer.args.posonlyargs + outer.args.args + outer.args.kwonlyargs}
    if names & parameters:
        reject('function names must not shadow owner parameters')
    for child in children:
        args = child.args
        if (child.decorator_list or args.defaults or args.kw_defaults or args.posonlyargs
                or args.kwonlyargs or args.vararg or args.kwarg or getattr(child, 'type_params', [])):
            reject('decorators, defaults, and non-positional parameters are unsupported')
        if not postponed and (child.returns is not None or any(arg.annotation for arg in args.args)):
            reject('annotated definitions require from __future__ import annotations')
        if '@formalsw' in (ast.get_docstring(child, clean=False) or ''):
            reject('put contracts on the enclosing function')

    table = next(scope for scope in symtable.symtable(ast.unparse(outer), '<closure-cells>', 'exec').get_children()
                 if scope.get_type() == 'function' and scope.get_name() == outer.name)
    # Comprehensions can have the same synthetic scope name as a real local
    # function (for example genexpr). Resolve the namespace of its binding.
    scopes = {}
    for child in children:
        namespaces = table.lookup(child.name).get_namespaces()
        if (len(namespaces) != 1 or namespaces[0].get_type() != 'function'
                or namespaces[0].get_name() != child.name):
            reject('local function bindings need one unambiguous lexical namespace')
        scopes[child.name] = namespaces[0]
    if set(scopes) != names:
        reject('unsupported lexical function scopes')
    free = {name: set(scopes[name].get_frees()) for name in names}
    for child in children:
        if names & set(scopes[child.name].get_locals()):
            reject('group function names must not be shadowed in a child')
        if names & set(scopes[child.name].get_nonlocals()):
            reject('nonlocal function bindings must not be rebound')

    group_edges = {name: free[name] & names for name in names}
    required_functions = {name: {name} | group_edges[name] for name in names}
    all_data = set().union(*(free[name] - names for name in names))
    for name in all_data:
        if not table.lookup(name).is_local():
            reject('captures must resolve to owner data bindings')

    # A direct alias to a uniquely protected module function may be specialized.
    # Every other function-valued capture stays explicitly unsupported.
    initializers = {}
    for statement in outer.body:
        if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
            initializers.setdefault(statement.targets[0].id, (statement, statement.value))
        elif isinstance(statement, ast.AnnAssign) and statement.value is not None and isinstance(statement.target, ast.Name):
            initializers.setdefault(statement.target.id, (statement, statement.value))
    module_functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    aliases = {}
    for name in all_data:
        value = initializers.get(name, (None, None))[1]
        called = any(isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == name
                     for child in children if name in free[child.name] for node in ast.walk(child))
        module_function_value = isinstance(value, ast.Name) and value.id in module_functions
        if not called and not module_function_value:
            continue
        if not module_function_value or not table.lookup(value.id).is_global():
            reject('captured callable values require a protected module-function alias')
        target = module_functions[value.id]
        if bindings(module, value.id) != [target] or target.decorator_list:
            reject('captured module-function aliases require a unique stable undecorated binding')
        if any(isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del))
               and isinstance(node.value, ast.Name) and node.value.id == value.id for node in ast.walk(module)):
            reject('captured module-function aliases must not have mutated attributes')
        if any(isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
               and node.func.id in {'setattr', 'delattr', 'eval', 'exec', 'globals', 'locals', 'vars', '__import__'}
               for node in ast.walk(module)):
            reject('captured module-function aliases do not support dynamic rebinding or inspection')
        if any(value.id in set(scopes[child.name].get_locals()) for child in children):
            reject('specialized module target must not be shadowed in a child')
        if any(isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del))
               and node.id == value.id or isinstance(node, ast.arg) and node.arg == value.id
               for node in ast.walk(outer)):
            reject('specialized module target must not be shadowed in a lexical or comprehension scope')
        if any(name in set(scopes[child.name].get_locals()) for child in children):
            reject('captured callable alias must not be shadowed in a child')
        aliases[name] = value.id

    if set(aliases) & parameters:
        reject('protected callable aliases must not be owner parameters')

    data = all_data - set(aliases)
    direct_data = {name: free[name] & data for name in names}
    required_data = {name: set(direct_data[name]) for name in names}
    changed = True
    while changed:
        changed = False
        for name in names:
            functions = set(required_functions[name])
            cells = set(required_data[name])
            for sibling in group_edges[name]:
                functions.update(required_functions[sibling])
                cells.update(required_data[sibling])
            if functions != required_functions[name] or cells != required_data[name]:
                required_functions[name] = functions
                required_data[name] = cells
                changed = True

    # Validate nonescaping function names and aliases before emitting any syntax.
    protected = names | set(aliases)

    def implicit_bindings(node):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            return {alias.asname or alias.name.split('.')[0] for alias in node.names}
        if isinstance(node, ast.ExceptHandler):
            return {node.name} if node.name else set()
        if isinstance(node, (ast.MatchAs, ast.MatchStar)):
            return {node.name} if node.name else set()
        if isinstance(node, ast.MatchMapping):
            return {node.rest} if node.rest else set()
        return set()

    parents = {id(child): node for node in ast.walk(outer) for child in ast.iter_child_nodes(node)}
    alias_initializers = {id(initializers[name][0]): name for name in aliases}
    for node in ast.walk(outer):
        if implicit_bindings(node) & protected:
            reject('local function/alias bindings must not be replaced by imports, handlers, or patterns')
        if isinstance(node, ast.Name) and node.id in protected:
            parent = parents.get(id(node))
            if (node.id in aliases and isinstance(node.ctx, ast.Store)
                    and id(parent) in alias_initializers and alias_initializers[id(parent)] == node.id):
                continue
            if (not isinstance(node.ctx, ast.Load) or not isinstance(parent, ast.Call)
                    or parent.func is not node):
                reject('local function/alias values must not escape or be rebound')
            if parent.keywords or any(isinstance(arg, ast.Starred) for arg in parent.args):
                reject('local function/alias calls require ordinary positional arguments')

    for child in children:
        for node in ast.walk(child):
            if isinstance(node, ast.Nonlocal) and not set(node.names) <= direct_data[child.name]:
                reject('nonlocal declarations require supported owner data cells')
    if any(isinstance(node, ast.Nonlocal) for statement in outer.body if statement not in children for node in ast.walk(statement)):
        reject('the owner cannot declare nonlocal bindings')

    # Captured writes are deliberately limited to simple name stores. Subscript
    # mutation of an object stored in a cell is an ordinary supported operation.
    allowed_stores = set()
    for node in ast.walk(outer):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            allowed_stores.add(id(node.targets[0]))
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)) and isinstance(node.target, ast.Name):
            allowed_stores.add(id(node.target))
    # Child locals with a captured spelling are not owner-cell stores.
    def bound_in_target(target):
        return {node.id for node in ast.walk(target) if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)}

    class ValidateStores(ast.NodeVisitor):
        def __init__(self, active):
            self.active = active
            self.shadowed = set()

        def visit_FunctionDef(self, node):
            return

        def generic_visit(self, node):
            if implicit_bindings(node) & (self.active - self.shadowed):
                reject('captured bindings cannot be import, exception, or pattern targets')
            return super().generic_visit(node)

        def visit_Name(self, node):
            if (node.id in self.active - self.shadowed and isinstance(node.ctx, ast.Store)
                    and id(node) not in allowed_stores):
                reject('captured bindings support only simple assignments and augmented assignments')

        def comprehension(self, node):
            self.visit(node.generators[0].iter)
            previous = self.shadowed
            targets = set().union(*(bound_in_target(gen.target) for gen in node.generators))
            if targets & protected:
                reject('comprehension targets must not shadow group function/alias names')
            self.shadowed = previous | targets
            for index, gen in enumerate(node.generators):
                if gen.is_async:
                    reject('asynchronous comprehensions are unsupported')
                self.visit(gen.target)
                if index:
                    self.visit(gen.iter)
                for condition in gen.ifs:
                    self.visit(condition)
            for field in ('elt', 'key', 'value'):
                if hasattr(node, field):
                    self.visit(getattr(node, field))
            self.shadowed = previous

        visit_ListComp = comprehension
        visit_SetComp = comprehension
        visit_DictComp = comprehension
        visit_GeneratorExp = comprehension

    validator = ValidateStores(data)
    for statement in outer.body:
        if statement not in children:
            validator.visit(statement)
    for child in children:
        validator = ValidateStores(direct_data[child.name])
        for statement in child.body:
            validator.visit(statement)

    available = set(parameters)
    defined = set()
    first_bindings = {}
    for statement in outer.body:
        if statement in children:
            if not required_data[statement.name] <= available:
                reject('captured data must be initialized before its local definition')
            if not (free[statement.name] & set(aliases)) <= available:
                reject('captured callable aliases must be initialized before their local definition')
            defined.add(statement.name)
            continue
        newly_bound = None
        if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
            newly_bound = statement.targets[0].id
        elif isinstance(statement, ast.AnnAssign) and statement.value is not None and isinstance(statement.target, ast.Name):
            newly_bound = statement.target.id
        for node in ast.walk(statement):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                name = node.func.id
                if name in names and not required_functions[name] <= defined:
                    reject('calls must follow every transitively required sibling definition')
                if name in aliases and name not in available:
                    reject('calls must follow their protected alias initialization')
            if (isinstance(node, ast.Name) and node.id in data and node.id not in available
                    and not (isinstance(node.ctx, ast.Store) and node.id == newly_bound)):
                reject('captured data cannot be read or written before initialization')
        if newly_bound is not None:
            if newly_bound in data and newly_bound not in available:
                first_bindings[id(statement)] = newly_bound
            available.add(newly_bound)
    if not data <= available:
        reject('all captured data requires definite owner initialization')

    reserved = set(occupied)
    reserved.update(node.arg for node in ast.walk(module) if isinstance(node, ast.arg))
    reserved.update(alias.asname or alias.name.split('.')[0] for node in ast.walk(module)
                    if isinstance(node, (ast.Import, ast.ImportFrom)) for alias in node.names)
    reserved.update(node.name for node in ast.walk(module) if isinstance(node, ast.ExceptHandler) and node.name)
    for node in ast.walk(module):
        if isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name:
            reserved.add(node.name)
        elif isinstance(node, ast.MatchMapping) and node.rest:
            reserved.add(node.rest)
        elif isinstance(node, (ast.Nonlocal, ast.Global)):
            reserved.update(node.names)

    def fresh(proposed):
        while proposed in reserved:
            proposed += '_'
        reserved.add(proposed)
        return proposed

    cell_names = {name: fresh(f'__formalsw_cell_{outer.name}_{name}') for name in sorted(data)}
    lifted_names = {child.name: fresh(f'__formalsw_local_{outer.name}_{child.name}') for child in children}
    capture_order = {name: sorted(required_data[name]) for name in names}

    class Rewrite(ast.NodeTransformer):
        def __init__(self, active_data, active_functions, active_aliases, owner=False):
            self.active_data = active_data
            self.active_functions = active_functions
            self.active_aliases = active_aliases
            self.owner = owner
            self.shadowed = set()

        def visit_FunctionDef(self, node):
            return None if self.owner and node in children else node

        def visit_Nonlocal(self, node):
            return None

        def visit_Name(self, node):
            if node.id in self.active_data - self.shadowed:
                result = ast.Subscript(value=ast.Name(id=cell_names[node.id], ctx=ast.Load()),
                    slice=ast.Constant(value=0), ctx=copy.deepcopy(node.ctx))
                return ast.copy_location(result, node)
            return node

        def visit_Call(self, node):
            original = node.func.id if isinstance(node.func, ast.Name) else None
            self.generic_visit(node)
            if original in self.active_functions and original not in self.shadowed:
                node.func = ast.copy_location(ast.Name(id=lifted_names[original], ctx=ast.Load()), node.func)
                node.args.extend(ast.copy_location(ast.Name(id=cell_names[name], ctx=ast.Load()), node)
                                 for name in capture_order[original])
            elif original in self.active_aliases and original not in self.shadowed:
                node.func = ast.copy_location(ast.Name(id=aliases[original], ctx=ast.Load()), node.func)
            return node

        def visit_Assign(self, node):
            if self.owner and id(node) in alias_initializers:
                return None
            if self.owner and id(node) in first_bindings:
                name = first_bindings[id(node)]
                result = ast.Assign(targets=[ast.Name(id=cell_names[name], ctx=ast.Store())],
                    value=ast.List(elts=[self.visit(node.value)], ctx=ast.Load()))
                result.formalsw_closure_cell = name
                return ast.copy_location(result, node)
            return self.generic_visit(node)

        def visit_AnnAssign(self, node):
            if self.owner and id(node) in alias_initializers:
                return None
            if self.owner and id(node) in first_bindings:
                name = first_bindings[id(node)]
                result = ast.Assign(targets=[ast.Name(id=cell_names[name], ctx=ast.Store())],
                    value=ast.List(elts=[self.visit(node.value)], ctx=ast.Load()))
                result.formalsw_closure_cell = name
                return ast.copy_location(result, node)
            if isinstance(node.target, ast.Name) and node.target.id in self.active_data - self.shadowed:
                # A function-local annotation is not evaluated. Keep the actual
                # value assignment while avoiding a malformed simple AnnAssign
                # whose lowered target would no longer be a Name.
                if node.value is None:
                    return ast.copy_location(ast.Pass(), node)
                return ast.copy_location(ast.Assign(targets=[self.visit(node.target)],
                    value=self.visit(node.value)), node)
            # Local annotations are not evaluated. Keep their original syntax.
            node.target = self.visit(node.target)
            if node.value is not None:
                node.value = self.visit(node.value)
            return node

        def comprehension(self, node):
            node.generators[0].iter = self.visit(node.generators[0].iter)
            previous = self.shadowed
            self.shadowed = previous | set().union(*(bound_in_target(gen.target) for gen in node.generators))
            for index, gen in enumerate(node.generators):
                gen.target = self.visit(gen.target)
                if index:
                    gen.iter = self.visit(gen.iter)
                gen.ifs = [self.visit(condition) for condition in gen.ifs]
            for field in ('elt', 'key', 'value'):
                if hasattr(node, field):
                    setattr(node, field, self.visit(getattr(node, field)))
            self.shadowed = previous
            return node

        visit_ListComp = comprehension
        visit_SetComp = comprehension
        visit_DictComp = comprehension
        visit_GeneratorExp = comprehension

    # Rewrite copies while preserving identity maps used only for the owner's
    # initializer/definition positions; original AST objects remain untouched.
    owner_copy = copy.deepcopy(outer)
    copy_children = [node for node in owner_copy.body if isinstance(node, ast.FunctionDef)]
    owner_first = {id(copied): first_bindings[id(original)] for original, copied in zip(outer.body, owner_copy.body)
                   if id(original) in first_bindings}
    owner_aliases = {id(copied): alias_initializers[id(original)] for original, copied in zip(outer.body, owner_copy.body)
                     if id(original) in alias_initializers}
    children_original = children
    children = copy_children
    first_bindings = owner_first
    alias_initializers = owner_aliases
    rewritten = Rewrite(data, names, set(aliases), owner=True)
    body = []
    for statement in owner_copy.body:
        result = rewritten.visit(statement)
        if result is not None:
            body.append(result)
    parameter_cells = []
    for name in sorted(data & parameters):
        statement = ast.Assign(targets=[ast.Name(id=cell_names[name], ctx=ast.Store())],
            value=ast.List(elts=[ast.Name(id=name, ctx=ast.Load())], ctx=ast.Load()))
        statement.formalsw_closure_cell = name
        parameter_cells.append(ast.copy_location(statement, outer))
    insert = 1 if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str) else 0
    body[insert:insert] = parameter_cells
    if not body:
        body = [ast.copy_location(ast.Pass(), outer)]

    lifted = []
    for original in children_original:
        function = copy.deepcopy(original)
        function.name = lifted_names[original.name]
        function.formalsw_markers = []
        function.formalsw_imported = True
        function.formalsw_closure_cells = tuple(cell_names[name] for name in capture_order[original.name])
        function.formalsw_callback_bindings = tuple(dict.fromkeys(
            [*getattr(function, 'formalsw_callback_bindings', ()), *(aliases[name] for name in sorted(free[original.name] & set(aliases)))]))
        for name in capture_order[original.name]:
            argument = ast.arg(arg=cell_names[name], annotation=None)
            argument.formalsw_capture = True
            function.args.args.append(ast.copy_location(argument, original))
        transform = Rewrite(direct_data[original.name], group_edges[original.name], free[original.name] & set(aliases))
        function.body = [updated for statement in function.body if (updated := transform.visit(statement)) is not None]
        if not function.body:
            function.body = [ast.copy_location(ast.Pass(), original)]
        lifted.append(function)
    # The owner also needs the identity guard for aliases used directly there.
    callback_guards = tuple(dict.fromkeys([*getattr(outer, 'formalsw_callback_bindings', ()), *aliases.values()]))
    for function in lifted:
        function.formalsw_callback_bindings = tuple(dict.fromkeys([*function.formalsw_callback_bindings, *callback_guards]))
    # Return owner guard metadata separately: the dispatcher installs it only on success.
    occupied.update(reserved)
    return lifted, body, callback_guards
