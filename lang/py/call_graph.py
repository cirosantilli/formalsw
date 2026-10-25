"""Direct calls and named callbacks that may execute in a function body."""
import ast


def call_targets(node):
    if not isinstance(node, ast.Call):
        return ()
    names = [node.func.id] if isinstance(node.func, ast.Name) else []
    names.extend(keyword.value.id for keyword in node.keywords
                 if keyword.arg == 'key' and isinstance(keyword.value, ast.Name))
    return names
