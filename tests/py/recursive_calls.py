def countdown(n: int) -> int:
    """@formalsw: theorem returns (n : Nat) : Returns(this_function(n))"""
    if n == 0:
        return 0
    return countdown(n - 1) + 1


def delegated(n: int) -> int:
    """@formalsw: theorem equiv (n : Nat) :
      (this_function n).Equiv
        (FormalSW.PyAst.Calls.function RecursiveCallsAst.module "countdown" [.int n])
    """
    return countdown(n)


def choose(n: int) -> int:
    """@formalsw: Returns"""
    return 7 if n == 0 or True else countdown(-1)


def subtract(a: int, b: int) -> int:
    return a - b


def nested(n: int) -> int:
    """@formalsw: Returns"""
    return subtract(subtract(n, 1), subtract(2, 3))
