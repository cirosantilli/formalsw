"""
@formalsw: theorem spin_diverges (n : Int) :
  (FormalSW.PyAst.Calls.function ScalarLoopProgressAst.module "spin" [.int n]).Diverges
"""


def spin(n: int) -> int:
    while True:
        n += 1
