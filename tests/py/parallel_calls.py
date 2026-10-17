"""Different worker arguments and different functions share the same heap API.

An unmarked helper can be selected as a concurrent worker by its caller:
@formalsw: theorem module_worker_calls :
  CanReturn(Parallel([parallelFunction ParallelCallsAst.module "write_last" [.ref 0, .int 9]],
    { objects := [.array [.int 3, .int 4]] }), { objects := [.array [.int 3, .int 9]] })
"""


def write_last(data: list[int], value: int) -> None:
    data[-1] = value


def write_slot(index: int, data: list[int], value: int) -> None:
    """No mutex argument or special parameter order is required.

    @formalsw: theorem writes_the_requested_slot :
      CanReturn(Parallel([this_function [.int 1, .ref 0, .int 7]],
        { objects := [.array [.int 0, .int 0]] }), { objects := [.array [.int 0, .int 7]] })
    """
    data[index] = value


def write_other(data: list[int]) -> None:
    """A different one-argument worker can participate in the same run.

    @formalsw: theorem independent_writes :
      Ensures(Parallel([
        parallelFunction ParallelCallsAst.module "write_slot" [.int 1, .ref 0, .int 7],
        this_function [.ref 0]], { objects := [.array [.int 0, .int 0]] }),
        fun state => state.item 0 0 = some (.int 5) ∧ state.item 0 1 = some (.int 7))
    """
    data[0] = 5


class Box:
    def __init__(self):
        self.value = 0


def add_amount(box: Box, amount: int) -> None:
    """Plain objects may carry scalar fields as well as links.

    @formalsw: theorem updates_scalar_field :
      CanReturn(Parallel([this_function [.ref 0, .int 3]],
        { objects := [.object [("value", .int 4)]] }),
        { objects := [.object [("value", .int 7)]] })
    """
    snapshot = box.value
    box.value = snapshot + amount
