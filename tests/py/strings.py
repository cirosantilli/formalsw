def stringify(n: int) -> str:
    """
    @formalsw: Returns
    """
    return str(n)


def reverse(s: str) -> str:
    """
    @formalsw: Returns
    """
    return s[::-1]


def identity(s: str) -> str:
    return s


def double_reverse(s: str) -> str:
    """
    @formalsw: Equiv(identity)
    """
    return reverse(reverse(s))


def palindrome(n: int) -> bool:
    """
    @formalsw: Returns
    """
    s = str(n)
    return s == s[::-1]


def unicode(n: int) -> str:
    """
    @formalsw: Returns
    """
    s = 'Aé😺Z'
    return s[True] + s[-2] + s[3:0:-2] + s[None:None:-1]


def scalar_conversions(n: int) -> str:
    """
    @formalsw: Returns
    """
    return str() + str(True) + str(False) + str(None) + str('x')


def minus_one(n: int) -> int:
    return -1


def helper_bound(s: str) -> str:
    """
    @formalsw: Equiv(reverse)
    """
    return s[::minus_one(0)]


def bad_step(n: int) -> str:
    """
    @formalsw: Throws
    """
    return 'text'[::False]


def bad_index(n: int) -> str:
    """
    @formalsw: Throws
    """
    return ''[0]


def ordered_bounds(n: int) -> str:
    """
    @formalsw: Throws
    """
    return 'text'['wrong':1 // 0:0]


def step_before_bound(n: int) -> str:
    """
    @formalsw: Throws
    """
    return 'text'['wrong'::0]


def receiver_before_bounds(n: int) -> str:
    """
    @formalsw: Throws
    """
    return (n // 0)[::0]


if __name__ == '__main__':
    for n in (-123, -1, 0, 1, 11, 121, 123, 10 ** 100):
        assert stringify(n) == str(n)
        assert palindrome(n) == (str(n) == str(n)[::-1])
        assert unicode(n) == 'é😺ZéZ😺éA'
        assert scalar_conversions(n) == 'TrueFalseNonex'
    for s in ('', 'x', 'Aé😺Z', 'racecar', 'e\u0301'):
        assert reverse(s) == s[::-1]
        assert double_reverse(s) == s
        assert helper_bound(s) == reverse(s)
    for function, error in ((bad_step, ValueError), (bad_index, IndexError),
                            (ordered_bounds, ZeroDivisionError), (step_before_bound, ValueError),
                            (receiver_before_bounds, ZeroDivisionError)):
        try:
            function(0)
        except error:
            pass
        else:
            raise AssertionError(function.__name__)
