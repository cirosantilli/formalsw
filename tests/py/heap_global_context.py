TABLE: dict[int, int] = {}


def read(key: int) -> int:
    """
    @formalsw: Returns
    """
    return TABLE.get(key, 0)


def forward(key: int) -> int:
    """
    @formalsw: Requires(len(TABLE) >= 0)
    @formalsw: Returns
    @formalsw: Equiv(read)
    """
    return read(key)


def update(key: int, value: int) -> int:
    """
    @formalsw: Returns
    """
    TABLE[key] = value
    return read(key)
