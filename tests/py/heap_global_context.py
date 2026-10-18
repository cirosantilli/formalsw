TABLE: dict[int, int] = {}


def read(key: int) -> int:
    return TABLE.get(key, 0)


def forward(key: int) -> int:
    return read(key)


def update(key: int, value: int) -> int:
    TABLE[key] = value
    return read(key)
