#!/usr/bin/env python3
"""Independent finite checks for the partial-return 1011/1111 exclusion."""
import sys
sys.dont_write_bytecode = True
from verify_noncontracting import affine, replay


def indexed(n):
    if n == 0:
        return 1
    parent, column = divmod(n, 4)
    return 1 - indexed(parent) if column == 1 else 1


def main():
    bits = [1]
    for k in range(8):
        assert bits == [indexed(n) for n in range(4**k)]
        assert 5*sum(bits) == 4*4**k + (-1)**k
        if k < 7:
            bits = [x for b in bits for x in ([1, 0, 1, 1] if b else [1, 1, 1, 1])]
    assert bits[:4] == [1, 0, 1, 1]
    assert 3**4 > 2**5  # Exact supercritical comparison; no uniform chunks can contract.
    for k in range(7):
        size = 4**k
        r = sum(bits[:2*size])
        assert bits[:size] == bits[2*size:3*size]
        assert 5*r == 8*size - 3*(-1)**k
        assert 8*size-3 <= 5*r <= 8*size+3
        assert 13*size <= 5*(size+r)+3
        assert 5*r <= 8*size+3
        # The closing base comparison, without constructing doubly exponential powers.
        assert 2**13 == 8192 > 6561 == 3**8
    finite = bits[:81]
    r, c = affine(finite)
    modulus = 2**81
    witnesses = []
    for q in (1, 5):
        p = (-c*q * pow(3**r, -1, modulus)) % modulus
        for initial in (p, p-modulus):
            end = replay(initial, q, finite)
            assert replay(3*initial, 3*q, finite) == 3*end
            assert replay(-initial, -q, finite) == -end
            witnesses.append((initial, q, end))
    # A finite partial return is compatible with rational realization: 1 has 101.
    assert replay(1, 1, [1, 0, 1]) == 2
    print('1011/1111: literal levels 0..7, partial returns and signed balances PASS')
    print('Exact height ledger 8192>6561; signed/unreduced 81-bit prefixes PASS')
    for row in witnesses:
        print('finite witness:', *row)


if __name__ == '__main__':
    main()
