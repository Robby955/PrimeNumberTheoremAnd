"""Probe FKS2 Corollary 8 with the public theta rows.

This is a diagnostic for Table4Ext.allCells_trusted.  It evaluates the Lean
definitions of delta, mu_num, and eps_pi_num for a few small Table 4 rows using
the theta values printed in the public ancillary PDF.  It also evaluates the
first integer row where corollary_14_normalized can be converted to an Etheta
numerical bound by Etheta.classicalBound.to_numericalBound.

The integer public theta rows fail for early rows, but subdividing and reusing
the previous integer theta bound can already certify the first representative
rows numerically.  The remaining proof work is to turn that inherited-bound
pattern into Lean certificates and extend it across all Table 4 rows.

Requires: mpmath
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence

import mpmath as mp

mp.mp.dps = 80


# Public Table 1 theta values from the paper source for log x = 10, ..., 36.
VISIBLE_EPS_THETA = {
    10: mp.mpf("0.013139"),
    11: mp.mpf("0.0079693"),
    12: mp.mpf("0.0048336"),
    13: mp.mpf("0.0029318"),
    14: mp.mpf("0.0017782"),
    15: mp.mpf("0.0010786"),
    16: mp.mpf("0.00065416"),
    17: mp.mpf("0.00039677"),
    18: mp.mpf("0.00024065"),
    19: mp.mpf("0.00014597"),
    20: mp.mpf("8.8530e-5"),
    21: mp.mpf("5.3691e-5"),
    22: mp.mpf("3.2563e-5"),
    23: mp.mpf("1.9748e-5"),
    24: mp.mpf("1.1975e-5"),
    25: mp.mpf("7.2632e-6"),
    26: mp.mpf("4.4057e-6"),
    27: mp.mpf("2.6727e-6"),
    28: mp.mpf("1.6216e-6"),
    29: mp.mpf("9.8390e-7"),
    30: mp.mpf("5.9691e-7"),
    31: mp.mpf("3.6216e-7"),
    32: mp.mpf("2.1972e-7"),
    33: mp.mpf("1.3331e-7"),
    34: mp.mpf("8.0875e-8"),
    35: mp.mpf("4.9068e-8"),
    36: mp.mpf("2.9699e-8"),
}


# First rows of Table4ExtData_00.lean, as exact decimals.
TABLE4_EPS_PI = {
    10: mp.mpf("0.016251"),
    11: mp.mpf("0.0098536"),
    12: mp.mpf("0.0057149"),
    13: mp.mpf("0.0034755"),
    14: mp.mpf("0.0020222"),
    15: mp.mpf("0.0012356"),
    16: mp.mpf("0.0007503"),
    17: mp.mpf("0.00044264"),
}


def primes_upto(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n + 1 : p] = b"\x00" * (((n - start) // p) + 1)
    return [i for i, flag in enumerate(sieve) if flag]


def li_interval_from_2(x: mp.mpf) -> mp.mpf:
    """Lean's Li x is integral from 2 to x."""
    return mp.li(x) - mp.li(2)


_delta_cache: dict[int, mp.mpf] = {}


def delta_at_exp(log_x0: int) -> mp.mpf:
    """Lean FKS2.delta at x0 = exp(log_x0)."""
    if log_x0 in _delta_cache:
        return _delta_cache[log_x0]

    x0 = mp.e**log_x0
    primes = primes_upto(int(mp.floor(x0)))
    pi_x0 = mp.mpf(len(primes))
    theta_x0 = mp.fsum(mp.log(p) for p in primes)
    li_x0 = li_interval_from_2(x0)
    value = abs((pi_x0 - li_x0) / (x0 / mp.log(x0)) - (theta_x0 - x0) / x0)
    _delta_cache[log_x0] = value
    return value


def _key(x: mp.mpf | int | str) -> str:
    return mp.nstr(mp.mpf(x), 80)


_exp_cache: dict[str, mp.mpf] = {}
_li_cache: dict[str, mp.mpf] = {}


def exp_log_node(node: mp.mpf | int | str) -> mp.mpf:
    key = _key(node)
    if key not in _exp_cache:
        _exp_cache[key] = mp.e ** mp.mpf(key)
    return _exp_cache[key]


def li_at_log_node(node: mp.mpf | int | str) -> mp.mpf:
    key = _key(node)
    if key not in _li_cache:
        _li_cache[key] = li_interval_from_2(exp_log_node(key))
    return _li_cache[key]


def li_exp_interval(a: mp.mpf | int | str, b: mp.mpf | int | str) -> mp.mpf:
    return li_at_log_node(b) - li_at_log_node(a)


def mu_num_1(
    nodes: Sequence[mp.mpf],
    eps_theta: Callable[[mp.mpf], mp.mpf],
    log_x0: int,
    i: int,
) -> mp.mpf:
    x0 = mp.e**log_x0
    x1 = exp_log_node(nodes[i])
    x2 = exp_log_node(nodes[i + 1])
    eps_x1 = eps_theta(nodes[i])
    integral_sum = mp.fsum(
        eps_theta(nodes[k])
        * (
            li_exp_interval(nodes[k], nodes[k + 1])
            + exp_log_node(nodes[k]) / nodes[k]
            - exp_log_node(nodes[k + 1]) / nodes[k + 1]
        )
        for k in range(i)
    )
    return (
        (x0 * mp.log(x1)) / (eps_x1 * x1 * mp.log(x0)) * delta_at_exp(log_x0)
        + (mp.log(x1)) / (eps_x1 * x1) * integral_sum
        + (mp.log(x2) / x2)
        * (li_at_log_node(nodes[i + 1]) - x2 / nodes[i + 1] - li_at_log_node(nodes[i]) + x1 / nodes[i])
    )


def mu_num_2(
    nodes: Sequence[mp.mpf],
    eps_theta: Callable[[mp.mpf], mp.mpf],
    log_x0: int,
    i: int,
) -> mp.mpf:
    x0 = mp.e**log_x0
    x1 = exp_log_node(nodes[i])
    eps_x1 = eps_theta(nodes[i])
    integral_sum = mp.fsum(
        eps_theta(nodes[k])
        * (
            li_exp_interval(nodes[k], nodes[k + 1])
            + exp_log_node(nodes[k]) / nodes[k]
            - exp_log_node(nodes[k + 1]) / nodes[k + 1]
        )
        for k in range(i)
    )
    return (
        (x0 * mp.log(x1)) / (eps_x1 * x1 * mp.log(x0)) * delta_at_exp(log_x0)
        + (mp.log(x1)) / (eps_x1 * x1) * integral_sum
        + 1 / (mp.log(x1) + mp.log(mp.log(x1)) - 1)
    )


def eps_pi_num(
    nodes: Sequence[mp.mpf],
    eps_theta: Callable[[mp.mpf], mp.mpf],
    log_x0: int,
    i: int,
) -> mp.mpf:
    x1 = exp_log_node(nodes[i])
    x2 = exp_log_node(nodes[i + 1])
    mu = (
        mu_num_1(nodes, eps_theta, log_x0, i)
        if x2 <= x1 * mp.log(x1)
        else mu_num_2(nodes, eps_theta, log_x0, i)
    )
    return eps_theta(nodes[i]) * (1 + mu)


def eps_theta_visible(log_x: mp.mpf) -> mp.mpf:
    return VISIBLE_EPS_THETA[int(log_x)]


def eps_theta_inherited_visible(log_x: mp.mpf) -> mp.mpf:
    return VISIBLE_EPS_THETA[int(mp.floor(log_x))]


def eps_theta_classical_normalized(log_x: mp.mpf) -> mp.mpf:
    """corollary_14_normalized admissible bound at x = exp(log_x)."""
    b = mp.mpf(log_x)
    return mp.mpf("9.22023") * b**mp.mpf("1.5") * mp.e ** (-mp.mpf("0.8476") * mp.sqrt(b))


def integer_nodes(row: int, end: int = 36) -> list[mp.mpf]:
    return [mp.mpf(n) for n in range(row, end + 1)]


def uniform_nodes(row: int, denominator: int, end: int = 36) -> list[mp.mpf]:
    step = mp.mpf(1) / denominator
    return [mp.mpf(row) + step * j for j in range((end - row) * denominator + 1)]


def max_eps_pi_term(
    row: int,
    eps_theta: Callable[[mp.mpf], mp.mpf],
    nodes: Sequence[mp.mpf],
) -> tuple[int, mp.mpf, mp.mpf, mp.mpf]:
    values = [
        (i, nodes[i], nodes[i + 1], eps_pi_num(nodes, eps_theta, row, i))
        for i in range(len(nodes) - 1)
    ]
    return max(values, key=lambda item: item[3])


def report(row: int, label: str, eps_theta: Callable[[mp.mpf], mp.mpf], nodes: Sequence[mp.mpf]) -> None:
    i, left, right, value = max_eps_pi_term(row, eps_theta, nodes)
    target = TABLE4_EPS_PI[row]
    print(f"{label} row b={row}")
    print(f"  delta(exp({row})) = {mp.nstr(delta_at_exp(row), 30)}")
    print(f"  max term interval = [{left}, {right}] at i={i}")
    print(f"  max eps_pi_num = {mp.nstr(value, 30)}")
    print(f"  table eps = {mp.nstr(target, 30)}")
    print(f"  ratio = {mp.nstr(value / target, 30)}")
    print(f"  passes = {value <= target}")


def first_passing_denominator(row: int, denominators: Sequence[int]) -> tuple[int, mp.mpf] | None:
    target = TABLE4_EPS_PI[row]
    for denominator in denominators:
        _, _, _, value = max_eps_pi_term(
            row, eps_theta_inherited_visible, uniform_nodes(row, denominator)
        )
        if value <= target:
            return denominator, value / target
    return None


def report_denominator_search() -> None:
    print("visible theta inherited-grid search rows 10..17")
    for row in range(10, 18):
        found = first_passing_denominator(row, [1, 2, 3, 4, 5, 8, 10, 12, 16, 20])
        if found is None:
            print(f"  b={row}: no pass through denominator 20")
            continue
        denominator, ratio = found
        print(f"  b={row}: denominator {denominator}, ratio {mp.nstr(ratio, 12)}")


def main() -> None:
    threshold_log = (mp.mpf(3) / mp.mpf("0.8476")) ** 2
    print(f"classical-to-numeric threshold log = {mp.nstr(threshold_log, 30)}")
    print()
    report(10, "visible theta integer grid", eps_theta_visible, integer_nodes(10))
    print()
    report(10, "visible theta inherited quarter grid", eps_theta_inherited_visible, uniform_nodes(10, 4))
    print()
    report(13, "visible theta integer grid", eps_theta_visible, integer_nodes(13))
    print()
    report(13, "visible theta inherited half grid", eps_theta_inherited_visible, uniform_nodes(13, 2))
    print()
    report(13, "corollary_14_normalized theta", eps_theta_classical_normalized, integer_nodes(13))
    print()
    report_denominator_search()


if __name__ == "__main__":
    main()
