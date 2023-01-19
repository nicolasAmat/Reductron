#!/usr/bin/env python3

"""
Reductron: Automated Polyhedral Abstraction Prover

This file is part of Reductron.

Reductron is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Reductron is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Reductron. If not, see <https://www.gnu.org/licenses/>.
"""
from __future__ import annotations
__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "1.0"

import argparse
import logging as log
import time
from typing import Optional

from reductron.ptio.ptnet import PetriNet, Sequence
from reductron.ptio.presburger import Presburger
from reductron.interfaces.z3 import Z3
from reductron.interfaces.fast import tau_star
from reductron.ptio.polyhedron import Polyhedron


def smt_and(constraints: list[str]) -> str:
    if not constraints:
        return "true"

    smt_input = ' '.join(constraints)

    if len(constraints) > 1:
        smt_input = '(and {})'.format(smt_input)

    return smt_input


def smt_or(constraints: list[str]) -> str:
    if not constraints:
        return "false"

    smt_input = ' '.join(constraints)

    if len(constraints) > 1:
        smt_input = '(or {})'.format(smt_input)

    return smt_input

def smt_forall(declaration: list[str], constraint: str) -> str:
    if not declaration:
        return constraint
    smt_declaration = ' '.join(map(lambda var: "({} Int)".format(var), declaration))
    smt_non_negative = smt_and(['(>= {} 0)'.format(var) for var in declaration])
    return "(forall ({}) {})".format(smt_declaration, smt_imply(smt_non_negative, constraint))


def smt_exists(declaration: list[str], constraint: str) -> str:
    if not declaration:
        return constraint
    smt_declaration = ' '.join(map(lambda var: "({} Int)".format(var), declaration))
    smt_non_negative = smt_and(['(>= {} 0)'.format(var) for var in declaration])
    return "(exists ({}) {})".format(smt_declaration, smt_and([smt_non_negative, constraint]))


def smt_imply(left: str, right: str) -> str:
    return "(=> {} {})".format(left, right)


def smt_equiv(left: str, right: str) -> str:
    return smt_and([smt_imply(left, right), smt_imply(right, left)])


def smt_tau_star(e: Polyhedron, k, k_prime, on_reduced: bool = False) -> str:
    """ tau*(N, C)(k, k_prime)

        exists p2. (E(p1, p2) /\ E(p1', p2))
    """
    if not on_reduced:
        k1, k2, common = k, None, k
        k1_prime, k2_prime, common_prime = k_prime, None, k_prime
    else:
        k1, k2, common = None, k, k
        k1_prime, k2_prime, common_prime = None, k_prime, k_prime

    return smt_exists(e.smtlib_declare(exclude_initial=not on_reduced, exclude_reduced=on_reduced), smt_and([e.smtlib(k1=k1, k2=k2, common=common), e.smtlib(k1=k1_prime, k2=k2_prime, common=common_prime)]))


def smt_hat_t(n1: PetriNet, c1: Presburger, e: Polyhedron, k: int, k_prime: int, l: Optional[str] = None, on_reduced: bool = False) -> str:
    """ T^(N, C)(k, k_prime)

        exists p1''. tau*(p1, p1'') /\ T(p'', p')
    """
    k_intermediate = k
    while k_intermediate == k or k_intermediate == k_prime:
        k_intermediate += 1
    
    return smt_exists(c1.smtlib_declare(k_intermediate), smt_and([smt_tau_star(e, k, k_intermediate, on_reduced=on_reduced), n1.smtlib_transition_relation(k_intermediate, k_prime, l=l)]))


def check_silent_reachability_set(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Polyhedron, tau_star: list[Sequence], on_reduced: bool = False) -> bool:
    """ Check the silent reachability set of N1 (resp N2) from Fast is equivalent to E /\ C2 (resp E /\ C1).

        forall p1. p1^k. C1(p1) => ((exists p2. E(p1^k, p2) /\ C2(p2)) <=> (exists p1^0 ... p^k-1. tau_star[0](p1^0, p1^1) /\ ... /\ tau_star[k-1](p1^k-1, p1^k))

        F  := forall p1. p1^k. F1
        F1 := C1(p1) => F2
        F2 :=  F3 <=> F4
        F3 := exists p2. F5
        F4 := exists p1^0 ... p^k-1. F6
        F5 := E(p1^k, p2) /\ C2(p2)
        F6 := tau_star[0](p1^0, p1^1) /\ ... /\ tau_star[k-1](p1^k-1, p1^k)
    """
    k_max = len(tau_star)

    if k_max == 0:
        return True

    if not on_reduced:
        k1, k2, common = k_max, None, k_max
    else:
        k1, k2, common = None, k_max, k_max

    f6 = smt_and([sequence.smtlib(k) for k, sequence in enumerate(tau_star)])
    
    f5 = smt_and([e.smtlib(k1=0, k2=k2, common=common), e.smtlib(k1=k1, k2=k2, common=common), c2.smtlib()])

    f4 = smt_exists([var for k in range(1, k_max) for var in c1.smtlib_declare(k=k)], f6)
    
    f3 = smt_exists(e.smtlib_declare(k1=k1, k2=k2, common=common, exclude_initial=not on_reduced, exclude_reduced=on_reduced), f5)

    f2 = smt_equiv(f3, f4)

    f1 = smt_imply(c1.smtlib(0), f2)

    f = smt_forall(c1.smtlib_declare(0) + c1.smtlib_declare(k_max), f1)

    return solver.check_sat(f)


def core_1(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Polyhedron, on_reduced: bool = False) -> bool:
    """ Check (CORE 1)

        forall p1. C1(p1) => exists p2. E(p1, p2) /\ C2(P2)

        F  := forall p1. F1
        F1 := F2 => F3
        F2 := C1(p1)
        F3 := exists p2. F4
        F4 := E(p1, p2) /\ C2(P2)
    """

    f4 = smt_and([e.smtlib(), c2.smtlib()])

    f3 = smt_exists(e.smtlib_declare(exclude_initial=not on_reduced, exclude_reduced=on_reduced), f4)

    f2 = c1.smtlib()

    f1 = smt_imply(f2, f3)

    f = smt_forall(c1.smtlib_declare(), f1)

    return solver.check_sat(f)


def core_2(solver: Z3, n1: PetriNet, c1: Presburger, e: Polyhedron, n2: PetriNet, c2: Presburger, on_reduced: bool = False) -> bool:
    """ Check (CORE 2)

        forall p1 p1' l. C1(p1) /\ T^(C_1)(p1, p1', l) => exists p1'' T^(C1)(p1, p1'', l) /\ C1(p1'') /\ tau*(p1'', p1')

        F  := forall p1 p1' l. F1
        F1 :=  F2 => F3
        F2 := C1(p1) /\ T^(C_1)(p1, p1', l)
        F3 := exists p1''. F4
        F4 := T^(C1)(p1, p1'', l) /\ C1(p1'') /\ tau*(p1'', p1')
    """
    l, k, k_prime, k_hiatus = "l", 0, 1, 2

    f4 = smt_and([smt_hat_t(n1, c1, e, k, k_hiatus, l, on_reduced=on_reduced), c1.smtlib(k_hiatus), smt_tau_star(e, k_hiatus, k_prime, on_reduced=on_reduced)])

    f3 = smt_exists(c1.smtlib_declare(k_hiatus), f4)

    f2 = smt_and([c1.smtlib(k), smt_hat_t(n1, c1, e, k, k_prime, l, on_reduced=on_reduced)])

    f1 = smt_imply(f2, f3)

    f = smt_forall(c1.smtlib_declare(k) + c1.smtlib_declare(k_prime) + [l], f1)

    return solver.check_sat(f)


def core_3(solver: Z3, n1: PetriNet, c1: Presburger, e: Polyhedron, n2: PetriNet, c2: Presburger, on_reduced: bool = False) -> bool:
    """ Check (CORE 3)

        forall p1 p2 p1'. C1(p1) /\ C2(p2) /\ E(p1, p2) /\ T(C1)(p1, p1', l) => exists p2'. C2(p2') /\ E(p1', p2') /\ T(C2)(p2, p2', l)

        F  := forall p1 p2. (F1 => F2)
        F1 := C1(p1) /\ C2(p2) /\ E(p1, p2) /\ T(C1)(p1, p1', l)
        F2 = exists p2'. F3
        F3 := C2(p2') /\ E(p1', p2') /\ T(C2)(p2, p2', l)
    """
    l, k, k_prime = "l", 0, 1
    
    f3 = smt_and([c2.smtlib(k_prime), e.smtlib(k1=k_prime, k2=k_prime, common=k_prime), smt_hat_t(n2, c2, e, k, k_prime, l, on_reduced=not on_reduced)])
    
    f2 = smt_exists(e.smtlib_declare(k1=k_prime, k2=k_prime, common=k_prime, exclude_initial=not on_reduced, exclude_reduced=on_reduced), f3)
    
    f1 = smt_and([c1.smtlib(k), c2.smtlib(k), e.smtlib(k1=k, k2=k, common=k), smt_hat_t(n1, c1, e, k, k_prime, l, on_reduced=on_reduced)])
    
    f = smt_forall(e.smtlib_declare(k1=k, k2=k, common=k) + c1.smtlib_declare(k_prime) + ["l"], smt_imply(f1, f2))

    return solver.check_sat(f)


def core_4(solver: Z3, n1: PetriNet, c1: Presburger, e: Polyhedron, n2: PetriNet, c2: Presburger, on_reduced: bool = False) -> bool:
    """ Check (CORE 4)

        forall p1 p2 p1'. C1(p1) /\ C2(p2) /\ E(p1, p2) /\ tau*(p1, p1') => E(p1', p2)

        F  := forall p1 p2 p1'. F1
        F1 := F2 => F3
        F2 := C1(p1) /\ C2(p2) /\ E(p1, p2) /\ tau*(p1, p1')
        F3 := E(p1', p2)
    """
    k, k_prime = 0, 1

    if not on_reduced:
        k1_prime, k2_prime, common_prime = k_prime, k, k_prime
    else:
        k1_prime, k2_prime, common_prime = k, k_prime, k_prime
    
    f3 = e.smtlib(k1=k1_prime, k2=k2_prime, common=common_prime)
    
    f2 = smt_and([c1.smtlib(k), c2.smtlib(k), e.smtlib(k1=k, k2=k, common=k), smt_tau_star(e, k, k_prime, on_reduced=on_reduced)])

    f1 = smt_imply(f2, f3)

    f = smt_forall(e.smtlib_declare(k1=k, k2=k, common=k) + c1.smtlib_declare(k_prime), f1)

    return solver.check_sat(f)


def core_5(solver: Z3, n1: PetriNet, c1: Presburger, e: Polyhedron, n2: PetriNet, c2: Presburger, on_reduced: bool = False) -> bool:
    """ Check (CORE 5)

        forall p1 p2 p1'. C1(p1) /\ C2(p2) /\ E(p1, p2) /\ E(p1', p2) => tau*(p1, p1')

        F := forall p1 p2 p1'. F1
        F1 := F2 => F3
        F2 := C1(p1) /\ C2(p2) /\ E(p1, p2) /\ E(p1', p2)
        F3 := tau*(p1, p1')
    """
    k, k_prime = 0, 1

    if not on_reduced:
        k1_prime, k2_prime, common_prime = k_prime, k, k_prime
    else:
        k1_prime, k2_prime, common_prime = k, k_prime, k_prime
    
    f3 = smt_tau_star(e, k, k_prime, on_reduced=on_reduced)
    
    f2 = smt_and([c1.smtlib(k), c2.smtlib(k), e.smtlib(k1=k, k2=k, common=k), e.smtlib(k1=k1_prime, k2=k2_prime, common=common_prime)])

    f1 = smt_imply(f2, f3)

    f = smt_forall(e.smtlib_declare(k1=k, k2=k, common=k) + e.smtlib_declare(k1=k1_prime, k2=k2_prime, common=common_prime, exclude_initial=on_reduced, exclude_reduced=not on_reduced), f1)

    return solver.check_sat(f)


def main():
    """ Main function.
    """
    # Start time
    start_time = time.time()

    # Arguments parser
    parser = argparse.ArgumentParser(description='Reductron - Automated Polyhedral Abstraction Prover')

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 1.0',
                        help="show the version number and exit")

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        help="increase output verbosity")

    parser.add_argument('--debug',
                        action='store_true',
                        help="print the SMT-LIB input/output")

    parser.add_argument('-i', '--initial-net',
                        metavar='initial',
                        type=str,
                        required=True,
                        help='path to the initial Petri Net (.net format)')

    parser.add_argument('-r', '--reduced-net',
                        metavar='reduced',
                        type=str,
                        required=True,
                        help='path to the reduced Petri Net (.net format)')

    parser.add_argument('--show-time',
                        action='store_true',
                        help="show the execution time")

    results = parser.parse_args()

    # Set the verbose level
    if results.verbose:
        log.basicConfig(format="%(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(message)s")

    # Parse nets N1 and N2
    n1 = PetriNet(results.initial_net)
    log.info("N1:")
    log.info("---")
    log.info(n1)

    n2 = PetriNet(results.reduced_net)
    log.info("N2:")
    log.info("---")
    log.info(n2)

    # Parse constraints C1 and C2
    c1 = Presburger(results.initial_net, n1.places.keys(), "C1")
    log.info("C1:")
    log.info("---")
    log.info(c1)
    log.info("")

    c2 = Presburger(results.reduced_net, n2.places.keys(), "C2")
    log.info("C2:")
    log.info("---")
    log.info(c2)
    log.info("")

    # Parse system of reductions E
    e = Polyhedron(results.reduced_net, n1.places.keys(), n2.places.keys())
    log.info("E:")
    log.info("--")
    log.info(e)
    log.info("")

    # Compute tau*
    tau1_star = tau_star(n1, c1, results.debug)
    log.info("tau1*:")
    log.info("------")
    log.info(''.join(map(str, tau1_star)))
    log.info("")

    tau2_star = tau_star(n2, c2, results.debug)
    log.info("tau2*:")
    log.info("------")
    log.info(''.join(map(str, tau2_star)))
    log.info("")

    # Instantiate a SMT-solver
    solver = Z3(results.debug)

    print("> Check the silent reachability set of N1 from Fast is conform to E /\ C2")
    print("(Conform):", check_silent_reachability_set(solver, n1, c1, n2, c2, e, tau1_star) )

    print()

    print("> Check the silent reachability set of N2 from Fast is conform to E /\ C1")
    print("(Conform):", check_silent_reachability_set(solver, n2, c2, n1, c1, e, tau2_star, on_reduced=True) )

    print()

    print("> Check that (N2, C2) is a strong E-abstraction of (N1, C1):")
    print("(CORE 1):", core_1(solver, n1, c1, n2, c2, e))
    print("(CORE 2):", core_2(solver, n1, c1, e, n2, c2))
    print("(CORE 3):", core_3(solver, n1, c1, e, n2, c2))
    print("(CORE 4):", core_4(solver, n1, c1, e, n2, c2))
    print("(CORE 5):", core_5(solver, n1, c1, e, n2, c2))

    print()

    print("> Check that (N1, C1) is a strong E-abstraction of (N2, C2):")
    print("(CORE 1):", core_1(solver, n2, c2, n1, c1, e, on_reduced=True))
    print("(CORE 2):", core_2(solver, n2, c2, e, n1, c1, on_reduced=True))
    print("(CORE 3):", core_3(solver, n2, c2, e, n1, c1, on_reduced=True))
    print("(CORE 4):", core_4(solver, n2, c2, e, n1, c1, on_reduced=True))
    print("(CORE 5):", core_5(solver, n2, c2, e, n1, c1, on_reduced=True))


if __name__ == '__main__':
    main()

