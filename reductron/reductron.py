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


def smt_and(constraints: list[str]):
    if not constraints:
        return "true"

    smt_input = ' '.join(constraints)

    if len(constraints) > 1:
        smt_input = '(and {})'.format(smt_input)

    return smt_input


def smt_or(constraints: list[str]):
    if not constraints:
        return "false"

    smt_input = ' '.join(constraints)

    if len(constraints) > 1:
        smt_input = '(or {})'.format(smt_input)

    return smt_input

def smt_forall(declaration: list[str], constraint: str):
    smt_declaration = ' '.join(map(lambda var: "({} Int)".format(var), declaration))
    smt_non_negative = smt_and(['(>= {} 0)'.format(var) for var in declaration])
    return "(forall ({}) {})".format(smt_declaration, smt_imply(smt_non_negative, constraint))


def smt_exists(declaration: list[str], constraint: str):
    smt_declaration = ' '.join(map(lambda var: "({} Int)".format(var), declaration))
    smt_non_negative = smt_and(['(>= {} 0)'.format(var) for var in declaration])
    return "(exists ({}) {})".format(smt_declaration, smt_and([smt_non_negative, constraint]))


def smt_imply(left, right):
    return "(=> {} {})".format(left, right)


def smt_equiv(left, right):
    return smt_and([smt_imply(left, right), smt_imply(right, left)])


def check_silent_reachability_set(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Polyhedron, tau_star: list[Sequence], on_reduced: bool = False) -> bool:
    """ Check the silent reachability set of N1 (resp N2) from Fast is conform to E /\ C2 (resp E /\ C1).

        forall p1^k. ((exists p2. E(p1, p2) /\ C(2)) <=> (exists p1^0 ... p^k-1. C1(p1^0) /\ tau_star[0](p1^0, p1^1) /\ ... /\ tau_star[k-1](p1^k-1, p1^k))
    """
    k_max = len(tau_star)

    if not on_reduced:
        k1 = k_max
        k2 = None
        kx = None
        exclude_initial = True
        exclude_reduced = False
    else:
        k1 = None
        k2 = k_max
        kx = None
        exclude_initial = False
        exclude_reduced = True

    left_equiv = smt_exists(e.smtlib_declare(k1=k1, k2=k2, kx=kx, common=k_max, exclude_initial=exclude_initial, exclude_reduced=exclude_reduced),
                            smt_and([e.smtlib(k1=k1, k2=k2, kx=kx, common=k_max), c2.smtlib()]))
    
    if tau_star:
        right_equiv = smt_exists([var for k in range(k_max) for var in c1.smtlib_declare(k=k)], 
                                smt_and([c1.smtlib(0)] + [sequence.smtlib(k) for k, sequence in enumerate(tau_star)]))
    else:
        right_equiv = c1.smtlib(k=k_max)

    smt_input = smt_forall(c1.smtlib_declare(k_max), smt_equiv(left_equiv, right_equiv))

    return solver.check_sat(smt_input)

def core_1(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Polyhedron, on_reduced: bool = False) -> bool:
    """ Check (CORE 1)

        forall p1. (C1(p1) => exists p2 x. E(p1, p2, x) /\ C2(P2))
    """
    if not on_reduced:
        exclude_initial = True
        exclude_reduced = False
    else:
        exclude_initial = False
        exclude_reduced = True

    left_implies = c1.smtlib()
    right_implies = smt_exists(e.smtlib_declare(exclude_initial=exclude_initial, exclude_reduced=exclude_reduced), smt_and([e.smtlib(), c2.smtlib()]))

    smt_input = smt_forall(c1.smtlib_declare(), smt_imply(left_implies, right_implies))

    return solver.check_sat(smt_input)


# def core_2(solver: Z3, n1: PetriNet, c1: Presburger) -> bool:
#     """ Check (CORE 2)

#         forall p1 p1' l. (C1(p1) /\ T^(C_1)(p1, p1', l) => exists p1'' T^(C1)(p1, p1'', l) /\ C1(p1'') /\ tau*(p1'', p1'))
#     """
    
#     left_implies = c1.smtlib()
#     right_implies = smt_exists(e.smtlib_declare(exclude_initial=exclude_initial, exclude_reduced=exclude_reduced), smt_and([e.smtlib(), c2.smtlib()]))

#     smt_input = smt_forall(c1.smtlib_declare(), smt_imply(left_implies, right_implies))

#     return solver.check_sat(smt_input)



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
    tau1_star = tau_star(n1, c1)
    log.info("tau1*:")
    log.info("------")
    log.info(''.join(map(str, tau1_star)))
    log.info("")

    tau2_star = tau_star(n2, c2)
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
    verdict = core_1(solver, n1, c1, n2, c2, e)
    print("(CORE 1):", core_1(solver, n1, c1, n2, c2, e))
    # print("(CORE 2):", core_2(solver, n1, c1))

    print()

    print("> Check that (N1, C1) is a strong E-abstraction of (N2, C2):")
    verdict = core_1(solver, n2, c2, n1, c1, e, on_reduced=True)
    print("(CORE 1):", core_1(solver, n2, c2, n1, c1, e, on_reduced=True))
    # print("(CORE 2):", core_2(solver, n2, c2))



if __name__ == '__main__':
    main()

