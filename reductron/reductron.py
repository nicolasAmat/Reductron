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


def smt_forall(declaration: str, constraint: str):
    return "(forall ({}) {})".format(declaration, constraint)


def smt_exists(declaration: str, constraint: str):
    return "(exists ({}) {})".format(declaration, constraint)


def smt_imply(left, right):
    return "(=> {} {})".format(left, right)


def smt_equiv(left, right):
    return smt_and([smt_imply(left, right), smt_imply(right, left)])



def check_silent_reachability_set(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Polyhedron, tau_star: list[Sequence]) -> bool:
    """ Check.
    """
    smt_input = ""

    k_max = len(tau_star)

    left_equiv = smt_exists(e.smtlib_declare(k1=k_max, common=k_max, exclude_initial=True), 
                            smt_and([e.smtlib(k1=k_max, common=k_max), c2.smtlib()]))
    
    right_equiv = smt_exists(''.join([c1.smtlib_declare(k=k) for k in range(k_max)]), 
                              smt_and([c1.smtlib(0)] + [sequence.smtlib(k) for k, sequence in enumerate(tau_star)]))
    
    smt_input = smt_forall(c1.smtlib_declare(k_max), smt_equiv(left_equiv, right_equiv))

    return solver.check_sat(smt_input)

def core_1(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Polyhedron) -> bool:
    """ Check (CORE 1)

        \forall p1. (C1(p1) \implies \exists p2 x. E(p1, p2, x) /\ C2(P2))
    """
    left_implies = c1.smtlib()
    right_implies = smt_exists(e.smtlib_declare(exclude_initial=True), smt_and([e.smtlib(), c2.smtlib()]))

    smt_input = smt_forall(n1.smtlib_declare_places(), smt_imply(left_implies, right_implies))

    return solver.check_sat(smt_input)


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

    check_silent_reachability_set(solver, n1, c1, n2, c2, e, tau1_star) 

    print("> Check that (N2, C2) is a strong E-abstraction of (N1, C1):")
    verdict = core_1(solver, n1, c1, n2, c2, e)
    print("(CORE 1):", verdict)    

    print()

    print("> Check that (N1, C1) is a strong E-abstraction of (N2, C2):")
    verdict = core_1(solver, n2, c2, n1, c1, e)
    print("(CORE 1):", verdict)    

        

if __name__ == '__main__':
    main()

