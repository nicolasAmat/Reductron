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

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "1.0"

import argparse
import logging as log
import time
from typing import Optional

from reductron.ptio.ptnet import PetriNet, Transition
from reductron.ptio.presburger import Presburger
from reductron.interfaces.z3 import Z3
from reductron.interfaces.fast import tau_star


def smt_and(l):
    smt_input = ' '.join(l)
    if len(l) > 1:
        smt_input = '(and {})'.format(smt_input)
    return smt_input


def smt_or(l):
    smt_input = ' '.join(l)
    if len(l) > 1:
        smt_input = '(or {})'.format(smt_input)
    return smt_input


def smt_non_negative(l, k=None):
    smt_input = ''
    if l:
        smt_input = smt_and(['(>= {} 0)'.format(elem.smtlib(k)) for elem in l])
    return smt_input


def smt_list(l, k=None):
    if l:
        return '(' + ' '.join(map(lambda elem: "({} Int)".format(elem.smtlib(k)), l)) + ')'
    return '()'


def smt_forall(l, constraint):
    return "(forall {} {})".format(smt_list(l), constraint)


def smt_exists(l, constraint):
    return "(exists {} {})".format(smt_list(l), constraint)


def smt_imply(left, right):
    return "(=> {} {})".format(left, right)


def smt_assert(constraint):
    return "(assert {})".format(constraint)


def smt_silent_reachability_set(n: PetriNet, c: Presburger, e: Presburger, k: Optional[int] = None) -> str:
    # TODO: Use k
    return smt_exists(set(n.places.values()) | set(e.additional_vars.values()), smt_and([e.smtlib(), c.smtlib()]))

def smt_saturated_sequence():
    pass


def check_silent_reachability_set(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Presburger, tau_star: list[list[Transition]]) -> bool:
    smt_input = ""

    k_max = len(tau_star)

    left_equiv = smt_silent_reachability_set(n2, c2, e, k_max)

    variables = ["k_{}".format(i) for i in range(k_max)] + [pl.smtlib(k) for pl in n1.places.values() for k in range(k_max)]
    saturated_sequences = [smt_saturated_sequence(sequence, k) for k, sequence in enumerate(tau_star)]
    right_equiv = "(exists ({}) {})".format(' '.join(variables), smt_and([c1.smtlib(0)] + saturated_sequences))


    solver.reset()
    solver.write(smt_input)

    return solver.check_sat()


def core_1(solver: Z3, n1: PetriNet, c1: Presburger, n2: PetriNet, c2: Presburger, e: Presburger) -> bool:
    left_imply = smt_and([smt_non_negative(n1.places.values()), c1.smtlib()])
    
    variables = set(n2.places.values()) | set(e.additional_vars.values())
    right_imply = smt_exists(variables, smt_and([smt_non_negative(variables), e.smtlib(), c2.smtlib()]))
    
    smt_input = smt_assert(smt_forall(n1.places.values(), smt_imply(left_imply, right_imply)))
    
    solver.reset()
    solver.write(smt_input)
    
    return solver.check_sat()




def main():
    """ Main function.
    """
    # Start time
    start_time = time.time()

    # Arguments parser
    parser = argparse.ArgumentParser(
        description='Reductron: Automated Polyhedral Abstraction Prover')

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
    c1 = Presburger(n1.places.keys(), "C1")
    c1.parse_coherency_constraint(results.initial_net)
    log.info("C1:")
    log.info("---")
    log.info(c1)
    log.info("")

    c2 = Presburger(n2.places.keys(), "C2")
    c2.parse_coherency_constraint(results.reduced_net)
    log.info("C2:")
    log.info("---")
    log.info(c2)
    log.info("")

    # Parse system of reductions E
    e = Presburger(n1.places.keys() | n2.places.keys(), "E")
    e.parse_reduction_system(results.reduced_net)
    log.info("E:")
    log.info("--")
    log.info(e)
    log.info("")

    # Compute tau*
    tau1_star = tau_star(n1, c1)
    tau2_star = tau_star(n2, c2)

    # Instantiate a SMT-solver
    solver = Z3(results.debug)

    print("> Check that (N2, C2) is a strong E-abstraction of (N1, C1):")
    verdict = core_1(solver, n1, c1, n2, c2, e)
    print("(CORE 1):", verdict)    

    print()

    print("> Check that (N1, C1) is a strong E-abstraction of (N2, C2):")
    verdict = core_1(solver, n2, c2, n1, c1, e)
    print("(CORE 1):", verdict)    


    # Change nets in presbuger to free-variables

    # Check transitions

    # ndrio net -> pnml
    # xsltproc pnml -> fast + region

    # Call fast
    # Check E /\ C1 equiv fast
        
    

if __name__ == '__main__':
    main()

