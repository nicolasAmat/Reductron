
"""
z3 Interface

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

import logging as log
import sys
from subprocess import PIPE, Popen
from typing import Optional


class Z3:
    """ z3 interface.

    Note
    ----
    Uses SMT-LIB v2 format
    Standard: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf

    Dependency: https://github.com/Z3Prover/z3

    This class can easily be hacked to replace Z3
    by another SMT solver supporting the SMT-LIB format.

    Attributes
    ----------
    solver : Popen
        A z3 process.
    aborted : bool
        Aborted flag.
    debug : bool
        Debugging flag.
    """

    def __init__(self, debug: bool = False, timeout: int = 0) -> None:
        """ Initializer.

        Parameters
        ----------
        debug : bool, optional
            Debugging flag.
        timeout : int, optional
            Timeout of the solver.
        solver_pids : Queue of int, optional
            Queue of solver pids.
        """
        # Solver
        process = ['z3', '-in']
        if timeout:
            process.append('-T:{}'.format(timeout))
        self.solver: Popen = Popen(process, stdin=PIPE, stdout=PIPE)

        # Flags
        self.aborted: bool = False
        self.debug: bool = debug

    def kill(self) -> None:
        """" Kill the process.
        """
        self.solver.kill()

    def abort(self) -> None:
        """ Abort the solver.
        """
        log.warning("z3 process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

    def write(self, input: str, debug: bool = False) -> None:
        """ Write instructions to the standard input.

        Parameters
        ----------
        input : str 
            Input instructions.
        debug : bool
            Debugging flag.
        """
        if self.debug or debug:
            print(input)

        if input != "":
            try:
                self.solver.stdin.write(bytes(input, 'utf-8'))
            except BrokenPipeError:
                self.abort()

    def flush(self) -> None:
        """ Flush the standard input.
        """
        try:
            self.solver.stdin.flush()
        except BrokenPipeError:
            self.abort()

    def readline(self, debug: bool = False):
        """ Read a line from the standard output.

        Parameters
        ----------
        debug : bool, optional
            Debugging flag.

        Returns
        -------
        str
            Line read.
        """
        try:
            smt_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(smt_output)

        return smt_output

    def reset(self) -> None:
        """ Reset.

        Note
        ----
        Erase all assertions and declarations.
        """
        self.write("(reset)\n")

    def check_sat(self, input: str) -> Optional[bool]:
        """ Check the satisfiability of the current stack of z3.

        Parameters
        ----------
        input : str 
            Input query.

        Returns
        -------
        bool, optional
            Satisfiability of the current stack.
        """
        self.reset()
        self.write("(assert {})\n".format(input))
        self.write("(check-sat)\n")
        self.flush()

        sat = self.readline()

        if sat == 'sat':
            return True
        elif sat == 'unsat':
            return False
        else:
            self.abort()

        return None


def smt_and(constraints: list[str]) -> str:
    if not constraints:
        return "true"

    smt_input = ' '.join(constraints)

    if len(constraints) > 1:
        smt_input = '(and {})'.format(smt_input)

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
