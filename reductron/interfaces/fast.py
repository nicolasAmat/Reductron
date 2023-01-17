
"""
Fast Interface

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

from subprocess import PIPE, Popen, run
import tempfile
import sys
import os

from reductron.ptio.ptnet import PetriNet, Transition
from reductron.ptio.presburger import Presburger


def tau_star(net: PetriNet, region: Presburger) -> list[list[Transition]]:
    """ Compute tau star

    Parameters
    ----------
    net : str
        Net.
    region : str
        Region.

    Returns
    -------
    list of list of Transition
        List of sequences.
    """
    if not net.silent_transitions:
        return []

    pnml_fp = tempfile.NamedTemporaryFile(suffix='.pnml')

    ndrio = Popen(["ndrio", '-NET', '-', '-pnml', pnml_fp.name], stdin=PIPE)

    ndrio.stdin.write(bytes(net.silent_restriction(), 'utf-8'))
    ndrio.stdin.flush()
    ndrio.stdin.close()

    ndrio.wait()
    if ndrio.returncode:
        sys.exit("Error: ndrio failed!")
    
    xsltproc = run(['xsltproc', 'utils/pnml2fst.xslt', pnml_fp.name], stdout=PIPE)
    if xsltproc.returncode:
        sys.exit("Error: xsltproc failed!")

    fst = xsltproc.stdout.decode('utf-8').splitlines()

    region_index = None
    for index, line in enumerate(fst):
        if ' Region init :=' in line:
            region_index = index
            break

    if not region_index:
        sys.exit("Error: xsltproc failed!")

    fst[index] = ' Region init := {{{} && state=marking}};'.format(region.fast())

    fast_fp = tempfile.NamedTemporaryFile(suffix='.fst', mode="w")
    fast_fp.write('\n'.join(fst))
    fast_fp.flush()

    os.environ['FAST_DEFAULT_ENGINE'] = 'prestaf'
    fast = run(['fast', fast_fp.name], stderr=PIPE)
    if fast.returncode:
        sys.exit("Error: fast failed!")

    fast_fp.close()

    transitions = []

    for line in fast.stderr.decode('utf-8').splitlines():
        if 'OK !' in line:
            transitions.append([net.transitions[line.split(' ')[2]]])

    return transitions

