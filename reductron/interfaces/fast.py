
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

from reductron.ptio.ptnet import PetriNet, Transition, Sequence
from reductron.ptio.presburger import Presburger


def tau_star(ptnet: PetriNet, region: Presburger, debug: bool = False) -> list[list[Transition]]:
    """ Compute tau star

    Parameters
    ----------
    ptnet : str
        Net.
    region : str
        Region.

    Returns
    -------
    list of list of Transition
        List of sequences.
    """
    if not ptnet.silent_transitions:
        return []

    pnml_fp = tempfile.NamedTemporaryFile(suffix='.pnml')

    ndrio = Popen(["ndrio", '-NET', '-', '-pnml', pnml_fp.name], stdin=PIPE)

    ndrio.stdin.write(bytes(ptnet.silent_restriction(), 'utf-8'))
    ndrio.stdin.flush()
    ndrio.stdin.close()

    ndrio.wait()
    if ndrio.returncode:
        sys.exit("Error: ndrio failed!")
    
    xsltproc = run(['xsltproc', 'utils/pnml2fst.xslt', pnml_fp.name], stdout=PIPE)
    if xsltproc.returncode:
        sys.exit("Error: xsltproc failed!")

    fst = xsltproc.stdout.decode('utf-8').splitlines()

    var_index, region_index = None, None
    for index, line in enumerate(fst):
        if 'var ' in line:
            var_index = index
        if ' Region init :=' in line:
            region_index = index
            break

    if not (var_index and region_index):
        sys.exit("Error: xsltproc failed!")

    fst[var_index] = fst[var_index].replace(';', '') + ', ' + ', '.join(region.fast_variables()) + ';'

    fst[region_index] = ' Region init := {{{} && state=marking}};'.format(region.fast())

    if debug:
        print('\n'.join(fst))

    fast_fp = tempfile.NamedTemporaryFile(suffix='.fst', mode="w")
    fast_fp.write('\n'.join(fst))
    fast_fp.flush()

    os.environ['FAST_DEFAULT_ENGINE'] = 'prestaf'
    fast = run(['fast', fast_fp.name], stderr=PIPE)
    if fast.returncode:
        sys.exit("Error: fast failed!")

    fast_fp.close()

    sequences, counter = [], 0
    for line in fast.stderr.decode('utf-8').splitlines():
        
        if debug:
            print(line)
        
        if 'OK !' in line:
            fast_sequences = line.split(' ')[2].replace('(', '').replace(')', '').split('+')
            for fast_sub_sequence in fast_sequences:
                sequences.append(Sequence(ptnet, "tau{}".format(counter), [ptnet.transitions[tr] for tr in fast_sub_sequence.split('.')]))
            counter += 1
    
    return sequences
